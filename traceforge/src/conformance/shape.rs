//! Declared value shapes: the type information the summary encoder needs to
//! tell an empty set from an empty map.
//!
//! The encoder works from a value's derived `Debug` text, where an empty
//! `HashSet` and an empty `HashMap` both print `{}`. A non-empty map is refused
//! from its text alone (`k: v`), but `{}` is ambiguous. A message type that
//! implements [`SummaryShape`] (normally `#[derive(SummaryShape)]`) and is
//! declared with [`declare`] before the run tells the encoder, position by
//! position, whether a `{}` is a set (encoded `[]`) or a map (refused, as JMC
//! refuses every map).
//!
//! The rule is refuse-unless-declared: a `{}` in a value of an undeclared type,
//! or at a position the declared shape does not cover, is refused. A default
//! that assumed "no maps" would encode an empty map as an empty set, the silent
//! acceptance the format forbids; a program that sends no `{}` needs no
//! declaration, so existing programs keep building and exporting unchanged.

use std::any::TypeId;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::rc::Rc;
use std::sync::{Arc, OnceLock, RwLock};

/// A field's shape, computed when the encoder reaches it (so recursive types
/// are finite).
pub type ShapeFn = fn() -> Shape;

/// How a type prints in derived `Debug`, as far as the encoder needs it.
#[derive(Clone)]
pub enum Shape {
    /// An integer, a boolean, a string, a character: no braces inside.
    Scalar,
    /// A process identity.
    Thread,
    /// `[a, b]`: a `Vec`, an array, a slice, a `VecDeque`.
    List(ShapeFn),
    /// `{a, b}`: a `HashSet` or `BTreeSet`.
    Set(ShapeFn),
    /// `{k: v}`: a `HashMap` or `BTreeMap`; refused, also when empty.
    Map,
    /// A struct, tuple struct or unit struct: its name and its fields in order.
    Record(&'static str, Vec<ShapeFn>),
    /// An enum: per variant, its name and its fields in order.
    Variants(Vec<(&'static str, Vec<ShapeFn>)>),
    /// Not described: a `{}` inside is refused.
    Opaque,
}

/// A type whose shape the encoder can follow. Derive it with
/// `#[derive(SummaryShape)]`; every field's type must implement it too (the
/// standard collections, integers, `bool`, `String`, `Option`, `Result`,
/// `Box`, `Rc`, `Arc` and `ThreadId` do).
pub trait SummaryShape {
    fn shape() -> Shape;
}

fn shape_table() -> &'static RwLock<HashMap<TypeId, ShapeFn>> {
    static R: OnceLock<RwLock<HashMap<TypeId, ShapeFn>>> = OnceLock::new();
    R.get_or_init(Default::default)
}

/// Declares the message type `T` to the encoder: a `{}` in a value of type `T`
/// is then a set or a map as `T`'s shape says. Call it once per message type,
/// before the run (declaring twice is harmless).
pub fn declare<T: SummaryShape + 'static>() {
    shape_table().write().expect("conformance: the shape registry is poisoned").insert(TypeId::of::<T>(), T::shape);
}

/// The declared shape of the type `id`, or [`Shape::Opaque`].
pub(crate) fn declared(id: TypeId) -> Shape {
    match shape_table().read().expect("conformance: the shape registry is poisoned").get(&id) {
        Some(f) => f(),
        None => Shape::Opaque,
    }
}

macro_rules! scalar {
    ($($t:ty),*) => { $(impl SummaryShape for $t { fn shape() -> Shape { Shape::Scalar } })* };
}
scalar!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize, bool, char, String, str);

impl SummaryShape for crate::thread::ThreadId {
    fn shape() -> Shape {
        Shape::Thread
    }
}

impl<T: SummaryShape + ?Sized> SummaryShape for &T {
    fn shape() -> Shape {
        T::shape()
    }
}
impl<T: SummaryShape + ?Sized> SummaryShape for Box<T> {
    fn shape() -> Shape {
        T::shape()
    }
}
impl<T: SummaryShape + ?Sized> SummaryShape for Rc<T> {
    fn shape() -> Shape {
        T::shape()
    }
}
impl<T: SummaryShape + ?Sized> SummaryShape for Arc<T> {
    fn shape() -> Shape {
        T::shape()
    }
}
impl<T: SummaryShape> SummaryShape for Vec<T> {
    fn shape() -> Shape {
        Shape::List(T::shape)
    }
}
impl<T: SummaryShape> SummaryShape for VecDeque<T> {
    fn shape() -> Shape {
        Shape::List(T::shape)
    }
}
impl<T: SummaryShape> SummaryShape for [T] {
    fn shape() -> Shape {
        Shape::List(T::shape)
    }
}
impl<T: SummaryShape, const N: usize> SummaryShape for [T; N] {
    fn shape() -> Shape {
        Shape::List(T::shape)
    }
}
impl<T: SummaryShape, S> SummaryShape for HashSet<T, S> {
    fn shape() -> Shape {
        Shape::Set(T::shape)
    }
}
impl<T: SummaryShape> SummaryShape for BTreeSet<T> {
    fn shape() -> Shape {
        Shape::Set(T::shape)
    }
}
impl<K, V, S> SummaryShape for HashMap<K, V, S> {
    fn shape() -> Shape {
        Shape::Map
    }
}
impl<K, V> SummaryShape for BTreeMap<K, V> {
    fn shape() -> Shape {
        Shape::Map
    }
}
impl<T: SummaryShape> SummaryShape for Option<T> {
    fn shape() -> Shape {
        Shape::Variants(vec![("None", vec![]), ("Some", vec![T::shape as ShapeFn])])
    }
}
/// `()` and tuples print as anonymous tuples, which the encoder refuses; they
/// implement the trait so that a type holding one (in a variant that is not
/// sent, or as `Result<T, ()>`) can still be declared.
macro_rules! opaque {
    ($($t:ty),*) => { $(impl SummaryShape for $t { fn shape() -> Shape { Shape::Opaque } })* };
}
opaque!(());
impl<A> SummaryShape for (A,) {
    fn shape() -> Shape {
        Shape::Opaque
    }
}
impl<A, B> SummaryShape for (A, B) {
    fn shape() -> Shape {
        Shape::Opaque
    }
}
impl<A, B, C> SummaryShape for (A, B, C) {
    fn shape() -> Shape {
        Shape::Opaque
    }
}
impl<A, B, C, D> SummaryShape for (A, B, C, D) {
    fn shape() -> Shape {
        Shape::Opaque
    }
}

impl<T: SummaryShape, E: SummaryShape> SummaryShape for Result<T, E> {
    fn shape() -> Shape {
        Shape::Variants(vec![("Ok", vec![T::shape as ShapeFn]), ("Err", vec![E::shape as ShapeFn])])
    }
}
