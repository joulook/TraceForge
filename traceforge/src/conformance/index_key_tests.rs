use super::*;
use std::any::TypeId;

#[test]
fn ei_fixed_type_set_and_std_hash() {
    fn check<T: Default + Hash + 'static>() {
        let value = T::default();
        let mut expected = DefaultHasher::new();
        value.hash(&mut expected);
        let mut actual = DefaultHasher::new();
        value_hashers()[&TypeId::of::<T>()](&value, &mut actual);
        assert_eq!(actual.finish(), expected.finish());
    }
    macro_rules! third {
        ($t:ty, $u:ty; $($v:ty),*) => { $(check::<($t, $u, $v)>();)* };
    }
    macro_rules! second {
        ($t:ty; $($u:ty),*) => { $(
            check::<($t, $u)>();
            third!($t, $u; u8, u16, u32, u64, u128, usize,
                i8, i16, i32, i64, i128, isize, char, bool, String);
        )* };
    }
    macro_rules! first {
        ($($t:ty),*) => { $(
            check::<$t>();
            check::<Vec<$t>>();
            check::<Option<$t>>();
            second!($t; u8, u16, u32, u64, u128, usize,
                i8, i16, i32, i64, i128, isize, char, bool, String);
        )* };
    }
    first!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize, char, bool, String);
    assert_eq!(value_hashers().len(), 3 * 15 + 15 * 15 + 15 * 15 * 15);
    for excluded in [
        TypeId::of::<f32>(),
        TypeId::of::<f64>(),
        TypeId::of::<&str>(),
        TypeId::of::<()>(),
        TypeId::of::<Vec<Option<u64>>>(),
        TypeId::of::<crate::conformance::interchange::DecVal>(),
    ] {
        assert!(!value_hashers().contains_key(&excluded));
    }
}

#[test]
fn ei_key_uses_values_kinds_and_concrete_types() {
    fn sig(value: crate::Val, recv: bool) -> Sig {
        let obs = if recv {
            Obs::Recv(Some(value))
        } else {
            Obs::Send(value)
        };
        Sig::from_words(
            [("a".into(), Status::Done)].into(),
            [("a".into(), vec![obs])].into(),
        )
    }
    let a = sig(crate::Val::new(1u64), false);
    assert_ne!(a.value_key(), sig(crate::Val::new(2u64), false).value_key());
    assert_ne!(a.value_key(), sig(crate::Val::new(1u64), true).value_key());
    assert_ne!(a.value_key(), sig(crate::Val::new(1i64), false).value_key());
    let mut renamed = crate::Val::new(1u64);
    renamed.type_name = "not the type".into();
    assert_eq!(a.value_key(), sig(renamed, false).value_key());
    // Unsupported scalars and containers stay constant within a shape.
    assert_eq!(
        sig(crate::Val::new("a"), false).value_key(),
        sig(crate::Val::new("b"), false).value_key()
    );
    assert_eq!(
        sig(crate::Val::new(1.0f64), false).value_key(),
        sig(crate::Val::new(2.0f64), false).value_key()
    );
    assert_ne!(
        sig(crate::Val::new((1u64, 'a', String::from("x"))), false).value_key(),
        sig(crate::Val::new((1u64, 'a', String::from("y"))), false).value_key()
    );
}
