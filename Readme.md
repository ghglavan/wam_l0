# M0 Machine from the WAM book

Right now, we can build a query and a program by calling the procedures on the Machine struct:

Example (exercise 2.3):

``` rust
use wam_l0::*;
let mut m = Machine::new(1_000, 100);

// ?- p(f(X), h(Y, f(a)), Y)
m.put_structure(Func("a".into(), 0), 7);
m.put_structure(Func("f".into(), 1), 6);
m.set_value(7);
m.put_structure(Func("h".into(), 2), 3);
m.set_variable(4);
m.set_value(6);
m.put_structure(Func("f".into(), 1), 2);
m.set_variable(5);
m.put_structure(Func("p".into(), 3), 1);
m.set_value(2);
m.set_value(3);
m.set_value(4);
// p(Z, h(Z,W), f(W))
m.get_structure(Func("p".into(), 3), 1).unwrap();
m.unify_variable(2);
m.unify_variable(3);
m.unify_variable(4);
m.get_structure(Func("h".into(), 2), 3).unwrap();
m.unify_value(2).unwrap();
m.unify_variable(5);
m.get_structure(Func("f".into(), 1), 4).unwrap();
m.unify_value(5).unwrap();
assert_eq!(
"f(f(a))",
m.full_deref(&Address(AddressType::Register, 2))
.expect("could not full_deref X2")
);
assert_eq!(
"f(f(a))",
m.full_deref(&Address(AddressType::Register, 4))
.expect("could not full_deref X4")
);
assert_eq!(
"f(a)",
m.full_deref(&Address(AddressType::Register, 5))
.expect("could not full_deref X5")
);

```