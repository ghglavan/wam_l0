//! An m0 implementation following the WAM book
//!
//! Right now, all we can do is to build a query
//! and a program and unify them.
//!
//! For now, the query and program are built
//! directly by calling machine functions like
//! [Machine::put_structure] to construct things
//! on the heap.
//!
//! Example (exercise from the book):
//! ```
//! use wam_l0::*;
//! let mut m = Machine::new(1_000, 100);
//!
//! // ?- p(f(X), h(Y, f(a)), Y)
//! m.put_structure(Func("a".into(), 0), 7);
//! m.put_structure(Func("f".into(), 1), 6);
//! m.set_value(7);
//! m.put_structure(Func("h".into(), 2), 3);
//! m.set_variable(4);
//! m.set_value(6);
//! m.put_structure(Func("f".into(), 1), 2);
//! m.set_variable(5);
//! m.put_structure(Func("p".into(), 3), 1);
//! m.set_value(2);
//! m.set_value(3);
//! m.set_value(4);
//! // p(Z, h(Z,W), f(W))
//! m.get_structure(Func("p".into(), 3), 1).unwrap();
//! m.unify_variable(2);
//! m.unify_variable(3);
//! m.unify_variable(4);
//! m.get_structure(Func("h".into(), 2), 3).unwrap();
//! m.unify_value(2).unwrap();
//! m.unify_variable(5);
//! m.get_structure(Func("f".into(), 1), 4).unwrap();
//! m.unify_value(5).unwrap();
//! assert_eq!(
//!     "f(f(a))",
//!     m.full_deref(&Address(AddressType::Register, 2))
//!         .expect("could not full_deref X2")
//! );
//! assert_eq!(
//!     "f(f(a))",
//!     m.full_deref(&Address(AddressType::Register, 4))
//!         .expect("could not full_deref X4")
//! );
//! assert_eq!(
//!     "f(a)",
//!     m.full_deref(&Address(AddressType::Register, 5))
//!         .expect("could not full_deref X5")
//! );
//! ```

use core::fmt;
use std::fmt::Write as _;
use std::usize;

/// A machine error
#[derive(thiserror::Error, Debug)]
pub enum WAMError {
    #[error("Error derefing addr `{0}`")]
    DerefError(Address),
    #[error("Error binding `{0}` <-> `{1}`")]
    BindError(Address, Address),
    #[error("Error matching `{0}` = `{1}`")]
    FuncMatchError(Func, Func),
    #[error("Error matching `{0}` = `{1}`")]
    MatchError(String, String),
    #[error("Expected address `{1}`, got `{0}`")]
    WrongAddressType(AddressType, AddressType),

    #[error("Looping at address `{0}`")]
    Looping(Address),
}

/// The possible type of an address
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AddressType {
    /// An address on the heap
    Heap,
    /// A register address
    Register,
}

impl fmt::Display for AddressType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        <Self as fmt::Debug>::fmt(&self, f)
    }
}

/// An address on the heap or a register
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Address(pub AddressType, pub usize);

impl Address {
    pub fn incr(self, step: usize) -> Self {
        Self(self.0, self.1 + step)
    }
}

impl fmt::Display for Address {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        <Self as fmt::Debug>::fmt(&self, f)
    }
}

/// A function
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Func(pub String, pub usize);

impl fmt::Display for Func {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        <Self as fmt::Debug>::fmt(&self, f)
    }
}

/// One element of the heap
#[derive(Debug, Clone)]
pub enum Cell {
    /// A <STR, ADDR> as defined in the book
    Str(Address),
    /// A <REF, ADDR> as defined in the book
    Ref(Address),
    /// A f|n as defined in the book
    Fun(Func),
}

impl fmt::Display for Cell {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        <Self as fmt::Debug>::fmt(&self, f)
    }
}

impl Cell {
    pub fn is_ref(&self) -> bool {
        matches!(self, Self::Ref(_))
    }
}

/// Heap is a vector of cells. It is used to
/// build the stack as queries and programs
/// are built
pub type Heap = Vec<Cell>;

/// Registers is a vector of cells.
pub type Registers = Vec<Cell>;

/// The state machine containing the heap
/// and registers
pub struct Machine {
    heap: Heap,
    registers: Registers,

    s: Address,
    h: usize,
    w: bool,
}

impl Machine {
    /// Create a new machine with heap_size heap cells and ref_size register cells
    pub fn new(heap_size: usize, ref_size: usize) -> Self {
        let registers = vec![Cell::Ref(Address(AddressType::Register, usize::MAX)); ref_size];

        Self {
            heap: Vec::with_capacity(heap_size),
            registers,

            s: Address(AddressType::Heap, 0),
            w: false,
            h: 0,
        }
    }

    /// Get a reference to the cell at an address
    /// independent of the [AddressType]
    pub fn store(&self, a: &Address) -> &Cell {
        match a.0 {
            AddressType::Heap => &self.heap[a.1],
            AddressType::Register => &self.registers[a.1],
        }
    }

    /// Get a mut reference to the cell at an address
    /// independent of the [AddressType]
    pub fn store_mut(&mut self, a: &Address) -> &mut Cell {
        match a.0 {
            AddressType::Heap => &mut self.heap[a.1],
            AddressType::Register => &mut self.registers[a.1],
        }
    }

    /// The put_structure procedure as defined in WAM
    pub fn put_structure(&mut self, f: Func, x_i: usize) {
        self.heap
            .push(Cell::Str(Address(AddressType::Heap, self.h + 1)));
        self.heap.push(Cell::Fun(f));
        self.registers[x_i] = self.heap[self.h].clone();
        self.h += 2;
    }

    /// The set_variable procedure as defined in WAM
    pub fn set_variable(&mut self, x_i: usize) {
        self.heap
            .push(Cell::Ref(Address(AddressType::Heap, self.h)));
        self.registers[x_i] = self.heap[self.h].clone();
        self.h += 1;
    }

    /// The set_value procedure as defined in WAM
    pub fn set_value(&mut self, x_i: usize) {
        self.heap.push(self.registers[x_i].clone());
        self.h += 1;
    }

    fn deref(&self, addr: &Address) -> Address {
        match self.store(addr) {
            Cell::Ref(a) if a != addr => self.deref(&a),
            _ => addr.clone(),
        }
    }

    fn bind(&mut self, addr1: &Address, addr2: &Address) -> Result<(), WAMError> {
        let c = self.store_mut(addr1);

        if let Cell::Ref(a) = c {
            *a = addr2.clone();
            return Ok(());
        }

        let c = self.store_mut(addr2);

        if let Cell::Ref(a) = c {
            *a = addr1.clone();
            return Ok(());
        }

        Err(WAMError::BindError(addr1.clone(), addr2.clone()))
    }

    /// The get_structure procedure as defined in WAM
    pub fn get_structure(&mut self, f: Func, x_i: usize) -> Result<(), WAMError> {
        let addr = self.deref(&Address(AddressType::Register, x_i));
        match self.store(&addr) {
            Cell::Ref(_) => {
                self.heap
                    .push(Cell::Str(Address(AddressType::Heap, self.h + 1)));
                self.heap.push(Cell::Fun(f));

                self.bind(&addr, &Address(AddressType::Heap, self.h))?;

                self.h += 2;
                self.w = true;
                Ok(())
            }
            Cell::Str(a) => match &self.heap[a.1] {
                Cell::Fun(f1) => {
                    if f1 == &f {
                        if !matches!(a.0, AddressType::Heap) {
                            return Err(WAMError::WrongAddressType(a.0.clone(), AddressType::Heap));
                        }
                        self.s = Address(AddressType::Heap, a.1 + 1);
                        self.w = false;
                        Ok(())
                    } else {
                        return Err(WAMError::FuncMatchError(f1.clone(), f));
                    }
                }
                x => return Err(WAMError::MatchError(x.to_string(), f.to_string())),
            },
            _ => return Err(WAMError::DerefError(Address(AddressType::Register, x_i))),
        }
    }

    /// The unify_variable as defined in WAM
    pub fn unify_variable(&mut self, x_i: usize) {
        if !self.w {
            self.registers[x_i] = self.heap[self.s.1].clone();
        } else {
            self.heap
                .push(Cell::Ref(Address(AddressType::Heap, self.h + 1)));
            self.registers[x_i] = self.heap[self.h].clone();
            self.h += 1;
        }

        self.s.1 += 1;
    }

    fn unify(&mut self, addr1: &Address, addr2: &Address) -> Result<(), WAMError> {
        let mut pdl = vec![addr1.clone(), addr2.clone()];

        while pdl.len() > 1 {
            let d1 = self.deref(&pdl.pop().unwrap());
            let d2 = self.deref(&pdl.pop().unwrap());

            let c1 = self.store(&d1);
            if d1 != d2 {
                let c2 = self.store(&d2);

                if c1.is_ref() || c2.is_ref() {
                    self.bind(&d1, &d2)?;
                } else {
                    match (c1, c2) {
                        (Cell::Str(v1), Cell::Str(v2)) => match (self.store(v1), self.store(v2)) {
                            (Cell::Fun(f1), Cell::Fun(f2)) => {
                                if f1 == f2 {
                                    for i in 0..f1.1 {
                                        pdl.push(v1.clone().incr(i + 1));
                                        pdl.push(v2.clone().incr(i + 1));
                                    }
                                } else {
                                    return Err(WAMError::FuncMatchError(f1.clone(), f2.clone()));
                                }
                            }
                            (cell1, cell2) => {
                                return Err(WAMError::MatchError(
                                    cell1.to_string(),
                                    cell2.to_string(),
                                ))
                            }
                        },
                        // cannot realy happen, here just to be sure
                        (cell1, cell2) => {
                            return Err(WAMError::MatchError(cell1.to_string(), cell2.to_string()))
                        }
                    };
                }
            }
        }

        Ok(())
    }

    /// The unify_value as defined in WAM
    pub fn unify_value(&mut self, x_i: usize) -> Result<(), WAMError> {
        if !self.w {
            self.unify(&Address(AddressType::Register, x_i), &self.s.clone())?;
        } else {
            self.heap
                .push(Cell::Ref(Address(AddressType::Register, x_i)));
            self.h += 1;
        }

        self.s.1 += 1;
        Ok(())
    }

    /// Walk an address chain and contruct an identifier
    pub fn full_deref(&self, addr: &Address) -> Result<String, WAMError> {
        match self.store(addr) {
            Cell::Ref(a2) => {
                if a2 == addr {
                    return Err(WAMError::Looping(a2.clone()));
                }
                self.full_deref(a2)
            }
            Cell::Str(a2) => match self.store(a2) {
                Cell::Fun(f) => {
                    let mut s = f.0.clone();
                    if f.1 > 0 {
                        s.push_str("(");
                    }
                    for i in 0..f.1 {
                        s.push_str(&self.full_deref(&a2.clone().incr(i + 1))?);
                    }
                    if f.1 > 0 {
                        s.push_str(")");
                    }
                    return Ok(s);
                }
                _ => return Err(WAMError::DerefError(addr.clone())),
            },
            x => return Err(WAMError::MatchError(x.to_string(), "Ref or Str".into())),
        }
    }

    /// Get the heap from 0 to h
    pub fn get_heap(&self, h: usize) -> Result<String, std::fmt::Error> {
        let mut s = String::new();
        for i in 0..h {
            write!(&mut s, "{i}: ")?;
            match &self.heap[i] {
                Cell::Ref(a) => write!(&mut s, "<REF, <{},{}>>", a.0, a.1)?,
                Cell::Str(a) => write!(&mut s, "<STR, <{},{}>>", a.0, a.1)?,
                Cell::Fun(f) => write!(&mut s, "{}|{}", f.0, f.1)?,
            }
            writeln!(&mut s)?;
        }
        Ok(s)
    }

    /// Get registers from 0 to last_r
    pub fn get_registers(&self, last_r: usize) -> Result<String, std::fmt::Error> {
        let mut s = String::new();
        for i in 0..last_r {
            write!(&mut s, "X{}: ", i)?;
            match &self.registers[i] {
                Cell::Ref(a) => write!(&mut s, "<REF, <{},{}>", a.0, a.1)?,
                Cell::Str(a) => write!(&mut s, "<STR, <{},{}>", a.0, a.1)?,
                Cell::Fun(f) => write!(&mut s, "{}|{}", f.0, f.1)?,
            }
            writeln!(&mut s)?;
        }
        Ok(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unify1() {
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
    }
}
