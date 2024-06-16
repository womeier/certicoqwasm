#![allow(dead_code)]
#![allow(non_camel_case_types)]
#![allow(unused_imports)]
#![allow(non_snake_case)]
#![allow(unused_variables)]

use std::marker::PhantomData;

fn __nat_succ(x: u64) -> u64 {
  x.checked_add(1).unwrap()
}

macro_rules! __nat_elim {
    ($zcase:expr, $pred:ident, $scase:expr, $val:expr) => {
        { let v = $val;
        if v == 0 { $zcase } else { let $pred = v - 1; $scase } }
    }
}

macro_rules! __andb { ($b1:expr, $b2:expr) => { $b1 && $b2 } }
macro_rules! __orb { ($b1:expr, $b2:expr) => { $b1 || $b2 } }

fn __pos_onebit(x: u64) -> u64 {
  x.checked_mul(2).unwrap() + 1
}

fn __pos_zerobit(x: u64) -> u64 {
  x.checked_mul(2).unwrap()
}

macro_rules! __pos_elim {
    ($p:ident, $onebcase:expr, $p2:ident, $zerobcase:expr, $onecase:expr, $val:expr) => {
        {
            let n = $val;
            if n == 1 {
                $onecase
            } else if (n & 1) == 0 {
                let $p2 = n >> 1;
                $zerobcase
            } else {
                let $p = n >> 1;
                $onebcase
            }
        }
    }
}

fn __Z_frompos(z: u64) -> i64 {
  use std::convert::TryFrom;

  i64::try_from(z).unwrap()
}

fn __Z_fromneg(z : u64) -> i64 {
  use std::convert::TryFrom;

  i64::try_from(z).unwrap().checked_neg().unwrap()
}

macro_rules! __Z_elim {
    ($zero_case:expr, $p:ident, $pos_case:expr, $p2:ident, $neg_case:expr, $val:expr) => {
        {
            let n = $val;
            if n == 0 {
                $zero_case
            } else if n < 0 {
                let $p2 = n.unsigned_abs();
                $neg_case
            } else {
                let $p = n as u64;
                $pos_case
            }
        }
    }
}

fn __N_frompos(z: u64) -> u64 {
  z
}

macro_rules! __N_elim {
    ($zero_case:expr, $p:ident, $pos_case:expr, $val:expr) => {
        { let $p = $val; if $p == 0 { $zero_case } else { $pos_case } }
    }
}

type __pair<A, B> = (A, B);

macro_rules! __pair_elim {
    ($fst:ident, $snd:ident, $body:expr, $p:expr) => {
        { let ($fst, $snd) = $p; $body }
    }
}

fn __mk_pair<A: Copy, B: Copy>(a: A, b: B) -> __pair<A, B> { (a, b) }

fn hint_app<TArg, TRet>(f: &dyn Fn(TArg) -> TRet) -> &dyn Fn(TArg) -> TRet {
  f
}

#[derive(Debug, Clone)]
pub enum Coq_Init_Datatypes_nat<'a> {
  O(PhantomData<&'a ()>),
  S(PhantomData<&'a ()>, &'a Coq_Init_Datatypes_nat<'a>)
}

#[derive(Debug, Clone)]
pub enum Coq_Numbers_BinNums_positive<'a> {
  xI(PhantomData<&'a ()>, &'a Coq_Numbers_BinNums_positive<'a>),
  xO(PhantomData<&'a ()>, &'a Coq_Numbers_BinNums_positive<'a>),
  xH(PhantomData<&'a ()>)
}

#[derive(Debug, Clone)]
pub enum Coq_Numbers_BinNums_Z<'a> {
  Z0(PhantomData<&'a ()>),
  Zpos(PhantomData<&'a ()>, &'a Coq_Numbers_BinNums_positive<'a>),
  Zneg(PhantomData<&'a ()>, &'a Coq_Numbers_BinNums_positive<'a>)
}

#[derive(Debug, Clone)]
pub enum Coq_Init_Datatypes_comparison<'a> {
  Eq(PhantomData<&'a ()>),
  Lt(PhantomData<&'a ()>),
  Gt(PhantomData<&'a ()>)
}

struct Program {
  __alloc: bumpalo::Bump,
}

impl<'a> Program {
fn new() -> Self {
  Program {
    __alloc: bumpalo::Bump::new(),
  }
}

fn alloc<T>(&'a self, t: T) -> &'a T {
  self.__alloc.alloc(t)
}

fn closure<TArg, TRet>(&'a self, F: impl Fn(TArg) -> TRet + 'a) -> &'a dyn Fn(TArg) -> TRet {
  self.__alloc.alloc(F)
}

fn Coq_PArith_BinPosDef_Pos_succ(&'a self, x: &'a Coq_Numbers_BinNums_positive<'a>) -> &'a Coq_Numbers_BinNums_positive<'a> {
  match x {
    &Coq_Numbers_BinNums_positive::xI(_, p) => {
      self.alloc(
        Coq_Numbers_BinNums_positive::xO(
          PhantomData,
          self.Coq_PArith_BinPosDef_Pos_succ(
            p)))
    },
    &Coq_Numbers_BinNums_positive::xO(_, p) => {
      self.alloc(
        Coq_Numbers_BinNums_positive::xI(
          PhantomData,
          p))
    },
    &Coq_Numbers_BinNums_positive::xH(_) => {
      self.alloc(
        Coq_Numbers_BinNums_positive::xO(
          PhantomData,
          self.alloc(
            Coq_Numbers_BinNums_positive::xH(
              PhantomData))))
    },
  }
}
fn Coq_PArith_BinPosDef_Pos_succ__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_positive<'a>) -> &'a Coq_Numbers_BinNums_positive<'a> {
  self.closure(move |x| {
    self.Coq_PArith_BinPosDef_Pos_succ(
      x)
  })
}

fn Coq_PArith_BinPosDef_Pos_add(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_positive<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_positive<'a>) -> &'a Coq_Numbers_BinNums_positive<'a> {
  let add = self.alloc(std::cell::Cell::new(None));
  let add_carry = self.alloc(std::cell::Cell::new(None));
  add.set(Some(
    self.closure(move |x| {
      self.closure(move |y| {
        match x {
          &Coq_Numbers_BinNums_positive::xI(_, p) => {
            match y {
              &Coq_Numbers_BinNums_positive::xI(_, q) => {
                self.alloc(
                  Coq_Numbers_BinNums_positive::xO(
                    PhantomData,
                    hint_app(hint_app(add_carry.get().unwrap())(p))(q)))
              },
              &Coq_Numbers_BinNums_positive::xO(_, q) => {
                self.alloc(
                  Coq_Numbers_BinNums_positive::xI(
                    PhantomData,
                    hint_app(hint_app(add.get().unwrap())(p))(q)))
              },
              &Coq_Numbers_BinNums_positive::xH(_) => {
                self.alloc(
                  Coq_Numbers_BinNums_positive::xO(
                    PhantomData,
                    self.Coq_PArith_BinPosDef_Pos_succ(
                      p)))
              },
            }
          },
          &Coq_Numbers_BinNums_positive::xO(_, p) => {
            match y {
              &Coq_Numbers_BinNums_positive::xI(_, q) => {
                self.alloc(
                  Coq_Numbers_BinNums_positive::xI(
                    PhantomData,
                    hint_app(hint_app(add.get().unwrap())(p))(q)))
              },
              &Coq_Numbers_BinNums_positive::xO(_, q) => {
                self.alloc(
                  Coq_Numbers_BinNums_positive::xO(
                    PhantomData,
                    hint_app(hint_app(add.get().unwrap())(p))(q)))
              },
              &Coq_Numbers_BinNums_positive::xH(_) => {
                self.alloc(
                  Coq_Numbers_BinNums_positive::xI(
                    PhantomData,
                    p))
              },
            }
          },
          &Coq_Numbers_BinNums_positive::xH(_) => {
            match y {
              &Coq_Numbers_BinNums_positive::xI(_, q) => {
                self.alloc(
                  Coq_Numbers_BinNums_positive::xO(
                    PhantomData,
                    self.Coq_PArith_BinPosDef_Pos_succ(
                      q)))
              },
              &Coq_Numbers_BinNums_positive::xO(_, q) => {
                self.alloc(
                  Coq_Numbers_BinNums_positive::xI(
                    PhantomData,
                    q))
              },
              &Coq_Numbers_BinNums_positive::xH(_) => {
                self.alloc(
                  Coq_Numbers_BinNums_positive::xO(
                    PhantomData,
                    self.alloc(
                      Coq_Numbers_BinNums_positive::xH(
                        PhantomData))))
              },
            }
          },
        }
      })
    })));
  add_carry.set(Some(
    self.closure(move |x| {
      self.closure(move |y| {
        match x {
          &Coq_Numbers_BinNums_positive::xI(_, p) => {
            match y {
              &Coq_Numbers_BinNums_positive::xI(_, q) => {
                self.alloc(
                  Coq_Numbers_BinNums_positive::xI(
                    PhantomData,
                    hint_app(hint_app(add_carry.get().unwrap())(p))(q)))
              },
              &Coq_Numbers_BinNums_positive::xO(_, q) => {
                self.alloc(
                  Coq_Numbers_BinNums_positive::xO(
                    PhantomData,
                    hint_app(hint_app(add_carry.get().unwrap())(p))(q)))
              },
              &Coq_Numbers_BinNums_positive::xH(_) => {
                self.alloc(
                  Coq_Numbers_BinNums_positive::xI(
                    PhantomData,
                    self.Coq_PArith_BinPosDef_Pos_succ(
                      p)))
              },
            }
          },
          &Coq_Numbers_BinNums_positive::xO(_, p) => {
            match y {
              &Coq_Numbers_BinNums_positive::xI(_, q) => {
                self.alloc(
                  Coq_Numbers_BinNums_positive::xO(
                    PhantomData,
                    hint_app(hint_app(add_carry.get().unwrap())(p))(q)))
              },
              &Coq_Numbers_BinNums_positive::xO(_, q) => {
                self.alloc(
                  Coq_Numbers_BinNums_positive::xI(
                    PhantomData,
                    hint_app(hint_app(add.get().unwrap())(p))(q)))
              },
              &Coq_Numbers_BinNums_positive::xH(_) => {
                self.alloc(
                  Coq_Numbers_BinNums_positive::xO(
                    PhantomData,
                    self.Coq_PArith_BinPosDef_Pos_succ(
                      p)))
              },
            }
          },
          &Coq_Numbers_BinNums_positive::xH(_) => {
            match y {
              &Coq_Numbers_BinNums_positive::xI(_, q) => {
                self.alloc(
                  Coq_Numbers_BinNums_positive::xI(
                    PhantomData,
                    self.Coq_PArith_BinPosDef_Pos_succ(
                      q)))
              },
              &Coq_Numbers_BinNums_positive::xO(_, q) => {
                self.alloc(
                  Coq_Numbers_BinNums_positive::xO(
                    PhantomData,
                    self.Coq_PArith_BinPosDef_Pos_succ(
                      q)))
              },
              &Coq_Numbers_BinNums_positive::xH(_) => {
                self.alloc(
                  Coq_Numbers_BinNums_positive::xI(
                    PhantomData,
                    self.alloc(
                      Coq_Numbers_BinNums_positive::xH(
                        PhantomData))))
              },
            }
          },
        }
      })
    })));
  add.get().unwrap()
}

fn Coq_PArith_BinPosDef_Pos_mul(&'a self, x: &'a Coq_Numbers_BinNums_positive<'a>, y: &'a Coq_Numbers_BinNums_positive<'a>) -> &'a Coq_Numbers_BinNums_positive<'a> {
  match x {
    &Coq_Numbers_BinNums_positive::xI(_, p) => {
      self.Coq_PArith_BinPosDef_Pos_add()(
        y)(
        self.alloc(
          Coq_Numbers_BinNums_positive::xO(
            PhantomData,
            self.Coq_PArith_BinPosDef_Pos_mul(
              p,
              y))))
    },
    &Coq_Numbers_BinNums_positive::xO(_, p) => {
      self.alloc(
        Coq_Numbers_BinNums_positive::xO(
          PhantomData,
          self.Coq_PArith_BinPosDef_Pos_mul(
            p,
            y)))
    },
    &Coq_Numbers_BinNums_positive::xH(_) => {
      y
    },
  }
}
fn Coq_PArith_BinPosDef_Pos_mul__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_positive<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_positive<'a>) -> &'a Coq_Numbers_BinNums_positive<'a> {
  self.closure(move |x| {
    self.closure(move |y| {
      self.Coq_PArith_BinPosDef_Pos_mul(
        x,
        y)
    })
  })
}

fn Coq_ZArith_BinIntDef_Z_mul(&'a self, x: &'a Coq_Numbers_BinNums_Z<'a>, y: &'a Coq_Numbers_BinNums_Z<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  match x {
    &Coq_Numbers_BinNums_Z::Z0(_) => {
      self.alloc(
        Coq_Numbers_BinNums_Z::Z0(
          PhantomData))
    },
    &Coq_Numbers_BinNums_Z::Zpos(_, x2) => {
      match y {
        &Coq_Numbers_BinNums_Z::Z0(_) => {
          self.alloc(
            Coq_Numbers_BinNums_Z::Z0(
              PhantomData))
        },
        &Coq_Numbers_BinNums_Z::Zpos(_, y2) => {
          self.alloc(
            Coq_Numbers_BinNums_Z::Zpos(
              PhantomData,
              self.Coq_PArith_BinPosDef_Pos_mul(
                x2,
                y2)))
        },
        &Coq_Numbers_BinNums_Z::Zneg(_, y2) => {
          self.alloc(
            Coq_Numbers_BinNums_Z::Zneg(
              PhantomData,
              self.Coq_PArith_BinPosDef_Pos_mul(
                x2,
                y2)))
        },
      }
    },
    &Coq_Numbers_BinNums_Z::Zneg(_, x2) => {
      match y {
        &Coq_Numbers_BinNums_Z::Z0(_) => {
          self.alloc(
            Coq_Numbers_BinNums_Z::Z0(
              PhantomData))
        },
        &Coq_Numbers_BinNums_Z::Zpos(_, y2) => {
          self.alloc(
            Coq_Numbers_BinNums_Z::Zneg(
              PhantomData,
              self.Coq_PArith_BinPosDef_Pos_mul(
                x2,
                y2)))
        },
        &Coq_Numbers_BinNums_Z::Zneg(_, y2) => {
          self.alloc(
            Coq_Numbers_BinNums_Z::Zpos(
              PhantomData,
              self.Coq_PArith_BinPosDef_Pos_mul(
                x2,
                y2)))
        },
      }
    },
  }
}
fn Coq_ZArith_BinIntDef_Z_mul__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  self.closure(move |x| {
    self.closure(move |y| {
      self.Coq_ZArith_BinIntDef_Z_mul(
        x,
        y)
    })
  })
}

fn Coq_PArith_BinPosDef_Pos_compare_cont(&'a self, r: &'a Coq_Init_Datatypes_comparison<'a>, x: &'a Coq_Numbers_BinNums_positive<'a>, y: &'a Coq_Numbers_BinNums_positive<'a>) -> &'a Coq_Init_Datatypes_comparison<'a> {
  match x {
    &Coq_Numbers_BinNums_positive::xI(_, p) => {
      match y {
        &Coq_Numbers_BinNums_positive::xI(_, q) => {
          self.Coq_PArith_BinPosDef_Pos_compare_cont(
            r,
            p,
            q)
        },
        &Coq_Numbers_BinNums_positive::xO(_, q) => {
          self.Coq_PArith_BinPosDef_Pos_compare_cont(
            self.alloc(
              Coq_Init_Datatypes_comparison::Gt(
                PhantomData)),
            p,
            q)
        },
        &Coq_Numbers_BinNums_positive::xH(_) => {
          self.alloc(
            Coq_Init_Datatypes_comparison::Gt(
              PhantomData))
        },
      }
    },
    &Coq_Numbers_BinNums_positive::xO(_, p) => {
      match y {
        &Coq_Numbers_BinNums_positive::xI(_, q) => {
          self.Coq_PArith_BinPosDef_Pos_compare_cont(
            self.alloc(
              Coq_Init_Datatypes_comparison::Lt(
                PhantomData)),
            p,
            q)
        },
        &Coq_Numbers_BinNums_positive::xO(_, q) => {
          self.Coq_PArith_BinPosDef_Pos_compare_cont(
            r,
            p,
            q)
        },
        &Coq_Numbers_BinNums_positive::xH(_) => {
          self.alloc(
            Coq_Init_Datatypes_comparison::Gt(
              PhantomData))
        },
      }
    },
    &Coq_Numbers_BinNums_positive::xH(_) => {
      match y {
        &Coq_Numbers_BinNums_positive::xI(_, q) => {
          self.alloc(
            Coq_Init_Datatypes_comparison::Lt(
              PhantomData))
        },
        &Coq_Numbers_BinNums_positive::xO(_, q) => {
          self.alloc(
            Coq_Init_Datatypes_comparison::Lt(
              PhantomData))
        },
        &Coq_Numbers_BinNums_positive::xH(_) => {
          r
        },
      }
    },
  }
}
fn Coq_PArith_BinPosDef_Pos_compare_cont__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_comparison<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_positive<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_positive<'a>) -> &'a Coq_Init_Datatypes_comparison<'a> {
  self.closure(move |r| {
    self.closure(move |x| {
      self.closure(move |y| {
        self.Coq_PArith_BinPosDef_Pos_compare_cont(
          r,
          x,
          y)
      })
    })
  })
}

fn Coq_PArith_BinPosDef_Pos_compare(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_positive<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_positive<'a>) -> &'a Coq_Init_Datatypes_comparison<'a> {
  self.Coq_PArith_BinPosDef_Pos_compare_cont__curried()(
    self.alloc(
      Coq_Init_Datatypes_comparison::Eq(
        PhantomData)))
}

fn Coq_Init_Datatypes_CompOpp(&'a self, r: &'a Coq_Init_Datatypes_comparison<'a>) -> &'a Coq_Init_Datatypes_comparison<'a> {
  match r {
    &Coq_Init_Datatypes_comparison::Eq(_) => {
      self.alloc(
        Coq_Init_Datatypes_comparison::Eq(
          PhantomData))
    },
    &Coq_Init_Datatypes_comparison::Lt(_) => {
      self.alloc(
        Coq_Init_Datatypes_comparison::Gt(
          PhantomData))
    },
    &Coq_Init_Datatypes_comparison::Gt(_) => {
      self.alloc(
        Coq_Init_Datatypes_comparison::Lt(
          PhantomData))
    },
  }
}
fn Coq_Init_Datatypes_CompOpp__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_comparison<'a>) -> &'a Coq_Init_Datatypes_comparison<'a> {
  self.closure(move |r| {
    self.Coq_Init_Datatypes_CompOpp(
      r)
  })
}

fn Coq_ZArith_BinIntDef_Z_compare(&'a self, x: &'a Coq_Numbers_BinNums_Z<'a>, y: &'a Coq_Numbers_BinNums_Z<'a>) -> &'a Coq_Init_Datatypes_comparison<'a> {
  match x {
    &Coq_Numbers_BinNums_Z::Z0(_) => {
      match y {
        &Coq_Numbers_BinNums_Z::Z0(_) => {
          self.alloc(
            Coq_Init_Datatypes_comparison::Eq(
              PhantomData))
        },
        &Coq_Numbers_BinNums_Z::Zpos(_, y2) => {
          self.alloc(
            Coq_Init_Datatypes_comparison::Lt(
              PhantomData))
        },
        &Coq_Numbers_BinNums_Z::Zneg(_, y2) => {
          self.alloc(
            Coq_Init_Datatypes_comparison::Gt(
              PhantomData))
        },
      }
    },
    &Coq_Numbers_BinNums_Z::Zpos(_, x2) => {
      match y {
        &Coq_Numbers_BinNums_Z::Z0(_) => {
          self.alloc(
            Coq_Init_Datatypes_comparison::Gt(
              PhantomData))
        },
        &Coq_Numbers_BinNums_Z::Zpos(_, y2) => {
          self.Coq_PArith_BinPosDef_Pos_compare()(
            x2)(
            y2)
        },
        &Coq_Numbers_BinNums_Z::Zneg(_, y2) => {
          self.alloc(
            Coq_Init_Datatypes_comparison::Gt(
              PhantomData))
        },
      }
    },
    &Coq_Numbers_BinNums_Z::Zneg(_, x2) => {
      match y {
        &Coq_Numbers_BinNums_Z::Z0(_) => {
          self.alloc(
            Coq_Init_Datatypes_comparison::Lt(
              PhantomData))
        },
        &Coq_Numbers_BinNums_Z::Zpos(_, y2) => {
          self.alloc(
            Coq_Init_Datatypes_comparison::Lt(
              PhantomData))
        },
        &Coq_Numbers_BinNums_Z::Zneg(_, y2) => {
          self.Coq_Init_Datatypes_CompOpp(
            self.Coq_PArith_BinPosDef_Pos_compare()(
              x2)(
              y2))
        },
      }
    },
  }
}
fn Coq_ZArith_BinIntDef_Z_compare__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a Coq_Init_Datatypes_comparison<'a> {
  self.closure(move |x| {
    self.closure(move |y| {
      self.Coq_ZArith_BinIntDef_Z_compare(
        x,
        y)
    })
  })
}

fn Coq_ZArith_BinIntDef_Z_ltb(&'a self, x: &'a Coq_Numbers_BinNums_Z<'a>, y: &'a Coq_Numbers_BinNums_Z<'a>) -> bool {
  match self.Coq_ZArith_BinIntDef_Z_compare(
          x,
          y) {
    &Coq_Init_Datatypes_comparison::Eq(_) => {
      false
    },
    &Coq_Init_Datatypes_comparison::Lt(_) => {
      true
    },
    &Coq_Init_Datatypes_comparison::Gt(_) => {
      false
    },
  }
}
fn Coq_ZArith_BinIntDef_Z_ltb__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> bool {
  self.closure(move |x| {
    self.closure(move |y| {
      self.Coq_ZArith_BinIntDef_Z_ltb(
        x,
        y)
    })
  })
}

fn Coq_ZArith_BinIntDef_Z_double(&'a self, x: &'a Coq_Numbers_BinNums_Z<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  match x {
    &Coq_Numbers_BinNums_Z::Z0(_) => {
      self.alloc(
        Coq_Numbers_BinNums_Z::Z0(
          PhantomData))
    },
    &Coq_Numbers_BinNums_Z::Zpos(_, p) => {
      self.alloc(
        Coq_Numbers_BinNums_Z::Zpos(
          PhantomData,
          self.alloc(
            Coq_Numbers_BinNums_positive::xO(
              PhantomData,
              p))))
    },
    &Coq_Numbers_BinNums_Z::Zneg(_, p) => {
      self.alloc(
        Coq_Numbers_BinNums_Z::Zneg(
          PhantomData,
          self.alloc(
            Coq_Numbers_BinNums_positive::xO(
              PhantomData,
              p))))
    },
  }
}
fn Coq_ZArith_BinIntDef_Z_double__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  self.closure(move |x| {
    self.Coq_ZArith_BinIntDef_Z_double(
      x)
  })
}

fn Coq_PArith_BinPosDef_Pos_pred_double(&'a self, x: &'a Coq_Numbers_BinNums_positive<'a>) -> &'a Coq_Numbers_BinNums_positive<'a> {
  match x {
    &Coq_Numbers_BinNums_positive::xI(_, p) => {
      self.alloc(
        Coq_Numbers_BinNums_positive::xI(
          PhantomData,
          self.alloc(
            Coq_Numbers_BinNums_positive::xO(
              PhantomData,
              p))))
    },
    &Coq_Numbers_BinNums_positive::xO(_, p) => {
      self.alloc(
        Coq_Numbers_BinNums_positive::xI(
          PhantomData,
          self.Coq_PArith_BinPosDef_Pos_pred_double(
            p)))
    },
    &Coq_Numbers_BinNums_positive::xH(_) => {
      self.alloc(
        Coq_Numbers_BinNums_positive::xH(
          PhantomData))
    },
  }
}
fn Coq_PArith_BinPosDef_Pos_pred_double__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_positive<'a>) -> &'a Coq_Numbers_BinNums_positive<'a> {
  self.closure(move |x| {
    self.Coq_PArith_BinPosDef_Pos_pred_double(
      x)
  })
}

fn Coq_ZArith_BinIntDef_Z_succ_double(&'a self, x: &'a Coq_Numbers_BinNums_Z<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  match x {
    &Coq_Numbers_BinNums_Z::Z0(_) => {
      self.alloc(
        Coq_Numbers_BinNums_Z::Zpos(
          PhantomData,
          self.alloc(
            Coq_Numbers_BinNums_positive::xH(
              PhantomData))))
    },
    &Coq_Numbers_BinNums_Z::Zpos(_, p) => {
      self.alloc(
        Coq_Numbers_BinNums_Z::Zpos(
          PhantomData,
          self.alloc(
            Coq_Numbers_BinNums_positive::xI(
              PhantomData,
              p))))
    },
    &Coq_Numbers_BinNums_Z::Zneg(_, p) => {
      self.alloc(
        Coq_Numbers_BinNums_Z::Zneg(
          PhantomData,
          self.Coq_PArith_BinPosDef_Pos_pred_double(
            p)))
    },
  }
}
fn Coq_ZArith_BinIntDef_Z_succ_double__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  self.closure(move |x| {
    self.Coq_ZArith_BinIntDef_Z_succ_double(
      x)
  })
}

fn Coq_ZArith_BinIntDef_Z_pred_double(&'a self, x: &'a Coq_Numbers_BinNums_Z<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  match x {
    &Coq_Numbers_BinNums_Z::Z0(_) => {
      self.alloc(
        Coq_Numbers_BinNums_Z::Zneg(
          PhantomData,
          self.alloc(
            Coq_Numbers_BinNums_positive::xH(
              PhantomData))))
    },
    &Coq_Numbers_BinNums_Z::Zpos(_, p) => {
      self.alloc(
        Coq_Numbers_BinNums_Z::Zpos(
          PhantomData,
          self.Coq_PArith_BinPosDef_Pos_pred_double(
            p)))
    },
    &Coq_Numbers_BinNums_Z::Zneg(_, p) => {
      self.alloc(
        Coq_Numbers_BinNums_Z::Zneg(
          PhantomData,
          self.alloc(
            Coq_Numbers_BinNums_positive::xI(
              PhantomData,
              p))))
    },
  }
}
fn Coq_ZArith_BinIntDef_Z_pred_double__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  self.closure(move |x| {
    self.Coq_ZArith_BinIntDef_Z_pred_double(
      x)
  })
}

fn Coq_ZArith_BinIntDef_Z_pos_sub(&'a self, x: &'a Coq_Numbers_BinNums_positive<'a>, y: &'a Coq_Numbers_BinNums_positive<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  match x {
    &Coq_Numbers_BinNums_positive::xI(_, p) => {
      match y {
        &Coq_Numbers_BinNums_positive::xI(_, q) => {
          self.Coq_ZArith_BinIntDef_Z_double(
            self.Coq_ZArith_BinIntDef_Z_pos_sub(
              p,
              q))
        },
        &Coq_Numbers_BinNums_positive::xO(_, q) => {
          self.Coq_ZArith_BinIntDef_Z_succ_double(
            self.Coq_ZArith_BinIntDef_Z_pos_sub(
              p,
              q))
        },
        &Coq_Numbers_BinNums_positive::xH(_) => {
          self.alloc(
            Coq_Numbers_BinNums_Z::Zpos(
              PhantomData,
              self.alloc(
                Coq_Numbers_BinNums_positive::xO(
                  PhantomData,
                  p))))
        },
      }
    },
    &Coq_Numbers_BinNums_positive::xO(_, p) => {
      match y {
        &Coq_Numbers_BinNums_positive::xI(_, q) => {
          self.Coq_ZArith_BinIntDef_Z_pred_double(
            self.Coq_ZArith_BinIntDef_Z_pos_sub(
              p,
              q))
        },
        &Coq_Numbers_BinNums_positive::xO(_, q) => {
          self.Coq_ZArith_BinIntDef_Z_double(
            self.Coq_ZArith_BinIntDef_Z_pos_sub(
              p,
              q))
        },
        &Coq_Numbers_BinNums_positive::xH(_) => {
          self.alloc(
            Coq_Numbers_BinNums_Z::Zpos(
              PhantomData,
              self.Coq_PArith_BinPosDef_Pos_pred_double(
                p)))
        },
      }
    },
    &Coq_Numbers_BinNums_positive::xH(_) => {
      match y {
        &Coq_Numbers_BinNums_positive::xI(_, q) => {
          self.alloc(
            Coq_Numbers_BinNums_Z::Zneg(
              PhantomData,
              self.alloc(
                Coq_Numbers_BinNums_positive::xO(
                  PhantomData,
                  q))))
        },
        &Coq_Numbers_BinNums_positive::xO(_, q) => {
          self.alloc(
            Coq_Numbers_BinNums_Z::Zneg(
              PhantomData,
              self.Coq_PArith_BinPosDef_Pos_pred_double(
                q)))
        },
        &Coq_Numbers_BinNums_positive::xH(_) => {
          self.alloc(
            Coq_Numbers_BinNums_Z::Z0(
              PhantomData))
        },
      }
    },
  }
}
fn Coq_ZArith_BinIntDef_Z_pos_sub__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_positive<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_positive<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  self.closure(move |x| {
    self.closure(move |y| {
      self.Coq_ZArith_BinIntDef_Z_pos_sub(
        x,
        y)
    })
  })
}

fn Coq_ZArith_BinIntDef_Z_add(&'a self, x: &'a Coq_Numbers_BinNums_Z<'a>, y: &'a Coq_Numbers_BinNums_Z<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  match x {
    &Coq_Numbers_BinNums_Z::Z0(_) => {
      y
    },
    &Coq_Numbers_BinNums_Z::Zpos(_, x2) => {
      match y {
        &Coq_Numbers_BinNums_Z::Z0(_) => {
          x
        },
        &Coq_Numbers_BinNums_Z::Zpos(_, y2) => {
          self.alloc(
            Coq_Numbers_BinNums_Z::Zpos(
              PhantomData,
              self.Coq_PArith_BinPosDef_Pos_add()(
                x2)(
                y2)))
        },
        &Coq_Numbers_BinNums_Z::Zneg(_, y2) => {
          self.Coq_ZArith_BinIntDef_Z_pos_sub(
            x2,
            y2)
        },
      }
    },
    &Coq_Numbers_BinNums_Z::Zneg(_, x2) => {
      match y {
        &Coq_Numbers_BinNums_Z::Z0(_) => {
          x
        },
        &Coq_Numbers_BinNums_Z::Zpos(_, y2) => {
          self.Coq_ZArith_BinIntDef_Z_pos_sub(
            y2,
            x2)
        },
        &Coq_Numbers_BinNums_Z::Zneg(_, y2) => {
          self.alloc(
            Coq_Numbers_BinNums_Z::Zneg(
              PhantomData,
              self.Coq_PArith_BinPosDef_Pos_add()(
                x2)(
                y2)))
        },
      }
    },
  }
}
fn Coq_ZArith_BinIntDef_Z_add__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  self.closure(move |x| {
    self.closure(move |y| {
      self.Coq_ZArith_BinIntDef_Z_add(
        x,
        y)
    })
  })
}


fn Coq_Init_Datatypes_orb__curried(&'a self) -> &'a dyn Fn(bool) -> &'a dyn Fn(bool) -> bool {
  self.closure(move |b1| {
    self.closure(move |b2| {
      __orb!(
        b1,
        b2)
    })
  })
}

fn Coq_PArith_BinPosDef_Pos_eqb(&'a self, p: &'a Coq_Numbers_BinNums_positive<'a>, q: &'a Coq_Numbers_BinNums_positive<'a>) -> bool {
  match p {
    &Coq_Numbers_BinNums_positive::xI(_, p2) => {
      match q {
        &Coq_Numbers_BinNums_positive::xI(_, q2) => {
          self.Coq_PArith_BinPosDef_Pos_eqb(
            p2,
            q2)
        },
        &Coq_Numbers_BinNums_positive::xO(_, p0) => {
          false
        },
        &Coq_Numbers_BinNums_positive::xH(_) => {
          false
        },
      }
    },
    &Coq_Numbers_BinNums_positive::xO(_, p2) => {
      match q {
        &Coq_Numbers_BinNums_positive::xI(_, p0) => {
          false
        },
        &Coq_Numbers_BinNums_positive::xO(_, q2) => {
          self.Coq_PArith_BinPosDef_Pos_eqb(
            p2,
            q2)
        },
        &Coq_Numbers_BinNums_positive::xH(_) => {
          false
        },
      }
    },
    &Coq_Numbers_BinNums_positive::xH(_) => {
      match q {
        &Coq_Numbers_BinNums_positive::xI(_, p0) => {
          false
        },
        &Coq_Numbers_BinNums_positive::xO(_, p0) => {
          false
        },
        &Coq_Numbers_BinNums_positive::xH(_) => {
          true
        },
      }
    },
  }
}
fn Coq_PArith_BinPosDef_Pos_eqb__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_positive<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_positive<'a>) -> bool {
  self.closure(move |p| {
    self.closure(move |q| {
      self.Coq_PArith_BinPosDef_Pos_eqb(
        p,
        q)
    })
  })
}

fn Coq_ZArith_BinIntDef_Z_eqb(&'a self, x: &'a Coq_Numbers_BinNums_Z<'a>, y: &'a Coq_Numbers_BinNums_Z<'a>) -> bool {
  match x {
    &Coq_Numbers_BinNums_Z::Z0(_) => {
      match y {
        &Coq_Numbers_BinNums_Z::Z0(_) => {
          true
        },
        &Coq_Numbers_BinNums_Z::Zpos(_, p) => {
          false
        },
        &Coq_Numbers_BinNums_Z::Zneg(_, p) => {
          false
        },
      }
    },
    &Coq_Numbers_BinNums_Z::Zpos(_, p) => {
      match y {
        &Coq_Numbers_BinNums_Z::Z0(_) => {
          false
        },
        &Coq_Numbers_BinNums_Z::Zpos(_, q) => {
          self.Coq_PArith_BinPosDef_Pos_eqb(
            p,
            q)
        },
        &Coq_Numbers_BinNums_Z::Zneg(_, p0) => {
          false
        },
      }
    },
    &Coq_Numbers_BinNums_Z::Zneg(_, p) => {
      match y {
        &Coq_Numbers_BinNums_Z::Z0(_) => {
          false
        },
        &Coq_Numbers_BinNums_Z::Zpos(_, p0) => {
          false
        },
        &Coq_Numbers_BinNums_Z::Zneg(_, q) => {
          self.Coq_PArith_BinPosDef_Pos_eqb(
            p,
            q)
        },
      }
    },
  }
}
fn Coq_ZArith_BinIntDef_Z_eqb__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> bool {
  self.closure(move |x| {
    self.closure(move |y| {
      self.Coq_ZArith_BinIntDef_Z_eqb(
        x,
        y)
    })
  })
}


fn Coq_Init_Datatypes_andb__curried(&'a self) -> &'a dyn Fn(bool) -> &'a dyn Fn(bool) -> bool {
  self.closure(move |b1| {
    self.closure(move |b2| {
      __andb!(
        b1,
        b2)
    })
  })
}

fn Coq_ZArith_BinIntDef_Z_odd(&'a self, z: &'a Coq_Numbers_BinNums_Z<'a>) -> bool {
  match z {
    &Coq_Numbers_BinNums_Z::Z0(_) => {
      false
    },
    &Coq_Numbers_BinNums_Z::Zpos(_, p) => {
      match p {
        &Coq_Numbers_BinNums_positive::xI(_, p0) => {
          true
        },
        &Coq_Numbers_BinNums_positive::xO(_, p0) => {
          false
        },
        &Coq_Numbers_BinNums_positive::xH(_) => {
          true
        },
      }
    },
    &Coq_Numbers_BinNums_Z::Zneg(_, p) => {
      match p {
        &Coq_Numbers_BinNums_positive::xI(_, p0) => {
          true
        },
        &Coq_Numbers_BinNums_positive::xO(_, p0) => {
          false
        },
        &Coq_Numbers_BinNums_positive::xH(_) => {
          true
        },
      }
    },
  }
}
fn Coq_ZArith_BinIntDef_Z_odd__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> bool {
  self.closure(move |z| {
    self.Coq_ZArith_BinIntDef_Z_odd(
      z)
  })
}

fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_odd(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> bool {
  self.Coq_ZArith_BinIntDef_Z_odd__curried()
}

fn Coq_ZArith_BinIntDef_Z_opp(&'a self, x: &'a Coq_Numbers_BinNums_Z<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  match x {
    &Coq_Numbers_BinNums_Z::Z0(_) => {
      self.alloc(
        Coq_Numbers_BinNums_Z::Z0(
          PhantomData))
    },
    &Coq_Numbers_BinNums_Z::Zpos(_, x2) => {
      self.alloc(
        Coq_Numbers_BinNums_Z::Zneg(
          PhantomData,
          x2))
    },
    &Coq_Numbers_BinNums_Z::Zneg(_, x2) => {
      self.alloc(
        Coq_Numbers_BinNums_Z::Zpos(
          PhantomData,
          x2))
    },
  }
}
fn Coq_ZArith_BinIntDef_Z_opp__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  self.closure(move |x| {
    self.Coq_ZArith_BinIntDef_Z_opp(
      x)
  })
}

fn Coq_ZArith_BinIntDef_Z_sub(&'a self, m: &'a Coq_Numbers_BinNums_Z<'a>, n: &'a Coq_Numbers_BinNums_Z<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  self.Coq_ZArith_BinIntDef_Z_add(
    m,
    self.Coq_ZArith_BinIntDef_Z_opp(
      n))
}
fn Coq_ZArith_BinIntDef_Z_sub__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  self.closure(move |m| {
    self.closure(move |n| {
      self.Coq_ZArith_BinIntDef_Z_sub(
        m,
        n)
    })
  })
}

fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_shiftr(&'a self, a: &'a Coq_Numbers_BinNums_Z<'a>, b: &'a Coq_Numbers_BinNums_Z<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  match match b {
          &Coq_Numbers_BinNums_Z::Z0(_) => {
            self.alloc(
              Coq_Numbers_BinNums_Z::Z0(
                PhantomData))
          },
          &Coq_Numbers_BinNums_Z::Zpos(_, x) => {
            self.alloc(
              Coq_Numbers_BinNums_Z::Zneg(
                PhantomData,
                x))
          },
          &Coq_Numbers_BinNums_Z::Zneg(_, x) => {
            self.alloc(
              Coq_Numbers_BinNums_Z::Zpos(
                PhantomData,
                x))
          },
        } {
    &Coq_Numbers_BinNums_Z::Z0(_) => {
      a
    },
    &Coq_Numbers_BinNums_Z::Zpos(_, p) => {
      hint_app(hint_app({ let iter_fix = self.alloc(std::cell::Cell::new(None));
                          iter_fix.set(Some(
                            self.closure(move |x| {
                              self.closure(move |n| {
                                match n {
                                  &Coq_Numbers_BinNums_positive::xI(_, n2) => {
                                    match hint_app(hint_app(iter_fix.get().unwrap())(hint_app(hint_app(iter_fix.get().unwrap())(x))(n2)))(n2) {
                                      &Coq_Numbers_BinNums_Z::Z0(_) => {
                                        self.alloc(
                                          Coq_Numbers_BinNums_Z::Z0(
                                            PhantomData))
                                      },
                                      &Coq_Numbers_BinNums_Z::Zpos(_, y) => {
                                        self.alloc(
                                          Coq_Numbers_BinNums_Z::Zpos(
                                            PhantomData,
                                            self.alloc(
                                              Coq_Numbers_BinNums_positive::xO(
                                                PhantomData,
                                                y))))
                                      },
                                      &Coq_Numbers_BinNums_Z::Zneg(_, y) => {
                                        self.alloc(
                                          Coq_Numbers_BinNums_Z::Zneg(
                                            PhantomData,
                                            self.alloc(
                                              Coq_Numbers_BinNums_positive::xO(
                                                PhantomData,
                                                y))))
                                      },
                                    }
                                  },
                                  &Coq_Numbers_BinNums_positive::xO(_, n2) => {
                                    hint_app(hint_app(iter_fix.get().unwrap())(hint_app(hint_app(iter_fix.get().unwrap())(x))(n2)))(n2)
                                  },
                                  &Coq_Numbers_BinNums_positive::xH(_) => {
                                    match x {
                                      &Coq_Numbers_BinNums_Z::Z0(_) => {
                                        self.alloc(
                                          Coq_Numbers_BinNums_Z::Z0(
                                            PhantomData))
                                      },
                                      &Coq_Numbers_BinNums_Z::Zpos(_, y) => {
                                        self.alloc(
                                          Coq_Numbers_BinNums_Z::Zpos(
                                            PhantomData,
                                            self.alloc(
                                              Coq_Numbers_BinNums_positive::xO(
                                                PhantomData,
                                                y))))
                                      },
                                      &Coq_Numbers_BinNums_Z::Zneg(_, y) => {
                                        self.alloc(
                                          Coq_Numbers_BinNums_Z::Zneg(
                                            PhantomData,
                                            self.alloc(
                                              Coq_Numbers_BinNums_positive::xO(
                                                PhantomData,
                                                y))))
                                      },
                                    }
                                  },
                                }
                              })
                            })));
                          iter_fix.get().unwrap() })(a))(p)
    },
    &Coq_Numbers_BinNums_Z::Zneg(_, p) => {
      hint_app(hint_app({ let iter_fix2 = self.alloc(std::cell::Cell::new(None));
                          iter_fix2.set(Some(
                            self.closure(move |x| {
                              self.closure(move |n| {
                                match n {
                                  &Coq_Numbers_BinNums_positive::xI(_, n2) => {
                                    match hint_app(hint_app(iter_fix2.get().unwrap())(hint_app(hint_app(iter_fix2.get().unwrap())(x))(n2)))(n2) {
                                      &Coq_Numbers_BinNums_Z::Z0(_) => {
                                        self.alloc(
                                          Coq_Numbers_BinNums_Z::Z0(
                                            PhantomData))
                                      },
                                      &Coq_Numbers_BinNums_Z::Zpos(_, p2) => {
                                        match p2 {
                                          &Coq_Numbers_BinNums_positive::xI(_, p0) => {
                                            self.alloc(
                                              Coq_Numbers_BinNums_Z::Zpos(
                                                PhantomData,
                                                match p2 {
                                                  &Coq_Numbers_BinNums_positive::xI(_, p3) => {
                                                    p3
                                                  },
                                                  &Coq_Numbers_BinNums_positive::xO(_, p3) => {
                                                    p3
                                                  },
                                                  &Coq_Numbers_BinNums_positive::xH(_) => {
                                                    self.alloc(
                                                      Coq_Numbers_BinNums_positive::xH(
                                                        PhantomData))
                                                  },
                                                }))
                                          },
                                          &Coq_Numbers_BinNums_positive::xO(_, p0) => {
                                            self.alloc(
                                              Coq_Numbers_BinNums_Z::Zpos(
                                                PhantomData,
                                                match p2 {
                                                  &Coq_Numbers_BinNums_positive::xI(_, p3) => {
                                                    p3
                                                  },
                                                  &Coq_Numbers_BinNums_positive::xO(_, p3) => {
                                                    p3
                                                  },
                                                  &Coq_Numbers_BinNums_positive::xH(_) => {
                                                    self.alloc(
                                                      Coq_Numbers_BinNums_positive::xH(
                                                        PhantomData))
                                                  },
                                                }))
                                          },
                                          &Coq_Numbers_BinNums_positive::xH(_) => {
                                            self.alloc(
                                              Coq_Numbers_BinNums_Z::Z0(
                                                PhantomData))
                                          },
                                        }
                                      },
                                      &Coq_Numbers_BinNums_Z::Zneg(_, p2) => {
                                        self.alloc(
                                          Coq_Numbers_BinNums_Z::Zneg(
                                            PhantomData,
                                            match p2 {
                                              &Coq_Numbers_BinNums_positive::xI(_, p3) => {
                                                hint_app({ let succ = self.alloc(std::cell::Cell::new(None));
                                                           succ.set(Some(
                                                             self.closure(move |x2| {
                                                               match x2 {
                                                                 &Coq_Numbers_BinNums_positive::xI(_, p4) => {
                                                                   self.alloc(
                                                                     Coq_Numbers_BinNums_positive::xO(
                                                                       PhantomData,
                                                                       hint_app(succ.get().unwrap())(p4)))
                                                                 },
                                                                 &Coq_Numbers_BinNums_positive::xO(_, p4) => {
                                                                   self.alloc(
                                                                     Coq_Numbers_BinNums_positive::xI(
                                                                       PhantomData,
                                                                       p4))
                                                                 },
                                                                 &Coq_Numbers_BinNums_positive::xH(_) => {
                                                                   self.alloc(
                                                                     Coq_Numbers_BinNums_positive::xO(
                                                                       PhantomData,
                                                                       self.alloc(
                                                                         Coq_Numbers_BinNums_positive::xH(
                                                                           PhantomData))))
                                                                 },
                                                               }
                                                             })));
                                                           succ.get().unwrap() })(p3)
                                              },
                                              &Coq_Numbers_BinNums_positive::xO(_, p3) => {
                                                p3
                                              },
                                              &Coq_Numbers_BinNums_positive::xH(_) => {
                                                self.alloc(
                                                  Coq_Numbers_BinNums_positive::xH(
                                                    PhantomData))
                                              },
                                            }))
                                      },
                                    }
                                  },
                                  &Coq_Numbers_BinNums_positive::xO(_, n2) => {
                                    hint_app(hint_app(iter_fix2.get().unwrap())(hint_app(hint_app(iter_fix2.get().unwrap())(x))(n2)))(n2)
                                  },
                                  &Coq_Numbers_BinNums_positive::xH(_) => {
                                    match x {
                                      &Coq_Numbers_BinNums_Z::Z0(_) => {
                                        self.alloc(
                                          Coq_Numbers_BinNums_Z::Z0(
                                            PhantomData))
                                      },
                                      &Coq_Numbers_BinNums_Z::Zpos(_, p2) => {
                                        match p2 {
                                          &Coq_Numbers_BinNums_positive::xI(_, p0) => {
                                            self.alloc(
                                              Coq_Numbers_BinNums_Z::Zpos(
                                                PhantomData,
                                                match p2 {
                                                  &Coq_Numbers_BinNums_positive::xI(_, p3) => {
                                                    p3
                                                  },
                                                  &Coq_Numbers_BinNums_positive::xO(_, p3) => {
                                                    p3
                                                  },
                                                  &Coq_Numbers_BinNums_positive::xH(_) => {
                                                    self.alloc(
                                                      Coq_Numbers_BinNums_positive::xH(
                                                        PhantomData))
                                                  },
                                                }))
                                          },
                                          &Coq_Numbers_BinNums_positive::xO(_, p0) => {
                                            self.alloc(
                                              Coq_Numbers_BinNums_Z::Zpos(
                                                PhantomData,
                                                match p2 {
                                                  &Coq_Numbers_BinNums_positive::xI(_, p3) => {
                                                    p3
                                                  },
                                                  &Coq_Numbers_BinNums_positive::xO(_, p3) => {
                                                    p3
                                                  },
                                                  &Coq_Numbers_BinNums_positive::xH(_) => {
                                                    self.alloc(
                                                      Coq_Numbers_BinNums_positive::xH(
                                                        PhantomData))
                                                  },
                                                }))
                                          },
                                          &Coq_Numbers_BinNums_positive::xH(_) => {
                                            self.alloc(
                                              Coq_Numbers_BinNums_Z::Z0(
                                                PhantomData))
                                          },
                                        }
                                      },
                                      &Coq_Numbers_BinNums_Z::Zneg(_, p2) => {
                                        self.alloc(
                                          Coq_Numbers_BinNums_Z::Zneg(
                                            PhantomData,
                                            match p2 {
                                              &Coq_Numbers_BinNums_positive::xI(_, p3) => {
                                                hint_app({ let succ2 = self.alloc(std::cell::Cell::new(None));
                                                           succ2.set(Some(
                                                             self.closure(move |x2| {
                                                               match x2 {
                                                                 &Coq_Numbers_BinNums_positive::xI(_, p4) => {
                                                                   self.alloc(
                                                                     Coq_Numbers_BinNums_positive::xO(
                                                                       PhantomData,
                                                                       hint_app(succ2.get().unwrap())(p4)))
                                                                 },
                                                                 &Coq_Numbers_BinNums_positive::xO(_, p4) => {
                                                                   self.alloc(
                                                                     Coq_Numbers_BinNums_positive::xI(
                                                                       PhantomData,
                                                                       p4))
                                                                 },
                                                                 &Coq_Numbers_BinNums_positive::xH(_) => {
                                                                   self.alloc(
                                                                     Coq_Numbers_BinNums_positive::xO(
                                                                       PhantomData,
                                                                       self.alloc(
                                                                         Coq_Numbers_BinNums_positive::xH(
                                                                           PhantomData))))
                                                                 },
                                                               }
                                                             })));
                                                           succ2.get().unwrap() })(p3)
                                              },
                                              &Coq_Numbers_BinNums_positive::xO(_, p3) => {
                                                p3
                                              },
                                              &Coq_Numbers_BinNums_positive::xH(_) => {
                                                self.alloc(
                                                  Coq_Numbers_BinNums_positive::xH(
                                                    PhantomData))
                                              },
                                            }))
                                      },
                                    }
                                  },
                                }
                              })
                            })));
                          iter_fix2.get().unwrap() })(a))(p)
    },
  }
}
fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_shiftr__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  self.closure(move |a| {
    self.closure(move |b| {
      self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_shiftr(
        a,
        b)
    })
  })
}

fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_divstep(&'a self, d: &'a Coq_Numbers_BinNums_Z<'a>, f: &'a Coq_Numbers_BinNums_Z<'a>, g: &'a Coq_Numbers_BinNums_Z<'a>) -> __pair<__pair<&'a Coq_Numbers_BinNums_Z<'a>, &'a Coq_Numbers_BinNums_Z<'a>>, &'a Coq_Numbers_BinNums_Z<'a>> {
  match __andb!(
          self.Coq_ZArith_BinIntDef_Z_ltb(
            self.alloc(
              Coq_Numbers_BinNums_Z::Z0(
                PhantomData)),
            d),
          self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_odd()(
            g)) {
    true => {
      __mk_pair(
        __mk_pair(
          self.Coq_ZArith_BinIntDef_Z_sub(
            self.alloc(
              Coq_Numbers_BinNums_Z::Zpos(
                PhantomData,
                self.alloc(
                  Coq_Numbers_BinNums_positive::xH(
                    PhantomData)))),
            d),
          g),
        self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_shiftr(
          self.Coq_ZArith_BinIntDef_Z_sub(
            g,
            f),
          self.alloc(
            Coq_Numbers_BinNums_Z::Zpos(
              PhantomData,
              self.alloc(
                Coq_Numbers_BinNums_positive::xH(
                  PhantomData))))))
    },
    false => {
      __mk_pair(
        __mk_pair(
          self.Coq_ZArith_BinIntDef_Z_add(
            self.alloc(
              Coq_Numbers_BinNums_Z::Zpos(
                PhantomData,
                self.alloc(
                  Coq_Numbers_BinNums_positive::xH(
                    PhantomData)))),
            d),
          f),
        self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_shiftr(
          self.Coq_ZArith_BinIntDef_Z_add(
            g,
            self.Coq_ZArith_BinIntDef_Z_mul(
              match self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_odd()(
                      g) {
                true => {
                  self.alloc(
                    Coq_Numbers_BinNums_Z::Zpos(
                      PhantomData,
                      self.alloc(
                        Coq_Numbers_BinNums_positive::xH(
                          PhantomData))))
                },
                false => {
                  self.alloc(
                    Coq_Numbers_BinNums_Z::Z0(
                      PhantomData))
                },
              },
              f)),
          self.alloc(
            Coq_Numbers_BinNums_Z::Zpos(
              PhantomData,
              self.alloc(
                Coq_Numbers_BinNums_positive::xH(
                  PhantomData))))))
    },
  }
}
fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_divstep__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> __pair<__pair<&'a Coq_Numbers_BinNums_Z<'a>, &'a Coq_Numbers_BinNums_Z<'a>>, &'a Coq_Numbers_BinNums_Z<'a>> {
  self.closure(move |d| {
    self.closure(move |f| {
      self.closure(move |g| {
        self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_divstep(
          d,
          f,
          g)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_needs_n_steps(&'a self, d: &'a Coq_Numbers_BinNums_Z<'a>, a: &'a Coq_Numbers_BinNums_Z<'a>, b: &'a Coq_Numbers_BinNums_Z<'a>, n: &'a Coq_Init_Datatypes_nat<'a>) -> bool {
  match n {
    &Coq_Init_Datatypes_nat::O(_) => {
      true
    },
    &Coq_Init_Datatypes_nat::S(_, n2) => {
      match self.Coq_ZArith_BinIntDef_Z_eqb(
              b,
              self.alloc(
                Coq_Numbers_BinNums_Z::Z0(
                  PhantomData))) {
        true => {
          false
        },
        false => {
          __pair_elim!(
            b2, p, {
              __pair_elim!(
                a2, d2, {
                  self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_needs_n_steps(
                    a2,
                    d2,
                    p,
                    n2)
                },
                b2)
            },
            self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_divstep(
              d,
              a,
              b))
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_needs_n_steps__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_nat<'a>) -> bool {
  self.closure(move |d| {
    self.closure(move |a| {
      self.closure(move |b| {
        self.closure(move |n| {
          self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_needs_n_steps(
            d,
            a,
            b,
            n)
        })
      })
    })
  })
}

fn Coq_ZArith_BinIntDef_Z_min(&'a self, n: &'a Coq_Numbers_BinNums_Z<'a>, m: &'a Coq_Numbers_BinNums_Z<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  match self.Coq_ZArith_BinIntDef_Z_compare(
          n,
          m) {
    &Coq_Init_Datatypes_comparison::Eq(_) => {
      n
    },
    &Coq_Init_Datatypes_comparison::Lt(_) => {
      n
    },
    &Coq_Init_Datatypes_comparison::Gt(_) => {
      m
    },
  }
}
fn Coq_ZArith_BinIntDef_Z_min__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  self.closure(move |n| {
    self.closure(move |m| {
      self.Coq_ZArith_BinIntDef_Z_min(
        n,
        m)
    })
  })
}

fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_min_needs_n_steps_nat(&'a self, a: &'a Coq_Numbers_BinNums_Z<'a>, b: &'a Coq_Numbers_BinNums_Z<'a>, n: &'a Coq_Init_Datatypes_nat<'a>, acc: &'a Coq_Numbers_BinNums_Z<'a>, fuel: &'a Coq_Init_Datatypes_nat<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  match fuel {
    &Coq_Init_Datatypes_nat::O(_) => {
      self.alloc(
        Coq_Numbers_BinNums_Z::Z0(
          PhantomData))
    },
    &Coq_Init_Datatypes_nat::S(_, fuel2) => {
      let a2 =
        self.Coq_ZArith_BinIntDef_Z_mul(
          a,
          a);
      match self.Coq_ZArith_BinIntDef_Z_ltb(
              acc,
              a2) {
        true => {
          acc
        },
        false => {
          let length =
            self.Coq_ZArith_BinIntDef_Z_add(
              a2,
              self.Coq_ZArith_BinIntDef_Z_mul(
                b,
                b));
          match self.Coq_ZArith_BinIntDef_Z_ltb(
                  acc,
                  length) {
            true => {
              self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_min_needs_n_steps_nat(
                self.Coq_ZArith_BinIntDef_Z_add(
                  a,
                  self.alloc(
                    Coq_Numbers_BinNums_Z::Zpos(
                      PhantomData,
                      self.alloc(
                        Coq_Numbers_BinNums_positive::xO(
                          PhantomData,
                          self.alloc(
                            Coq_Numbers_BinNums_positive::xH(
                              PhantomData))))))),
                self.alloc(
                  Coq_Numbers_BinNums_Z::Z0(
                    PhantomData)),
                n,
                acc,
                fuel2)
            },
            false => {
              match __orb!(
                      self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_needs_n_steps(
                        self.alloc(
                          Coq_Numbers_BinNums_Z::Zpos(
                            PhantomData,
                            self.alloc(
                              Coq_Numbers_BinNums_positive::xH(
                                PhantomData)))),
                        a,
                        self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_shiftr(
                          b,
                          self.alloc(
                            Coq_Numbers_BinNums_Z::Zpos(
                              PhantomData,
                              self.alloc(
                                Coq_Numbers_BinNums_positive::xH(
                                  PhantomData))))),
                        n),
                      self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_needs_n_steps(
                        self.alloc(
                          Coq_Numbers_BinNums_Z::Zpos(
                            PhantomData,
                            self.alloc(
                              Coq_Numbers_BinNums_positive::xH(
                                PhantomData)))),
                        a,
                        self.Coq_ZArith_BinIntDef_Z_opp(
                          self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_shiftr(
                            b,
                            self.alloc(
                              Coq_Numbers_BinNums_Z::Zpos(
                                PhantomData,
                                self.alloc(
                                  Coq_Numbers_BinNums_positive::xH(
                                    PhantomData)))))),
                        n)) {
                true => {
                  self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_min_needs_n_steps_nat(
                    self.Coq_ZArith_BinIntDef_Z_add(
                      a,
                      self.alloc(
                        Coq_Numbers_BinNums_Z::Zpos(
                          PhantomData,
                          self.alloc(
                            Coq_Numbers_BinNums_positive::xO(
                              PhantomData,
                              self.alloc(
                                Coq_Numbers_BinNums_positive::xH(
                                  PhantomData))))))),
                    self.alloc(
                      Coq_Numbers_BinNums_Z::Z0(
                        PhantomData)),
                    n,
                    self.Coq_ZArith_BinIntDef_Z_min(
                      length,
                      acc),
                    fuel2)
                },
                false => {
                  self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_min_needs_n_steps_nat(
                    a,
                    self.Coq_ZArith_BinIntDef_Z_add(
                      b,
                      self.alloc(
                        Coq_Numbers_BinNums_Z::Zpos(
                          PhantomData,
                          self.alloc(
                            Coq_Numbers_BinNums_positive::xO(
                              PhantomData,
                              self.alloc(
                                Coq_Numbers_BinNums_positive::xH(
                                  PhantomData))))))),
                    n,
                    acc,
                    fuel2)
                },
              }
            },
          }
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_min_needs_n_steps_nat__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_nat<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_nat<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  self.closure(move |a| {
    self.closure(move |b| {
      self.closure(move |n| {
        self.closure(move |acc| {
          self.closure(move |fuel| {
            self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_min_needs_n_steps_nat(
              a,
              b,
              n,
              acc,
              fuel)
          })
        })
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_shiftl(&'a self, a: &'a Coq_Numbers_BinNums_Z<'a>, b: &'a Coq_Numbers_BinNums_Z<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  match b {
    &Coq_Numbers_BinNums_Z::Z0(_) => {
      a
    },
    &Coq_Numbers_BinNums_Z::Zpos(_, p) => {
      hint_app(hint_app({ let iter_fix3 = self.alloc(std::cell::Cell::new(None));
                          iter_fix3.set(Some(
                            self.closure(move |x| {
                              self.closure(move |n| {
                                match n {
                                  &Coq_Numbers_BinNums_positive::xI(_, n2) => {
                                    match hint_app(hint_app(iter_fix3.get().unwrap())(hint_app(hint_app(iter_fix3.get().unwrap())(x))(n2)))(n2) {
                                      &Coq_Numbers_BinNums_Z::Z0(_) => {
                                        self.alloc(
                                          Coq_Numbers_BinNums_Z::Z0(
                                            PhantomData))
                                      },
                                      &Coq_Numbers_BinNums_Z::Zpos(_, y) => {
                                        self.alloc(
                                          Coq_Numbers_BinNums_Z::Zpos(
                                            PhantomData,
                                            self.alloc(
                                              Coq_Numbers_BinNums_positive::xO(
                                                PhantomData,
                                                y))))
                                      },
                                      &Coq_Numbers_BinNums_Z::Zneg(_, y) => {
                                        self.alloc(
                                          Coq_Numbers_BinNums_Z::Zneg(
                                            PhantomData,
                                            self.alloc(
                                              Coq_Numbers_BinNums_positive::xO(
                                                PhantomData,
                                                y))))
                                      },
                                    }
                                  },
                                  &Coq_Numbers_BinNums_positive::xO(_, n2) => {
                                    hint_app(hint_app(iter_fix3.get().unwrap())(hint_app(hint_app(iter_fix3.get().unwrap())(x))(n2)))(n2)
                                  },
                                  &Coq_Numbers_BinNums_positive::xH(_) => {
                                    match x {
                                      &Coq_Numbers_BinNums_Z::Z0(_) => {
                                        self.alloc(
                                          Coq_Numbers_BinNums_Z::Z0(
                                            PhantomData))
                                      },
                                      &Coq_Numbers_BinNums_Z::Zpos(_, y) => {
                                        self.alloc(
                                          Coq_Numbers_BinNums_Z::Zpos(
                                            PhantomData,
                                            self.alloc(
                                              Coq_Numbers_BinNums_positive::xO(
                                                PhantomData,
                                                y))))
                                      },
                                      &Coq_Numbers_BinNums_Z::Zneg(_, y) => {
                                        self.alloc(
                                          Coq_Numbers_BinNums_Z::Zneg(
                                            PhantomData,
                                            self.alloc(
                                              Coq_Numbers_BinNums_positive::xO(
                                                PhantomData,
                                                y))))
                                      },
                                    }
                                  },
                                }
                              })
                            })));
                          iter_fix3.get().unwrap() })(a))(p)
    },
    &Coq_Numbers_BinNums_Z::Zneg(_, p) => {
      hint_app(hint_app({ let iter_fix4 = self.alloc(std::cell::Cell::new(None));
                          iter_fix4.set(Some(
                            self.closure(move |x| {
                              self.closure(move |n| {
                                match n {
                                  &Coq_Numbers_BinNums_positive::xI(_, n2) => {
                                    match hint_app(hint_app(iter_fix4.get().unwrap())(hint_app(hint_app(iter_fix4.get().unwrap())(x))(n2)))(n2) {
                                      &Coq_Numbers_BinNums_Z::Z0(_) => {
                                        self.alloc(
                                          Coq_Numbers_BinNums_Z::Z0(
                                            PhantomData))
                                      },
                                      &Coq_Numbers_BinNums_Z::Zpos(_, p2) => {
                                        match p2 {
                                          &Coq_Numbers_BinNums_positive::xI(_, p0) => {
                                            self.alloc(
                                              Coq_Numbers_BinNums_Z::Zpos(
                                                PhantomData,
                                                match p2 {
                                                  &Coq_Numbers_BinNums_positive::xI(_, p3) => {
                                                    p3
                                                  },
                                                  &Coq_Numbers_BinNums_positive::xO(_, p3) => {
                                                    p3
                                                  },
                                                  &Coq_Numbers_BinNums_positive::xH(_) => {
                                                    self.alloc(
                                                      Coq_Numbers_BinNums_positive::xH(
                                                        PhantomData))
                                                  },
                                                }))
                                          },
                                          &Coq_Numbers_BinNums_positive::xO(_, p0) => {
                                            self.alloc(
                                              Coq_Numbers_BinNums_Z::Zpos(
                                                PhantomData,
                                                match p2 {
                                                  &Coq_Numbers_BinNums_positive::xI(_, p3) => {
                                                    p3
                                                  },
                                                  &Coq_Numbers_BinNums_positive::xO(_, p3) => {
                                                    p3
                                                  },
                                                  &Coq_Numbers_BinNums_positive::xH(_) => {
                                                    self.alloc(
                                                      Coq_Numbers_BinNums_positive::xH(
                                                        PhantomData))
                                                  },
                                                }))
                                          },
                                          &Coq_Numbers_BinNums_positive::xH(_) => {
                                            self.alloc(
                                              Coq_Numbers_BinNums_Z::Z0(
                                                PhantomData))
                                          },
                                        }
                                      },
                                      &Coq_Numbers_BinNums_Z::Zneg(_, p2) => {
                                        self.alloc(
                                          Coq_Numbers_BinNums_Z::Zneg(
                                            PhantomData,
                                            match p2 {
                                              &Coq_Numbers_BinNums_positive::xI(_, p3) => {
                                                hint_app({ let succ3 = self.alloc(std::cell::Cell::new(None));
                                                           succ3.set(Some(
                                                             self.closure(move |x2| {
                                                               match x2 {
                                                                 &Coq_Numbers_BinNums_positive::xI(_, p4) => {
                                                                   self.alloc(
                                                                     Coq_Numbers_BinNums_positive::xO(
                                                                       PhantomData,
                                                                       hint_app(succ3.get().unwrap())(p4)))
                                                                 },
                                                                 &Coq_Numbers_BinNums_positive::xO(_, p4) => {
                                                                   self.alloc(
                                                                     Coq_Numbers_BinNums_positive::xI(
                                                                       PhantomData,
                                                                       p4))
                                                                 },
                                                                 &Coq_Numbers_BinNums_positive::xH(_) => {
                                                                   self.alloc(
                                                                     Coq_Numbers_BinNums_positive::xO(
                                                                       PhantomData,
                                                                       self.alloc(
                                                                         Coq_Numbers_BinNums_positive::xH(
                                                                           PhantomData))))
                                                                 },
                                                               }
                                                             })));
                                                           succ3.get().unwrap() })(p3)
                                              },
                                              &Coq_Numbers_BinNums_positive::xO(_, p3) => {
                                                p3
                                              },
                                              &Coq_Numbers_BinNums_positive::xH(_) => {
                                                self.alloc(
                                                  Coq_Numbers_BinNums_positive::xH(
                                                    PhantomData))
                                              },
                                            }))
                                      },
                                    }
                                  },
                                  &Coq_Numbers_BinNums_positive::xO(_, n2) => {
                                    hint_app(hint_app(iter_fix4.get().unwrap())(hint_app(hint_app(iter_fix4.get().unwrap())(x))(n2)))(n2)
                                  },
                                  &Coq_Numbers_BinNums_positive::xH(_) => {
                                    match x {
                                      &Coq_Numbers_BinNums_Z::Z0(_) => {
                                        self.alloc(
                                          Coq_Numbers_BinNums_Z::Z0(
                                            PhantomData))
                                      },
                                      &Coq_Numbers_BinNums_Z::Zpos(_, p2) => {
                                        match p2 {
                                          &Coq_Numbers_BinNums_positive::xI(_, p0) => {
                                            self.alloc(
                                              Coq_Numbers_BinNums_Z::Zpos(
                                                PhantomData,
                                                match p2 {
                                                  &Coq_Numbers_BinNums_positive::xI(_, p3) => {
                                                    p3
                                                  },
                                                  &Coq_Numbers_BinNums_positive::xO(_, p3) => {
                                                    p3
                                                  },
                                                  &Coq_Numbers_BinNums_positive::xH(_) => {
                                                    self.alloc(
                                                      Coq_Numbers_BinNums_positive::xH(
                                                        PhantomData))
                                                  },
                                                }))
                                          },
                                          &Coq_Numbers_BinNums_positive::xO(_, p0) => {
                                            self.alloc(
                                              Coq_Numbers_BinNums_Z::Zpos(
                                                PhantomData,
                                                match p2 {
                                                  &Coq_Numbers_BinNums_positive::xI(_, p3) => {
                                                    p3
                                                  },
                                                  &Coq_Numbers_BinNums_positive::xO(_, p3) => {
                                                    p3
                                                  },
                                                  &Coq_Numbers_BinNums_positive::xH(_) => {
                                                    self.alloc(
                                                      Coq_Numbers_BinNums_positive::xH(
                                                        PhantomData))
                                                  },
                                                }))
                                          },
                                          &Coq_Numbers_BinNums_positive::xH(_) => {
                                            self.alloc(
                                              Coq_Numbers_BinNums_Z::Z0(
                                                PhantomData))
                                          },
                                        }
                                      },
                                      &Coq_Numbers_BinNums_Z::Zneg(_, p2) => {
                                        self.alloc(
                                          Coq_Numbers_BinNums_Z::Zneg(
                                            PhantomData,
                                            match p2 {
                                              &Coq_Numbers_BinNums_positive::xI(_, p3) => {
                                                hint_app({ let succ4 = self.alloc(std::cell::Cell::new(None));
                                                           succ4.set(Some(
                                                             self.closure(move |x2| {
                                                               match x2 {
                                                                 &Coq_Numbers_BinNums_positive::xI(_, p4) => {
                                                                   self.alloc(
                                                                     Coq_Numbers_BinNums_positive::xO(
                                                                       PhantomData,
                                                                       hint_app(succ4.get().unwrap())(p4)))
                                                                 },
                                                                 &Coq_Numbers_BinNums_positive::xO(_, p4) => {
                                                                   self.alloc(
                                                                     Coq_Numbers_BinNums_positive::xI(
                                                                       PhantomData,
                                                                       p4))
                                                                 },
                                                                 &Coq_Numbers_BinNums_positive::xH(_) => {
                                                                   self.alloc(
                                                                     Coq_Numbers_BinNums_positive::xO(
                                                                       PhantomData,
                                                                       self.alloc(
                                                                         Coq_Numbers_BinNums_positive::xH(
                                                                           PhantomData))))
                                                                 },
                                                               }
                                                             })));
                                                           succ4.get().unwrap() })(p3)
                                              },
                                              &Coq_Numbers_BinNums_positive::xO(_, p3) => {
                                                p3
                                              },
                                              &Coq_Numbers_BinNums_positive::xH(_) => {
                                                self.alloc(
                                                  Coq_Numbers_BinNums_positive::xH(
                                                    PhantomData))
                                              },
                                            }))
                                      },
                                    }
                                  },
                                }
                              })
                            })));
                          iter_fix4.get().unwrap() })(a))(p)
    },
  }
}
fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_shiftl__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_Z<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  self.closure(move |a| {
    self.closure(move |b| {
      self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_shiftl(
        a,
        b)
    })
  })
}

fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_nat_shiftl(&'a self, a: &'a Coq_Init_Datatypes_nat<'a>, n: &'a Coq_Init_Datatypes_nat<'a>) -> &'a Coq_Init_Datatypes_nat<'a> {
  match n {
    &Coq_Init_Datatypes_nat::O(_) => {
      a
    },
    &Coq_Init_Datatypes_nat::S(_, n2) => {
      hint_app(hint_app({ let add2 = self.alloc(std::cell::Cell::new(None));
                          add2.set(Some(
                            self.closure(move |n3| {
                              self.closure(move |m| {
                                match n3 {
                                  &Coq_Init_Datatypes_nat::O(_) => {
                                    m
                                  },
                                  &Coq_Init_Datatypes_nat::S(_, p) => {
                                    self.alloc(
                                      Coq_Init_Datatypes_nat::S(
                                        PhantomData,
                                        hint_app(hint_app(add2.get().unwrap())(p))(m)))
                                  },
                                }
                              })
                            })));
                          add2.get().unwrap() })(self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_nat_shiftl(
                                                   a,
                                                   n2)))(self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_nat_shiftl(
                                                           a,
                                                           n2))
    },
  }
}
fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_nat_shiftl__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_nat<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_nat<'a>) -> &'a Coq_Init_Datatypes_nat<'a> {
  self.closure(move |a| {
    self.closure(move |n| {
      self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_nat_shiftl(
        a,
        n)
    })
  })
}

fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_W(&'a self, n: &'a Coq_Init_Datatypes_nat<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_min_needs_n_steps_nat(
    self.alloc(
      Coq_Numbers_BinNums_Z::Zpos(
        PhantomData,
        self.alloc(
          Coq_Numbers_BinNums_positive::xH(
            PhantomData)))),
    self.alloc(
      Coq_Numbers_BinNums_Z::Z0(
        PhantomData)),
    n,
    self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_shiftl(
      self.alloc(
        Coq_Numbers_BinNums_Z::Zpos(
          PhantomData,
          self.alloc(
            Coq_Numbers_BinNums_positive::xH(
              PhantomData)))),
      self.alloc(
        Coq_Numbers_BinNums_Z::Zpos(
          PhantomData,
          self.alloc(
            Coq_Numbers_BinNums_positive::xO(
              PhantomData,
              self.alloc(
                Coq_Numbers_BinNums_positive::xI(
                  PhantomData,
                  self.alloc(
                    Coq_Numbers_BinNums_positive::xI(
                      PhantomData,
                      self.alloc(
                        Coq_Numbers_BinNums_positive::xI(
                          PhantomData,
                          self.alloc(
                            Coq_Numbers_BinNums_positive::xI(
                              PhantomData,
                              self.alloc(
                                Coq_Numbers_BinNums_positive::xH(
                                  PhantomData))))))))))))))),
    self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_nat_shiftl(
      self.alloc(
        Coq_Init_Datatypes_nat::S(
          PhantomData,
          self.alloc(
            Coq_Init_Datatypes_nat::O(
              PhantomData)))),
      self.alloc(
        Coq_Init_Datatypes_nat::S(
          PhantomData,
          self.alloc(
            Coq_Init_Datatypes_nat::S(
              PhantomData,
              self.alloc(
                Coq_Init_Datatypes_nat::S(
                  PhantomData,
                  self.alloc(
                    Coq_Init_Datatypes_nat::S(
                      PhantomData,
                      self.alloc(
                        Coq_Init_Datatypes_nat::S(
                          PhantomData,
                          self.alloc(
                            Coq_Init_Datatypes_nat::S(
                              PhantomData,
                              self.alloc(
                                Coq_Init_Datatypes_nat::S(
                                  PhantomData,
                                  self.alloc(
                                    Coq_Init_Datatypes_nat::S(
                                      PhantomData,
                                      self.alloc(
                                        Coq_Init_Datatypes_nat::S(
                                          PhantomData,
                                          self.alloc(
                                            Coq_Init_Datatypes_nat::S(
                                              PhantomData,
                                              self.alloc(
                                                Coq_Init_Datatypes_nat::S(
                                                  PhantomData,
                                                  self.alloc(
                                                    Coq_Init_Datatypes_nat::S(
                                                      PhantomData,
                                                      self.alloc(
                                                        Coq_Init_Datatypes_nat::S(
                                                          PhantomData,
                                                          self.alloc(
                                                            Coq_Init_Datatypes_nat::S(
                                                              PhantomData,
                                                              self.alloc(
                                                                Coq_Init_Datatypes_nat::S(
                                                                  PhantomData,
                                                                  self.alloc(
                                                                    Coq_Init_Datatypes_nat::S(
                                                                      PhantomData,
                                                                      self.alloc(
                                                                        Coq_Init_Datatypes_nat::S(
                                                                          PhantomData,
                                                                          self.alloc(
                                                                            Coq_Init_Datatypes_nat::S(
                                                                              PhantomData,
                                                                              self.alloc(
                                                                                Coq_Init_Datatypes_nat::S(
                                                                                  PhantomData,
                                                                                  self.alloc(
                                                                                    Coq_Init_Datatypes_nat::S(
                                                                                      PhantomData,
                                                                                      self.alloc(
                                                                                        Coq_Init_Datatypes_nat::S(
                                                                                          PhantomData,
                                                                                          self.alloc(
                                                                                            Coq_Init_Datatypes_nat::S(
                                                                                              PhantomData,
                                                                                              self.alloc(
                                                                                                Coq_Init_Datatypes_nat::S(
                                                                                                  PhantomData,
                                                                                                  self.alloc(
                                                                                                    Coq_Init_Datatypes_nat::S(
                                                                                                      PhantomData,
                                                                                                      self.alloc(
                                                                                                        Coq_Init_Datatypes_nat::S(
                                                                                                          PhantomData,
                                                                                                          self.alloc(
                                                                                                            Coq_Init_Datatypes_nat::S(
                                                                                                              PhantomData,
                                                                                                              self.alloc(
                                                                                                                Coq_Init_Datatypes_nat::S(
                                                                                                                  PhantomData,
                                                                                                                  self.alloc(
                                                                                                                    Coq_Init_Datatypes_nat::S(
                                                                                                                      PhantomData,
                                                                                                                      self.alloc(
                                                                                                                        Coq_Init_Datatypes_nat::S(
                                                                                                                          PhantomData,
                                                                                                                          self.alloc(
                                                                                                                            Coq_Init_Datatypes_nat::S(
                                                                                                                              PhantomData,
                                                                                                                              self.alloc(
                                                                                                                                Coq_Init_Datatypes_nat::S(
                                                                                                                                  PhantomData,
                                                                                                                                  self.alloc(
                                                                                                                                    Coq_Init_Datatypes_nat::S(
                                                                                                                                      PhantomData,
                                                                                                                                      self.alloc(
                                                                                                                                        Coq_Init_Datatypes_nat::S(
                                                                                                                                          PhantomData,
                                                                                                                                          self.alloc(
                                                                                                                                            Coq_Init_Datatypes_nat::S(
                                                                                                                                              PhantomData,
                                                                                                                                              self.alloc(
                                                                                                                                                Coq_Init_Datatypes_nat::S(
                                                                                                                                                  PhantomData,
                                                                                                                                                  self.alloc(
                                                                                                                                                    Coq_Init_Datatypes_nat::S(
                                                                                                                                                      PhantomData,
                                                                                                                                                      self.alloc(
                                                                                                                                                        Coq_Init_Datatypes_nat::S(
                                                                                                                                                          PhantomData,
                                                                                                                                                          self.alloc(
                                                                                                                                                            Coq_Init_Datatypes_nat::S(
                                                                                                                                                              PhantomData,
                                                                                                                                                              self.alloc(
                                                                                                                                                                Coq_Init_Datatypes_nat::S(
                                                                                                                                                                  PhantomData,
                                                                                                                                                                  self.alloc(
                                                                                                                                                                    Coq_Init_Datatypes_nat::S(
                                                                                                                                                                      PhantomData,
                                                                                                                                                                      self.alloc(
                                                                                                                                                                        Coq_Init_Datatypes_nat::S(
                                                                                                                                                                          PhantomData,
                                                                                                                                                                          self.alloc(
                                                                                                                                                                            Coq_Init_Datatypes_nat::S(
                                                                                                                                                                              PhantomData,
                                                                                                                                                                              self.alloc(
                                                                                                                                                                                Coq_Init_Datatypes_nat::S(
                                                                                                                                                                                  PhantomData,
                                                                                                                                                                                  self.alloc(
                                                                                                                                                                                    Coq_Init_Datatypes_nat::S(
                                                                                                                                                                                      PhantomData,
                                                                                                                                                                                      self.alloc(
                                                                                                                                                                                        Coq_Init_Datatypes_nat::O(
                                                                                                                                                                                          PhantomData))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
}
fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_W__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_nat<'a>) -> &'a Coq_Numbers_BinNums_Z<'a> {
  self.closure(move |n| {
    self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_W(
      n)
  })
}

fn CertiCoq_Benchmarks_tests_bernstein_yang(&'a self) -> &'a Coq_Numbers_BinNums_Z<'a> {
  self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_W(
    self.alloc(
      Coq_Init_Datatypes_nat::S(
        PhantomData,
        self.alloc(
          Coq_Init_Datatypes_nat::S(
            PhantomData,
            self.alloc(
              Coq_Init_Datatypes_nat::S(
                PhantomData,
                self.alloc(
                  Coq_Init_Datatypes_nat::S(
                    PhantomData,
                    self.alloc(
                      Coq_Init_Datatypes_nat::S(
                        PhantomData,
                        self.alloc(
                          Coq_Init_Datatypes_nat::S(
                            PhantomData,
                            self.alloc(
                              Coq_Init_Datatypes_nat::S(
                                PhantomData,
                                self.alloc(
                                  Coq_Init_Datatypes_nat::S(
                                    PhantomData,
                                    self.alloc(
                                      Coq_Init_Datatypes_nat::S(
                                        PhantomData,
                                        self.alloc(
                                          Coq_Init_Datatypes_nat::S(
                                            PhantomData,
                                            self.alloc(
                                              Coq_Init_Datatypes_nat::O(
                                                PhantomData)))))))))))))))))))))))
}
}
pub fn main() {
  Program::new().CertiCoq_Benchmarks_tests_bernstein_yang();
}
