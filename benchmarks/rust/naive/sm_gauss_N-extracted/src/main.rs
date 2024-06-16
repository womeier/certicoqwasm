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

#[derive(Clone)]
pub enum Coq_Numbers_BinNums_positive<'a> {
  xI(PhantomData<&'a ()>, &'a Coq_Numbers_BinNums_positive<'a>),
  xO(PhantomData<&'a ()>, &'a Coq_Numbers_BinNums_positive<'a>),
  xH(PhantomData<&'a ()>)
}

#[derive(Clone)]
pub enum Coq_Numbers_BinNums_N<'a> {
  N0(PhantomData<&'a ()>),
  Npos(PhantomData<&'a ()>, &'a Coq_Numbers_BinNums_positive<'a>)
}

#[derive( Clone)]
pub enum CertiCoq_Benchmarks_lib_stack_machine_Numeric<'a, A> {
  Build_Numeric(PhantomData<&'a A>, &'a dyn Fn(A) -> &'a dyn Fn(A) -> A, &'a dyn Fn(A) -> &'a dyn Fn(A) -> A, &'a dyn Fn(A) -> &'a dyn Fn(A) -> A, A)
}

#[derive( Clone)]
pub enum Coq_Strings_Ascii_ascii<'a> {
  Ascii(PhantomData<&'a ()>, bool, bool, bool, bool, bool, bool, bool, bool)
}

#[derive( Clone)]
pub enum Coq_Strings_String_string<'a> {
  EmptyString(PhantomData<&'a ()>),
  String(PhantomData<&'a ()>, &'a Coq_Strings_Ascii_ascii<'a>, &'a Coq_Strings_String_string<'a>)
}

#[derive( Clone)]
pub enum CertiCoq_Benchmarks_lib_stack_machine_id<'a> {
  Id(PhantomData<&'a ()>, &'a Coq_Strings_String_string<'a>)
}

type CertiCoq_Benchmarks_lib_stack_machine_total_map<'a, A> = &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_stack_machine_id<'a>) -> A;

type CertiCoq_Benchmarks_lib_stack_machine_state<'a, A> = CertiCoq_Benchmarks_lib_stack_machine_total_map<'a, A>;

#[derive( Clone)]
pub enum Coq_Init_Datatypes_list<'a, A> {
  nil(PhantomData<&'a A>),
  cons(PhantomData<&'a A>, A, &'a Coq_Init_Datatypes_list<'a, A>)
}

#[derive( Clone)]
pub enum CertiCoq_Benchmarks_lib_stack_machine_sinstr<'a, A> {
  SPush(PhantomData<&'a A>, A),
  SLoad(PhantomData<&'a A>, &'a CertiCoq_Benchmarks_lib_stack_machine_id<'a>),
  SPlus(PhantomData<&'a A>),
  SMinus(PhantomData<&'a A>),
  SMult(PhantomData<&'a A>)
}

#[derive( Clone)]
pub enum Coq_PArith_BinPosDef_Pos_mask<'a> {
  IsNul(PhantomData<&'a ()>),
  IsPos(PhantomData<&'a ()>, &'a Coq_Numbers_BinNums_positive<'a>),
  IsNeg(PhantomData<&'a ()>)
}

#[derive( Clone)]
pub enum CertiCoq_Benchmarks_lib_stack_machine_aexp<'a, A> {
  ANum(PhantomData<&'a A>, A),
  AId(PhantomData<&'a A>, &'a CertiCoq_Benchmarks_lib_stack_machine_id<'a>),
  APlus(PhantomData<&'a A>, &'a CertiCoq_Benchmarks_lib_stack_machine_aexp<'a, A>, &'a CertiCoq_Benchmarks_lib_stack_machine_aexp<'a, A>),
  AMinus(PhantomData<&'a A>, &'a CertiCoq_Benchmarks_lib_stack_machine_aexp<'a, A>, &'a CertiCoq_Benchmarks_lib_stack_machine_aexp<'a, A>),
  AMult(PhantomData<&'a A>, &'a CertiCoq_Benchmarks_lib_stack_machine_aexp<'a, A>, &'a CertiCoq_Benchmarks_lib_stack_machine_aexp<'a, A>)
}

#[derive( Clone)]
pub enum Coq_Init_Datatypes_nat<'a> {
  O(PhantomData<&'a ()>),
  S(PhantomData<&'a ()>, &'a Coq_Init_Datatypes_nat<'a>)
}

#[derive( Clone)]
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

fn CertiCoq_Benchmarks_lib_stack_machine_plus<A: Copy>(&'a self, Numeric: &'a CertiCoq_Benchmarks_lib_stack_machine_Numeric<'a, A>) -> &'a dyn Fn(A) -> &'a dyn Fn(A) -> A {
  match Numeric {
    &CertiCoq_Benchmarks_lib_stack_machine_Numeric::Build_Numeric(_, plus, minus, mult, zero) => {
      plus
    },
  }
}
fn CertiCoq_Benchmarks_lib_stack_machine_plus__curried<A: Copy>(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_stack_machine_Numeric<'a, A>) -> &'a dyn Fn(A) -> &'a dyn Fn(A) -> A {
  self.closure(move |Numeric| {
    self.CertiCoq_Benchmarks_lib_stack_machine_plus(
      Numeric)
  })
}

fn Coq_Lists_List_hd<A: Copy>(&'a self, default: A, l: &'a Coq_Init_Datatypes_list<'a, A>) -> A {
  match l {
    &Coq_Init_Datatypes_list::nil(_) => {
      default
    },
    &Coq_Init_Datatypes_list::cons(_, x, l0) => {
      x
    },
  }
}
fn Coq_Lists_List_hd__curried<A: Copy>(&'a self) -> &'a dyn Fn(A) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> A {
  self.closure(move |default| {
    self.closure(move |l| {
      self.Coq_Lists_List_hd(
        default,
        l)
    })
  })
}

fn CertiCoq_Benchmarks_lib_stack_machine_zero<A: Copy>(&'a self, Numeric: &'a CertiCoq_Benchmarks_lib_stack_machine_Numeric<'a, A>) -> A {
  match Numeric {
    &CertiCoq_Benchmarks_lib_stack_machine_Numeric::Build_Numeric(_, plus, minus, mult, zero) => {
      zero
    },
  }
}
fn CertiCoq_Benchmarks_lib_stack_machine_zero__curried<A: Copy>(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_stack_machine_Numeric<'a, A>) -> A {
  self.closure(move |Numeric| {
    self.CertiCoq_Benchmarks_lib_stack_machine_zero(
      Numeric)
  })
}

fn Coq_Lists_List_tl<A: Copy>(&'a self, l: &'a Coq_Init_Datatypes_list<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  match l {
    &Coq_Init_Datatypes_list::nil(_) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
    &Coq_Init_Datatypes_list::cons(_, a, m) => {
      m
    },
  }
}
fn Coq_Lists_List_tl__curried<A: Copy>(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  self.closure(move |l| {
    self.Coq_Lists_List_tl(
      l)
  })
}

fn CertiCoq_Benchmarks_lib_stack_machine_minus<A: Copy>(&'a self, Numeric: &'a CertiCoq_Benchmarks_lib_stack_machine_Numeric<'a, A>) -> &'a dyn Fn(A) -> &'a dyn Fn(A) -> A {
  match Numeric {
    &CertiCoq_Benchmarks_lib_stack_machine_Numeric::Build_Numeric(_, plus, minus, mult, zero) => {
      minus
    },
  }
}
fn CertiCoq_Benchmarks_lib_stack_machine_minus__curried<A: Copy>(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_stack_machine_Numeric<'a, A>) -> &'a dyn Fn(A) -> &'a dyn Fn(A) -> A {
  self.closure(move |Numeric| {
    self.CertiCoq_Benchmarks_lib_stack_machine_minus(
      Numeric)
  })
}

fn CertiCoq_Benchmarks_lib_stack_machine_mult<A: Copy>(&'a self, Numeric: &'a CertiCoq_Benchmarks_lib_stack_machine_Numeric<'a, A>) -> &'a dyn Fn(A) -> &'a dyn Fn(A) -> A {
  match Numeric {
    &CertiCoq_Benchmarks_lib_stack_machine_Numeric::Build_Numeric(_, plus, minus, mult, zero) => {
      mult
    },
  }
}
fn CertiCoq_Benchmarks_lib_stack_machine_mult__curried<A: Copy>(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_stack_machine_Numeric<'a, A>) -> &'a dyn Fn(A) -> &'a dyn Fn(A) -> A {
  self.closure(move |Numeric| {
    self.CertiCoq_Benchmarks_lib_stack_machine_mult(
      Numeric)
  })
}

fn CertiCoq_Benchmarks_lib_stack_machine_s_execute<A: Copy>(&'a self, A: (), H: &'a CertiCoq_Benchmarks_lib_stack_machine_Numeric<'a, A>, st: CertiCoq_Benchmarks_lib_stack_machine_state<'a, A>, stack: &'a Coq_Init_Datatypes_list<'a, A>, prog: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_stack_machine_sinstr<'a, A>>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  match prog {
    &Coq_Init_Datatypes_list::nil(_) => {
      stack
    },
    &Coq_Init_Datatypes_list::cons(_, s, prog2) => {
      match s {
        &CertiCoq_Benchmarks_lib_stack_machine_sinstr::SPush(_, n) => {
          self.CertiCoq_Benchmarks_lib_stack_machine_s_execute(
            (),
            H,
            st,
            self.alloc(
              Coq_Init_Datatypes_list::cons(
                PhantomData,
                n,
                stack)),
            prog2)
        },
        &CertiCoq_Benchmarks_lib_stack_machine_sinstr::SLoad(_, k) => {
          self.CertiCoq_Benchmarks_lib_stack_machine_s_execute(
            (),
            H,
            st,
            self.alloc(
              Coq_Init_Datatypes_list::cons(
                PhantomData,
                hint_app(st)(k),
                stack)),
            prog2)
        },
        &CertiCoq_Benchmarks_lib_stack_machine_sinstr::SPlus(_) => {
          self.CertiCoq_Benchmarks_lib_stack_machine_s_execute(
            (),
            H,
            st,
            self.alloc(
              Coq_Init_Datatypes_list::cons(
                PhantomData,
                self.CertiCoq_Benchmarks_lib_stack_machine_plus(
                  H)(
                  self.Coq_Lists_List_hd(
                    self.CertiCoq_Benchmarks_lib_stack_machine_zero(
                      H),
                    self.Coq_Lists_List_tl(
                      stack)))(
                  self.Coq_Lists_List_hd(
                    self.CertiCoq_Benchmarks_lib_stack_machine_zero(
                      H),
                    stack)),
                self.Coq_Lists_List_tl(
                  self.Coq_Lists_List_tl(
                    stack)))),
            prog2)
        },
        &CertiCoq_Benchmarks_lib_stack_machine_sinstr::SMinus(_) => {
          self.CertiCoq_Benchmarks_lib_stack_machine_s_execute(
            (),
            H,
            st,
            self.alloc(
              Coq_Init_Datatypes_list::cons(
                PhantomData,
                self.CertiCoq_Benchmarks_lib_stack_machine_minus(
                  H)(
                  self.Coq_Lists_List_hd(
                    self.CertiCoq_Benchmarks_lib_stack_machine_zero(
                      H),
                    self.Coq_Lists_List_tl(
                      stack)))(
                  self.Coq_Lists_List_hd(
                    self.CertiCoq_Benchmarks_lib_stack_machine_zero(
                      H),
                    stack)),
                self.Coq_Lists_List_tl(
                  self.Coq_Lists_List_tl(
                    stack)))),
            prog2)
        },
        &CertiCoq_Benchmarks_lib_stack_machine_sinstr::SMult(_) => {
          self.CertiCoq_Benchmarks_lib_stack_machine_s_execute(
            (),
            H,
            st,
            self.alloc(
              Coq_Init_Datatypes_list::cons(
                PhantomData,
                self.CertiCoq_Benchmarks_lib_stack_machine_mult(
                  H)(
                  self.Coq_Lists_List_hd(
                    self.CertiCoq_Benchmarks_lib_stack_machine_zero(
                      H),
                    self.Coq_Lists_List_tl(
                      stack)))(
                  self.Coq_Lists_List_hd(
                    self.CertiCoq_Benchmarks_lib_stack_machine_zero(
                      H),
                    stack)),
                self.Coq_Lists_List_tl(
                  self.Coq_Lists_List_tl(
                    stack)))),
            prog2)
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_stack_machine_s_execute__curried<A: Copy>(&'a self) -> &'a dyn Fn(()) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_stack_machine_Numeric<'a, A>) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_stack_machine_state<'a, A>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_stack_machine_sinstr<'a, A>>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  self.closure(move |A| {
    self.closure(move |H| {
      self.closure(move |st| {
        self.closure(move |stack| {
          self.closure(move |prog| {
            self.CertiCoq_Benchmarks_lib_stack_machine_s_execute(
              A,
              H,
              st,
              stack,
              prog)
          })
        })
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_stack_machine_t_empty<A: Copy>(&'a self, v: A) -> CertiCoq_Benchmarks_lib_stack_machine_total_map<'a, A> {
  self.closure(move |x| {
    v
  })
}
fn CertiCoq_Benchmarks_lib_stack_machine_t_empty__curried<A: Copy>(&'a self) -> &'a dyn Fn(A) -> CertiCoq_Benchmarks_lib_stack_machine_total_map<'a, A> {
  self.closure(move |v| {
    self.CertiCoq_Benchmarks_lib_stack_machine_t_empty(
      v)
  })
}

fn CertiCoq_Benchmarks_lib_stack_machine_s_execute_<A: Copy>(&'a self, H: &'a CertiCoq_Benchmarks_lib_stack_machine_Numeric<'a, A>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_stack_machine_sinstr<'a, A>>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  self.CertiCoq_Benchmarks_lib_stack_machine_s_execute__curried()(
    ())(
    H)(
    self.CertiCoq_Benchmarks_lib_stack_machine_t_empty(
      self.CertiCoq_Benchmarks_lib_stack_machine_zero(
        H)))(
    self.alloc(
      Coq_Init_Datatypes_list::nil(
        PhantomData)))
}
fn CertiCoq_Benchmarks_lib_stack_machine_s_execute___curried<A: Copy>(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_stack_machine_Numeric<'a, A>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_stack_machine_sinstr<'a, A>>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  self.closure(move |H| {
    self.CertiCoq_Benchmarks_lib_stack_machine_s_execute_(
      H)
  })
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

fn Coq_NArith_BinNatDef_N_add(&'a self, n: &'a Coq_Numbers_BinNums_N<'a>, m: &'a Coq_Numbers_BinNums_N<'a>) -> &'a Coq_Numbers_BinNums_N<'a> {
  match n {
    &Coq_Numbers_BinNums_N::N0(_) => {
      m
    },
    &Coq_Numbers_BinNums_N::Npos(_, p) => {
      match m {
        &Coq_Numbers_BinNums_N::N0(_) => {
          n
        },
        &Coq_Numbers_BinNums_N::Npos(_, q) => {
          self.alloc(
            Coq_Numbers_BinNums_N::Npos(
              PhantomData,
              self.Coq_PArith_BinPosDef_Pos_add()(
                p)(
                q)))
        },
      }
    },
  }
}
fn Coq_NArith_BinNatDef_N_add__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_N<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_N<'a>) -> &'a Coq_Numbers_BinNums_N<'a> {
  self.closure(move |n| {
    self.closure(move |m| {
      self.Coq_NArith_BinNatDef_N_add(
        n,
        m)
    })
  })
}

fn Coq_PArith_BinPosDef_Pos_double_mask(&'a self, x: &'a Coq_PArith_BinPosDef_Pos_mask<'a>) -> &'a Coq_PArith_BinPosDef_Pos_mask<'a> {
  match x {
    &Coq_PArith_BinPosDef_Pos_mask::IsNul(_) => {
      self.alloc(
        Coq_PArith_BinPosDef_Pos_mask::IsNul(
          PhantomData))
    },
    &Coq_PArith_BinPosDef_Pos_mask::IsPos(_, p) => {
      self.alloc(
        Coq_PArith_BinPosDef_Pos_mask::IsPos(
          PhantomData,
          self.alloc(
            Coq_Numbers_BinNums_positive::xO(
              PhantomData,
              p))))
    },
    &Coq_PArith_BinPosDef_Pos_mask::IsNeg(_) => {
      self.alloc(
        Coq_PArith_BinPosDef_Pos_mask::IsNeg(
          PhantomData))
    },
  }
}
fn Coq_PArith_BinPosDef_Pos_double_mask__curried(&'a self) -> &'a dyn Fn(&'a Coq_PArith_BinPosDef_Pos_mask<'a>) -> &'a Coq_PArith_BinPosDef_Pos_mask<'a> {
  self.closure(move |x| {
    self.Coq_PArith_BinPosDef_Pos_double_mask(
      x)
  })
}

fn Coq_PArith_BinPosDef_Pos_succ_double_mask(&'a self, x: &'a Coq_PArith_BinPosDef_Pos_mask<'a>) -> &'a Coq_PArith_BinPosDef_Pos_mask<'a> {
  match x {
    &Coq_PArith_BinPosDef_Pos_mask::IsNul(_) => {
      self.alloc(
        Coq_PArith_BinPosDef_Pos_mask::IsPos(
          PhantomData,
          self.alloc(
            Coq_Numbers_BinNums_positive::xH(
              PhantomData))))
    },
    &Coq_PArith_BinPosDef_Pos_mask::IsPos(_, p) => {
      self.alloc(
        Coq_PArith_BinPosDef_Pos_mask::IsPos(
          PhantomData,
          self.alloc(
            Coq_Numbers_BinNums_positive::xI(
              PhantomData,
              p))))
    },
    &Coq_PArith_BinPosDef_Pos_mask::IsNeg(_) => {
      self.alloc(
        Coq_PArith_BinPosDef_Pos_mask::IsNeg(
          PhantomData))
    },
  }
}
fn Coq_PArith_BinPosDef_Pos_succ_double_mask__curried(&'a self) -> &'a dyn Fn(&'a Coq_PArith_BinPosDef_Pos_mask<'a>) -> &'a Coq_PArith_BinPosDef_Pos_mask<'a> {
  self.closure(move |x| {
    self.Coq_PArith_BinPosDef_Pos_succ_double_mask(
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

fn Coq_PArith_BinPosDef_Pos_double_pred_mask(&'a self, x: &'a Coq_Numbers_BinNums_positive<'a>) -> &'a Coq_PArith_BinPosDef_Pos_mask<'a> {
  match x {
    &Coq_Numbers_BinNums_positive::xI(_, p) => {
      self.alloc(
        Coq_PArith_BinPosDef_Pos_mask::IsPos(
          PhantomData,
          self.alloc(
            Coq_Numbers_BinNums_positive::xO(
              PhantomData,
              self.alloc(
                Coq_Numbers_BinNums_positive::xO(
                  PhantomData,
                  p))))))
    },
    &Coq_Numbers_BinNums_positive::xO(_, p) => {
      self.alloc(
        Coq_PArith_BinPosDef_Pos_mask::IsPos(
          PhantomData,
          self.alloc(
            Coq_Numbers_BinNums_positive::xO(
              PhantomData,
              self.Coq_PArith_BinPosDef_Pos_pred_double(
                p)))))
    },
    &Coq_Numbers_BinNums_positive::xH(_) => {
      self.alloc(
        Coq_PArith_BinPosDef_Pos_mask::IsNul(
          PhantomData))
    },
  }
}
fn Coq_PArith_BinPosDef_Pos_double_pred_mask__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_positive<'a>) -> &'a Coq_PArith_BinPosDef_Pos_mask<'a> {
  self.closure(move |x| {
    self.Coq_PArith_BinPosDef_Pos_double_pred_mask(
      x)
  })
}

fn Coq_PArith_BinPosDef_Pos_sub_mask(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_positive<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_positive<'a>) -> &'a Coq_PArith_BinPosDef_Pos_mask<'a> {
  let sub_mask = self.alloc(std::cell::Cell::new(None));
  let sub_mask_carry = self.alloc(std::cell::Cell::new(None));
  sub_mask.set(Some(
    self.closure(move |x| {
      self.closure(move |y| {
        match x {
          &Coq_Numbers_BinNums_positive::xI(_, p) => {
            match y {
              &Coq_Numbers_BinNums_positive::xI(_, q) => {
                self.Coq_PArith_BinPosDef_Pos_double_mask(
                  hint_app(hint_app(sub_mask.get().unwrap())(p))(q))
              },
              &Coq_Numbers_BinNums_positive::xO(_, q) => {
                self.Coq_PArith_BinPosDef_Pos_succ_double_mask(
                  hint_app(hint_app(sub_mask.get().unwrap())(p))(q))
              },
              &Coq_Numbers_BinNums_positive::xH(_) => {
                self.alloc(
                  Coq_PArith_BinPosDef_Pos_mask::IsPos(
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
                self.Coq_PArith_BinPosDef_Pos_succ_double_mask(
                  hint_app(hint_app(sub_mask_carry.get().unwrap())(p))(q))
              },
              &Coq_Numbers_BinNums_positive::xO(_, q) => {
                self.Coq_PArith_BinPosDef_Pos_double_mask(
                  hint_app(hint_app(sub_mask.get().unwrap())(p))(q))
              },
              &Coq_Numbers_BinNums_positive::xH(_) => {
                self.alloc(
                  Coq_PArith_BinPosDef_Pos_mask::IsPos(
                    PhantomData,
                    self.Coq_PArith_BinPosDef_Pos_pred_double(
                      p)))
              },
            }
          },
          &Coq_Numbers_BinNums_positive::xH(_) => {
            match y {
              &Coq_Numbers_BinNums_positive::xI(_, p) => {
                self.alloc(
                  Coq_PArith_BinPosDef_Pos_mask::IsNeg(
                    PhantomData))
              },
              &Coq_Numbers_BinNums_positive::xO(_, p) => {
                self.alloc(
                  Coq_PArith_BinPosDef_Pos_mask::IsNeg(
                    PhantomData))
              },
              &Coq_Numbers_BinNums_positive::xH(_) => {
                self.alloc(
                  Coq_PArith_BinPosDef_Pos_mask::IsNul(
                    PhantomData))
              },
            }
          },
        }
      })
    })));
  sub_mask_carry.set(Some(
    self.closure(move |x| {
      self.closure(move |y| {
        match x {
          &Coq_Numbers_BinNums_positive::xI(_, p) => {
            match y {
              &Coq_Numbers_BinNums_positive::xI(_, q) => {
                self.Coq_PArith_BinPosDef_Pos_succ_double_mask(
                  hint_app(hint_app(sub_mask_carry.get().unwrap())(p))(q))
              },
              &Coq_Numbers_BinNums_positive::xO(_, q) => {
                self.Coq_PArith_BinPosDef_Pos_double_mask(
                  hint_app(hint_app(sub_mask.get().unwrap())(p))(q))
              },
              &Coq_Numbers_BinNums_positive::xH(_) => {
                self.alloc(
                  Coq_PArith_BinPosDef_Pos_mask::IsPos(
                    PhantomData,
                    self.Coq_PArith_BinPosDef_Pos_pred_double(
                      p)))
              },
            }
          },
          &Coq_Numbers_BinNums_positive::xO(_, p) => {
            match y {
              &Coq_Numbers_BinNums_positive::xI(_, q) => {
                self.Coq_PArith_BinPosDef_Pos_double_mask(
                  hint_app(hint_app(sub_mask_carry.get().unwrap())(p))(q))
              },
              &Coq_Numbers_BinNums_positive::xO(_, q) => {
                self.Coq_PArith_BinPosDef_Pos_succ_double_mask(
                  hint_app(hint_app(sub_mask_carry.get().unwrap())(p))(q))
              },
              &Coq_Numbers_BinNums_positive::xH(_) => {
                self.Coq_PArith_BinPosDef_Pos_double_pred_mask(
                  p)
              },
            }
          },
          &Coq_Numbers_BinNums_positive::xH(_) => {
            self.alloc(
              Coq_PArith_BinPosDef_Pos_mask::IsNeg(
                PhantomData))
          },
        }
      })
    })));
  sub_mask.get().unwrap()
}

fn Coq_NArith_BinNatDef_N_sub(&'a self, n: &'a Coq_Numbers_BinNums_N<'a>, m: &'a Coq_Numbers_BinNums_N<'a>) -> &'a Coq_Numbers_BinNums_N<'a> {
  match n {
    &Coq_Numbers_BinNums_N::N0(_) => {
      self.alloc(
        Coq_Numbers_BinNums_N::N0(
          PhantomData))
    },
    &Coq_Numbers_BinNums_N::Npos(_, n2) => {
      match m {
        &Coq_Numbers_BinNums_N::N0(_) => {
          n
        },
        &Coq_Numbers_BinNums_N::Npos(_, m2) => {
          match self.Coq_PArith_BinPosDef_Pos_sub_mask()(
                  n2)(
                  m2) {
            &Coq_PArith_BinPosDef_Pos_mask::IsNul(_) => {
              self.alloc(
                Coq_Numbers_BinNums_N::N0(
                  PhantomData))
            },
            &Coq_PArith_BinPosDef_Pos_mask::IsPos(_, p) => {
              self.alloc(
                Coq_Numbers_BinNums_N::Npos(
                  PhantomData,
                  p))
            },
            &Coq_PArith_BinPosDef_Pos_mask::IsNeg(_) => {
              self.alloc(
                Coq_Numbers_BinNums_N::N0(
                  PhantomData))
            },
          }
        },
      }
    },
  }
}
fn Coq_NArith_BinNatDef_N_sub__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_N<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_N<'a>) -> &'a Coq_Numbers_BinNums_N<'a> {
  self.closure(move |n| {
    self.closure(move |m| {
      self.Coq_NArith_BinNatDef_N_sub(
        n,
        m)
    })
  })
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

fn Coq_NArith_BinNatDef_N_mul(&'a self, n: &'a Coq_Numbers_BinNums_N<'a>, m: &'a Coq_Numbers_BinNums_N<'a>) -> &'a Coq_Numbers_BinNums_N<'a> {
  match n {
    &Coq_Numbers_BinNums_N::N0(_) => {
      self.alloc(
        Coq_Numbers_BinNums_N::N0(
          PhantomData))
    },
    &Coq_Numbers_BinNums_N::Npos(_, p) => {
      match m {
        &Coq_Numbers_BinNums_N::N0(_) => {
          self.alloc(
            Coq_Numbers_BinNums_N::N0(
              PhantomData))
        },
        &Coq_Numbers_BinNums_N::Npos(_, q) => {
          self.alloc(
            Coq_Numbers_BinNums_N::Npos(
              PhantomData,
              self.Coq_PArith_BinPosDef_Pos_mul(
                p,
                q)))
        },
      }
    },
  }
}
fn Coq_NArith_BinNatDef_N_mul__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_N<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_N<'a>) -> &'a Coq_Numbers_BinNums_N<'a> {
  self.closure(move |n| {
    self.closure(move |m| {
      self.Coq_NArith_BinNatDef_N_mul(
        n,
        m)
    })
  })
}

fn CertiCoq_Benchmarks_lib_stack_machine_NumericBinNat(&'a self) -> &'a CertiCoq_Benchmarks_lib_stack_machine_Numeric<'a, &'a Coq_Numbers_BinNums_N<'a>> {
  self.alloc(
    CertiCoq_Benchmarks_lib_stack_machine_Numeric::Build_Numeric(
      PhantomData,
      self.closure(move |x| {
        self.closure(move |y| {
          self.Coq_NArith_BinNatDef_N_add(
            x,
            y)
        })
      }),
      self.closure(move |x| {
        self.closure(move |y| {
          self.Coq_NArith_BinNatDef_N_sub(
            x,
            y)
        })
      }),
      self.closure(move |x| {
        self.closure(move |y| {
          self.Coq_NArith_BinNatDef_N_mul(
            x,
            y)
        })
      }),
      self.alloc(
        Coq_Numbers_BinNums_N::N0(
          PhantomData))))
}

fn Coq_Init_Datatypes_app<A: Copy>(&'a self, l: &'a Coq_Init_Datatypes_list<'a, A>, m: &'a Coq_Init_Datatypes_list<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  match l {
    &Coq_Init_Datatypes_list::nil(_) => {
      m
    },
    &Coq_Init_Datatypes_list::cons(_, a, l1) => {
      self.alloc(
        Coq_Init_Datatypes_list::cons(
          PhantomData,
          a,
          self.Coq_Init_Datatypes_app(
            l1,
            m)))
    },
  }
}
fn Coq_Init_Datatypes_app__curried<A: Copy>(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  self.closure(move |l| {
    self.closure(move |m| {
      self.Coq_Init_Datatypes_app(
        l,
        m)
    })
  })
}

fn CertiCoq_Benchmarks_lib_stack_machine_s_compile<A: Copy>(&'a self, A: (), H: &'a CertiCoq_Benchmarks_lib_stack_machine_Numeric<'a, A>, e: &'a CertiCoq_Benchmarks_lib_stack_machine_aexp<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_stack_machine_sinstr<'a, A>> {
  match e {
    &CertiCoq_Benchmarks_lib_stack_machine_aexp::ANum(_, x) => {
      self.alloc(
        Coq_Init_Datatypes_list::cons(
          PhantomData,
          self.alloc(
            CertiCoq_Benchmarks_lib_stack_machine_sinstr::SPush(
              PhantomData,
              x)),
          self.alloc(
            Coq_Init_Datatypes_list::nil(
              PhantomData))))
    },
    &CertiCoq_Benchmarks_lib_stack_machine_aexp::AId(_, k) => {
      self.alloc(
        Coq_Init_Datatypes_list::cons(
          PhantomData,
          self.alloc(
            CertiCoq_Benchmarks_lib_stack_machine_sinstr::SLoad(
              PhantomData,
              k)),
          self.alloc(
            Coq_Init_Datatypes_list::nil(
              PhantomData))))
    },
    &CertiCoq_Benchmarks_lib_stack_machine_aexp::APlus(_, a1, a2) => {
      self.Coq_Init_Datatypes_app(
        self.CertiCoq_Benchmarks_lib_stack_machine_s_compile(
          (),
          H,
          a1),
        self.Coq_Init_Datatypes_app(
          self.CertiCoq_Benchmarks_lib_stack_machine_s_compile(
            (),
            H,
            a2),
          self.alloc(
            Coq_Init_Datatypes_list::cons(
              PhantomData,
              self.alloc(
                CertiCoq_Benchmarks_lib_stack_machine_sinstr::SPlus(
                  PhantomData)),
              self.alloc(
                Coq_Init_Datatypes_list::nil(
                  PhantomData))))))
    },
    &CertiCoq_Benchmarks_lib_stack_machine_aexp::AMinus(_, a1, a2) => {
      self.Coq_Init_Datatypes_app(
        self.CertiCoq_Benchmarks_lib_stack_machine_s_compile(
          (),
          H,
          a1),
        self.Coq_Init_Datatypes_app(
          self.CertiCoq_Benchmarks_lib_stack_machine_s_compile(
            (),
            H,
            a2),
          self.alloc(
            Coq_Init_Datatypes_list::cons(
              PhantomData,
              self.alloc(
                CertiCoq_Benchmarks_lib_stack_machine_sinstr::SMinus(
                  PhantomData)),
              self.alloc(
                Coq_Init_Datatypes_list::nil(
                  PhantomData))))))
    },
    &CertiCoq_Benchmarks_lib_stack_machine_aexp::AMult(_, a1, a2) => {
      self.Coq_Init_Datatypes_app(
        self.CertiCoq_Benchmarks_lib_stack_machine_s_compile(
          (),
          H,
          a1),
        self.Coq_Init_Datatypes_app(
          self.CertiCoq_Benchmarks_lib_stack_machine_s_compile(
            (),
            H,
            a2),
          self.alloc(
            Coq_Init_Datatypes_list::cons(
              PhantomData,
              self.alloc(
                CertiCoq_Benchmarks_lib_stack_machine_sinstr::SMult(
                  PhantomData)),
              self.alloc(
                Coq_Init_Datatypes_list::nil(
                  PhantomData))))))
    },
  }
}
fn CertiCoq_Benchmarks_lib_stack_machine_s_compile__curried<A: Copy>(&'a self) -> &'a dyn Fn(()) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_stack_machine_Numeric<'a, A>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_stack_machine_aexp<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_stack_machine_sinstr<'a, A>> {
  self.closure(move |A| {
    self.closure(move |H| {
      self.closure(move |e| {
        self.CertiCoq_Benchmarks_lib_stack_machine_s_compile(
          A,
          H,
          e)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_stack_machine_gauss_sum_aexp_N_aux(&'a self, guard: &'a Coq_Init_Datatypes_nat<'a>, n: &'a Coq_Numbers_BinNums_N<'a>) -> &'a CertiCoq_Benchmarks_lib_stack_machine_aexp<'a, &'a Coq_Numbers_BinNums_N<'a>> {
  match guard {
    &Coq_Init_Datatypes_nat::O(_) => {
      self.alloc(
        CertiCoq_Benchmarks_lib_stack_machine_aexp::ANum(
          PhantomData,
          self.alloc(
            Coq_Numbers_BinNums_N::N0(
              PhantomData))))
    },
    &Coq_Init_Datatypes_nat::S(_, g) => {
      self.alloc(
        CertiCoq_Benchmarks_lib_stack_machine_aexp::APlus(
          PhantomData,
          self.alloc(
            CertiCoq_Benchmarks_lib_stack_machine_aexp::ANum(
              PhantomData,
              n)),
          self.CertiCoq_Benchmarks_lib_stack_machine_gauss_sum_aexp_N_aux(
            g,
            self.Coq_NArith_BinNatDef_N_sub(
              n,
              self.alloc(
                Coq_Numbers_BinNums_N::Npos(
                  PhantomData,
                  self.alloc(
                    Coq_Numbers_BinNums_positive::xH(
                      PhantomData))))))))
    },
  }
}
fn CertiCoq_Benchmarks_lib_stack_machine_gauss_sum_aexp_N_aux__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_nat<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_N<'a>) -> &'a CertiCoq_Benchmarks_lib_stack_machine_aexp<'a, &'a Coq_Numbers_BinNums_N<'a>> {
  self.closure(move |guard| {
    self.closure(move |n| {
      self.CertiCoq_Benchmarks_lib_stack_machine_gauss_sum_aexp_N_aux(
        guard,
        n)
    })
  })
}

fn Coq_PArith_BinPosDef_Pos_iter_op<A: Copy>(&'a self, op: &'a dyn Fn(A) -> &'a dyn Fn(A) -> A, p: &'a Coq_Numbers_BinNums_positive<'a>, a: A) -> A {
  match p {
    &Coq_Numbers_BinNums_positive::xI(_, p2) => {
      hint_app(hint_app(op)(a))(self.Coq_PArith_BinPosDef_Pos_iter_op(
                                  op,
                                  p2,
                                  hint_app(hint_app(op)(a))(a)))
    },
    &Coq_Numbers_BinNums_positive::xO(_, p2) => {
      self.Coq_PArith_BinPosDef_Pos_iter_op(
        op,
        p2,
        hint_app(hint_app(op)(a))(a))
    },
    &Coq_Numbers_BinNums_positive::xH(_) => {
      a
    },
  }
}
fn Coq_PArith_BinPosDef_Pos_iter_op__curried<A: Copy>(&'a self) -> &'a dyn Fn(&'a dyn Fn(A) -> &'a dyn Fn(A) -> A) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_positive<'a>) -> &'a dyn Fn(A) -> A {
  self.closure(move |op| {
    self.closure(move |p| {
      self.closure(move |a| {
        self.Coq_PArith_BinPosDef_Pos_iter_op(
          op,
          p,
          a)
      })
    })
  })
}

fn Coq_Init_Nat_add(&'a self, n: &'a Coq_Init_Datatypes_nat<'a>, m: &'a Coq_Init_Datatypes_nat<'a>) -> &'a Coq_Init_Datatypes_nat<'a> {
  match n {
    &Coq_Init_Datatypes_nat::O(_) => {
      m
    },
    &Coq_Init_Datatypes_nat::S(_, p) => {
      self.alloc(
        Coq_Init_Datatypes_nat::S(
          PhantomData,
          self.Coq_Init_Nat_add(
            p,
            m)))
    },
  }
}
fn Coq_Init_Nat_add__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_nat<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_nat<'a>) -> &'a Coq_Init_Datatypes_nat<'a> {
  self.closure(move |n| {
    self.closure(move |m| {
      self.Coq_Init_Nat_add(
        n,
        m)
    })
  })
}

fn Coq_PArith_BinPosDef_Pos_to_nat(&'a self, x: &'a Coq_Numbers_BinNums_positive<'a>) -> &'a Coq_Init_Datatypes_nat<'a> {
  self.Coq_PArith_BinPosDef_Pos_iter_op(
    self.Coq_Init_Nat_add__curried(),
    x,
    self.alloc(
      Coq_Init_Datatypes_nat::S(
        PhantomData,
        self.alloc(
          Coq_Init_Datatypes_nat::O(
            PhantomData)))))
}
fn Coq_PArith_BinPosDef_Pos_to_nat__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_positive<'a>) -> &'a Coq_Init_Datatypes_nat<'a> {
  self.closure(move |x| {
    self.Coq_PArith_BinPosDef_Pos_to_nat(
      x)
  })
}

fn Coq_NArith_BinNatDef_N_to_nat(&'a self, a: &'a Coq_Numbers_BinNums_N<'a>) -> &'a Coq_Init_Datatypes_nat<'a> {
  match a {
    &Coq_Numbers_BinNums_N::N0(_) => {
      self.alloc(
        Coq_Init_Datatypes_nat::O(
          PhantomData))
    },
    &Coq_Numbers_BinNums_N::Npos(_, p) => {
      self.Coq_PArith_BinPosDef_Pos_to_nat(
        p)
    },
  }
}
fn Coq_NArith_BinNatDef_N_to_nat__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_N<'a>) -> &'a Coq_Init_Datatypes_nat<'a> {
  self.closure(move |a| {
    self.Coq_NArith_BinNatDef_N_to_nat(
      a)
  })
}

fn CertiCoq_Benchmarks_lib_stack_machine_gauss_sum_aexp_N(&'a self, n: &'a Coq_Numbers_BinNums_N<'a>) -> &'a CertiCoq_Benchmarks_lib_stack_machine_aexp<'a, &'a Coq_Numbers_BinNums_N<'a>> {
  self.CertiCoq_Benchmarks_lib_stack_machine_gauss_sum_aexp_N_aux(
    self.Coq_NArith_BinNatDef_N_to_nat(
      n),
    n)
}
fn CertiCoq_Benchmarks_lib_stack_machine_gauss_sum_aexp_N__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_N<'a>) -> &'a CertiCoq_Benchmarks_lib_stack_machine_aexp<'a, &'a Coq_Numbers_BinNums_N<'a>> {
  self.closure(move |n| {
    self.CertiCoq_Benchmarks_lib_stack_machine_gauss_sum_aexp_N(
      n)
  })
}

fn CertiCoq_Benchmarks_lib_stack_machine_gauss_sum_sintrs_N(&'a self, n: &'a Coq_Numbers_BinNums_N<'a>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_stack_machine_sinstr<'a, &'a Coq_Numbers_BinNums_N<'a>>> {
  self.CertiCoq_Benchmarks_lib_stack_machine_s_compile(
    (),
    self.CertiCoq_Benchmarks_lib_stack_machine_NumericBinNat(),
    self.CertiCoq_Benchmarks_lib_stack_machine_gauss_sum_aexp_N(
      n))
}
fn CertiCoq_Benchmarks_lib_stack_machine_gauss_sum_sintrs_N__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_N<'a>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_stack_machine_sinstr<'a, &'a Coq_Numbers_BinNums_N<'a>>> {
  self.closure(move |n| {
    self.CertiCoq_Benchmarks_lib_stack_machine_gauss_sum_sintrs_N(
      n)
  })
}

fn Coq_Init_Datatypes_fst<A: Copy, B: Copy>(&'a self, p: __pair<A, B>) -> A {
  __pair_elim!(
    y, x, {
      y
    },
    p)
}
fn Coq_Init_Datatypes_fst__curried<A: Copy, B: Copy>(&'a self) -> &'a dyn Fn(__pair<A, B>) -> A {
  self.closure(move |p| {
    self.Coq_Init_Datatypes_fst(
      p)
  })
}

fn Coq_NArith_BinNatDef_N_succ_double(&'a self, x: &'a Coq_Numbers_BinNums_N<'a>) -> &'a Coq_Numbers_BinNums_N<'a> {
  match x {
    &Coq_Numbers_BinNums_N::N0(_) => {
      self.alloc(
        Coq_Numbers_BinNums_N::Npos(
          PhantomData,
          self.alloc(
            Coq_Numbers_BinNums_positive::xH(
              PhantomData))))
    },
    &Coq_Numbers_BinNums_N::Npos(_, p) => {
      self.alloc(
        Coq_Numbers_BinNums_N::Npos(
          PhantomData,
          self.alloc(
            Coq_Numbers_BinNums_positive::xI(
              PhantomData,
              p))))
    },
  }
}
fn Coq_NArith_BinNatDef_N_succ_double__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_N<'a>) -> &'a Coq_Numbers_BinNums_N<'a> {
  self.closure(move |x| {
    self.Coq_NArith_BinNatDef_N_succ_double(
      x)
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

fn Coq_NArith_BinNatDef_N_compare(&'a self, n: &'a Coq_Numbers_BinNums_N<'a>, m: &'a Coq_Numbers_BinNums_N<'a>) -> &'a Coq_Init_Datatypes_comparison<'a> {
  match n {
    &Coq_Numbers_BinNums_N::N0(_) => {
      match m {
        &Coq_Numbers_BinNums_N::N0(_) => {
          self.alloc(
            Coq_Init_Datatypes_comparison::Eq(
              PhantomData))
        },
        &Coq_Numbers_BinNums_N::Npos(_, m2) => {
          self.alloc(
            Coq_Init_Datatypes_comparison::Lt(
              PhantomData))
        },
      }
    },
    &Coq_Numbers_BinNums_N::Npos(_, n2) => {
      match m {
        &Coq_Numbers_BinNums_N::N0(_) => {
          self.alloc(
            Coq_Init_Datatypes_comparison::Gt(
              PhantomData))
        },
        &Coq_Numbers_BinNums_N::Npos(_, m2) => {
          self.Coq_PArith_BinPosDef_Pos_compare()(
            n2)(
            m2)
        },
      }
    },
  }
}
fn Coq_NArith_BinNatDef_N_compare__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_N<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_N<'a>) -> &'a Coq_Init_Datatypes_comparison<'a> {
  self.closure(move |n| {
    self.closure(move |m| {
      self.Coq_NArith_BinNatDef_N_compare(
        n,
        m)
    })
  })
}

fn Coq_NArith_BinNatDef_N_leb(&'a self, x: &'a Coq_Numbers_BinNums_N<'a>, y: &'a Coq_Numbers_BinNums_N<'a>) -> bool {
  match self.Coq_NArith_BinNatDef_N_compare(
          x,
          y) {
    &Coq_Init_Datatypes_comparison::Eq(_) => {
      true
    },
    &Coq_Init_Datatypes_comparison::Lt(_) => {
      true
    },
    &Coq_Init_Datatypes_comparison::Gt(_) => {
      false
    },
  }
}
fn Coq_NArith_BinNatDef_N_leb__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_N<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_N<'a>) -> bool {
  self.closure(move |x| {
    self.closure(move |y| {
      self.Coq_NArith_BinNatDef_N_leb(
        x,
        y)
    })
  })
}

fn Coq_NArith_BinNatDef_N_double(&'a self, n: &'a Coq_Numbers_BinNums_N<'a>) -> &'a Coq_Numbers_BinNums_N<'a> {
  match n {
    &Coq_Numbers_BinNums_N::N0(_) => {
      self.alloc(
        Coq_Numbers_BinNums_N::N0(
          PhantomData))
    },
    &Coq_Numbers_BinNums_N::Npos(_, p) => {
      self.alloc(
        Coq_Numbers_BinNums_N::Npos(
          PhantomData,
          self.alloc(
            Coq_Numbers_BinNums_positive::xO(
              PhantomData,
              p))))
    },
  }
}
fn Coq_NArith_BinNatDef_N_double__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_N<'a>) -> &'a Coq_Numbers_BinNums_N<'a> {
  self.closure(move |n| {
    self.Coq_NArith_BinNatDef_N_double(
      n)
  })
}

fn Coq_NArith_BinNatDef_N_pos_div_eucl(&'a self, a: &'a Coq_Numbers_BinNums_positive<'a>, b: &'a Coq_Numbers_BinNums_N<'a>) -> __pair<&'a Coq_Numbers_BinNums_N<'a>, &'a Coq_Numbers_BinNums_N<'a>> {
  match a {
    &Coq_Numbers_BinNums_positive::xI(_, a2) => {
      __pair_elim!(
        r, q, {
          let r2 =
            self.Coq_NArith_BinNatDef_N_succ_double(
              q);
          match self.Coq_NArith_BinNatDef_N_leb(
                  b,
                  r2) {
            true => {
              __mk_pair(
                self.Coq_NArith_BinNatDef_N_succ_double(
                  r),
                self.Coq_NArith_BinNatDef_N_sub(
                  r2,
                  b))
            },
            false => {
              __mk_pair(
                self.Coq_NArith_BinNatDef_N_double(
                  r),
                r2)
            },
          }
        },
        self.Coq_NArith_BinNatDef_N_pos_div_eucl(
          a2,
          b))
    },
    &Coq_Numbers_BinNums_positive::xO(_, a2) => {
      __pair_elim!(
        r, q, {
          let r2 =
            self.Coq_NArith_BinNatDef_N_double(
              q);
          match self.Coq_NArith_BinNatDef_N_leb(
                  b,
                  r2) {
            true => {
              __mk_pair(
                self.Coq_NArith_BinNatDef_N_succ_double(
                  r),
                self.Coq_NArith_BinNatDef_N_sub(
                  r2,
                  b))
            },
            false => {
              __mk_pair(
                self.Coq_NArith_BinNatDef_N_double(
                  r),
                r2)
            },
          }
        },
        self.Coq_NArith_BinNatDef_N_pos_div_eucl(
          a2,
          b))
    },
    &Coq_Numbers_BinNums_positive::xH(_) => {
      match b {
        &Coq_Numbers_BinNums_N::N0(_) => {
          __mk_pair(
            self.alloc(
              Coq_Numbers_BinNums_N::N0(
                PhantomData)),
            self.alloc(
              Coq_Numbers_BinNums_N::Npos(
                PhantomData,
                self.alloc(
                  Coq_Numbers_BinNums_positive::xH(
                    PhantomData)))))
        },
        &Coq_Numbers_BinNums_N::Npos(_, p) => {
          match p {
            &Coq_Numbers_BinNums_positive::xI(_, p0) => {
              __mk_pair(
                self.alloc(
                  Coq_Numbers_BinNums_N::N0(
                    PhantomData)),
                self.alloc(
                  Coq_Numbers_BinNums_N::Npos(
                    PhantomData,
                    self.alloc(
                      Coq_Numbers_BinNums_positive::xH(
                        PhantomData)))))
            },
            &Coq_Numbers_BinNums_positive::xO(_, p0) => {
              __mk_pair(
                self.alloc(
                  Coq_Numbers_BinNums_N::N0(
                    PhantomData)),
                self.alloc(
                  Coq_Numbers_BinNums_N::Npos(
                    PhantomData,
                    self.alloc(
                      Coq_Numbers_BinNums_positive::xH(
                        PhantomData)))))
            },
            &Coq_Numbers_BinNums_positive::xH(_) => {
              __mk_pair(
                self.alloc(
                  Coq_Numbers_BinNums_N::Npos(
                    PhantomData,
                    self.alloc(
                      Coq_Numbers_BinNums_positive::xH(
                        PhantomData)))),
                self.alloc(
                  Coq_Numbers_BinNums_N::N0(
                    PhantomData)))
            },
          }
        },
      }
    },
  }
}
fn Coq_NArith_BinNatDef_N_pos_div_eucl__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_positive<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_N<'a>) -> __pair<&'a Coq_Numbers_BinNums_N<'a>, &'a Coq_Numbers_BinNums_N<'a>> {
  self.closure(move |a| {
    self.closure(move |b| {
      self.Coq_NArith_BinNatDef_N_pos_div_eucl(
        a,
        b)
    })
  })
}

fn Coq_NArith_BinNatDef_N_div_eucl(&'a self, a: &'a Coq_Numbers_BinNums_N<'a>, b: &'a Coq_Numbers_BinNums_N<'a>) -> __pair<&'a Coq_Numbers_BinNums_N<'a>, &'a Coq_Numbers_BinNums_N<'a>> {
  match a {
    &Coq_Numbers_BinNums_N::N0(_) => {
      __mk_pair(
        self.alloc(
          Coq_Numbers_BinNums_N::N0(
            PhantomData)),
        self.alloc(
          Coq_Numbers_BinNums_N::N0(
            PhantomData)))
    },
    &Coq_Numbers_BinNums_N::Npos(_, na) => {
      match b {
        &Coq_Numbers_BinNums_N::N0(_) => {
          __mk_pair(
            self.alloc(
              Coq_Numbers_BinNums_N::N0(
                PhantomData)),
            a)
        },
        &Coq_Numbers_BinNums_N::Npos(_, p) => {
          self.Coq_NArith_BinNatDef_N_pos_div_eucl(
            na,
            b)
        },
      }
    },
  }
}
fn Coq_NArith_BinNatDef_N_div_eucl__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_N<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_N<'a>) -> __pair<&'a Coq_Numbers_BinNums_N<'a>, &'a Coq_Numbers_BinNums_N<'a>> {
  self.closure(move |a| {
    self.closure(move |b| {
      self.Coq_NArith_BinNatDef_N_div_eucl(
        a,
        b)
    })
  })
}

fn Coq_NArith_BinNatDef_N_div(&'a self, a: &'a Coq_Numbers_BinNums_N<'a>, b: &'a Coq_Numbers_BinNums_N<'a>) -> &'a Coq_Numbers_BinNums_N<'a> {
  self.Coq_Init_Datatypes_fst(
    self.Coq_NArith_BinNatDef_N_div_eucl(
      a,
      b))
}
fn Coq_NArith_BinNatDef_N_div__curried(&'a self) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_N<'a>) -> &'a dyn Fn(&'a Coq_Numbers_BinNums_N<'a>) -> &'a Coq_Numbers_BinNums_N<'a> {
  self.closure(move |a| {
    self.closure(move |b| {
      self.Coq_NArith_BinNatDef_N_div(
        a,
        b)
    })
  })
}

fn CertiCoq_Benchmarks_tests_stack_machine_gauss_N(&'a self) -> Option<&'a Coq_Numbers_BinNums_N<'a>> {
  let n =
    self.alloc(
      Coq_Numbers_BinNums_N::Npos(
        PhantomData,
        self.alloc(
          Coq_Numbers_BinNums_positive::xO(
            PhantomData,
            self.alloc(
              Coq_Numbers_BinNums_positive::xO(
                PhantomData,
                self.alloc(
                  Coq_Numbers_BinNums_positive::xO(
                    PhantomData,
                    self.alloc(
                      Coq_Numbers_BinNums_positive::xI(
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
                                                PhantomData))))))))))))))))))))));
  match self.CertiCoq_Benchmarks_lib_stack_machine_s_execute_(
          self.CertiCoq_Benchmarks_lib_stack_machine_NumericBinNat())(
          self.CertiCoq_Benchmarks_lib_stack_machine_gauss_sum_sintrs_N(
            n)) {
    &Coq_Init_Datatypes_list::nil(_) => {
      None
    },
    &Coq_Init_Datatypes_list::cons(_, n2, l) => {
      match l {
        &Coq_Init_Datatypes_list::nil(_) => {
          Some(
            self.Coq_NArith_BinNatDef_N_sub(
              n2,
              self.Coq_NArith_BinNatDef_N_div(
                self.Coq_NArith_BinNatDef_N_mul(
                  n,
                  self.Coq_NArith_BinNatDef_N_add(
                    n,
                    self.alloc(
                      Coq_Numbers_BinNums_N::Npos(
                        PhantomData,
                        self.alloc(
                          Coq_Numbers_BinNums_positive::xH(
                            PhantomData)))))),
                self.alloc(
                  Coq_Numbers_BinNums_N::Npos(
                    PhantomData,
                    self.alloc(
                      Coq_Numbers_BinNums_positive::xO(
                        PhantomData,
                        self.alloc(
                          Coq_Numbers_BinNums_positive::xH(
                            PhantomData)))))))))
        },
        &Coq_Init_Datatypes_list::cons(_, n0, l0) => {
          None
        },
      }
    },
  }
}
}
pub fn main() {
  Program::new().CertiCoq_Benchmarks_tests_stack_machine_gauss_N();
}
