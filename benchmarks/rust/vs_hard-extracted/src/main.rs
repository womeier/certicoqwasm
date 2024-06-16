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
pub enum Coq_Init_Datatypes_list<'a, A> {
  nil(PhantomData<&'a A>),
  cons(PhantomData<&'a A>, A, &'a Coq_Init_Datatypes_list<'a, A>)
}

type Coq_PArith_BinPosDef_Pos_t<'a> = u64;

type CertiCoq_Benchmarks_lib_vs_var<'a> = Coq_PArith_BinPosDef_Pos_t<'a>;

#[derive(Debug, Clone)]
pub enum CertiCoq_Benchmarks_lib_vs_expr<'a> {
  Nil(PhantomData<&'a ()>),
  Var(PhantomData<&'a ()>, CertiCoq_Benchmarks_lib_vs_var<'a>)
}

#[derive(Debug, Clone)]
pub enum CertiCoq_Benchmarks_lib_vs_pn_atom<'a> {
  Equ(PhantomData<&'a ()>, &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, &'a CertiCoq_Benchmarks_lib_vs_expr<'a>),
  Nequ(PhantomData<&'a ()>, &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, &'a CertiCoq_Benchmarks_lib_vs_expr<'a>)
}

#[derive(Debug, Clone)]
pub enum CertiCoq_Benchmarks_lib_vs_space_atom<'a> {
  Next(PhantomData<&'a ()>, &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, &'a CertiCoq_Benchmarks_lib_vs_expr<'a>),
  Lseg(PhantomData<&'a ()>, &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, &'a CertiCoq_Benchmarks_lib_vs_expr<'a>)
}

#[derive(Debug, Clone)]
pub enum CertiCoq_Benchmarks_lib_vs_assertion<'a> {
  Assertion(PhantomData<&'a ()>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pn_atom<'a>>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>)
}

#[derive(Debug, Clone)]
pub enum CertiCoq_Benchmarks_lib_vs_entailment<'a> {
  Entailment(PhantomData<&'a ()>, &'a CertiCoq_Benchmarks_lib_vs_assertion<'a>, &'a CertiCoq_Benchmarks_lib_vs_assertion<'a>)
}

#[derive(Debug, Clone)]
pub enum CertiCoq_Benchmarks_lib_vs_pure_atom<'a> {
  Eqv(PhantomData<&'a ()>, &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, &'a CertiCoq_Benchmarks_lib_vs_expr<'a>)
}

#[derive(Debug, Clone)]
pub enum CertiCoq_Benchmarks_lib_vs_clause<'a> {
  PureClause(PhantomData<&'a ()>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>, CertiCoq_Benchmarks_lib_vs_var<'a>),
  PosSpaceClause(PhantomData<&'a ()>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>),
  NegSpaceClause(PhantomData<&'a ()>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>)
}

#[derive(Debug, Clone)]
pub enum Coq_MSets_MSetRBT_color<'a> {
  Red(PhantomData<&'a ()>),
  Black(PhantomData<&'a ()>)
}

type Coq_MSets_MSetRBT_Color_t<'a> = &'a Coq_MSets_MSetRBT_color<'a>;

#[derive(Debug, Clone)]
pub enum CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a> {
  Leaf(PhantomData<&'a ()>),
  Node(PhantomData<&'a ()>, Coq_MSets_MSetRBT_Color_t<'a>, &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>)
}

type CertiCoq_Benchmarks_lib_vs_M_Raw_t<'a> = &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>;

type CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a> = &'a CertiCoq_Benchmarks_lib_vs_clause<'a>;

#[derive(Debug, Clone)]
pub enum CertiCoq_Benchmarks_lib_vs_M_t_<'a> {
  Mkt(PhantomData<&'a ()>, CertiCoq_Benchmarks_lib_vs_M_Raw_t<'a>)
}

type CertiCoq_Benchmarks_lib_vs_M_t<'a> = &'a CertiCoq_Benchmarks_lib_vs_M_t_<'a>;

type CertiCoq_Benchmarks_lib_vs_M_elt<'a> = &'a CertiCoq_Benchmarks_lib_vs_clause<'a>;

type CertiCoq_Benchmarks_lib_vs_Superposition_model<'a> = &'a Coq_Init_Datatypes_list<'a, __pair<CertiCoq_Benchmarks_lib_vs_var<'a>, &'a CertiCoq_Benchmarks_lib_vs_expr<'a>>>;

#[derive(Debug, Clone)]
pub enum CertiCoq_Benchmarks_lib_vs_VeriStar_veristar_result<'a> {
  Valid(PhantomData<&'a ()>),
  C_example(PhantomData<&'a ()>, CertiCoq_Benchmarks_lib_vs_Superposition_model<'a>),
  Aborted(PhantomData<&'a ()>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>)
}

#[derive(Debug, Clone)]
pub enum CertiCoq_Benchmarks_lib_vs_Superposition_superposition_result<'a> {
  Valid(PhantomData<&'a ()>),
  C_example(PhantomData<&'a ()>, CertiCoq_Benchmarks_lib_vs_Superposition_model<'a>, CertiCoq_Benchmarks_lib_vs_M_t<'a>),
  Aborted(PhantomData<&'a ()>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>)
}

#[derive(Debug, Clone)]
pub enum CertiCoq_Benchmarks_lib_vs_ce_type<'a> {
  CexpL(PhantomData<&'a ()>),
  CexpR(PhantomData<&'a ()>),
  CexpEf(PhantomData<&'a ()>)
}

#[derive(Debug, Clone)]
pub enum Coq_Init_Datatypes_sum<'a, A, B> {
  inl(PhantomData<&'a (A, B)>, A),
  inr(PhantomData<&'a (A, B)>, B)
}

#[derive(Debug, Clone)]
pub enum Coq_Init_Specif_sumbool<'a> {
  left(PhantomData<&'a ()>),
  right(PhantomData<&'a ()>)
}

type Coq_Init_Datatypes_ID<'a> = &'a dyn Fn(()) -> &'a dyn Fn(()) -> ();

#[derive(Debug, Clone)]
pub enum Coq_Init_Logic_and<'a> {
  conj(PhantomData<&'a ()>)
}

#[derive(Debug, Clone)]
pub enum Coq_Init_Specif_sig<'a, A> {
  exist(PhantomData<&'a A>, A)
}

#[derive(Debug, Clone)]
pub enum CertiCoq_Benchmarks_lib_vs_M_Raw_enumeration<'a> {
  End(PhantomData<&'a ()>),
  More(PhantomData<&'a ()>, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>, &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, &'a CertiCoq_Benchmarks_lib_vs_M_Raw_enumeration<'a>)
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

fn Coq_PArith_BinPosDef_Pos_succ(&'a self, a: u64) -> u64 { a + 1 }
fn Coq_PArith_BinPosDef_Pos_succ__curried(&'a self) -> &'a dyn Fn(u64) -> u64 {
  self.closure(move |x| {
    self.Coq_PArith_BinPosDef_Pos_succ(
      x)
  })
}

fn Coq_PArith_BinPosDef_Pos_add(&'a self, a: u64, b: u64) -> u64 { a + b }

fn CertiCoq_Benchmarks_lib_vs_add_id(&'a self) -> &'a dyn Fn(u64) -> &'a dyn Fn(u64) -> u64 {
  self.Coq_PArith_BinPosDef_Pos_add()
}

fn CertiCoq_Benchmarks_lib_vs_list_prio<A: Copy>(&'a self, A: (), weight: CertiCoq_Benchmarks_lib_vs_var<'a>, l: &'a Coq_Init_Datatypes_list<'a, A>, p: CertiCoq_Benchmarks_lib_vs_var<'a>) -> CertiCoq_Benchmarks_lib_vs_var<'a> {
  match l {
    &Coq_Init_Datatypes_list::nil(_) => {
      p
    },
    &Coq_Init_Datatypes_list::cons(_, a, l2) => {
      self.CertiCoq_Benchmarks_lib_vs_list_prio(
        (),
        weight,
        l2,
        self.CertiCoq_Benchmarks_lib_vs_add_id()(
          weight)(
          p))
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_list_prio__curried<A: Copy>(&'a self) -> &'a dyn Fn(()) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_var<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_var<'a>) -> CertiCoq_Benchmarks_lib_vs_var<'a> {
  self.closure(move |A| {
    self.closure(move |weight| {
      self.closure(move |l| {
        self.closure(move |p| {
          self.CertiCoq_Benchmarks_lib_vs_list_prio(
            A,
            weight,
            l,
            p)
        })
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_Z2id(&'a self, z: i64) -> Coq_PArith_BinPosDef_Pos_t<'a> {
  __Z_elim!(
    {
      1
    },
    p, {
      self.Coq_PArith_BinPosDef_Pos_add()(
        p)(
        1)
    },
    p, {
      1
    },
    z)
}
fn CertiCoq_Benchmarks_lib_vs_Z2id__curried(&'a self) -> &'a dyn Fn(i64) -> Coq_PArith_BinPosDef_Pos_t<'a> {
  self.closure(move |z| {
    self.CertiCoq_Benchmarks_lib_vs_Z2id(
      z)
  })
}

fn CertiCoq_Benchmarks_lib_vs_var2(&'a self) -> CertiCoq_Benchmarks_lib_vs_var<'a> {
  self.CertiCoq_Benchmarks_lib_vs_Z2id(
    __Z_frompos(
      __pos_zerobit(
        1)))
}

fn CertiCoq_Benchmarks_lib_vs_var1(&'a self) -> CertiCoq_Benchmarks_lib_vs_var<'a> {
  self.CertiCoq_Benchmarks_lib_vs_Z2id(
    __Z_frompos(
      1))
}

fn CertiCoq_Benchmarks_lib_vs_var0(&'a self) -> CertiCoq_Benchmarks_lib_vs_var<'a> {
  self.CertiCoq_Benchmarks_lib_vs_Z2id(
    0)
}

fn CertiCoq_Benchmarks_lib_vs_prio(&'a self, gamma: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>, delta: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> CertiCoq_Benchmarks_lib_vs_var<'a> {
  self.CertiCoq_Benchmarks_lib_vs_list_prio(
    (),
    self.CertiCoq_Benchmarks_lib_vs_var2(),
    gamma,
    self.CertiCoq_Benchmarks_lib_vs_list_prio(
      (),
      self.CertiCoq_Benchmarks_lib_vs_var1(),
      delta,
      self.CertiCoq_Benchmarks_lib_vs_var0()))
}
fn CertiCoq_Benchmarks_lib_vs_prio__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> CertiCoq_Benchmarks_lib_vs_var<'a> {
  self.closure(move |gamma| {
    self.closure(move |delta| {
      self.CertiCoq_Benchmarks_lib_vs_prio(
        gamma,
        delta)
    })
  })
}

fn Coq_Lists_List_fold_left<A: Copy, B: Copy>(&'a self, f: &'a dyn Fn(A) -> &'a dyn Fn(B) -> A, l: &'a Coq_Init_Datatypes_list<'a, B>, a0: A) -> A {
  match l {
    &Coq_Init_Datatypes_list::nil(_) => {
      a0
    },
    &Coq_Init_Datatypes_list::cons(_, b, t) => {
      self.Coq_Lists_List_fold_left(
        f,
        t,
        hint_app(hint_app(f)(a0))(b))
    },
  }
}
fn Coq_Lists_List_fold_left__curried<A: Copy, B: Copy>(&'a self) -> &'a dyn Fn(&'a dyn Fn(A) -> &'a dyn Fn(B) -> A) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, B>) -> &'a dyn Fn(A) -> A {
  self.closure(move |f| {
    self.closure(move |l| {
      self.closure(move |a0| {
        self.Coq_Lists_List_fold_left(
          f,
          l,
          a0)
      })
    })
  })
}

fn Coq_PArith_BinPosDef_Pos_compare(&'a self, a: u64, b: u64) -> std::cmp::Ordering {
  a.cmp(&b)
}

fn CertiCoq_Benchmarks_lib_vs_prio1000(&'a self) -> Coq_PArith_BinPosDef_Pos_t<'a> {
  self.CertiCoq_Benchmarks_lib_vs_Z2id(
    __Z_frompos(
      __pos_zerobit(
        __pos_zerobit(
          __pos_zerobit(
            __pos_onebit(
              __pos_zerobit(
                __pos_onebit(
                  __pos_onebit(
                    __pos_onebit(
                      __pos_onebit(
                        1)))))))))))
}

fn CertiCoq_Benchmarks_lib_vs_prio1001(&'a self) -> Coq_PArith_BinPosDef_Pos_t<'a> {
  self.CertiCoq_Benchmarks_lib_vs_Z2id(
    __Z_frompos(
      __pos_onebit(
        __pos_zerobit(
          __pos_zerobit(
            __pos_onebit(
              __pos_zerobit(
                __pos_onebit(
                  __pos_onebit(
                    __pos_onebit(
                      __pos_onebit(
                        1)))))))))))
}

fn CertiCoq_Benchmarks_lib_vs_clause_prio(&'a self, cl: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> CertiCoq_Benchmarks_lib_vs_var<'a> {
  match cl {
    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma, delta, prio) => {
      prio
    },
    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
      self.CertiCoq_Benchmarks_lib_vs_prio1000()
    },
    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
      self.CertiCoq_Benchmarks_lib_vs_prio1001()
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_clause_prio__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> CertiCoq_Benchmarks_lib_vs_var<'a> {
  self.closure(move |cl| {
    self.CertiCoq_Benchmarks_lib_vs_clause_prio(
      cl)
  })
}

fn CertiCoq_Benchmarks_lib_vs_compare_list<A: Copy>(&'a self, A: (), f: &'a dyn Fn(A) -> &'a dyn Fn(A) -> std::cmp::Ordering, xl: &'a Coq_Init_Datatypes_list<'a, A>, yl: &'a Coq_Init_Datatypes_list<'a, A>) -> std::cmp::Ordering {
  match xl {
    &Coq_Init_Datatypes_list::nil(_) => {
      match yl {
        &Coq_Init_Datatypes_list::nil(_) => {
          std::cmp::Ordering::Equal
        },
        &Coq_Init_Datatypes_list::cons(_, a, l) => {
          std::cmp::Ordering::Less
        },
      }
    },
    &Coq_Init_Datatypes_list::cons(_, x, xl2) => {
      match yl {
        &Coq_Init_Datatypes_list::nil(_) => {
          std::cmp::Ordering::Greater
        },
        &Coq_Init_Datatypes_list::cons(_, y, yl2) => {
          match hint_app(hint_app(f)(x))(y) {
            std::cmp::Ordering::Equal => {
              self.CertiCoq_Benchmarks_lib_vs_compare_list(
                (),
                f,
                xl2,
                yl2)
            },
            std::cmp::Ordering::Less => {
              std::cmp::Ordering::Less
            },
            std::cmp::Ordering::Greater => {
              std::cmp::Ordering::Greater
            },
          }
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_compare_list__curried<A: Copy>(&'a self) -> &'a dyn Fn(()) -> &'a dyn Fn(&'a dyn Fn(A) -> &'a dyn Fn(A) -> std::cmp::Ordering) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> std::cmp::Ordering {
  self.closure(move |A| {
    self.closure(move |f| {
      self.closure(move |xl| {
        self.closure(move |yl| {
          self.CertiCoq_Benchmarks_lib_vs_compare_list(
            A,
            f,
            xl,
            yl)
        })
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_expr_cmp(&'a self, e: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, e2: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> std::cmp::Ordering {
  match e {
    &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
      match e2 {
        &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
          std::cmp::Ordering::Equal
        },
        &CertiCoq_Benchmarks_lib_vs_expr::Var(_, v) => {
          std::cmp::Ordering::Less
        },
      }
    },
    &CertiCoq_Benchmarks_lib_vs_expr::Var(_, v) => {
      match e2 {
        &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
          std::cmp::Ordering::Greater
        },
        &CertiCoq_Benchmarks_lib_vs_expr::Var(_, v2) => {
          self.Coq_PArith_BinPosDef_Pos_compare()(
            v)(
            v2)
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_expr_cmp__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> std::cmp::Ordering {
  self.closure(move |e| {
    self.closure(move |e2| {
      self.CertiCoq_Benchmarks_lib_vs_expr_cmp(
        e,
        e2)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_pure_atom_cmp(&'a self, a: &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>, a2: &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> std::cmp::Ordering {
  match a {
    &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, e1, e2) => {
      match a2 {
        &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, e12, e22) => {
          match self.CertiCoq_Benchmarks_lib_vs_expr_cmp(
                  e1,
                  e12) {
            std::cmp::Ordering::Equal => {
              self.CertiCoq_Benchmarks_lib_vs_expr_cmp(
                e2,
                e22)
            },
            std::cmp::Ordering::Less => {
              std::cmp::Ordering::Less
            },
            std::cmp::Ordering::Greater => {
              std::cmp::Ordering::Greater
            },
          }
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> std::cmp::Ordering {
  self.closure(move |a| {
    self.closure(move |a2| {
      self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp(
        a,
        a2)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_compare_space_atom(&'a self, a: &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>, b: &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>) -> std::cmp::Ordering {
  match a {
    &CertiCoq_Benchmarks_lib_vs_space_atom::Next(_, i, j) => {
      match b {
        &CertiCoq_Benchmarks_lib_vs_space_atom::Next(_, i2, j2) => {
          match self.CertiCoq_Benchmarks_lib_vs_expr_cmp(
                  i,
                  i2) {
            std::cmp::Ordering::Equal => {
              self.CertiCoq_Benchmarks_lib_vs_expr_cmp(
                j,
                j2)
            },
            std::cmp::Ordering::Less => {
              std::cmp::Ordering::Less
            },
            std::cmp::Ordering::Greater => {
              std::cmp::Ordering::Greater
            },
          }
        },
        &CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(_, i2, j2) => {
          match self.CertiCoq_Benchmarks_lib_vs_expr_cmp(
                  i,
                  i2) {
            std::cmp::Ordering::Equal => {
              std::cmp::Ordering::Less
            },
            std::cmp::Ordering::Less => {
              std::cmp::Ordering::Less
            },
            std::cmp::Ordering::Greater => {
              std::cmp::Ordering::Greater
            },
          }
        },
      }
    },
    &CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(_, i, j) => {
      match b {
        &CertiCoq_Benchmarks_lib_vs_space_atom::Next(_, i2, j2) => {
          match self.CertiCoq_Benchmarks_lib_vs_expr_cmp(
                  i,
                  i2) {
            std::cmp::Ordering::Equal => {
              std::cmp::Ordering::Greater
            },
            std::cmp::Ordering::Less => {
              std::cmp::Ordering::Less
            },
            std::cmp::Ordering::Greater => {
              std::cmp::Ordering::Greater
            },
          }
        },
        &CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(_, i2, j2) => {
          match self.CertiCoq_Benchmarks_lib_vs_expr_cmp(
                  i,
                  i2) {
            std::cmp::Ordering::Equal => {
              self.CertiCoq_Benchmarks_lib_vs_expr_cmp(
                j,
                j2)
            },
            std::cmp::Ordering::Less => {
              std::cmp::Ordering::Less
            },
            std::cmp::Ordering::Greater => {
              std::cmp::Ordering::Greater
            },
          }
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_compare_space_atom__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>) -> std::cmp::Ordering {
  self.closure(move |a| {
    self.closure(move |b| {
      self.CertiCoq_Benchmarks_lib_vs_compare_space_atom(
        a,
        b)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_compare_clause(&'a self, cl1: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, cl2: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> std::cmp::Ordering {
  match cl1 {
    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, neg, pos, priority) => {
      match cl2 {
        &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, neg2, pos2, priority0) => {
          match self.CertiCoq_Benchmarks_lib_vs_compare_list(
                  (),
                  self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
                  neg,
                  neg2) {
            std::cmp::Ordering::Equal => {
              self.CertiCoq_Benchmarks_lib_vs_compare_list(
                (),
                self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
                pos,
                pos2)
            },
            std::cmp::Ordering::Less => {
              std::cmp::Ordering::Less
            },
            std::cmp::Ordering::Greater => {
              std::cmp::Ordering::Greater
            },
          }
        },
        &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
          std::cmp::Ordering::Less
        },
        &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
          std::cmp::Ordering::Less
        },
      }
    },
    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
      match cl2 {
        &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma0, delta0, priority) => {
          std::cmp::Ordering::Greater
        },
        &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma2, delta2, sigma2) => {
          match self.CertiCoq_Benchmarks_lib_vs_compare_list(
                  (),
                  self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
                  gamma,
                  gamma2) {
            std::cmp::Ordering::Equal => {
              match self.CertiCoq_Benchmarks_lib_vs_compare_list(
                      (),
                      self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
                      delta,
                      delta2) {
                std::cmp::Ordering::Equal => {
                  self.CertiCoq_Benchmarks_lib_vs_compare_list(
                    (),
                    self.CertiCoq_Benchmarks_lib_vs_compare_space_atom__curried(),
                    sigma,
                    sigma2)
                },
                std::cmp::Ordering::Less => {
                  std::cmp::Ordering::Less
                },
                std::cmp::Ordering::Greater => {
                  std::cmp::Ordering::Greater
                },
              }
            },
            std::cmp::Ordering::Less => {
              std::cmp::Ordering::Less
            },
            std::cmp::Ordering::Greater => {
              std::cmp::Ordering::Greater
            },
          }
        },
        &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma0, sigma0, delta0) => {
          std::cmp::Ordering::Less
        },
      }
    },
    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
      match cl2 {
        &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma0, delta0, priority) => {
          std::cmp::Ordering::Greater
        },
        &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma0, delta0, sigma0) => {
          std::cmp::Ordering::Greater
        },
        &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma2, sigma2, delta2) => {
          match self.CertiCoq_Benchmarks_lib_vs_compare_list(
                  (),
                  self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
                  gamma,
                  gamma2) {
            std::cmp::Ordering::Equal => {
              match self.CertiCoq_Benchmarks_lib_vs_compare_list(
                      (),
                      self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
                      delta,
                      delta2) {
                std::cmp::Ordering::Equal => {
                  self.CertiCoq_Benchmarks_lib_vs_compare_list(
                    (),
                    self.CertiCoq_Benchmarks_lib_vs_compare_space_atom__curried(),
                    sigma,
                    sigma2)
                },
                std::cmp::Ordering::Less => {
                  std::cmp::Ordering::Less
                },
                std::cmp::Ordering::Greater => {
                  std::cmp::Ordering::Greater
                },
              }
            },
            std::cmp::Ordering::Less => {
              std::cmp::Ordering::Less
            },
            std::cmp::Ordering::Greater => {
              std::cmp::Ordering::Greater
            },
          }
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_compare_clause__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> std::cmp::Ordering {
  self.closure(move |cl1| {
    self.closure(move |cl2| {
      self.CertiCoq_Benchmarks_lib_vs_compare_clause(
        cl1,
        cl2)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_compare_clause_(&'a self, cl1: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, cl2: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> std::cmp::Ordering {
  match self.Coq_PArith_BinPosDef_Pos_compare()(
          self.CertiCoq_Benchmarks_lib_vs_clause_prio(
            cl1))(
          self.CertiCoq_Benchmarks_lib_vs_clause_prio(
            cl2)) {
    std::cmp::Ordering::Equal => {
      self.CertiCoq_Benchmarks_lib_vs_compare_clause(
        cl1,
        cl2)
    },
    std::cmp::Ordering::Less => {
      std::cmp::Ordering::Less
    },
    std::cmp::Ordering::Greater => {
      std::cmp::Ordering::Greater
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_compare_clause___curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> std::cmp::Ordering {
  self.closure(move |cl1| {
    self.closure(move |cl2| {
      self.CertiCoq_Benchmarks_lib_vs_compare_clause_(
        cl1,
        cl2)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_makeBlack(&'a self, t: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a> {
  match t {
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
      self.alloc(
        CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(
          PhantomData))
    },
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t0, a, x, b) => {
      self.alloc(
        CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
          PhantomData,
          self.alloc(
            Coq_MSets_MSetRBT_color::Black(
              PhantomData)),
          a,
          x,
          b))
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_makeBlack__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a> {
  self.closure(move |t| {
    self.CertiCoq_Benchmarks_lib_vs_M_Raw_makeBlack(
      t)
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_lbal(&'a self, l: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, k: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, r: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a> {
  match l {
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
      self.alloc(
        CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
          PhantomData,
          self.alloc(
            Coq_MSets_MSetRBT_color::Black(
              PhantomData)),
          l,
          k,
          r))
    },
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t, a, x, c) => {
      match t {
        &Coq_MSets_MSetRBT_color::Red(_) => {
          match a {
            &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
              match c {
                &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
                  self.alloc(
                    CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                      PhantomData,
                      self.alloc(
                        Coq_MSets_MSetRBT_color::Black(
                          PhantomData)),
                      l,
                      k,
                      r))
                },
                &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t0, b, y, c2) => {
                  match t0 {
                    &Coq_MSets_MSetRBT_color::Red(_) => {
                      self.alloc(
                        CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                          PhantomData,
                          self.alloc(
                            Coq_MSets_MSetRBT_color::Red(
                              PhantomData)),
                          self.alloc(
                            CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                              PhantomData,
                              self.alloc(
                                Coq_MSets_MSetRBT_color::Black(
                                  PhantomData)),
                              a,
                              x,
                              b)),
                          y,
                          self.alloc(
                            CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                              PhantomData,
                              self.alloc(
                                Coq_MSets_MSetRBT_color::Black(
                                  PhantomData)),
                              c2,
                              k,
                              r))))
                    },
                    &Coq_MSets_MSetRBT_color::Black(_) => {
                      self.alloc(
                        CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                          PhantomData,
                          self.alloc(
                            Coq_MSets_MSetRBT_color::Black(
                              PhantomData)),
                          l,
                          k,
                          r))
                    },
                  }
                },
              }
            },
            &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t0, a2, x2, b) => {
              match t0 {
                &Coq_MSets_MSetRBT_color::Red(_) => {
                  self.alloc(
                    CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                      PhantomData,
                      self.alloc(
                        Coq_MSets_MSetRBT_color::Red(
                          PhantomData)),
                      self.alloc(
                        CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                          PhantomData,
                          self.alloc(
                            Coq_MSets_MSetRBT_color::Black(
                              PhantomData)),
                          a2,
                          x2,
                          b)),
                      x,
                      self.alloc(
                        CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                          PhantomData,
                          self.alloc(
                            Coq_MSets_MSetRBT_color::Black(
                              PhantomData)),
                          c,
                          k,
                          r))))
                },
                &Coq_MSets_MSetRBT_color::Black(_) => {
                  match c {
                    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
                      self.alloc(
                        CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                          PhantomData,
                          self.alloc(
                            Coq_MSets_MSetRBT_color::Black(
                              PhantomData)),
                          l,
                          k,
                          r))
                    },
                    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t1, b2, y, c2) => {
                      match t1 {
                        &Coq_MSets_MSetRBT_color::Red(_) => {
                          self.alloc(
                            CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                              PhantomData,
                              self.alloc(
                                Coq_MSets_MSetRBT_color::Red(
                                  PhantomData)),
                              self.alloc(
                                CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                                  PhantomData,
                                  self.alloc(
                                    Coq_MSets_MSetRBT_color::Black(
                                      PhantomData)),
                                  a,
                                  x,
                                  b2)),
                              y,
                              self.alloc(
                                CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                                  PhantomData,
                                  self.alloc(
                                    Coq_MSets_MSetRBT_color::Black(
                                      PhantomData)),
                                  c2,
                                  k,
                                  r))))
                        },
                        &Coq_MSets_MSetRBT_color::Black(_) => {
                          self.alloc(
                            CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                              PhantomData,
                              self.alloc(
                                Coq_MSets_MSetRBT_color::Black(
                                  PhantomData)),
                              l,
                              k,
                              r))
                        },
                      }
                    },
                  }
                },
              }
            },
          }
        },
        &Coq_MSets_MSetRBT_color::Black(_) => {
          self.alloc(
            CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
              PhantomData,
              self.alloc(
                Coq_MSets_MSetRBT_color::Black(
                  PhantomData)),
              l,
              k,
              r))
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_lbal__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a> {
  self.closure(move |l| {
    self.closure(move |k| {
      self.closure(move |r| {
        self.CertiCoq_Benchmarks_lib_vs_M_Raw_lbal(
          l,
          k,
          r)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_rbal(&'a self, l: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, k: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, r: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a> {
  match r {
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
      self.alloc(
        CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
          PhantomData,
          self.alloc(
            Coq_MSets_MSetRBT_color::Black(
              PhantomData)),
          l,
          k,
          r))
    },
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t, b, y, d) => {
      match t {
        &Coq_MSets_MSetRBT_color::Red(_) => {
          match b {
            &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
              match d {
                &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
                  self.alloc(
                    CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                      PhantomData,
                      self.alloc(
                        Coq_MSets_MSetRBT_color::Black(
                          PhantomData)),
                      l,
                      k,
                      r))
                },
                &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t0, c, z, d2) => {
                  match t0 {
                    &Coq_MSets_MSetRBT_color::Red(_) => {
                      self.alloc(
                        CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                          PhantomData,
                          self.alloc(
                            Coq_MSets_MSetRBT_color::Red(
                              PhantomData)),
                          self.alloc(
                            CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                              PhantomData,
                              self.alloc(
                                Coq_MSets_MSetRBT_color::Black(
                                  PhantomData)),
                              l,
                              k,
                              b)),
                          y,
                          self.alloc(
                            CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                              PhantomData,
                              self.alloc(
                                Coq_MSets_MSetRBT_color::Black(
                                  PhantomData)),
                              c,
                              z,
                              d2))))
                    },
                    &Coq_MSets_MSetRBT_color::Black(_) => {
                      self.alloc(
                        CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                          PhantomData,
                          self.alloc(
                            Coq_MSets_MSetRBT_color::Black(
                              PhantomData)),
                          l,
                          k,
                          r))
                    },
                  }
                },
              }
            },
            &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t0, b2, y2, c) => {
              match t0 {
                &Coq_MSets_MSetRBT_color::Red(_) => {
                  self.alloc(
                    CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                      PhantomData,
                      self.alloc(
                        Coq_MSets_MSetRBT_color::Red(
                          PhantomData)),
                      self.alloc(
                        CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                          PhantomData,
                          self.alloc(
                            Coq_MSets_MSetRBT_color::Black(
                              PhantomData)),
                          l,
                          k,
                          b2)),
                      y2,
                      self.alloc(
                        CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                          PhantomData,
                          self.alloc(
                            Coq_MSets_MSetRBT_color::Black(
                              PhantomData)),
                          c,
                          y,
                          d))))
                },
                &Coq_MSets_MSetRBT_color::Black(_) => {
                  match d {
                    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
                      self.alloc(
                        CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                          PhantomData,
                          self.alloc(
                            Coq_MSets_MSetRBT_color::Black(
                              PhantomData)),
                          l,
                          k,
                          r))
                    },
                    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t1, c2, z, d2) => {
                      match t1 {
                        &Coq_MSets_MSetRBT_color::Red(_) => {
                          self.alloc(
                            CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                              PhantomData,
                              self.alloc(
                                Coq_MSets_MSetRBT_color::Red(
                                  PhantomData)),
                              self.alloc(
                                CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                                  PhantomData,
                                  self.alloc(
                                    Coq_MSets_MSetRBT_color::Black(
                                      PhantomData)),
                                  l,
                                  k,
                                  b)),
                              y,
                              self.alloc(
                                CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                                  PhantomData,
                                  self.alloc(
                                    Coq_MSets_MSetRBT_color::Black(
                                      PhantomData)),
                                  c2,
                                  z,
                                  d2))))
                        },
                        &Coq_MSets_MSetRBT_color::Black(_) => {
                          self.alloc(
                            CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                              PhantomData,
                              self.alloc(
                                Coq_MSets_MSetRBT_color::Black(
                                  PhantomData)),
                              l,
                              k,
                              r))
                        },
                      }
                    },
                  }
                },
              }
            },
          }
        },
        &Coq_MSets_MSetRBT_color::Black(_) => {
          self.alloc(
            CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
              PhantomData,
              self.alloc(
                Coq_MSets_MSetRBT_color::Black(
                  PhantomData)),
              l,
              k,
              r))
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_rbal__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a> {
  self.closure(move |l| {
    self.closure(move |k| {
      self.closure(move |r| {
        self.CertiCoq_Benchmarks_lib_vs_M_Raw_rbal(
          l,
          k,
          r)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_ins(&'a self, x: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, s: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a> {
  match s {
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
      self.alloc(
        CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
          PhantomData,
          self.alloc(
            Coq_MSets_MSetRBT_color::Red(
              PhantomData)),
          self.alloc(
            CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(
              PhantomData)),
          x,
          self.alloc(
            CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(
              PhantomData))))
    },
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, c, l, y, r) => {
      match self.CertiCoq_Benchmarks_lib_vs_compare_clause_(
              x,
              y) {
        std::cmp::Ordering::Equal => {
          s
        },
        std::cmp::Ordering::Less => {
          match c {
            &Coq_MSets_MSetRBT_color::Red(_) => {
              self.alloc(
                CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                  PhantomData,
                  self.alloc(
                    Coq_MSets_MSetRBT_color::Red(
                      PhantomData)),
                  self.CertiCoq_Benchmarks_lib_vs_M_Raw_ins(
                    x,
                    l),
                  y,
                  r))
            },
            &Coq_MSets_MSetRBT_color::Black(_) => {
              self.CertiCoq_Benchmarks_lib_vs_M_Raw_lbal(
                self.CertiCoq_Benchmarks_lib_vs_M_Raw_ins(
                  x,
                  l),
                y,
                r)
            },
          }
        },
        std::cmp::Ordering::Greater => {
          match c {
            &Coq_MSets_MSetRBT_color::Red(_) => {
              self.alloc(
                CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                  PhantomData,
                  self.alloc(
                    Coq_MSets_MSetRBT_color::Red(
                      PhantomData)),
                  l,
                  y,
                  self.CertiCoq_Benchmarks_lib_vs_M_Raw_ins(
                    x,
                    r)))
            },
            &Coq_MSets_MSetRBT_color::Black(_) => {
              self.CertiCoq_Benchmarks_lib_vs_M_Raw_rbal(
                l,
                y,
                self.CertiCoq_Benchmarks_lib_vs_M_Raw_ins(
                  x,
                  r))
            },
          }
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_ins__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a> {
  self.closure(move |x| {
    self.closure(move |s| {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_ins(
        x,
        s)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_add(&'a self, x: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, s: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a> {
  self.CertiCoq_Benchmarks_lib_vs_M_Raw_makeBlack(
    self.CertiCoq_Benchmarks_lib_vs_M_Raw_ins(
      x,
      s))
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_add__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a> {
  self.closure(move |x| {
    self.closure(move |s| {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_add(
        x,
        s)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_this(&'a self, t: &'a CertiCoq_Benchmarks_lib_vs_M_t_<'a>) -> CertiCoq_Benchmarks_lib_vs_M_Raw_t<'a> {
  match t {
    &CertiCoq_Benchmarks_lib_vs_M_t_::Mkt(_, this) => {
      this
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_M_this__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_t_<'a>) -> CertiCoq_Benchmarks_lib_vs_M_Raw_t<'a> {
  self.closure(move |t| {
    self.CertiCoq_Benchmarks_lib_vs_M_this(
      t)
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_add(&'a self, x: CertiCoq_Benchmarks_lib_vs_M_elt<'a>, s: CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.alloc(
    CertiCoq_Benchmarks_lib_vs_M_t_::Mkt(
      PhantomData,
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_add(
        x,
        self.CertiCoq_Benchmarks_lib_vs_M_this(
          s))))
}
fn CertiCoq_Benchmarks_lib_vs_M_add__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_elt<'a>) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.closure(move |x| {
    self.closure(move |s| {
      self.CertiCoq_Benchmarks_lib_vs_M_add(
        x,
        s)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_empty(&'a self) -> &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a> {
  self.alloc(
    CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(
      PhantomData))
}

fn CertiCoq_Benchmarks_lib_vs_M_empty(&'a self) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.alloc(
    CertiCoq_Benchmarks_lib_vs_M_t_::Mkt(
      PhantomData,
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_empty()))
}

fn CertiCoq_Benchmarks_lib_vs_clause_list2set(&'a self, l: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.Coq_Lists_List_fold_left(
    self.closure(move |s0| {
      self.closure(move |c| {
        self.CertiCoq_Benchmarks_lib_vs_M_add(
          c,
          s0)
      })
    }),
    l,
    self.CertiCoq_Benchmarks_lib_vs_M_empty())
}
fn CertiCoq_Benchmarks_lib_vs_clause_list2set__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.closure(move |l| {
    self.CertiCoq_Benchmarks_lib_vs_clause_list2set(
      l)
  })
}

fn Coq_Lists_List_filter<A: Copy>(&'a self, f: &'a dyn Fn(A) -> bool, l: &'a Coq_Init_Datatypes_list<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  match l {
    &Coq_Init_Datatypes_list::nil(_) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
    &Coq_Init_Datatypes_list::cons(_, x, l2) => {
      match hint_app(f)(x) {
        true => {
          self.alloc(
            Coq_Init_Datatypes_list::cons(
              PhantomData,
              x,
              self.Coq_Lists_List_filter(
                f,
                l2)))
        },
        false => {
          self.Coq_Lists_List_filter(
            f,
            l2)
        },
      }
    },
  }
}
fn Coq_Lists_List_filter__curried<A: Copy>(&'a self) -> &'a dyn Fn(&'a dyn Fn(A) -> bool) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  self.closure(move |f| {
    self.closure(move |l| {
      self.Coq_Lists_List_filter(
        f,
        l)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_VeriStar_pureb(&'a self, c: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> bool {
  match c {
    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma, delta, priority) => {
      true
    },
    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
      false
    },
    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
      false
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_VeriStar_pureb__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> bool {
  self.closure(move |c| {
    self.CertiCoq_Benchmarks_lib_vs_VeriStar_pureb(
      c)
  })
}

fn CertiCoq_Benchmarks_lib_vs_VeriStar_pure_clauses(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.Coq_Lists_List_filter__curried()(
    self.CertiCoq_Benchmarks_lib_vs_VeriStar_pureb__curried())
}

fn Coq_Lists_List_map<A: Copy, B: Copy>(&'a self, f: &'a dyn Fn(A) -> B, l: &'a Coq_Init_Datatypes_list<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, B> {
  match l {
    &Coq_Init_Datatypes_list::nil(_) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
    &Coq_Init_Datatypes_list::cons(_, a, t) => {
      self.alloc(
        Coq_Init_Datatypes_list::cons(
          PhantomData,
          hint_app(f)(a),
          self.Coq_Lists_List_map(
            f,
            t)))
    },
  }
}
fn Coq_Lists_List_map__curried<A: Copy, B: Copy>(&'a self) -> &'a dyn Fn(&'a dyn Fn(A) -> B) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, B> {
  self.closure(move |f| {
    self.closure(move |l| {
      self.Coq_Lists_List_map(
        f,
        l)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_mkPureClause(&'a self, gamma: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>, delta: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> &'a CertiCoq_Benchmarks_lib_vs_clause<'a> {
  self.alloc(
    CertiCoq_Benchmarks_lib_vs_clause::PureClause(
      PhantomData,
      gamma,
      delta,
      self.CertiCoq_Benchmarks_lib_vs_prio(
        gamma,
        delta)))
}
fn CertiCoq_Benchmarks_lib_vs_mkPureClause__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> &'a CertiCoq_Benchmarks_lib_vs_clause<'a> {
  self.closure(move |gamma| {
    self.closure(move |delta| {
      self.CertiCoq_Benchmarks_lib_vs_mkPureClause(
        gamma,
        delta)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_insert_uniq<A: Copy>(&'a self, A: (), cmp: &'a dyn Fn(A) -> &'a dyn Fn(A) -> std::cmp::Ordering, a: A, l: &'a Coq_Init_Datatypes_list<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  match l {
    &Coq_Init_Datatypes_list::nil(_) => {
      self.alloc(
        Coq_Init_Datatypes_list::cons(
          PhantomData,
          a,
          self.alloc(
            Coq_Init_Datatypes_list::nil(
              PhantomData))))
    },
    &Coq_Init_Datatypes_list::cons(_, h, t) => {
      match hint_app(hint_app(cmp)(a))(h) {
        std::cmp::Ordering::Equal => {
          l
        },
        std::cmp::Ordering::Less => {
          self.alloc(
            Coq_Init_Datatypes_list::cons(
              PhantomData,
              h,
              self.CertiCoq_Benchmarks_lib_vs_insert_uniq(
                (),
                cmp,
                a,
                t)))
        },
        std::cmp::Ordering::Greater => {
          self.alloc(
            Coq_Init_Datatypes_list::cons(
              PhantomData,
              a,
              l))
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_insert_uniq__curried<A: Copy>(&'a self) -> &'a dyn Fn(()) -> &'a dyn Fn(&'a dyn Fn(A) -> &'a dyn Fn(A) -> std::cmp::Ordering) -> &'a dyn Fn(A) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  self.closure(move |A| {
    self.closure(move |cmp| {
      self.closure(move |a| {
        self.closure(move |l| {
          self.CertiCoq_Benchmarks_lib_vs_insert_uniq(
            A,
            cmp,
            a,
            l)
        })
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_rsort_uniq<A: Copy>(&'a self, A: (), cmp: &'a dyn Fn(A) -> &'a dyn Fn(A) -> std::cmp::Ordering, l: &'a Coq_Init_Datatypes_list<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  match l {
    &Coq_Init_Datatypes_list::nil(_) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
    &Coq_Init_Datatypes_list::cons(_, h, t) => {
      self.CertiCoq_Benchmarks_lib_vs_insert_uniq(
        (),
        cmp,
        h,
        self.CertiCoq_Benchmarks_lib_vs_rsort_uniq(
          (),
          cmp,
          t))
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_rsort_uniq__curried<A: Copy>(&'a self) -> &'a dyn Fn(()) -> &'a dyn Fn(&'a dyn Fn(A) -> &'a dyn Fn(A) -> std::cmp::Ordering) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  self.closure(move |A| {
    self.closure(move |cmp| {
      self.closure(move |l| {
        self.CertiCoq_Benchmarks_lib_vs_rsort_uniq(
          A,
          cmp,
          l)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_order_eqv_pure_atom(&'a self, a: &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a> {
  match a {
    &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, i, j) => {
      match self.CertiCoq_Benchmarks_lib_vs_expr_cmp(
              i,
              j) {
        std::cmp::Ordering::Equal => {
          self.alloc(
            CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
              PhantomData,
              i,
              j))
        },
        std::cmp::Ordering::Less => {
          self.alloc(
            CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
              PhantomData,
              j,
              i))
        },
        std::cmp::Ordering::Greater => {
          self.alloc(
            CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
              PhantomData,
              i,
              j))
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_order_eqv_pure_atom__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a> {
  self.closure(move |a| {
    self.CertiCoq_Benchmarks_lib_vs_order_eqv_pure_atom(
      a)
  })
}

fn CertiCoq_Benchmarks_lib_vs_normalize_atoms(&'a self, pa: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>> {
  self.CertiCoq_Benchmarks_lib_vs_rsort_uniq(
    (),
    self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
    self.Coq_Lists_List_map(
      self.CertiCoq_Benchmarks_lib_vs_order_eqv_pure_atom__curried(),
      pa))
}
fn CertiCoq_Benchmarks_lib_vs_normalize_atoms__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>> {
  self.closure(move |pa| {
    self.CertiCoq_Benchmarks_lib_vs_normalize_atoms(
      pa)
  })
}

fn CertiCoq_Benchmarks_lib_vs_nonreflex_atom(&'a self, a: &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> bool {
  match a {
    &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, i, j) => {
      match self.CertiCoq_Benchmarks_lib_vs_expr_cmp(
              i,
              j) {
        std::cmp::Ordering::Equal => {
          false
        },
        std::cmp::Ordering::Less => {
          true
        },
        std::cmp::Ordering::Greater => {
          true
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_nonreflex_atom__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> bool {
  self.closure(move |a| {
    self.CertiCoq_Benchmarks_lib_vs_nonreflex_atom(
      a)
  })
}

fn CertiCoq_Benchmarks_lib_vs_order_eqv_clause(&'a self, c: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_clause<'a> {
  match c {
    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, pa, pa2, priority) => {
      self.CertiCoq_Benchmarks_lib_vs_mkPureClause(
        self.CertiCoq_Benchmarks_lib_vs_normalize_atoms(
          self.Coq_Lists_List_filter(
            self.CertiCoq_Benchmarks_lib_vs_nonreflex_atom__curried(),
            pa)),
        self.CertiCoq_Benchmarks_lib_vs_normalize_atoms(
          pa2))
    },
    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, pa, pa2, sa) => {
      self.alloc(
        CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(
          PhantomData,
          self.CertiCoq_Benchmarks_lib_vs_normalize_atoms(
            self.Coq_Lists_List_filter(
              self.CertiCoq_Benchmarks_lib_vs_nonreflex_atom__curried(),
              pa)),
          self.CertiCoq_Benchmarks_lib_vs_normalize_atoms(
            pa2),
          sa))
    },
    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, pa, sa, pa2) => {
      self.alloc(
        CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(
          PhantomData,
          self.CertiCoq_Benchmarks_lib_vs_normalize_atoms(
            self.Coq_Lists_List_filter(
              self.CertiCoq_Benchmarks_lib_vs_nonreflex_atom__curried(),
              pa)),
          sa,
          self.CertiCoq_Benchmarks_lib_vs_normalize_atoms(
            pa2)))
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_order_eqv_clause__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_clause<'a> {
  self.closure(move |c| {
    self.CertiCoq_Benchmarks_lib_vs_order_eqv_clause(
      c)
  })
}

fn CertiCoq_Benchmarks_lib_vs_mk_pureR(&'a self, al: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pn_atom<'a>>) -> __pair<&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>> {
  match al {
    &Coq_Init_Datatypes_list::nil(_) => {
      __mk_pair(
        self.alloc(
          Coq_Init_Datatypes_list::nil(
            PhantomData)),
        self.alloc(
          Coq_Init_Datatypes_list::nil(
            PhantomData)))
    },
    &Coq_Init_Datatypes_list::cons(_, p, l) => {
      match p {
        &CertiCoq_Benchmarks_lib_vs_pn_atom::Equ(_, x, y) => {
          __pair_elim!(
            n, p2, {
              __mk_pair(
                self.alloc(
                  Coq_Init_Datatypes_list::cons(
                    PhantomData,
                    self.CertiCoq_Benchmarks_lib_vs_order_eqv_pure_atom(
                      self.alloc(
                        CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                          PhantomData,
                          x,
                          y))),
                    n)),
                p2)
            },
            self.CertiCoq_Benchmarks_lib_vs_mk_pureR(
              l))
        },
        &CertiCoq_Benchmarks_lib_vs_pn_atom::Nequ(_, x, y) => {
          __pair_elim!(
            n, p2, {
              __mk_pair(
                n,
                self.alloc(
                  Coq_Init_Datatypes_list::cons(
                    PhantomData,
                    self.CertiCoq_Benchmarks_lib_vs_order_eqv_pure_atom(
                      self.alloc(
                        CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                          PhantomData,
                          x,
                          y))),
                    p2)))
            },
            self.CertiCoq_Benchmarks_lib_vs_mk_pureR(
              l))
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_mk_pureR__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pn_atom<'a>>) -> __pair<&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>> {
  self.closure(move |al| {
    self.CertiCoq_Benchmarks_lib_vs_mk_pureR(
      al)
  })
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

fn CertiCoq_Benchmarks_lib_vs_mk_pureL(&'a self, a: &'a CertiCoq_Benchmarks_lib_vs_pn_atom<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_clause<'a> {
  match a {
    &CertiCoq_Benchmarks_lib_vs_pn_atom::Equ(_, x, y) => {
      self.CertiCoq_Benchmarks_lib_vs_mkPureClause(
        self.alloc(
          Coq_Init_Datatypes_list::nil(
            PhantomData)),
        self.alloc(
          Coq_Init_Datatypes_list::cons(
            PhantomData,
            self.CertiCoq_Benchmarks_lib_vs_order_eqv_pure_atom(
              self.alloc(
                CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                  PhantomData,
                  x,
                  y))),
            self.alloc(
              Coq_Init_Datatypes_list::nil(
                PhantomData)))))
    },
    &CertiCoq_Benchmarks_lib_vs_pn_atom::Nequ(_, x, y) => {
      self.CertiCoq_Benchmarks_lib_vs_mkPureClause(
        self.alloc(
          Coq_Init_Datatypes_list::cons(
            PhantomData,
            self.CertiCoq_Benchmarks_lib_vs_order_eqv_pure_atom(
              self.alloc(
                CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                  PhantomData,
                  x,
                  y))),
            self.alloc(
              Coq_Init_Datatypes_list::nil(
                PhantomData)))),
        self.alloc(
          Coq_Init_Datatypes_list::nil(
            PhantomData)))
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_mk_pureL__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_pn_atom<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_clause<'a> {
  self.closure(move |a| {
    self.CertiCoq_Benchmarks_lib_vs_mk_pureL(
      a)
  })
}

fn CertiCoq_Benchmarks_lib_vs_cnf(&'a self, en: &'a CertiCoq_Benchmarks_lib_vs_entailment<'a>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  match en {
    &CertiCoq_Benchmarks_lib_vs_entailment::Entailment(_, a, a0) => {
      match a {
        &CertiCoq_Benchmarks_lib_vs_assertion::Assertion(_, pureL, spaceL) => {
          match a0 {
            &CertiCoq_Benchmarks_lib_vs_assertion::Assertion(_, pureR, spaceR) => {
              __pair_elim!(
                n, p, {
                  self.Coq_Init_Datatypes_app(
                    self.Coq_Lists_List_map(
                      self.CertiCoq_Benchmarks_lib_vs_mk_pureL__curried(),
                      pureL),
                    self.Coq_Init_Datatypes_app(
                      self.alloc(
                        Coq_Init_Datatypes_list::cons(
                          PhantomData,
                          self.alloc(
                            CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(
                              PhantomData,
                              self.alloc(
                                Coq_Init_Datatypes_list::nil(
                                  PhantomData)),
                              self.alloc(
                                Coq_Init_Datatypes_list::nil(
                                  PhantomData)),
                              spaceL)),
                          self.alloc(
                            Coq_Init_Datatypes_list::nil(
                              PhantomData)))),
                      match spaceL {
                        &Coq_Init_Datatypes_list::nil(_) => {
                          match spaceR {
                            &Coq_Init_Datatypes_list::nil(_) => {
                              self.alloc(
                                Coq_Init_Datatypes_list::cons(
                                  PhantomData,
                                  self.CertiCoq_Benchmarks_lib_vs_mkPureClause(
                                    n,
                                    p),
                                  self.alloc(
                                    Coq_Init_Datatypes_list::nil(
                                      PhantomData))))
                            },
                            &Coq_Init_Datatypes_list::cons(_, s, l) => {
                              self.alloc(
                                Coq_Init_Datatypes_list::cons(
                                  PhantomData,
                                  self.alloc(
                                    CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(
                                      PhantomData,
                                      n,
                                      spaceR,
                                      p)),
                                  self.alloc(
                                    Coq_Init_Datatypes_list::nil(
                                      PhantomData))))
                            },
                          }
                        },
                        &Coq_Init_Datatypes_list::cons(_, s, l) => {
                          self.alloc(
                            Coq_Init_Datatypes_list::cons(
                              PhantomData,
                              self.alloc(
                                CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(
                                  PhantomData,
                                  n,
                                  spaceR,
                                  p)),
                              self.alloc(
                                Coq_Init_Datatypes_list::nil(
                                  PhantomData))))
                        },
                      }))
                },
                self.CertiCoq_Benchmarks_lib_vs_mk_pureR(
                  pureR))
            },
          }
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_cnf__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_entailment<'a>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.closure(move |en| {
    self.CertiCoq_Benchmarks_lib_vs_cnf(
      en)
  })
}

fn Coq_PArith_BinPosDef_Pos_eqb(&'a self, a: u64, b: u64) -> bool { a == b }
fn Coq_PArith_BinPosDef_Pos_eqb__curried(&'a self) -> &'a dyn Fn(u64) -> &'a dyn Fn(u64) -> bool {
  self.closure(move |p| {
    self.closure(move |q| {
      self.Coq_PArith_BinPosDef_Pos_eqb(
        p,
        q)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_elements_aux(&'a self, acc: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>, s: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  match s {
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
      acc
    },
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t, l, x, r) => {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_elements_aux(
        self.alloc(
          Coq_Init_Datatypes_list::cons(
            PhantomData,
            x,
            self.CertiCoq_Benchmarks_lib_vs_M_Raw_elements_aux(
              acc,
              r))),
        l)
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_elements_aux__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.closure(move |acc| {
    self.closure(move |s| {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_elements_aux(
        acc,
        s)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_elements(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.CertiCoq_Benchmarks_lib_vs_M_Raw_elements_aux__curried()(
    self.alloc(
      Coq_Init_Datatypes_list::nil(
        PhantomData)))
}

fn CertiCoq_Benchmarks_lib_vs_M_elements(&'a self, s: CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_elt<'a>> {
  self.CertiCoq_Benchmarks_lib_vs_M_Raw_elements()(
    self.CertiCoq_Benchmarks_lib_vs_M_this(
      s))
}
fn CertiCoq_Benchmarks_lib_vs_M_elements__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_elt<'a>> {
  self.closure(move |s| {
    self.CertiCoq_Benchmarks_lib_vs_M_elements(
      s)
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

fn Coq_Lists_List_existsb<A: Copy>(&'a self, f: &'a dyn Fn(A) -> bool, l: &'a Coq_Init_Datatypes_list<'a, A>) -> bool {
  match l {
    &Coq_Init_Datatypes_list::nil(_) => {
      false
    },
    &Coq_Init_Datatypes_list::cons(_, a, l2) => {
      __orb!(
        hint_app(f)(a),
        self.Coq_Lists_List_existsb(
          f,
          l2))
    },
  }
}
fn Coq_Lists_List_existsb__curried<A: Copy>(&'a self) -> &'a dyn Fn(&'a dyn Fn(A) -> bool) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> bool {
  self.closure(move |f| {
    self.closure(move |l| {
      self.Coq_Lists_List_existsb(
        f,
        l)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_is_empty_clause(&'a self, cl: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> bool {
  match cl {
    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma, delta, priority) => {
      match gamma {
        &Coq_Init_Datatypes_list::nil(_) => {
          match delta {
            &Coq_Init_Datatypes_list::nil(_) => {
              true
            },
            &Coq_Init_Datatypes_list::cons(_, p, l) => {
              false
            },
          }
        },
        &Coq_Init_Datatypes_list::cons(_, p, l) => {
          false
        },
      }
    },
    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
      false
    },
    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
      false
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_Superposition_is_empty_clause__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> bool {
  self.closure(move |cl| {
    self.CertiCoq_Benchmarks_lib_vs_Superposition_is_empty_clause(
      cl)
  })
}

fn CertiCoq_Benchmarks_lib_vs_remove_trivial_atoms(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>> {
  self.Coq_Lists_List_filter__curried()(
    self.closure(move |a| {
      match a {
        &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, e1, e2) => {
          match self.CertiCoq_Benchmarks_lib_vs_expr_cmp(
                  e1,
                  e2) {
            std::cmp::Ordering::Equal => {
              false
            },
            std::cmp::Ordering::Less => {
              true
            },
            std::cmp::Ordering::Greater => {
              true
            },
          }
        },
      }
    }))
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_delete_resolved(&'a self, c: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_clause<'a> {
  match c {
    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, neg, pos, priority) => {
      self.CertiCoq_Benchmarks_lib_vs_mkPureClause(
        self.CertiCoq_Benchmarks_lib_vs_rsort_uniq(
          (),
          self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
          self.CertiCoq_Benchmarks_lib_vs_remove_trivial_atoms()(
            neg)),
        self.CertiCoq_Benchmarks_lib_vs_rsort_uniq(
          (),
          self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
          pos))
    },
    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
      c
    },
    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
      c
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_Superposition_delete_resolved__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_clause<'a> {
  self.closure(move |c| {
    self.CertiCoq_Benchmarks_lib_vs_Superposition_delete_resolved(
      c)
  })
}

fn Coq_Lists_List_partition<A: Copy>(&'a self, f: &'a dyn Fn(A) -> bool, l: &'a Coq_Init_Datatypes_list<'a, A>) -> __pair<&'a Coq_Init_Datatypes_list<'a, A>, &'a Coq_Init_Datatypes_list<'a, A>> {
  match l {
    &Coq_Init_Datatypes_list::nil(_) => {
      __mk_pair(
        self.alloc(
          Coq_Init_Datatypes_list::nil(
            PhantomData)),
        self.alloc(
          Coq_Init_Datatypes_list::nil(
            PhantomData)))
    },
    &Coq_Init_Datatypes_list::cons(_, x, tl) => {
      __pair_elim!(
        d, g, {
          match hint_app(f)(x) {
            true => {
              __mk_pair(
                self.alloc(
                  Coq_Init_Datatypes_list::cons(
                    PhantomData,
                    x,
                    d)),
                g)
            },
            false => {
              __mk_pair(
                d,
                self.alloc(
                  Coq_Init_Datatypes_list::cons(
                    PhantomData,
                    x,
                    g)))
            },
          }
        },
        self.Coq_Lists_List_partition(
          f,
          tl))
    },
  }
}
fn Coq_Lists_List_partition__curried<A: Copy>(&'a self) -> &'a dyn Fn(&'a dyn Fn(A) -> bool) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> __pair<&'a Coq_Init_Datatypes_list<'a, A>, &'a Coq_Init_Datatypes_list<'a, A>> {
  self.closure(move |f| {
    self.closure(move |l| {
      self.Coq_Lists_List_partition(
        f,
        l)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_is_unit_clause(&'a self, cl: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> bool {
  match cl {
    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma, delta, priority) => {
      match gamma {
        &Coq_Init_Datatypes_list::nil(_) => {
          match delta {
            &Coq_Init_Datatypes_list::nil(_) => {
              false
            },
            &Coq_Init_Datatypes_list::cons(_, a, l) => {
              match l {
                &Coq_Init_Datatypes_list::nil(_) => {
                  true
                },
                &Coq_Init_Datatypes_list::cons(_, p, l0) => {
                  false
                },
              }
            },
          }
        },
        &Coq_Init_Datatypes_list::cons(_, p, l) => {
          false
        },
      }
    },
    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
      false
    },
    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
      false
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_Superposition_is_unit_clause__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> bool {
  self.closure(move |cl| {
    self.CertiCoq_Benchmarks_lib_vs_Superposition_is_unit_clause(
      cl)
  })
}

fn Coq_Lists_List_fold_right<A: Copy, B: Copy>(&'a self, f: &'a dyn Fn(B) -> &'a dyn Fn(A) -> A, a0: A, l: &'a Coq_Init_Datatypes_list<'a, B>) -> A {
  match l {
    &Coq_Init_Datatypes_list::nil(_) => {
      a0
    },
    &Coq_Init_Datatypes_list::cons(_, b, t) => {
      hint_app(hint_app(f)(b))(self.Coq_Lists_List_fold_right(
                                 f,
                                 a0,
                                 t))
    },
  }
}
fn Coq_Lists_List_fold_right__curried<A: Copy, B: Copy>(&'a self) -> &'a dyn Fn(&'a dyn Fn(B) -> &'a dyn Fn(A) -> A) -> &'a dyn Fn(A) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, B>) -> A {
  self.closure(move |f| {
    self.closure(move |a0| {
      self.closure(move |l| {
        self.Coq_Lists_List_fold_right(
          f,
          a0,
          l)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_compose<A: Copy, B: Copy, C: Copy>(&'a self, g: &'a dyn Fn(B) -> C, f: &'a dyn Fn(A) -> B, a: A) -> C {
  hint_app(g)(hint_app(f)(a))
}
fn CertiCoq_Benchmarks_lib_vs_compose__curried<A: Copy, B: Copy, C: Copy>(&'a self) -> &'a dyn Fn(&'a dyn Fn(B) -> C) -> &'a dyn Fn(&'a dyn Fn(A) -> B) -> &'a dyn Fn(A) -> C {
  self.closure(move |g| {
    self.closure(move |f| {
      self.closure(move |a| {
        self.CertiCoq_Benchmarks_lib_vs_compose(
          g,
          f,
          a)
      })
    })
  })
}

fn Coq_Numbers_BinNums_positive_rect<P: Copy>(&'a self, f: &'a dyn Fn(u64) -> &'a dyn Fn(P) -> P, f0: &'a dyn Fn(u64) -> &'a dyn Fn(P) -> P, f1: P, p: u64) -> P {
  __pos_elim!(
    p2, {
      hint_app(hint_app(f)(p2))(self.Coq_Numbers_BinNums_positive_rect(
                                  f,
                                  f0,
                                  f1,
                                  p2))
    },
    p2, {
      hint_app(hint_app(f0)(p2))(self.Coq_Numbers_BinNums_positive_rect(
                                   f,
                                   f0,
                                   f1,
                                   p2))
    },
    {
      f1
    },
    p)
}
fn Coq_Numbers_BinNums_positive_rect__curried<P: Copy>(&'a self) -> &'a dyn Fn(&'a dyn Fn(u64) -> &'a dyn Fn(P) -> P) -> &'a dyn Fn(&'a dyn Fn(u64) -> &'a dyn Fn(P) -> P) -> &'a dyn Fn(P) -> &'a dyn Fn(u64) -> P {
  self.closure(move |f| {
    self.closure(move |f0| {
      self.closure(move |f1| {
        self.closure(move |p| {
          self.Coq_Numbers_BinNums_positive_rect(
            f,
            f0,
            f1,
            p)
        })
      })
    })
  })
}

fn Coq_Numbers_BinNums_positive_rec<P: Copy>(&'a self) -> &'a dyn Fn(&'a dyn Fn(u64) -> &'a dyn Fn(P) -> P) -> &'a dyn Fn(&'a dyn Fn(u64) -> &'a dyn Fn(P) -> P) -> &'a dyn Fn(P) -> &'a dyn Fn(u64) -> P {
  self.Coq_Numbers_BinNums_positive_rect__curried()
}

fn Coq_Init_Specif_sumbool_rect<P: Copy>(&'a self, f: &'a dyn Fn(()) -> P, f0: &'a dyn Fn(()) -> P, s: &'a Coq_Init_Specif_sumbool<'a>) -> P {
  match s {
    &Coq_Init_Specif_sumbool::left(_) => {
      hint_app(f)(())
    },
    &Coq_Init_Specif_sumbool::right(_) => {
      hint_app(f0)(())
    },
  }
}
fn Coq_Init_Specif_sumbool_rect__curried<P: Copy>(&'a self) -> &'a dyn Fn(&'a dyn Fn(()) -> P) -> &'a dyn Fn(&'a dyn Fn(()) -> P) -> &'a dyn Fn(&'a Coq_Init_Specif_sumbool<'a>) -> P {
  self.closure(move |f| {
    self.closure(move |f0| {
      self.closure(move |s| {
        self.Coq_Init_Specif_sumbool_rect(
          f,
          f0,
          s)
      })
    })
  })
}

fn Coq_Init_Specif_sumbool_rec<P: Copy>(&'a self) -> &'a dyn Fn(&'a dyn Fn(()) -> P) -> &'a dyn Fn(&'a dyn Fn(()) -> P) -> &'a dyn Fn(&'a Coq_Init_Specif_sumbool<'a>) -> P {
  self.Coq_Init_Specif_sumbool_rect__curried()
}

fn Coq_PArith_BinPos_Pos_eq_dec(&'a self, x: u64, y: u64) -> &'a Coq_Init_Specif_sumbool<'a> {
  self.Coq_Numbers_BinNums_positive_rec()(
    self.closure(move |p| {
      self.closure(move |x2| {
        self.closure(move |x0| {
          __pos_elim!(
            p2, {
              hint_app(self.closure(move |p3| {
                         self.Coq_Init_Specif_sumbool_rec()(
                           self.closure(move |a| {
                             self.alloc(
                               Coq_Init_Specif_sumbool::left(
                                 PhantomData))
                           }))(
                           self.closure(move |diseq| {
                             self.alloc(
                               Coq_Init_Specif_sumbool::right(
                                 PhantomData))
                           }))(
                           hint_app(x2)(p3))
                       }))(p2)
            },
            p2, {
              hint_app(self.closure(move |p3| {
                         self.alloc(
                           Coq_Init_Specif_sumbool::right(
                             PhantomData))
                       }))(p2)
            },
            {
              self.alloc(
                Coq_Init_Specif_sumbool::right(
                  PhantomData))
            },
            x0)
        })
      })
    }))(
    self.closure(move |p| {
      self.closure(move |x2| {
        self.closure(move |x0| {
          __pos_elim!(
            p2, {
              hint_app(self.closure(move |p3| {
                         self.alloc(
                           Coq_Init_Specif_sumbool::right(
                             PhantomData))
                       }))(p2)
            },
            p2, {
              hint_app(self.closure(move |p3| {
                         self.Coq_Init_Specif_sumbool_rec()(
                           self.closure(move |a| {
                             self.alloc(
                               Coq_Init_Specif_sumbool::left(
                                 PhantomData))
                           }))(
                           self.closure(move |diseq| {
                             self.alloc(
                               Coq_Init_Specif_sumbool::right(
                                 PhantomData))
                           }))(
                           hint_app(x2)(p3))
                       }))(p2)
            },
            {
              self.alloc(
                Coq_Init_Specif_sumbool::right(
                  PhantomData))
            },
            x0)
        })
      })
    }))(
    self.closure(move |x0| {
      __pos_elim!(
        p, {
          hint_app(self.closure(move |p2| {
                     self.alloc(
                       Coq_Init_Specif_sumbool::right(
                         PhantomData))
                   }))(p)
        },
        p, {
          hint_app(self.closure(move |p2| {
                     self.alloc(
                       Coq_Init_Specif_sumbool::right(
                         PhantomData))
                   }))(p)
        },
        {
          self.alloc(
            Coq_Init_Specif_sumbool::left(
              PhantomData))
        },
        x0)
    }))(
    x)(
    y)
}
fn Coq_PArith_BinPos_Pos_eq_dec__curried(&'a self) -> &'a dyn Fn(u64) -> &'a dyn Fn(u64) -> &'a Coq_Init_Specif_sumbool<'a> {
  self.closure(move |x| {
    self.closure(move |y| {
      self.Coq_PArith_BinPos_Pos_eq_dec(
        x,
        y)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_subst_expr(&'a self, i: CertiCoq_Benchmarks_lib_vs_var<'a>, t: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, t2: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_expr<'a> {
  match t2 {
    &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
      self.alloc(
        CertiCoq_Benchmarks_lib_vs_expr::Nil(
          PhantomData))
    },
    &CertiCoq_Benchmarks_lib_vs_expr::Var(_, j) => {
      match self.Coq_PArith_BinPos_Pos_eq_dec(
              i,
              j) {
        &Coq_Init_Specif_sumbool::left(_) => {
          t
        },
        &Coq_Init_Specif_sumbool::right(_) => {
          t2
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_subst_expr__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_var<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_expr<'a> {
  self.closure(move |i| {
    self.closure(move |t| {
      self.closure(move |t2| {
        self.CertiCoq_Benchmarks_lib_vs_subst_expr(
          i,
          t,
          t2)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_subst_pure(&'a self, i: CertiCoq_Benchmarks_lib_vs_var<'a>, t: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, a: &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a> {
  match a {
    &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, t1, t2) => {
      self.alloc(
        CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
          PhantomData,
          self.CertiCoq_Benchmarks_lib_vs_subst_expr(
            i,
            t,
            t1),
          self.CertiCoq_Benchmarks_lib_vs_subst_expr(
            i,
            t,
            t2)))
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_subst_pure__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_var<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a> {
  self.closure(move |i| {
    self.closure(move |t| {
      self.closure(move |a| {
        self.CertiCoq_Benchmarks_lib_vs_subst_pure(
          i,
          t,
          a)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_subst_pures(&'a self, i: CertiCoq_Benchmarks_lib_vs_var<'a>, t: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, pa: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>> {
  self.Coq_Lists_List_map(
    self.CertiCoq_Benchmarks_lib_vs_subst_pure__curried()(
      i)(
      t),
    pa)
}
fn CertiCoq_Benchmarks_lib_vs_subst_pures__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_var<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>> {
  self.closure(move |i| {
    self.closure(move |t| {
      self.closure(move |pa| {
        self.CertiCoq_Benchmarks_lib_vs_subst_pures(
          i,
          t,
          pa)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_subst_pures_delete(&'a self, i: CertiCoq_Benchmarks_lib_vs_var<'a>, e: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>> {
  self.CertiCoq_Benchmarks_lib_vs_compose__curried()(
    self.CertiCoq_Benchmarks_lib_vs_remove_trivial_atoms())(
    self.CertiCoq_Benchmarks_lib_vs_subst_pures__curried()(
      i)(
      e))
}
fn CertiCoq_Benchmarks_lib_vs_subst_pures_delete__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_var<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>> {
  self.closure(move |i| {
    self.closure(move |e| {
      self.CertiCoq_Benchmarks_lib_vs_subst_pures_delete(
        i,
        e)
    })
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

fn Coq_Init_Datatypes_snd<A: Copy, B: Copy>(&'a self, p: __pair<A, B>) -> B {
  __pair_elim!(
    y, x, {
      x
    },
    p)
}
fn Coq_Init_Datatypes_snd__curried<A: Copy, B: Copy>(&'a self) -> &'a dyn Fn(__pair<A, B>) -> B {
  self.closure(move |p| {
    self.Coq_Init_Datatypes_snd(
      p)
  })
}

fn Coq_Init_Datatypes_negb(&'a self, b: bool) -> bool {
  match b {
    true => {
      false
    },
    false => {
      true
    },
  }
}
fn Coq_Init_Datatypes_negb__curried(&'a self) -> &'a dyn Fn(bool) -> bool {
  self.closure(move |b| {
    self.Coq_Init_Datatypes_negb(
      b)
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

fn Coq_Lists_List_forallb<A: Copy>(&'a self, f: &'a dyn Fn(A) -> bool, l: &'a Coq_Init_Datatypes_list<'a, A>) -> bool {
  match l {
    &Coq_Init_Datatypes_list::nil(_) => {
      true
    },
    &Coq_Init_Datatypes_list::cons(_, a, l2) => {
      __andb!(
        hint_app(f)(a),
        self.Coq_Lists_List_forallb(
          f,
          l2))
    },
  }
}
fn Coq_Lists_List_forallb__curried<A: Copy>(&'a self) -> &'a dyn Fn(&'a dyn Fn(A) -> bool) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> bool {
  self.closure(move |f| {
    self.closure(move |l| {
      self.Coq_Lists_List_forallb(
        f,
        l)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_is_model_of(&'a self, R: CertiCoq_Benchmarks_lib_vs_Superposition_model<'a>, gamma: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>, delta: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> bool {
  match self.Coq_Lists_List_fold_right(
          self.closure(move |ve| {
            self.CertiCoq_Benchmarks_lib_vs_subst_pures_delete(
              self.Coq_Init_Datatypes_fst(
                ve),
              self.Coq_Init_Datatypes_snd(
                ve))
          }),
          self.CertiCoq_Benchmarks_lib_vs_remove_trivial_atoms()(
            gamma),
          R) {
    &Coq_Init_Datatypes_list::nil(_) => {
      self.Coq_Init_Datatypes_negb(
        self.Coq_Lists_List_forallb(
          self.CertiCoq_Benchmarks_lib_vs_nonreflex_atom__curried(),
          self.Coq_Lists_List_fold_right(
            self.closure(move |ve| {
              self.CertiCoq_Benchmarks_lib_vs_subst_pures__curried()(
                self.Coq_Init_Datatypes_fst(
                  ve))(
                self.Coq_Init_Datatypes_snd(
                  ve))
            }),
            delta,
            R)))
    },
    &Coq_Init_Datatypes_list::cons(_, p, l) => {
      true
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_Superposition_is_model_of__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_Superposition_model<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> bool {
  self.closure(move |R| {
    self.closure(move |gamma| {
      self.closure(move |delta| {
        self.CertiCoq_Benchmarks_lib_vs_Superposition_is_model_of(
          R,
          gamma,
          delta)
      })
    })
  })
}

fn Coq_Lists_List_rev<A: Copy>(&'a self, l: &'a Coq_Init_Datatypes_list<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  match l {
    &Coq_Init_Datatypes_list::nil(_) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
    &Coq_Init_Datatypes_list::cons(_, x, l2) => {
      self.Coq_Init_Datatypes_app(
        self.Coq_Lists_List_rev(
          l2),
        self.alloc(
          Coq_Init_Datatypes_list::cons(
            PhantomData,
            x,
            self.alloc(
              Coq_Init_Datatypes_list::nil(
                PhantomData)))))
    },
  }
}
fn Coq_Lists_List_rev__curried<A: Copy>(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  self.closure(move |l| {
    self.Coq_Lists_List_rev(
      l)
  })
}

fn CertiCoq_Benchmarks_lib_vs_greater_than_expr(&'a self, i: CertiCoq_Benchmarks_lib_vs_var<'a>, e: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> bool {
  match e {
    &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
      true
    },
    &CertiCoq_Benchmarks_lib_vs_expr::Var(_, j) => {
      match self.Coq_PArith_BinPosDef_Pos_compare()(
              i)(
              j) {
        std::cmp::Ordering::Equal => {
          false
        },
        std::cmp::Ordering::Less => {
          false
        },
        std::cmp::Ordering::Greater => {
          true
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_greater_than_expr__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_var<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> bool {
  self.closure(move |i| {
    self.closure(move |e| {
      self.CertiCoq_Benchmarks_lib_vs_greater_than_expr(
        i,
        e)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_greater_than_all(&'a self, i: CertiCoq_Benchmarks_lib_vs_var<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> bool {
  self.Coq_Lists_List_forallb__curried()(
    self.closure(move |a| {
      match a {
        &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, x, y) => {
          __andb!(
            self.CertiCoq_Benchmarks_lib_vs_greater_than_expr(
              i,
              x),
            self.CertiCoq_Benchmarks_lib_vs_greater_than_expr(
              i,
              y))
        },
      }
    }))
}
fn CertiCoq_Benchmarks_lib_vs_greater_than_all__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_var<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> bool {
  self.closure(move |i| {
    self.CertiCoq_Benchmarks_lib_vs_greater_than_all(
      i)
  })
}

fn CertiCoq_Benchmarks_lib_vs_expr_lt(&'a self, a: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, b: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> bool {
  match self.CertiCoq_Benchmarks_lib_vs_expr_cmp(
          a,
          b) {
    std::cmp::Ordering::Equal => {
      false
    },
    std::cmp::Ordering::Less => {
      true
    },
    std::cmp::Ordering::Greater => {
      false
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_expr_lt__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> bool {
  self.closure(move |a| {
    self.closure(move |b| {
      self.CertiCoq_Benchmarks_lib_vs_expr_lt(
        a,
        b)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_expr_geq(&'a self, a: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, b: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> bool {
  match self.CertiCoq_Benchmarks_lib_vs_expr_cmp(
          a,
          b) {
    std::cmp::Ordering::Equal => {
      true
    },
    std::cmp::Ordering::Less => {
      false
    },
    std::cmp::Ordering::Greater => {
      true
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_expr_geq__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> bool {
  self.closure(move |a| {
    self.closure(move |b| {
      self.CertiCoq_Benchmarks_lib_vs_expr_geq(
        a,
        b)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_greater_than_atom(&'a self, s: &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>, u: &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> bool {
  match s {
    &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, s2, t) => {
      match u {
        &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, u2, v) => {
          __orb!(
            __orb!(
              __andb!(
                self.CertiCoq_Benchmarks_lib_vs_expr_lt(
                  u2,
                  s2),
                __orb!(
                  self.CertiCoq_Benchmarks_lib_vs_expr_geq(
                    s2,
                    v),
                  self.CertiCoq_Benchmarks_lib_vs_expr_geq(
                    t,
                    v))),
              __andb!(
                self.CertiCoq_Benchmarks_lib_vs_expr_lt(
                  v,
                  s2),
                __orb!(
                  self.CertiCoq_Benchmarks_lib_vs_expr_geq(
                    s2,
                    u2),
                  self.CertiCoq_Benchmarks_lib_vs_expr_geq(
                    t,
                    u2)))),
            __orb!(
              __andb!(
                self.CertiCoq_Benchmarks_lib_vs_expr_lt(
                  u2,
                  t),
                __orb!(
                  self.CertiCoq_Benchmarks_lib_vs_expr_geq(
                    s2,
                    v),
                  self.CertiCoq_Benchmarks_lib_vs_expr_geq(
                    t,
                    v))),
              __andb!(
                self.CertiCoq_Benchmarks_lib_vs_expr_lt(
                  v,
                  t),
                __orb!(
                  self.CertiCoq_Benchmarks_lib_vs_expr_geq(
                    s2,
                    u2),
                  self.CertiCoq_Benchmarks_lib_vs_expr_geq(
                    t,
                    u2)))))
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_greater_than_atom__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> bool {
  self.closure(move |s| {
    self.closure(move |u| {
      self.CertiCoq_Benchmarks_lib_vs_greater_than_atom(
        s,
        u)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_greater_than_atoms(&'a self, s: &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>, delta: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> bool {
  self.Coq_Lists_List_forallb(
    self.closure(move |u| {
      self.CertiCoq_Benchmarks_lib_vs_greater_than_atom(
        s,
        u)
    }),
    delta)
}
fn CertiCoq_Benchmarks_lib_vs_greater_than_atoms__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> bool {
  self.closure(move |s| {
    self.closure(move |delta| {
      self.CertiCoq_Benchmarks_lib_vs_greater_than_atoms(
        s,
        delta)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_reduces(&'a self, R: CertiCoq_Benchmarks_lib_vs_Superposition_model<'a>, v: CertiCoq_Benchmarks_lib_vs_var<'a>) -> bool {
  self.Coq_Lists_List_existsb(
    self.closure(move |ve| {
      match self.Coq_PArith_BinPos_Pos_eq_dec(
              v,
              self.Coq_Init_Datatypes_fst(
                ve)) {
        &Coq_Init_Specif_sumbool::left(_) => {
          true
        },
        &Coq_Init_Specif_sumbool::right(_) => {
          false
        },
      }
    }),
    R)
}
fn CertiCoq_Benchmarks_lib_vs_Superposition_reduces__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_Superposition_model<'a>) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_var<'a>) -> bool {
  self.closure(move |R| {
    self.closure(move |v| {
      self.CertiCoq_Benchmarks_lib_vs_Superposition_reduces(
        R,
        v)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_expr_eq(&'a self, a: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, b: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> bool {
  match self.CertiCoq_Benchmarks_lib_vs_expr_cmp(
          a,
          b) {
    std::cmp::Ordering::Equal => {
      true
    },
    std::cmp::Ordering::Less => {
      false
    },
    std::cmp::Ordering::Greater => {
      false
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_expr_eq__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> bool {
  self.closure(move |a| {
    self.closure(move |b| {
      self.CertiCoq_Benchmarks_lib_vs_expr_eq(
        a,
        b)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_norm_pure_atom(&'a self, a: &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a> {
  match a {
    &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, i, j) => {
      match self.CertiCoq_Benchmarks_lib_vs_expr_lt(
              i,
              j) {
        true => {
          self.alloc(
            CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
              PhantomData,
              j,
              i))
        },
        false => {
          self.alloc(
            CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
              PhantomData,
              i,
              j))
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_norm_pure_atom__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a> {
  self.closure(move |a| {
    self.CertiCoq_Benchmarks_lib_vs_norm_pure_atom(
      a)
  })
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_by(&'a self, s: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, t: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, atm: &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a> {
  match atm {
    &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, u, v) => {
      match self.CertiCoq_Benchmarks_lib_vs_expr_eq(
              s,
              u) {
        true => {
          match self.CertiCoq_Benchmarks_lib_vs_expr_eq(
                  s,
                  v) {
            true => {
              self.CertiCoq_Benchmarks_lib_vs_norm_pure_atom(
                self.alloc(
                  CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                    PhantomData,
                    t,
                    t)))
            },
            false => {
              self.CertiCoq_Benchmarks_lib_vs_norm_pure_atom(
                self.alloc(
                  CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                    PhantomData,
                    t,
                    v)))
            },
          }
        },
        false => {
          match self.CertiCoq_Benchmarks_lib_vs_expr_eq(
                  s,
                  v) {
            true => {
              self.CertiCoq_Benchmarks_lib_vs_norm_pure_atom(
                self.alloc(
                  CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                    PhantomData,
                    u,
                    t)))
            },
            false => {
              atm
            },
          }
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_by__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a> {
  self.closure(move |s| {
    self.closure(move |t| {
      self.closure(move |atm| {
        self.CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_by(
          s,
          t,
          atm)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_clause_generate(&'a self, R: CertiCoq_Benchmarks_lib_vs_Superposition_model<'a>, cl: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a Coq_Init_Datatypes_sum<'a, __pair<__pair<CertiCoq_Benchmarks_lib_vs_var<'a>, &'a CertiCoq_Benchmarks_lib_vs_expr<'a>>, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>, &'a CertiCoq_Benchmarks_lib_vs_ce_type<'a>> {
  match cl {
    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma, delta0, priority) => {
      match delta0 {
        &Coq_Init_Datatypes_list::nil(_) => {
          self.alloc(
            Coq_Init_Datatypes_sum::inr(
              PhantomData,
              self.alloc(
                CertiCoq_Benchmarks_lib_vs_ce_type::CexpL(
                  PhantomData))))
        },
        &Coq_Init_Datatypes_list::cons(_, p, delta) => {
          match p {
            &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, l, r) => {
              match l {
                &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
                  self.alloc(
                    Coq_Init_Datatypes_sum::inr(
                      PhantomData,
                      self.alloc(
                        CertiCoq_Benchmarks_lib_vs_ce_type::CexpL(
                          PhantomData))))
                },
                &CertiCoq_Benchmarks_lib_vs_expr::Var(_, l2) => {
                  match __andb!(
                          __andb!(
                            self.CertiCoq_Benchmarks_lib_vs_greater_than_expr(
                              l2,
                              r),
                            self.CertiCoq_Benchmarks_lib_vs_greater_than_all(
                              l2)(
                              gamma)),
                          self.CertiCoq_Benchmarks_lib_vs_greater_than_atoms(
                            self.alloc(
                              CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                                PhantomData,
                                l,
                                r)),
                            delta)) {
                    true => {
                      match self.CertiCoq_Benchmarks_lib_vs_Superposition_reduces(
                              R,
                              l2) {
                        true => {
                          self.alloc(
                            Coq_Init_Datatypes_sum::inr(
                              PhantomData,
                              self.alloc(
                                CertiCoq_Benchmarks_lib_vs_ce_type::CexpR(
                                  PhantomData))))
                        },
                        false => {
                          match self.CertiCoq_Benchmarks_lib_vs_Superposition_is_model_of(
                                  self.Coq_Lists_List_rev(
                                    R),
                                  self.alloc(
                                    Coq_Init_Datatypes_list::nil(
                                      PhantomData)),
                                  self.Coq_Lists_List_map(
                                    self.CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_by__curried()(
                                      l)(
                                      r),
                                    delta)) {
                            true => {
                              self.alloc(
                                Coq_Init_Datatypes_sum::inr(
                                  PhantomData,
                                  self.alloc(
                                    CertiCoq_Benchmarks_lib_vs_ce_type::CexpEf(
                                      PhantomData))))
                            },
                            false => {
                              self.alloc(
                                Coq_Init_Datatypes_sum::inl(
                                  PhantomData,
                                  __mk_pair(
                                    __mk_pair(
                                      l2,
                                      r),
                                    cl)))
                            },
                          }
                        },
                      }
                    },
                    false => {
                      self.alloc(
                        Coq_Init_Datatypes_sum::inr(
                          PhantomData,
                          self.alloc(
                            CertiCoq_Benchmarks_lib_vs_ce_type::CexpL(
                              PhantomData))))
                    },
                  }
                },
              }
            },
          }
        },
      }
    },
    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
      self.alloc(
        Coq_Init_Datatypes_sum::inr(
          PhantomData,
          self.alloc(
            CertiCoq_Benchmarks_lib_vs_ce_type::CexpL(
              PhantomData))))
    },
    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
      self.alloc(
        Coq_Init_Datatypes_sum::inr(
          PhantomData,
          self.alloc(
            CertiCoq_Benchmarks_lib_vs_ce_type::CexpL(
              PhantomData))))
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_Superposition_clause_generate__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_Superposition_model<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a Coq_Init_Datatypes_sum<'a, __pair<__pair<CertiCoq_Benchmarks_lib_vs_var<'a>, &'a CertiCoq_Benchmarks_lib_vs_expr<'a>>, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>, &'a CertiCoq_Benchmarks_lib_vs_ce_type<'a>> {
  self.closure(move |R| {
    self.closure(move |cl| {
      self.CertiCoq_Benchmarks_lib_vs_Superposition_clause_generate(
        R,
        cl)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_ce_clause(&'a self, R: &'a Coq_Init_Datatypes_list<'a, __pair<CertiCoq_Benchmarks_lib_vs_var<'a>, &'a CertiCoq_Benchmarks_lib_vs_expr<'a>>>, cl: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, ct: &'a CertiCoq_Benchmarks_lib_vs_ce_type<'a>) -> __pair<__pair<&'a Coq_Init_Datatypes_list<'a, __pair<CertiCoq_Benchmarks_lib_vs_var<'a>, &'a CertiCoq_Benchmarks_lib_vs_expr<'a>>>, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>, &'a CertiCoq_Benchmarks_lib_vs_ce_type<'a>> {
  __mk_pair(
    __mk_pair(
      R,
      cl),
    ct)
}
fn CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_ce_clause__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, __pair<CertiCoq_Benchmarks_lib_vs_var<'a>, &'a CertiCoq_Benchmarks_lib_vs_expr<'a>>>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_ce_type<'a>) -> __pair<__pair<&'a Coq_Init_Datatypes_list<'a, __pair<CertiCoq_Benchmarks_lib_vs_var<'a>, &'a CertiCoq_Benchmarks_lib_vs_expr<'a>>>, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>, &'a CertiCoq_Benchmarks_lib_vs_ce_type<'a>> {
  self.closure(move |R| {
    self.closure(move |cl| {
      self.closure(move |ct| {
        self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_ce_clause(
          R,
          cl,
          ct)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_partial_mod(&'a self, R: CertiCoq_Benchmarks_lib_vs_Superposition_model<'a>, acc: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>, l: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_sum<'a, __pair<CertiCoq_Benchmarks_lib_vs_Superposition_model<'a>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>>, __pair<__pair<CertiCoq_Benchmarks_lib_vs_Superposition_model<'a>, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>, &'a CertiCoq_Benchmarks_lib_vs_ce_type<'a>>> {
  match l {
    &Coq_Init_Datatypes_list::nil(_) => {
      self.alloc(
        Coq_Init_Datatypes_sum::inl(
          PhantomData,
          __mk_pair(
            R,
            acc)))
    },
    &Coq_Init_Datatypes_list::cons(_, cl, l2) => {
      match cl {
        &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma, delta, priority) => {
          match self.CertiCoq_Benchmarks_lib_vs_Superposition_is_model_of(
                  self.Coq_Lists_List_rev(
                    R),
                  gamma,
                  delta) {
            true => {
              self.CertiCoq_Benchmarks_lib_vs_Superposition_partial_mod(
                R,
                acc,
                l2)
            },
            false => {
              match self.CertiCoq_Benchmarks_lib_vs_Superposition_clause_generate(
                      R,
                      cl) {
                &Coq_Init_Datatypes_sum::inl(_, p) => {
                  __pair_elim!(
                    cl2, p0, {
                      __pair_elim!(
                        exp, v, {
                          self.CertiCoq_Benchmarks_lib_vs_Superposition_partial_mod(
                            self.alloc(
                              Coq_Init_Datatypes_list::cons(
                                PhantomData,
                                __mk_pair(
                                  exp,
                                  v),
                                R)),
                            self.alloc(
                              Coq_Init_Datatypes_list::cons(
                                PhantomData,
                                p0,
                                acc)),
                            l2)
                        },
                        cl2)
                    },
                    p)
                },
                &Coq_Init_Datatypes_sum::inr(_, cty) => {
                  self.alloc(
                    Coq_Init_Datatypes_sum::inr(
                      PhantomData,
                      self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_ce_clause(
                        R,
                        cl,
                        cty)))
                },
              }
            },
          }
        },
        &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
          self.alloc(
            Coq_Init_Datatypes_sum::inl(
              PhantomData,
              __mk_pair(
                R,
                acc)))
        },
        &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
          self.alloc(
            Coq_Init_Datatypes_sum::inl(
              PhantomData,
              __mk_pair(
                R,
                acc)))
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_Superposition_partial_mod__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_Superposition_model<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_sum<'a, __pair<CertiCoq_Benchmarks_lib_vs_Superposition_model<'a>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>>, __pair<__pair<CertiCoq_Benchmarks_lib_vs_Superposition_model<'a>, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>, &'a CertiCoq_Benchmarks_lib_vs_ce_type<'a>>> {
  self.closure(move |R| {
    self.closure(move |acc| {
      self.closure(move |l| {
        self.CertiCoq_Benchmarks_lib_vs_Superposition_partial_mod(
          R,
          acc,
          l)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_pure_atom_eq(&'a self, a: &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>, b: &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> bool {
  match self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp(
          a,
          b) {
    std::cmp::Ordering::Equal => {
      true
    },
    std::cmp::Ordering::Less => {
      false
    },
    std::cmp::Ordering::Greater => {
      false
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_pure_atom_eq__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> bool {
  self.closure(move |a| {
    self.closure(move |b| {
      self.CertiCoq_Benchmarks_lib_vs_pure_atom_eq(
        a,
        b)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_not_taut(&'a self, c: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> bool {
  self.Coq_Init_Datatypes_negb(
    match c {
      &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, neg, pos, priority) => {
        __orb!(
          self.Coq_Lists_List_existsb(
            self.closure(move |a| {
              self.Coq_Lists_List_existsb(
                self.closure(move |b| {
                  self.CertiCoq_Benchmarks_lib_vs_pure_atom_eq(
                    a,
                    b)
                }),
                pos)
            }),
            neg),
          self.Coq_Lists_List_existsb(
            self.closure(move |a| {
              match a {
                &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, e1, e2) => {
                  self.CertiCoq_Benchmarks_lib_vs_expr_eq(
                    e1,
                    e2)
                },
              }
            }),
            pos))
      },
      &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
        false
      },
      &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
        false
      },
    })
}
fn CertiCoq_Benchmarks_lib_vs_Superposition_not_taut__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> bool {
  self.closure(move |c| {
    self.CertiCoq_Benchmarks_lib_vs_Superposition_not_taut(
      c)
  })
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_expr(&'a self, s: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, t: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, u: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_expr<'a> {
  match self.CertiCoq_Benchmarks_lib_vs_expr_eq(
          s,
          u) {
    true => {
      t
    },
    false => {
      u
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_expr__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_expr<'a> {
  self.closure(move |s| {
    self.closure(move |t| {
      self.closure(move |u| {
        self.CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_expr(
          s,
          t,
          u)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_in_space(&'a self, s: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, t: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, atm: &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a> {
  match atm {
    &CertiCoq_Benchmarks_lib_vs_space_atom::Next(_, u, v) => {
      self.alloc(
        CertiCoq_Benchmarks_lib_vs_space_atom::Next(
          PhantomData,
          self.CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_expr(
            s,
            t,
            u),
          self.CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_expr(
            s,
            t,
            v)))
    },
    &CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(_, u, v) => {
      self.alloc(
        CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
          PhantomData,
          self.CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_expr(
            s,
            t,
            u),
          self.CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_expr(
            s,
            t,
            v)))
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_in_space__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a> {
  self.closure(move |s| {
    self.closure(move |t| {
      self.closure(move |atm| {
        self.CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_in_space(
          s,
          t,
          atm)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_demodulate(&'a self, c: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, d: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_clause<'a> {
  match c {
    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma, delta, priority) => {
      match gamma {
        &Coq_Init_Datatypes_list::nil(_) => {
          match delta {
            &Coq_Init_Datatypes_list::nil(_) => {
              d
            },
            &Coq_Init_Datatypes_list::cons(_, p, l) => {
              match p {
                &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, s, t) => {
                  match l {
                    &Coq_Init_Datatypes_list::nil(_) => {
                      match d {
                        &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, neg, pos, priority0) => {
                          self.CertiCoq_Benchmarks_lib_vs_mkPureClause(
                            self.Coq_Lists_List_map(
                              self.CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_by__curried()(
                                s)(
                                t),
                              neg),
                            self.Coq_Lists_List_map(
                              self.CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_by__curried()(
                                s)(
                                t),
                              pos))
                        },
                        &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, neg, pos, space) => {
                          self.alloc(
                            CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(
                              PhantomData,
                              self.Coq_Lists_List_map(
                                self.CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_by__curried()(
                                  s)(
                                  t),
                                neg),
                              self.Coq_Lists_List_map(
                                self.CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_by__curried()(
                                  s)(
                                  t),
                                pos),
                              self.Coq_Lists_List_map(
                                self.CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_in_space__curried()(
                                  s)(
                                  t),
                                space)))
                        },
                        &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, neg, space, pos) => {
                          self.alloc(
                            CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(
                              PhantomData,
                              self.Coq_Lists_List_map(
                                self.CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_by__curried()(
                                  s)(
                                  t),
                                neg),
                              self.Coq_Lists_List_map(
                                self.CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_in_space__curried()(
                                  s)(
                                  t),
                                space),
                              self.Coq_Lists_List_map(
                                self.CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_by__curried()(
                                  s)(
                                  t),
                                pos)))
                        },
                      }
                    },
                    &Coq_Init_Datatypes_list::cons(_, p0, l0) => {
                      d
                    },
                  }
                },
              }
            },
          }
        },
        &Coq_Init_Datatypes_list::cons(_, p, l) => {
          d
        },
      }
    },
    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
      d
    },
    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
      d
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_Superposition_demodulate__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_clause<'a> {
  self.closure(move |c| {
    self.closure(move |d| {
      self.CertiCoq_Benchmarks_lib_vs_Superposition_demodulate(
        c,
        d)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_simplify(&'a self, l: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>, c: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_clause<'a> {
  self.CertiCoq_Benchmarks_lib_vs_Superposition_delete_resolved(
    self.Coq_Lists_List_fold_left(
      self.closure(move |d| {
        self.closure(move |c2| {
          self.CertiCoq_Benchmarks_lib_vs_Superposition_demodulate(
            c2,
            d)
        })
      }),
      l,
      c))
}
fn CertiCoq_Benchmarks_lib_vs_Superposition_simplify__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_clause<'a> {
  self.closure(move |l| {
    self.closure(move |c| {
      self.CertiCoq_Benchmarks_lib_vs_Superposition_simplify(
        l,
        c)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_eqs_list(&'a self, l: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  l
}
fn CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_eqs_list__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.closure(move |l| {
    self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_eqs_list(
      l)
  })
}

fn CertiCoq_Benchmarks_lib_vs_isEq(&'a self, cc: std::cmp::Ordering) -> bool {
  match cc {
    std::cmp::Ordering::Equal => {
      true
    },
    std::cmp::Ordering::Less => {
      false
    },
    std::cmp::Ordering::Greater => {
      false
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_isEq__curried(&'a self) -> &'a dyn Fn(std::cmp::Ordering) -> bool {
  self.closure(move |cc| {
    self.CertiCoq_Benchmarks_lib_vs_isEq(
      cc)
  })
}

fn CertiCoq_Benchmarks_lib_vs_lookC<A: Copy, B: Copy>(&'a self, A_cmp: &'a dyn Fn(A) -> &'a dyn Fn(A) -> std::cmp::Ordering, fAB: &'a dyn Fn(A) -> B, a: A, cs: &'a Coq_Init_Datatypes_list<'a, __pair<A, B>>) -> B {
  match cs {
    &Coq_Init_Datatypes_list::nil(_) => {
      hint_app(fAB)(a)
    },
    &Coq_Init_Datatypes_list::cons(_, p, cs2) => {
      __pair_elim!(
        b1, a1, {
          match self.CertiCoq_Benchmarks_lib_vs_isEq(
                  hint_app(hint_app(A_cmp)(a))(b1)) {
            true => {
              a1
            },
            false => {
              self.CertiCoq_Benchmarks_lib_vs_lookC(
                A_cmp,
                fAB,
                a,
                cs2)
            },
          }
        },
        p)
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_lookC__curried<A: Copy, B: Copy>(&'a self) -> &'a dyn Fn(&'a dyn Fn(A) -> &'a dyn Fn(A) -> std::cmp::Ordering) -> &'a dyn Fn(&'a dyn Fn(A) -> B) -> &'a dyn Fn(A) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, __pair<A, B>>) -> B {
  self.closure(move |A_cmp| {
    self.closure(move |fAB| {
      self.closure(move |a| {
        self.closure(move |cs| {
          self.CertiCoq_Benchmarks_lib_vs_lookC(
            A_cmp,
            fAB,
            a,
            cs)
        })
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_rewriteC<A: Copy, B: Copy>(&'a self, B_cmp: &'a dyn Fn(B) -> &'a dyn Fn(B) -> std::cmp::Ordering, b1: B, b2: B, cs: &'a Coq_Init_Datatypes_list<'a, __pair<A, B>>) -> &'a Coq_Init_Datatypes_list<'a, __pair<A, B>> {
  match cs {
    &Coq_Init_Datatypes_list::nil(_) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
    &Coq_Init_Datatypes_list::cons(_, p, cs2) => {
      __pair_elim!(
        b12, a1, {
          let new_cs =
            self.CertiCoq_Benchmarks_lib_vs_rewriteC(
              B_cmp,
              b1,
              b2,
              cs2);
          match self.CertiCoq_Benchmarks_lib_vs_isEq(
                  hint_app(hint_app(B_cmp)(b1))(a1)) {
            true => {
              self.alloc(
                Coq_Init_Datatypes_list::cons(
                  PhantomData,
                  __mk_pair(
                    b12,
                    b2),
                  new_cs))
            },
            false => {
              self.alloc(
                Coq_Init_Datatypes_list::cons(
                  PhantomData,
                  __mk_pair(
                    b12,
                    a1),
                  new_cs))
            },
          }
        },
        p)
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_rewriteC__curried<A: Copy, B: Copy>(&'a self) -> &'a dyn Fn(&'a dyn Fn(B) -> &'a dyn Fn(B) -> std::cmp::Ordering) -> &'a dyn Fn(B) -> &'a dyn Fn(B) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, __pair<A, B>>) -> &'a Coq_Init_Datatypes_list<'a, __pair<A, B>> {
  self.closure(move |B_cmp| {
    self.closure(move |b1| {
      self.closure(move |b2| {
        self.closure(move |cs| {
          self.CertiCoq_Benchmarks_lib_vs_rewriteC(
            B_cmp,
            b1,
            b2,
            cs)
        })
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_mergeC<A: Copy, B: Copy>(&'a self, A_cmp: &'a dyn Fn(A) -> &'a dyn Fn(A) -> std::cmp::Ordering, B_cmp: &'a dyn Fn(B) -> &'a dyn Fn(B) -> std::cmp::Ordering, fAB: &'a dyn Fn(A) -> B, a1: A, a2: A, cs: &'a Coq_Init_Datatypes_list<'a, __pair<A, B>>) -> &'a Coq_Init_Datatypes_list<'a, __pair<A, B>> {
  match self.CertiCoq_Benchmarks_lib_vs_isEq(
          hint_app(hint_app(B_cmp)(self.CertiCoq_Benchmarks_lib_vs_lookC(
                                     A_cmp,
                                     fAB,
                                     a1,
                                     cs)))(self.CertiCoq_Benchmarks_lib_vs_lookC(
                                             A_cmp,
                                             fAB,
                                             a2,
                                             cs))) {
    true => {
      cs
    },
    false => {
      self.alloc(
        Coq_Init_Datatypes_list::cons(
          PhantomData,
          __mk_pair(
            a1,
            self.CertiCoq_Benchmarks_lib_vs_lookC(
              A_cmp,
              fAB,
              a2,
              cs)),
          self.alloc(
            Coq_Init_Datatypes_list::cons(
              PhantomData,
              __mk_pair(
                a2,
                self.CertiCoq_Benchmarks_lib_vs_lookC(
                  A_cmp,
                  fAB,
                  a2,
                  cs)),
              self.CertiCoq_Benchmarks_lib_vs_rewriteC(
                B_cmp,
                self.CertiCoq_Benchmarks_lib_vs_lookC(
                  A_cmp,
                  fAB,
                  a1,
                  cs),
                self.CertiCoq_Benchmarks_lib_vs_lookC(
                  A_cmp,
                  fAB,
                  a2,
                  cs),
                cs)))))
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_mergeC__curried<A: Copy, B: Copy>(&'a self) -> &'a dyn Fn(&'a dyn Fn(A) -> &'a dyn Fn(A) -> std::cmp::Ordering) -> &'a dyn Fn(&'a dyn Fn(B) -> &'a dyn Fn(B) -> std::cmp::Ordering) -> &'a dyn Fn(&'a dyn Fn(A) -> B) -> &'a dyn Fn(A) -> &'a dyn Fn(A) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, __pair<A, B>>) -> &'a Coq_Init_Datatypes_list<'a, __pair<A, B>> {
  self.closure(move |A_cmp| {
    self.closure(move |B_cmp| {
      self.closure(move |fAB| {
        self.closure(move |a1| {
          self.closure(move |a2| {
            self.closure(move |cs| {
              self.CertiCoq_Benchmarks_lib_vs_mergeC(
                A_cmp,
                B_cmp,
                fAB,
                a1,
                a2,
                cs)
            })
          })
        })
      })
    })
  })
}

fn Coq_Init_Datatypes_id(&'a self) -> Coq_Init_Datatypes_ID<'a> {
  self.closure(move |A| {
    self.closure(move |x| {
      x
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_cclose_aux(&'a self, l: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_list<'a, __pair<&'a CertiCoq_Benchmarks_lib_vs_expr<'a>, &'a CertiCoq_Benchmarks_lib_vs_expr<'a>>> {
  match l {
    &Coq_Init_Datatypes_list::nil(_) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
    &Coq_Init_Datatypes_list::cons(_, c, l2) => {
      match c {
        &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma, delta, priority) => {
          match gamma {
            &Coq_Init_Datatypes_list::nil(_) => {
              match delta {
                &Coq_Init_Datatypes_list::nil(_) => {
                  self.alloc(
                    Coq_Init_Datatypes_list::nil(
                      PhantomData))
                },
                &Coq_Init_Datatypes_list::cons(_, p, l0) => {
                  match p {
                    &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, s, t) => {
                      match l0 {
                        &Coq_Init_Datatypes_list::nil(_) => {
                          self.CertiCoq_Benchmarks_lib_vs_mergeC(
                            self.CertiCoq_Benchmarks_lib_vs_expr_cmp__curried(),
                            self.CertiCoq_Benchmarks_lib_vs_expr_cmp__curried(),
                            self.Coq_Init_Datatypes_id()(
                              ()),
                            s,
                            t,
                            self.CertiCoq_Benchmarks_lib_vs_cclose_aux(
                              l2))
                        },
                        &Coq_Init_Datatypes_list::cons(_, p0, l1) => {
                          self.alloc(
                            Coq_Init_Datatypes_list::nil(
                              PhantomData))
                        },
                      }
                    },
                  }
                },
              }
            },
            &Coq_Init_Datatypes_list::cons(_, p, l0) => {
              self.alloc(
                Coq_Init_Datatypes_list::nil(
                  PhantomData))
            },
          }
        },
        &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
          self.alloc(
            Coq_Init_Datatypes_list::nil(
              PhantomData))
        },
        &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
          self.alloc(
            Coq_Init_Datatypes_list::nil(
              PhantomData))
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_cclose_aux__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_list<'a, __pair<&'a CertiCoq_Benchmarks_lib_vs_expr<'a>, &'a CertiCoq_Benchmarks_lib_vs_expr<'a>>> {
  self.closure(move |l| {
    self.CertiCoq_Benchmarks_lib_vs_cclose_aux(
      l)
  })
}

fn CertiCoq_Benchmarks_lib_vs_cclose(&'a self, l: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.Coq_Lists_List_map(
    self.closure(move |p| {
      __pair_elim!(
        e2, e1, {
          self.CertiCoq_Benchmarks_lib_vs_mkPureClause(
            self.alloc(
              Coq_Init_Datatypes_list::nil(
                PhantomData)),
            self.alloc(
              Coq_Init_Datatypes_list::cons(
                PhantomData,
                self.alloc(
                  CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                    PhantomData,
                    e2,
                    e1)),
                self.alloc(
                  Coq_Init_Datatypes_list::nil(
                    PhantomData)))))
        },
        p)
    }),
    self.CertiCoq_Benchmarks_lib_vs_cclose_aux(
      l))
}
fn CertiCoq_Benchmarks_lib_vs_cclose__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.closure(move |l| {
    self.CertiCoq_Benchmarks_lib_vs_cclose(
      l)
  })
}

fn Coq_PArith_BinPosDef_Pos_pred(&'a self, a: u64) -> u64 { a - 1 }
fn Coq_PArith_BinPosDef_Pos_pred__curried(&'a self) -> &'a dyn Fn(u64) -> u64 {
  self.closure(move |x| {
    self.Coq_PArith_BinPosDef_Pos_pred(
      x)
  })
}

fn CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_pures_list(&'a self, l: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  l
}
fn CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_pures_list__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.closure(move |l| {
    self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_pures_list(
      l)
  })
}

fn CertiCoq_Benchmarks_lib_vs_isGeq(&'a self, cc: std::cmp::Ordering) -> bool {
  match cc {
    std::cmp::Ordering::Equal => {
      true
    },
    std::cmp::Ordering::Less => {
      false
    },
    std::cmp::Ordering::Greater => {
      true
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_isGeq__curried(&'a self) -> &'a dyn Fn(std::cmp::Ordering) -> bool {
  self.closure(move |cc| {
    self.CertiCoq_Benchmarks_lib_vs_isGeq(
      cc)
  })
}

fn CertiCoq_Benchmarks_lib_vs_insert<A: Copy>(&'a self, A: (), cmp: &'a dyn Fn(A) -> &'a dyn Fn(A) -> std::cmp::Ordering, a: A, l: &'a Coq_Init_Datatypes_list<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  match l {
    &Coq_Init_Datatypes_list::nil(_) => {
      self.alloc(
        Coq_Init_Datatypes_list::cons(
          PhantomData,
          a,
          self.alloc(
            Coq_Init_Datatypes_list::nil(
              PhantomData))))
    },
    &Coq_Init_Datatypes_list::cons(_, h, t) => {
      match self.CertiCoq_Benchmarks_lib_vs_isGeq(
              hint_app(hint_app(cmp)(a))(h)) {
        true => {
          self.alloc(
            Coq_Init_Datatypes_list::cons(
              PhantomData,
              a,
              l))
        },
        false => {
          self.alloc(
            Coq_Init_Datatypes_list::cons(
              PhantomData,
              h,
              self.CertiCoq_Benchmarks_lib_vs_insert(
                (),
                cmp,
                a,
                t)))
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_insert__curried<A: Copy>(&'a self) -> &'a dyn Fn(()) -> &'a dyn Fn(&'a dyn Fn(A) -> &'a dyn Fn(A) -> std::cmp::Ordering) -> &'a dyn Fn(A) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  self.closure(move |A| {
    self.closure(move |cmp| {
      self.closure(move |a| {
        self.closure(move |l| {
          self.CertiCoq_Benchmarks_lib_vs_insert(
            A,
            cmp,
            a,
            l)
        })
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_rsort<A: Copy>(&'a self, A: (), cmp: &'a dyn Fn(A) -> &'a dyn Fn(A) -> std::cmp::Ordering, l: &'a Coq_Init_Datatypes_list<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  match l {
    &Coq_Init_Datatypes_list::nil(_) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
    &Coq_Init_Datatypes_list::cons(_, h, t) => {
      self.CertiCoq_Benchmarks_lib_vs_insert(
        (),
        cmp,
        h,
        self.CertiCoq_Benchmarks_lib_vs_rsort(
          (),
          cmp,
          t))
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_rsort__curried<A: Copy>(&'a self) -> &'a dyn Fn(()) -> &'a dyn Fn(&'a dyn Fn(A) -> &'a dyn Fn(A) -> std::cmp::Ordering) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  self.closure(move |A| {
    self.closure(move |cmp| {
      self.closure(move |l| {
        self.CertiCoq_Benchmarks_lib_vs_rsort(
          A,
          cmp,
          l)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_rev_cmp<A: Copy>(&'a self, cmp: &'a dyn Fn(A) -> &'a dyn Fn(A) -> std::cmp::Ordering, a: A, b: A) -> std::cmp::Ordering {
  match hint_app(hint_app(cmp)(a))(b) {
    std::cmp::Ordering::Equal => {
      std::cmp::Ordering::Equal
    },
    std::cmp::Ordering::Less => {
      std::cmp::Ordering::Greater
    },
    std::cmp::Ordering::Greater => {
      std::cmp::Ordering::Less
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_rev_cmp__curried<A: Copy>(&'a self) -> &'a dyn Fn(&'a dyn Fn(A) -> &'a dyn Fn(A) -> std::cmp::Ordering) -> &'a dyn Fn(A) -> &'a dyn Fn(A) -> std::cmp::Ordering {
  self.closure(move |cmp| {
    self.closure(move |a| {
      self.closure(move |b| {
        self.CertiCoq_Benchmarks_lib_vs_rev_cmp(
          cmp,
          a,
          b)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_pn_atom_cmp(&'a self, a1: &'a CertiCoq_Benchmarks_lib_vs_pn_atom<'a>, a2: &'a CertiCoq_Benchmarks_lib_vs_pn_atom<'a>) -> std::cmp::Ordering {
  match a1 {
    &CertiCoq_Benchmarks_lib_vs_pn_atom::Equ(_, e1, e2) => {
      match a2 {
        &CertiCoq_Benchmarks_lib_vs_pn_atom::Equ(_, e12, e22) => {
          self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp(
            self.alloc(
              CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                PhantomData,
                e1,
                e2)),
            self.alloc(
              CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                PhantomData,
                e12,
                e22)))
        },
        &CertiCoq_Benchmarks_lib_vs_pn_atom::Nequ(_, e12, e22) => {
          match self.CertiCoq_Benchmarks_lib_vs_expr_eq(
                  e1,
                  e12) {
            true => {
              std::cmp::Ordering::Less
            },
            false => {
              self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp(
                self.alloc(
                  CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                    PhantomData,
                    e1,
                    e2)),
                self.alloc(
                  CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                    PhantomData,
                    e12,
                    e22)))
            },
          }
        },
      }
    },
    &CertiCoq_Benchmarks_lib_vs_pn_atom::Nequ(_, e1, e2) => {
      match a2 {
        &CertiCoq_Benchmarks_lib_vs_pn_atom::Equ(_, e12, e22) => {
          match self.CertiCoq_Benchmarks_lib_vs_expr_eq(
                  e1,
                  e12) {
            true => {
              std::cmp::Ordering::Greater
            },
            false => {
              self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp(
                self.alloc(
                  CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                    PhantomData,
                    e1,
                    e2)),
                self.alloc(
                  CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                    PhantomData,
                    e12,
                    e22)))
            },
          }
        },
        &CertiCoq_Benchmarks_lib_vs_pn_atom::Nequ(_, e12, e22) => {
          self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp(
            self.alloc(
              CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                PhantomData,
                e1,
                e2)),
            self.alloc(
              CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                PhantomData,
                e12,
                e22)))
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_pn_atom_cmp__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_pn_atom<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_pn_atom<'a>) -> std::cmp::Ordering {
  self.closure(move |a1| {
    self.closure(move |a2| {
      self.CertiCoq_Benchmarks_lib_vs_pn_atom_cmp(
        a1,
        a2)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_pure_atom2pn_atom(&'a self, b: bool, a: &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_pn_atom<'a> {
  match a {
    &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, e1, e2) => {
      match b {
        true => {
          self.alloc(
            CertiCoq_Benchmarks_lib_vs_pn_atom::Equ(
              PhantomData,
              e1,
              e2))
        },
        false => {
          self.alloc(
            CertiCoq_Benchmarks_lib_vs_pn_atom::Nequ(
              PhantomData,
              e1,
              e2))
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_pure_atom2pn_atom__curried(&'a self) -> &'a dyn Fn(bool) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_pn_atom<'a> {
  self.closure(move |b| {
    self.closure(move |a| {
      self.CertiCoq_Benchmarks_lib_vs_pure_atom2pn_atom(
        b,
        a)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_pure_clause2pn_list(&'a self, c: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pn_atom<'a>> {
  match c {
    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma, delta, priority) => {
      self.CertiCoq_Benchmarks_lib_vs_rsort(
        (),
        self.CertiCoq_Benchmarks_lib_vs_pn_atom_cmp__curried(),
        self.Coq_Init_Datatypes_app(
          self.Coq_Lists_List_map(
            self.CertiCoq_Benchmarks_lib_vs_pure_atom2pn_atom__curried()(
              false),
            gamma),
          self.Coq_Lists_List_map(
            self.CertiCoq_Benchmarks_lib_vs_pure_atom2pn_atom__curried()(
              true),
            delta)))
    },
    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_pure_clause2pn_list__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pn_atom<'a>> {
  self.closure(move |c| {
    self.CertiCoq_Benchmarks_lib_vs_pure_clause2pn_list(
      c)
  })
}

fn CertiCoq_Benchmarks_lib_vs_compare_clause2(&'a self, cl1: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, cl2: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> std::cmp::Ordering {
  match cl1 {
    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma, delta, priority) => {
      match cl2 {
        &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma0, delta0, priority0) => {
          self.CertiCoq_Benchmarks_lib_vs_compare_list(
            (),
            self.CertiCoq_Benchmarks_lib_vs_pn_atom_cmp__curried(),
            self.CertiCoq_Benchmarks_lib_vs_pure_clause2pn_list(
              cl1),
            self.CertiCoq_Benchmarks_lib_vs_pure_clause2pn_list(
              cl2))
        },
        &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma0, delta0, sigma) => {
          self.CertiCoq_Benchmarks_lib_vs_compare_clause(
            cl1,
            cl2)
        },
        &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma0, sigma, delta0) => {
          self.CertiCoq_Benchmarks_lib_vs_compare_clause(
            cl1,
            cl2)
        },
      }
    },
    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
      self.CertiCoq_Benchmarks_lib_vs_compare_clause(
        cl1,
        cl2)
    },
    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
      self.CertiCoq_Benchmarks_lib_vs_compare_clause(
        cl1,
        cl2)
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_compare_clause2__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> std::cmp::Ordering {
  self.closure(move |cl1| {
    self.closure(move |cl2| {
      self.CertiCoq_Benchmarks_lib_vs_compare_clause2(
        cl1,
        cl2)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_inferred_list(&'a self, l: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  l
}
fn CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_inferred_list__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.closure(move |l| {
    self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_inferred_list(
      l)
  })
}

fn CertiCoq_Benchmarks_lib_vs_merge<A: Copy>(&'a self, A: (), cmp: &'a dyn Fn(A) -> &'a dyn Fn(A) -> std::cmp::Ordering, l1: &'a Coq_Init_Datatypes_list<'a, A>, l2: &'a Coq_Init_Datatypes_list<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  let merge_aux = {
    let merge_aux = self.alloc(std::cell::Cell::new(None));
    merge_aux.set(Some(
      self.closure(move |l22| {
        match l1 {
          &Coq_Init_Datatypes_list::nil(_) => {
            l22
          },
          &Coq_Init_Datatypes_list::cons(_, a1, l12) => {
            match l22 {
              &Coq_Init_Datatypes_list::nil(_) => {
                l1
              },
              &Coq_Init_Datatypes_list::cons(_, a2, l23) => {
                match hint_app(hint_app(cmp)(a1))(a2) {
                  std::cmp::Ordering::Equal => {
                    self.alloc(
                      Coq_Init_Datatypes_list::cons(
                        PhantomData,
                        a1,
                        self.CertiCoq_Benchmarks_lib_vs_merge(
                          (),
                          cmp,
                          l12,
                          l23)))
                  },
                  std::cmp::Ordering::Less => {
                    self.alloc(
                      Coq_Init_Datatypes_list::cons(
                        PhantomData,
                        a2,
                        hint_app(merge_aux.get().unwrap())(l23)))
                  },
                  std::cmp::Ordering::Greater => {
                    self.alloc(
                      Coq_Init_Datatypes_list::cons(
                        PhantomData,
                        a1,
                        self.CertiCoq_Benchmarks_lib_vs_merge(
                          (),
                          cmp,
                          l12,
                          l22)))
                  },
                }
              },
            }
          },
        }
      })));
    merge_aux.get().unwrap()
  };
  hint_app(merge_aux)(l2)
}
fn CertiCoq_Benchmarks_lib_vs_merge__curried<A: Copy>(&'a self) -> &'a dyn Fn(()) -> &'a dyn Fn(&'a dyn Fn(A) -> &'a dyn Fn(A) -> std::cmp::Ordering) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  self.closure(move |A| {
    self.closure(move |cmp| {
      self.closure(move |l1| {
        self.closure(move |l2| {
          self.CertiCoq_Benchmarks_lib_vs_merge(
            A,
            cmp,
            l1,
            l2)
        })
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_ef_aux(&'a self, neg: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>, u0: CertiCoq_Benchmarks_lib_vs_var<'a>, u: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, v: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, pos0: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>, pos: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>, l0: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  match pos {
    &Coq_Init_Datatypes_list::nil(_) => {
      l0
    },
    &Coq_Init_Datatypes_list::cons(_, a2, pos2) => {
      match a2 {
        &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, s, t) => {
          match __andb!(
                  self.CertiCoq_Benchmarks_lib_vs_expr_eq(
                    s,
                    u),
                  self.CertiCoq_Benchmarks_lib_vs_greater_than_all(
                    u0)(
                    neg)) {
            true => {
              self.alloc(
                Coq_Init_Datatypes_list::cons(
                  PhantomData,
                  self.CertiCoq_Benchmarks_lib_vs_mkPureClause(
                    self.CertiCoq_Benchmarks_lib_vs_insert_uniq(
                      (),
                      self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
                      self.CertiCoq_Benchmarks_lib_vs_norm_pure_atom(
                        self.alloc(
                          CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                            PhantomData,
                            v,
                            t))),
                      neg),
                    self.CertiCoq_Benchmarks_lib_vs_insert_uniq(
                      (),
                      self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
                      self.CertiCoq_Benchmarks_lib_vs_norm_pure_atom(
                        self.alloc(
                          CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                            PhantomData,
                            u,
                            t))),
                      self.CertiCoq_Benchmarks_lib_vs_merge(
                        (),
                        self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
                        self.Coq_Lists_List_rev(
                          pos0),
                        pos))),
                  self.CertiCoq_Benchmarks_lib_vs_Superposition_ef_aux(
                    neg,
                    u0,
                    u,
                    v,
                    self.CertiCoq_Benchmarks_lib_vs_insert_uniq(
                      (),
                      self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
                      a2,
                      pos0),
                    pos2,
                    l0)))
            },
            false => {
              l0
            },
          }
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_Superposition_ef_aux__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_var<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.closure(move |neg| {
    self.closure(move |u0| {
      self.closure(move |u| {
        self.closure(move |v| {
          self.closure(move |pos0| {
            self.closure(move |pos| {
              self.closure(move |l0| {
                self.CertiCoq_Benchmarks_lib_vs_Superposition_ef_aux(
                  neg,
                  u0,
                  u,
                  v,
                  pos0,
                  pos,
                  l0)
              })
            })
          })
        })
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_ef(&'a self, cty: &'a CertiCoq_Benchmarks_lib_vs_ce_type<'a>, c: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, l0: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  match cty {
    &CertiCoq_Benchmarks_lib_vs_ce_type::CexpL(_) => {
      l0
    },
    &CertiCoq_Benchmarks_lib_vs_ce_type::CexpR(_) => {
      l0
    },
    &CertiCoq_Benchmarks_lib_vs_ce_type::CexpEf(_) => {
      match c {
        &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, neg, delta, priority) => {
          match delta {
            &Coq_Init_Datatypes_list::nil(_) => {
              l0
            },
            &Coq_Init_Datatypes_list::cons(_, p, pos) => {
              match p {
                &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, u, v) => {
                  match u {
                    &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
                      l0
                    },
                    &CertiCoq_Benchmarks_lib_vs_expr::Var(_, u0) => {
                      match self.CertiCoq_Benchmarks_lib_vs_greater_than_all(
                              u0)(
                              neg) {
                        true => {
                          self.CertiCoq_Benchmarks_lib_vs_Superposition_ef_aux(
                            neg,
                            u0,
                            u,
                            v,
                            self.alloc(
                              Coq_Init_Datatypes_list::nil(
                                PhantomData)),
                            pos,
                            l0)
                        },
                        false => {
                          l0
                        },
                      }
                    },
                  }
                },
              }
            },
          }
        },
        &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
          l0
        },
        &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
          l0
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_Superposition_ef__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_ce_type<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.closure(move |cty| {
    self.closure(move |c| {
      self.closure(move |l0| {
        self.CertiCoq_Benchmarks_lib_vs_Superposition_ef(
          cty,
          c,
          l0)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_pure_atom_gt(&'a self, a: &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>, b: &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> bool {
  match self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp(
          a,
          b) {
    std::cmp::Ordering::Equal => {
      false
    },
    std::cmp::Ordering::Less => {
      false
    },
    std::cmp::Ordering::Greater => {
      true
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_pure_atom_gt__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> bool {
  self.closure(move |a| {
    self.closure(move |b| {
      self.CertiCoq_Benchmarks_lib_vs_pure_atom_gt(
        a,
        b)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_pure_atom_gt1(&'a self, a: &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>, l: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> bool {
  match l {
    &Coq_Init_Datatypes_list::nil(_) => {
      true
    },
    &Coq_Init_Datatypes_list::cons(_, b, l0) => {
      self.CertiCoq_Benchmarks_lib_vs_pure_atom_gt(
        a,
        b)
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_Superposition_pure_atom_gt1__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>) -> bool {
  self.closure(move |a| {
    self.closure(move |l| {
      self.CertiCoq_Benchmarks_lib_vs_Superposition_pure_atom_gt1(
        a,
        l)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_sp(&'a self, cty: &'a CertiCoq_Benchmarks_lib_vs_ce_type<'a>, c: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, d: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, l0: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  match cty {
    &CertiCoq_Benchmarks_lib_vs_ce_type::CexpL(_) => {
      match c {
        &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma, pos, priority) => {
          match gamma {
            &Coq_Init_Datatypes_list::nil(_) => {
              l0
            },
            &Coq_Init_Datatypes_list::cons(_, p, neg) => {
              match p {
                &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, s, v) => {
                  match d {
                    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, neg2, delta, priority0) => {
                      match delta {
                        &Coq_Init_Datatypes_list::nil(_) => {
                          l0
                        },
                        &Coq_Init_Datatypes_list::cons(_, p0, pos2) => {
                          match p0 {
                            &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, s2, t) => {
                              match s2 {
                                &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
                                  l0
                                },
                                &CertiCoq_Benchmarks_lib_vs_expr::Var(_, s0) => {
                                  match __andb!(
                                          __andb!(
                                            __andb!(
                                              __andb!(
                                                self.CertiCoq_Benchmarks_lib_vs_expr_eq(
                                                  s2,
                                                  s),
                                                self.CertiCoq_Benchmarks_lib_vs_expr_lt(
                                                  t,
                                                  s2)),
                                              self.CertiCoq_Benchmarks_lib_vs_expr_lt(
                                                v,
                                                s)),
                                            self.CertiCoq_Benchmarks_lib_vs_Superposition_pure_atom_gt1(
                                              self.alloc(
                                                CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                                                  PhantomData,
                                                  s2,
                                                  t)),
                                              pos2)),
                                          self.CertiCoq_Benchmarks_lib_vs_greater_than_all(
                                            s0)(
                                            neg2)) {
                                    true => {
                                      self.alloc(
                                        Coq_Init_Datatypes_list::cons(
                                          PhantomData,
                                          self.CertiCoq_Benchmarks_lib_vs_mkPureClause(
                                            self.CertiCoq_Benchmarks_lib_vs_insert_uniq(
                                              (),
                                              self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
                                              self.CertiCoq_Benchmarks_lib_vs_norm_pure_atom(
                                                self.alloc(
                                                  CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                                                    PhantomData,
                                                    t,
                                                    v))),
                                              self.CertiCoq_Benchmarks_lib_vs_merge(
                                                (),
                                                self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
                                                neg2,
                                                neg)),
                                            self.CertiCoq_Benchmarks_lib_vs_merge(
                                              (),
                                              self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
                                              pos2,
                                              pos)),
                                          l0))
                                    },
                                    false => {
                                      l0
                                    },
                                  }
                                },
                              }
                            },
                          }
                        },
                      }
                    },
                    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma0, delta, sigma) => {
                      l0
                    },
                    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma0, sigma, delta) => {
                      l0
                    },
                  }
                },
              }
            },
          }
        },
        &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
          l0
        },
        &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
          l0
        },
      }
    },
    &CertiCoq_Benchmarks_lib_vs_ce_type::CexpR(_) => {
      match c {
        &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, neg, delta, priority) => {
          match delta {
            &Coq_Init_Datatypes_list::nil(_) => {
              l0
            },
            &Coq_Init_Datatypes_list::cons(_, p, pos) => {
              match p {
                &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, s, t) => {
                  match s {
                    &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
                      l0
                    },
                    &CertiCoq_Benchmarks_lib_vs_expr::Var(_, s0) => {
                      match d {
                        &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, neg2, delta0, priority0) => {
                          match delta0 {
                            &Coq_Init_Datatypes_list::nil(_) => {
                              l0
                            },
                            &Coq_Init_Datatypes_list::cons(_, p0, pos2) => {
                              match p0 {
                                &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, s2, v) => {
                                  match s2 {
                                    &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
                                      l0
                                    },
                                    &CertiCoq_Benchmarks_lib_vs_expr::Var(_, s02) => {
                                      match __andb!(
                                              __andb!(
                                                __andb!(
                                                  __andb!(
                                                    __andb!(
                                                      __andb!(
                                                        __andb!(
                                                          self.CertiCoq_Benchmarks_lib_vs_expr_eq(
                                                            s,
                                                            s2),
                                                          self.CertiCoq_Benchmarks_lib_vs_expr_lt(
                                                            t,
                                                            s)),
                                                        self.CertiCoq_Benchmarks_lib_vs_expr_lt(
                                                          v,
                                                          s2)),
                                                      self.CertiCoq_Benchmarks_lib_vs_Superposition_pure_atom_gt1(
                                                        self.alloc(
                                                          CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                                                            PhantomData,
                                                            s,
                                                            t)),
                                                        pos)),
                                                    self.CertiCoq_Benchmarks_lib_vs_Superposition_pure_atom_gt1(
                                                      self.alloc(
                                                        CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                                                          PhantomData,
                                                          s2,
                                                          v)),
                                                      pos2)),
                                                  self.CertiCoq_Benchmarks_lib_vs_pure_atom_gt(
                                                    self.alloc(
                                                      CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                                                        PhantomData,
                                                        s,
                                                        t)),
                                                    self.alloc(
                                                      CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                                                        PhantomData,
                                                        s2,
                                                        v)))),
                                                self.CertiCoq_Benchmarks_lib_vs_greater_than_all(
                                                  s0)(
                                                  neg)),
                                              self.CertiCoq_Benchmarks_lib_vs_greater_than_all(
                                                s02)(
                                                neg2)) {
                                        true => {
                                          self.alloc(
                                            Coq_Init_Datatypes_list::cons(
                                              PhantomData,
                                              self.CertiCoq_Benchmarks_lib_vs_mkPureClause(
                                                self.CertiCoq_Benchmarks_lib_vs_merge(
                                                  (),
                                                  self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
                                                  neg,
                                                  neg2),
                                                self.CertiCoq_Benchmarks_lib_vs_insert_uniq(
                                                  (),
                                                  self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
                                                  self.CertiCoq_Benchmarks_lib_vs_norm_pure_atom(
                                                    self.alloc(
                                                      CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                                                        PhantomData,
                                                        t,
                                                        v))),
                                                  self.CertiCoq_Benchmarks_lib_vs_merge(
                                                    (),
                                                    self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
                                                    pos,
                                                    pos2))),
                                              l0))
                                        },
                                        false => {
                                          l0
                                        },
                                      }
                                    },
                                  }
                                },
                              }
                            },
                          }
                        },
                        &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta0, sigma) => {
                          l0
                        },
                        &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta0) => {
                          l0
                        },
                      }
                    },
                  }
                },
              }
            },
          }
        },
        &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
          l0
        },
        &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
          l0
        },
      }
    },
    &CertiCoq_Benchmarks_lib_vs_ce_type::CexpEf(_) => {
      l0
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_Superposition_sp__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_ce_type<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.closure(move |cty| {
    self.closure(move |c| {
      self.closure(move |d| {
        self.closure(move |l0| {
          self.CertiCoq_Benchmarks_lib_vs_Superposition_sp(
            cty,
            c,
            d,
            l0)
        })
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_infer(&'a self, cty: &'a CertiCoq_Benchmarks_lib_vs_ce_type<'a>, c: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, l: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_inferred_list(
    self.CertiCoq_Benchmarks_lib_vs_rsort_uniq(
      (),
      self.CertiCoq_Benchmarks_lib_vs_compare_clause__curried(),
      self.Coq_Lists_List_filter(
        self.CertiCoq_Benchmarks_lib_vs_Superposition_not_taut__curried(),
        self.Coq_Lists_List_map(
          self.CertiCoq_Benchmarks_lib_vs_Superposition_simplify__curried()(
            self.alloc(
              Coq_Init_Datatypes_list::nil(
                PhantomData))),
          self.CertiCoq_Benchmarks_lib_vs_Superposition_ef(
            cty,
            c,
            self.Coq_Lists_List_fold_left(
              self.closure(move |l0| {
                self.closure(move |d| {
                  self.CertiCoq_Benchmarks_lib_vs_Superposition_sp(
                    cty,
                    c,
                    d,
                    l0)
                })
              }),
              l,
              self.alloc(
                Coq_Init_Datatypes_list::nil(
                  PhantomData))))))))
}
fn CertiCoq_Benchmarks_lib_vs_Superposition_infer__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_ce_type<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.closure(move |cty| {
    self.closure(move |c| {
      self.closure(move |l| {
        self.CertiCoq_Benchmarks_lib_vs_Superposition_infer(
          cty,
          c,
          l)
      })
    })
  })
}

fn Coq_Init_Specif_sig_rect<A: Copy, P0: Copy>(&'a self, f: &'a dyn Fn(A) -> &'a dyn Fn(()) -> P0, s: &'a Coq_Init_Specif_sig<'a, A>) -> P0 {
  match s {
    &Coq_Init_Specif_sig::exist(_, x) => {
      hint_app(hint_app(f)(x))(())
    },
  }
}
fn Coq_Init_Specif_sig_rect__curried<A: Copy, P0: Copy>(&'a self) -> &'a dyn Fn(&'a dyn Fn(A) -> &'a dyn Fn(()) -> P0) -> &'a dyn Fn(&'a Coq_Init_Specif_sig<'a, A>) -> P0 {
  self.closure(move |f| {
    self.closure(move |s| {
      self.Coq_Init_Specif_sig_rect(
        f,
        s)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_main_terminate(&'a self) -> &'a dyn Fn(u64) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Specif_sig<'a, __pair<__pair<__pair<&'a CertiCoq_Benchmarks_lib_vs_Superposition_superposition_result<'a>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>>, CertiCoq_Benchmarks_lib_vs_M_t<'a>>, CertiCoq_Benchmarks_lib_vs_M_t<'a>>> {
  hint_app(self.closure(move |h| {
             let H =
               ();
             hint_app(self.closure(move |_TmpHyp| {
                        self.closure(move |n| {
                          self.closure(move |units| {
                            self.closure(move |l| {
                              let Acc_n =
                                ();
                              hint_app(hint_app(hint_app(hint_app({ let hrec = self.alloc(std::cell::Cell::new(None));
                                                                    hrec.set(Some(
                                                                      self.closure(move |n2| {
                                                                        self.closure(move |units2| {
                                                                          self.closure(move |l2| {
                                                                            self.closure(move |Acc_n2| {
                                                                              hint_app(match self.Coq_PArith_BinPosDef_Pos_eqb(
                                                                                               n2,
                                                                                               1) {
                                                                                         true => {
                                                                                           self.closure(move |teq| {
                                                                                             self.alloc(
                                                                                               Coq_Init_Specif_sig::exist(
                                                                                                 PhantomData,
                                                                                                 __mk_pair(
                                                                                                   __mk_pair(
                                                                                                     __mk_pair(
                                                                                                       self.alloc(
                                                                                                         CertiCoq_Benchmarks_lib_vs_Superposition_superposition_result::Aborted(
                                                                                                           PhantomData,
                                                                                                           l2)),
                                                                                                       units2),
                                                                                                     self.CertiCoq_Benchmarks_lib_vs_M_empty()),
                                                                                                   self.CertiCoq_Benchmarks_lib_vs_M_empty())))
                                                                                           })
                                                                                         },
                                                                                         false => {
                                                                                           self.closure(move |teq| {
                                                                                             hint_app(match self.Coq_Lists_List_existsb(
                                                                                                              self.CertiCoq_Benchmarks_lib_vs_Superposition_is_empty_clause__curried(),
                                                                                                              self.Coq_Lists_List_map(
                                                                                                                self.CertiCoq_Benchmarks_lib_vs_Superposition_delete_resolved__curried(),
                                                                                                                l2)) {
                                                                                                        true => {
                                                                                                          self.closure(move |teq0| {
                                                                                                            self.alloc(
                                                                                                              Coq_Init_Specif_sig::exist(
                                                                                                                PhantomData,
                                                                                                                __mk_pair(
                                                                                                                  __mk_pair(
                                                                                                                    __mk_pair(
                                                                                                                      self.alloc(
                                                                                                                        CertiCoq_Benchmarks_lib_vs_Superposition_superposition_result::Valid(
                                                                                                                          PhantomData)),
                                                                                                                      units2),
                                                                                                                    self.CertiCoq_Benchmarks_lib_vs_M_empty()),
                                                                                                                  self.CertiCoq_Benchmarks_lib_vs_M_empty())))
                                                                                                          })
                                                                                                        },
                                                                                                        false => {
                                                                                                          self.closure(move |teq0| {
                                                                                                            hint_app(__pair_elim!(
                                                                                                                       b, a, {
                                                                                                                         hint_app(hint_app(self.closure(move |us| {
                                                                                                                                             self.closure(move |rs| {
                                                                                                                                               self.closure(move |teq1| {
                                                                                                                                                 hint_app(match self.CertiCoq_Benchmarks_lib_vs_Superposition_partial_mod(
                                                                                                                                                                  self.alloc(
                                                                                                                                                                    Coq_Init_Datatypes_list::nil(
                                                                                                                                                                      PhantomData)),
                                                                                                                                                                  self.alloc(
                                                                                                                                                                    Coq_Init_Datatypes_list::nil(
                                                                                                                                                                      PhantomData)),
                                                                                                                                                                  self.Coq_Lists_List_filter(
                                                                                                                                                                    self.CertiCoq_Benchmarks_lib_vs_Superposition_not_taut__curried(),
                                                                                                                                                                    self.Coq_Lists_List_map(
                                                                                                                                                                      self.CertiCoq_Benchmarks_lib_vs_Superposition_simplify__curried()(
                                                                                                                                                                        self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_eqs_list(
                                                                                                                                                                          self.CertiCoq_Benchmarks_lib_vs_cclose(
                                                                                                                                                                            us))),
                                                                                                                                                                      rs))) {
                                                                                                                                                            &Coq_Init_Datatypes_sum::inl(_, a2) => {
                                                                                                                                                              hint_app(self.closure(move |p| {
                                                                                                                                                                         self.closure(move |teq2| {
                                                                                                                                                                           hint_app(hint_app(__pair_elim!(
                                                                                                                                                                                               b2, a3, {
                                                                                                                                                                                                 hint_app(hint_app(self.closure(move |R| {
                                                                                                                                                                                                                     self.closure(move |selected| {
                                                                                                                                                                                                                       self.closure(move |teq3| {
                                                                                                                                                                                                                         self.closure(move |teq22| {
                                                                                                                                                                                                                           self.alloc(
                                                                                                                                                                                                                             Coq_Init_Specif_sig::exist(
                                                                                                                                                                                                                               PhantomData,
                                                                                                                                                                                                                               __mk_pair(
                                                                                                                                                                                                                                 __mk_pair(
                                                                                                                                                                                                                                   __mk_pair(
                                                                                                                                                                                                                                     self.alloc(
                                                                                                                                                                                                                                       CertiCoq_Benchmarks_lib_vs_Superposition_superposition_result::C_example(
                                                                                                                                                                                                                                         PhantomData,
                                                                                                                                                                                                                                         R,
                                                                                                                                                                                                                                         self.CertiCoq_Benchmarks_lib_vs_clause_list2set(
                                                                                                                                                                                                                                           selected))),
                                                                                                                                                                                                                                     self.CertiCoq_Benchmarks_lib_vs_cclose(
                                                                                                                                                                                                                                       self.Coq_Init_Datatypes_app(
                                                                                                                                                                                                                                         self.CertiCoq_Benchmarks_lib_vs_cclose(
                                                                                                                                                                                                                                           us),
                                                                                                                                                                                                                                         units2))),
                                                                                                                                                                                                                                   self.CertiCoq_Benchmarks_lib_vs_clause_list2set(
                                                                                                                                                                                                                                     self.Coq_Lists_List_filter(
                                                                                                                                                                                                                                       self.CertiCoq_Benchmarks_lib_vs_Superposition_not_taut__curried(),
                                                                                                                                                                                                                                       self.Coq_Lists_List_map(
                                                                                                                                                                                                                                         self.CertiCoq_Benchmarks_lib_vs_Superposition_simplify__curried()(
                                                                                                                                                                                                                                           self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_eqs_list(
                                                                                                                                                                                                                                             self.CertiCoq_Benchmarks_lib_vs_cclose(
                                                                                                                                                                                                                                               us))),
                                                                                                                                                                                                                                         rs)))),
                                                                                                                                                                                                                                 self.CertiCoq_Benchmarks_lib_vs_M_empty())))
                                                                                                                                                                                                                         })
                                                                                                                                                                                                                       })
                                                                                                                                                                                                                     })
                                                                                                                                                                                                                   }))(b2))(a3)
                                                                                                                                                                                               },
                                                                                                                                                                                               p))(()))(())
                                                                                                                                                                         })
                                                                                                                                                                       }))(a2)
                                                                                                                                                            },
                                                                                                                                                            &Coq_Init_Datatypes_sum::inr(_, b2) => {
                                                                                                                                                              hint_app(self.closure(move |p| {
                                                                                                                                                                         self.closure(move |teq2| {
                                                                                                                                                                           hint_app(hint_app(__pair_elim!(
                                                                                                                                                                                               b3, a2, {
                                                                                                                                                                                                 hint_app(hint_app(self.closure(move |p0| {
                                                                                                                                                                                                                     self.closure(move |cty| {
                                                                                                                                                                                                                       self.closure(move |teq3| {
                                                                                                                                                                                                                         self.closure(move |teq22| {
                                                                                                                                                                                                                           hint_app(hint_app(hint_app(__pair_elim!(
                                                                                                                                                                                                                                                        b4, a3, {
                                                                                                                                                                                                                                                          hint_app(hint_app(self.closure(move |R| {
                                                                                                                                                                                                                                                                              self.closure(move |cl| {
                                                                                                                                                                                                                                                                                self.closure(move |teq4| {
                                                                                                                                                                                                                                                                                  self.closure(move |teq32| {
                                                                                                                                                                                                                                                                                    self.closure(move |teq23| {
                                                                                                                                                                                                                                                                                      self.Coq_Init_Specif_sig_rect(
                                                                                                                                                                                                                                                                                        self.closure(move |rec_res| {
                                                                                                                                                                                                                                                                                          self.closure(move |p1| {
                                                                                                                                                                                                                                                                                            self.alloc(
                                                                                                                                                                                                                                                                                              Coq_Init_Specif_sig::exist(
                                                                                                                                                                                                                                                                                                PhantomData,
                                                                                                                                                                                                                                                                                                rec_res))
                                                                                                                                                                                                                                                                                          })
                                                                                                                                                                                                                                                                                        }),
                                                                                                                                                                                                                                                                                        hint_app(hint_app(hint_app(hint_app(hrec.get().unwrap())(self.Coq_PArith_BinPosDef_Pos_pred(
                                                                                                                                                                                                                                                                                                                                                   n2)))(self.CertiCoq_Benchmarks_lib_vs_cclose(
                                                                                                                                                                                                                                                                                                                                                           self.Coq_Init_Datatypes_app(
                                                                                                                                                                                                                                                                                                                                                             self.CertiCoq_Benchmarks_lib_vs_cclose(
                                                                                                                                                                                                                                                                                                                                                               us),
                                                                                                                                                                                                                                                                                                                                                             units2))))(self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_pures_list(
                                                                                                                                                                                                                                                                                                                                                                          self.CertiCoq_Benchmarks_lib_vs_rsort(
                                                                                                                                                                                                                                                                                                                                                                            (),
                                                                                                                                                                                                                                                                                                                                                                            self.CertiCoq_Benchmarks_lib_vs_rev_cmp__curried()(
                                                                                                                                                                                                                                                                                                                                                                              self.CertiCoq_Benchmarks_lib_vs_compare_clause2__curried()),
                                                                                                                                                                                                                                                                                                                                                                            self.Coq_Init_Datatypes_app(
                                                                                                                                                                                                                                                                                                                                                                              self.CertiCoq_Benchmarks_lib_vs_Superposition_infer(
                                                                                                                                                                                                                                                                                                                                                                                cty,
                                                                                                                                                                                                                                                                                                                                                                                cl,
                                                                                                                                                                                                                                                                                                                                                                                self.Coq_Lists_List_filter(
                                                                                                                                                                                                                                                                                                                                                                                  self.CertiCoq_Benchmarks_lib_vs_Superposition_not_taut__curried(),
                                                                                                                                                                                                                                                                                                                                                                                  self.Coq_Lists_List_map(
                                                                                                                                                                                                                                                                                                                                                                                    self.CertiCoq_Benchmarks_lib_vs_Superposition_simplify__curried()(
                                                                                                                                                                                                                                                                                                                                                                                      self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_eqs_list(
                                                                                                                                                                                                                                                                                                                                                                                        self.CertiCoq_Benchmarks_lib_vs_cclose(
                                                                                                                                                                                                                                                                                                                                                                                          us))),
                                                                                                                                                                                                                                                                                                                                                                                    rs))),
                                                                                                                                                                                                                                                                                                                                                                              self.Coq_Lists_List_filter(
                                                                                                                                                                                                                                                                                                                                                                                self.CertiCoq_Benchmarks_lib_vs_Superposition_not_taut__curried(),
                                                                                                                                                                                                                                                                                                                                                                                self.Coq_Lists_List_map(
                                                                                                                                                                                                                                                                                                                                                                                  self.CertiCoq_Benchmarks_lib_vs_Superposition_simplify__curried()(
                                                                                                                                                                                                                                                                                                                                                                                    self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_eqs_list(
                                                                                                                                                                                                                                                                                                                                                                                      self.CertiCoq_Benchmarks_lib_vs_cclose(
                                                                                                                                                                                                                                                                                                                                                                                        us))),
                                                                                                                                                                                                                                                                                                                                                                                  rs)))))))(()))
                                                                                                                                                                                                                                                                                    })
                                                                                                                                                                                                                                                                                  })
                                                                                                                                                                                                                                                                                })
                                                                                                                                                                                                                                                                              })
                                                                                                                                                                                                                                                                            }))(b4))(a3)
                                                                                                                                                                                                                                                        },
                                                                                                                                                                                                                                                        p0))(()))(()))(())
                                                                                                                                                                                                                         })
                                                                                                                                                                                                                       })
                                                                                                                                                                                                                     })
                                                                                                                                                                                                                   }))(b3))(a2)
                                                                                                                                                                                               },
                                                                                                                                                                                               p))(()))(())
                                                                                                                                                                         })
                                                                                                                                                                       }))(b2)
                                                                                                                                                            },
                                                                                                                                                          })(())
                                                                                                                                               })
                                                                                                                                             })
                                                                                                                                           }))(b))(a)
                                                                                                                       },
                                                                                                                       self.Coq_Lists_List_partition(
                                                                                                                         self.CertiCoq_Benchmarks_lib_vs_Superposition_is_unit_clause__curried(),
                                                                                                                         l2)))(())
                                                                                                          })
                                                                                                        },
                                                                                                      })(())
                                                                                           })
                                                                                         },
                                                                                       })(())
                                                                            })
                                                                          })
                                                                        })
                                                                      })));
                                                                    hrec.get().unwrap() })(n))(units))(l))(())
                            })
                          })
                        })
                      }))(())
           }))(())
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_main(&'a self, x: u64, x0: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>, x1: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> __pair<__pair<__pair<&'a CertiCoq_Benchmarks_lib_vs_Superposition_superposition_result<'a>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>>, CertiCoq_Benchmarks_lib_vs_M_t<'a>>, CertiCoq_Benchmarks_lib_vs_M_t<'a>> {
  match self.CertiCoq_Benchmarks_lib_vs_Superposition_main_terminate()(
          x)(
          x0)(
          x1) {
    &Coq_Init_Specif_sig::exist(_, v) => {
      v
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_Superposition_main__curried(&'a self) -> &'a dyn Fn(u64) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> __pair<__pair<__pair<&'a CertiCoq_Benchmarks_lib_vs_Superposition_superposition_result<'a>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>>, CertiCoq_Benchmarks_lib_vs_M_t<'a>>, CertiCoq_Benchmarks_lib_vs_M_t<'a>> {
  self.closure(move |x| {
    self.closure(move |x0| {
      self.closure(move |x1| {
        self.CertiCoq_Benchmarks_lib_vs_Superposition_main(
          x,
          x0,
          x1)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_bogus(&'a self) -> __pair<&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>> {
  __mk_pair(
    self.alloc(
      CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(
        PhantomData)),
    self.alloc(
      Coq_Init_Datatypes_list::nil(
        PhantomData)))
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_treeify_cont(&'a self, f: &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>) -> __pair<&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>>, g: &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>) -> __pair<&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>>, acc: &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>) -> __pair<&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>> {
  __pair_elim!(
    l0, l, {
      match l {
        &Coq_Init_Datatypes_list::nil(_) => {
          self.CertiCoq_Benchmarks_lib_vs_M_Raw_bogus()
        },
        &Coq_Init_Datatypes_list::cons(_, x, acc2) => {
          __pair_elim!(
            acc3, r, {
              __mk_pair(
                self.alloc(
                  CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
                    PhantomData,
                    self.alloc(
                      Coq_MSets_MSetRBT_color::Black(
                        PhantomData)),
                    l0,
                    x,
                    acc3)),
                r)
            },
            hint_app(g)(acc2))
        },
      }
    },
    hint_app(f)(acc))
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_treeify_cont__curried(&'a self) -> &'a dyn Fn(&'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>) -> __pair<&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>>) -> &'a dyn Fn(&'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>) -> __pair<&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>) -> __pair<&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>> {
  self.closure(move |f| {
    self.closure(move |g| {
      self.closure(move |acc| {
        self.CertiCoq_Benchmarks_lib_vs_M_Raw_treeify_cont(
          f,
          g,
          acc)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_treeify_zero(&'a self, acc: &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>) -> __pair<&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>> {
  __mk_pair(
    self.alloc(
      CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(
        PhantomData)),
    acc)
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_treeify_zero__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>) -> __pair<&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>> {
  self.closure(move |acc| {
    self.CertiCoq_Benchmarks_lib_vs_M_Raw_treeify_zero(
      acc)
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_treeify_one(&'a self, acc: &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>) -> __pair<&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>> {
  match acc {
    &Coq_Init_Datatypes_list::nil(_) => {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_bogus()
    },
    &Coq_Init_Datatypes_list::cons(_, x, acc2) => {
      __mk_pair(
        self.alloc(
          CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
            PhantomData,
            self.alloc(
              Coq_MSets_MSetRBT_color::Red(
                PhantomData)),
            self.alloc(
              CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(
                PhantomData)),
            x,
            self.alloc(
              CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(
                PhantomData)))),
        acc2)
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_treeify_one__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>) -> __pair<&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>> {
  self.closure(move |acc| {
    self.CertiCoq_Benchmarks_lib_vs_M_Raw_treeify_one(
      acc)
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_treeify_aux(&'a self, pred: bool, n: u64) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>) -> __pair<&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>> {
  __pos_elim!(
    n2, {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_treeify_cont__curried()(
        self.CertiCoq_Benchmarks_lib_vs_M_Raw_treeify_aux(
          false,
          n2))(
        self.CertiCoq_Benchmarks_lib_vs_M_Raw_treeify_aux(
          pred,
          n2))
    },
    n2, {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_treeify_cont__curried()(
        self.CertiCoq_Benchmarks_lib_vs_M_Raw_treeify_aux(
          pred,
          n2))(
        self.CertiCoq_Benchmarks_lib_vs_M_Raw_treeify_aux(
          true,
          n2))
    },
    {
      match pred {
        true => {
          self.CertiCoq_Benchmarks_lib_vs_M_Raw_treeify_zero__curried()
        },
        false => {
          self.CertiCoq_Benchmarks_lib_vs_M_Raw_treeify_one__curried()
        },
      }
    },
    n)
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_treeify_aux__curried(&'a self) -> &'a dyn Fn(bool) -> &'a dyn Fn(u64) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>) -> __pair<&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>> {
  self.closure(move |pred| {
    self.closure(move |n| {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_treeify_aux(
        pred,
        n)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_plength_aux(&'a self, l: &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>, p: u64) -> u64 {
  match l {
    &Coq_Init_Datatypes_list::nil(_) => {
      p
    },
    &Coq_Init_Datatypes_list::cons(_, e, l2) => {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_plength_aux(
        l2,
        self.Coq_PArith_BinPosDef_Pos_succ(
          p))
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_plength_aux__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>) -> &'a dyn Fn(u64) -> u64 {
  self.closure(move |l| {
    self.closure(move |p| {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_plength_aux(
        l,
        p)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_plength(&'a self, l: &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>) -> u64 {
  self.CertiCoq_Benchmarks_lib_vs_M_Raw_plength_aux(
    l,
    1)
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_plength__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>) -> u64 {
  self.closure(move |l| {
    self.CertiCoq_Benchmarks_lib_vs_M_Raw_plength(
      l)
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_treeify(&'a self, l: &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>) -> &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a> {
  self.Coq_Init_Datatypes_fst(
    self.CertiCoq_Benchmarks_lib_vs_M_Raw_treeify_aux(
      true,
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_plength(
        l))(
      l))
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_treeify__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>) -> &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a> {
  self.closure(move |l| {
    self.CertiCoq_Benchmarks_lib_vs_M_Raw_treeify(
      l)
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_filter_aux(&'a self, f: &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>) -> bool, s: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, acc: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  match s {
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
      acc
    },
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t, l, k, r) => {
      let acc2 =
        self.CertiCoq_Benchmarks_lib_vs_M_Raw_filter_aux(
          f,
          r,
          acc);
      match hint_app(f)(k) {
        true => {
          self.CertiCoq_Benchmarks_lib_vs_M_Raw_filter_aux(
            f,
            l,
            self.alloc(
              Coq_Init_Datatypes_list::cons(
                PhantomData,
                k,
                acc2)))
        },
        false => {
          self.CertiCoq_Benchmarks_lib_vs_M_Raw_filter_aux(
            f,
            l,
            acc2)
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_filter_aux__curried(&'a self) -> &'a dyn Fn(&'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>) -> bool) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.closure(move |f| {
    self.closure(move |s| {
      self.closure(move |acc| {
        self.CertiCoq_Benchmarks_lib_vs_M_Raw_filter_aux(
          f,
          s,
          acc)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_filter(&'a self, f: &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>) -> bool, s: CertiCoq_Benchmarks_lib_vs_M_Raw_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_Raw_t<'a> {
  self.CertiCoq_Benchmarks_lib_vs_M_Raw_treeify(
    self.CertiCoq_Benchmarks_lib_vs_M_Raw_filter_aux(
      f,
      s,
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))))
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_filter__curried(&'a self) -> &'a dyn Fn(&'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>) -> bool) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_Raw_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_Raw_t<'a> {
  self.closure(move |f| {
    self.closure(move |s| {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_filter(
        f,
        s)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_filter(&'a self, f: &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_elt<'a>) -> bool, s: CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.alloc(
    CertiCoq_Benchmarks_lib_vs_M_t_::Mkt(
      PhantomData,
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_filter(
        f,
        self.CertiCoq_Benchmarks_lib_vs_M_this(
          s))))
}
fn CertiCoq_Benchmarks_lib_vs_M_filter__curried(&'a self) -> &'a dyn Fn(&'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_elt<'a>) -> bool) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.closure(move |f| {
    self.closure(move |s| {
      self.CertiCoq_Benchmarks_lib_vs_M_filter(
        f,
        s)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_check_clauseset(&'a self, s: CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> __pair<__pair<__pair<&'a CertiCoq_Benchmarks_lib_vs_Superposition_superposition_result<'a>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>>, CertiCoq_Benchmarks_lib_vs_M_t<'a>>, CertiCoq_Benchmarks_lib_vs_M_t<'a>> {
  self.CertiCoq_Benchmarks_lib_vs_Superposition_main(
    __pos_zerobit(
      __pos_zerobit(
        __pos_zerobit(
          __pos_zerobit(
            __pos_zerobit(
              __pos_zerobit(
                __pos_zerobit(
                  __pos_zerobit(
                    __pos_zerobit(
                      __pos_onebit(
                        __pos_zerobit(
                          __pos_onebit(
                            __pos_zerobit(
                              __pos_zerobit(
                                __pos_onebit(
                                  __pos_onebit(
                                    __pos_zerobit(
                                      __pos_onebit(
                                        __pos_zerobit(
                                          __pos_onebit(
                                            __pos_onebit(
                                              __pos_zerobit(
                                                __pos_zerobit(
                                                  __pos_onebit(
                                                    __pos_onebit(
                                                      __pos_onebit(
                                                        __pos_zerobit(
                                                          __pos_onebit(
                                                            __pos_onebit(
                                                              1))))))))))))))))))))))))))))),
    self.alloc(
      Coq_Init_Datatypes_list::nil(
        PhantomData)),
    self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_pures_list(
      self.CertiCoq_Benchmarks_lib_vs_rsort(
        (),
        self.CertiCoq_Benchmarks_lib_vs_rev_cmp__curried()(
          self.CertiCoq_Benchmarks_lib_vs_compare_clause2__curried()),
        self.CertiCoq_Benchmarks_lib_vs_M_elements(
          self.CertiCoq_Benchmarks_lib_vs_M_filter(
            self.CertiCoq_Benchmarks_lib_vs_Superposition_not_taut__curried(),
            s)))))
}
fn CertiCoq_Benchmarks_lib_vs_Superposition_check_clauseset__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> __pair<__pair<__pair<&'a CertiCoq_Benchmarks_lib_vs_Superposition_superposition_result<'a>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>>, CertiCoq_Benchmarks_lib_vs_M_t<'a>>, CertiCoq_Benchmarks_lib_vs_M_t<'a>> {
  self.closure(move |s| {
    self.CertiCoq_Benchmarks_lib_vs_Superposition_check_clauseset(
      s)
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_cons(&'a self, s: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, e: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_enumeration<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_M_Raw_enumeration<'a> {
  match s {
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
      e
    },
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t, l, x, r) => {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_cons(
        l,
        self.alloc(
          CertiCoq_Benchmarks_lib_vs_M_Raw_enumeration::More(
            PhantomData,
            x,
            r,
            e)))
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_cons__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_enumeration<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_M_Raw_enumeration<'a> {
  self.closure(move |s| {
    self.closure(move |e| {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_cons(
        s,
        e)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_compare_more(&'a self, x1: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, cont: &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_enumeration<'a>) -> std::cmp::Ordering, e2: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_enumeration<'a>) -> std::cmp::Ordering {
  match e2 {
    &CertiCoq_Benchmarks_lib_vs_M_Raw_enumeration::End(_) => {
      std::cmp::Ordering::Greater
    },
    &CertiCoq_Benchmarks_lib_vs_M_Raw_enumeration::More(_, x2, r2, e22) => {
      match self.CertiCoq_Benchmarks_lib_vs_compare_clause_(
              x1,
              x2) {
        std::cmp::Ordering::Equal => {
          hint_app(cont)(self.CertiCoq_Benchmarks_lib_vs_M_Raw_cons(
                           r2,
                           e22))
        },
        std::cmp::Ordering::Less => {
          std::cmp::Ordering::Less
        },
        std::cmp::Ordering::Greater => {
          std::cmp::Ordering::Greater
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_compare_more__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_enumeration<'a>) -> std::cmp::Ordering) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_enumeration<'a>) -> std::cmp::Ordering {
  self.closure(move |x1| {
    self.closure(move |cont| {
      self.closure(move |e2| {
        self.CertiCoq_Benchmarks_lib_vs_M_Raw_compare_more(
          x1,
          cont,
          e2)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_compare_cont(&'a self, s1: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, cont: &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_enumeration<'a>) -> std::cmp::Ordering, e2: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_enumeration<'a>) -> std::cmp::Ordering {
  match s1 {
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
      hint_app(cont)(e2)
    },
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t, l1, x1, r1) => {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_compare_cont(
        l1,
        self.CertiCoq_Benchmarks_lib_vs_M_Raw_compare_more__curried()(
          x1)(
          self.CertiCoq_Benchmarks_lib_vs_M_Raw_compare_cont__curried()(
            r1)(
            cont)),
        e2)
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_compare_cont__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a dyn Fn(&'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_enumeration<'a>) -> std::cmp::Ordering) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_enumeration<'a>) -> std::cmp::Ordering {
  self.closure(move |s1| {
    self.closure(move |cont| {
      self.closure(move |e2| {
        self.CertiCoq_Benchmarks_lib_vs_M_Raw_compare_cont(
          s1,
          cont,
          e2)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_compare_end(&'a self, e2: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_enumeration<'a>) -> std::cmp::Ordering {
  match e2 {
    &CertiCoq_Benchmarks_lib_vs_M_Raw_enumeration::End(_) => {
      std::cmp::Ordering::Equal
    },
    &CertiCoq_Benchmarks_lib_vs_M_Raw_enumeration::More(_, e, t, e0) => {
      std::cmp::Ordering::Less
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_compare_end__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_enumeration<'a>) -> std::cmp::Ordering {
  self.closure(move |e2| {
    self.CertiCoq_Benchmarks_lib_vs_M_Raw_compare_end(
      e2)
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_compare(&'a self, s1: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, s2: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> std::cmp::Ordering {
  self.CertiCoq_Benchmarks_lib_vs_M_Raw_compare_cont(
    s1,
    self.CertiCoq_Benchmarks_lib_vs_M_Raw_compare_end__curried(),
    self.CertiCoq_Benchmarks_lib_vs_M_Raw_cons(
      s2,
      self.alloc(
        CertiCoq_Benchmarks_lib_vs_M_Raw_enumeration::End(
          PhantomData))))
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_compare__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> std::cmp::Ordering {
  self.closure(move |s1| {
    self.closure(move |s2| {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_compare(
        s1,
        s2)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_compare(&'a self, s: CertiCoq_Benchmarks_lib_vs_M_t<'a>, s2: CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> std::cmp::Ordering {
  self.CertiCoq_Benchmarks_lib_vs_M_Raw_compare(
    self.CertiCoq_Benchmarks_lib_vs_M_this(
      s),
    self.CertiCoq_Benchmarks_lib_vs_M_this(
      s2))
}
fn CertiCoq_Benchmarks_lib_vs_M_compare__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> std::cmp::Ordering {
  self.closure(move |s| {
    self.closure(move |s2| {
      self.CertiCoq_Benchmarks_lib_vs_M_compare(
        s,
        s2)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_skip_red(&'a self, t: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a> {
  match t {
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
      t
    },
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t0, t2, t1, t22) => {
      match t0 {
        &Coq_MSets_MSetRBT_color::Red(_) => {
          t2
        },
        &Coq_MSets_MSetRBT_color::Black(_) => {
          t
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_skip_red__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a> {
  self.closure(move |t| {
    self.CertiCoq_Benchmarks_lib_vs_M_Raw_skip_red(
      t)
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_skip_black(&'a self, t: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a> {
  match self.CertiCoq_Benchmarks_lib_vs_M_Raw_skip_red(
          t) {
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
      self.alloc(
        CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(
          PhantomData))
    },
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t0, t2, t1, t22) => {
      match t0 {
        &Coq_MSets_MSetRBT_color::Red(_) => {
          self.alloc(
            CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
              PhantomData,
              self.alloc(
                Coq_MSets_MSetRBT_color::Red(
                  PhantomData)),
              t2,
              t1,
              t22))
        },
        &Coq_MSets_MSetRBT_color::Black(_) => {
          t2
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_skip_black__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a> {
  self.closure(move |t| {
    self.CertiCoq_Benchmarks_lib_vs_M_Raw_skip_black(
      t)
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_compare_height(&'a self, s1x: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, s1: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, s2: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, s2x: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> std::cmp::Ordering {
  match self.CertiCoq_Benchmarks_lib_vs_M_Raw_skip_red(
          s1x) {
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
      match self.CertiCoq_Benchmarks_lib_vs_M_Raw_skip_red(
              s1) {
        &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
          match self.CertiCoq_Benchmarks_lib_vs_M_Raw_skip_red(
                  s2x) {
            &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
              std::cmp::Ordering::Equal
            },
            &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t, t0, t1, t2) => {
              std::cmp::Ordering::Less
            },
          }
        },
        &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t, s12, t0, t1) => {
          match self.CertiCoq_Benchmarks_lib_vs_M_Raw_skip_red(
                  s2) {
            &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
              std::cmp::Ordering::Equal
            },
            &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t2, s22, t3, t4) => {
              match self.CertiCoq_Benchmarks_lib_vs_M_Raw_skip_red(
                      s2x) {
                &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
                  std::cmp::Ordering::Equal
                },
                &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t5, s2x2, t6, t7) => {
                  self.CertiCoq_Benchmarks_lib_vs_M_Raw_compare_height(
                    self.alloc(
                      CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(
                        PhantomData)),
                    s12,
                    s22,
                    self.CertiCoq_Benchmarks_lib_vs_M_Raw_skip_black(
                      s2x2))
                },
              }
            },
          }
        },
      }
    },
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t, s1x2, t0, t1) => {
      match self.CertiCoq_Benchmarks_lib_vs_M_Raw_skip_red(
              s1) {
        &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
          match self.CertiCoq_Benchmarks_lib_vs_M_Raw_skip_red(
                  s2) {
            &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
              match self.CertiCoq_Benchmarks_lib_vs_M_Raw_skip_red(
                      s2x) {
                &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
                  std::cmp::Ordering::Greater
                },
                &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t2, t3, t4, t5) => {
                  std::cmp::Ordering::Less
                },
              }
            },
            &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t2, t3, t4, t5) => {
              match self.CertiCoq_Benchmarks_lib_vs_M_Raw_skip_red(
                      s2x) {
                &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
                  std::cmp::Ordering::Equal
                },
                &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t6, t7, t8, t9) => {
                  std::cmp::Ordering::Less
                },
              }
            },
          }
        },
        &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t2, s12, t3, t4) => {
          match self.CertiCoq_Benchmarks_lib_vs_M_Raw_skip_red(
                  s2) {
            &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
              std::cmp::Ordering::Greater
            },
            &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t5, s22, t6, t7) => {
              match self.CertiCoq_Benchmarks_lib_vs_M_Raw_skip_red(
                      s2x) {
                &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
                  self.CertiCoq_Benchmarks_lib_vs_M_Raw_compare_height(
                    self.CertiCoq_Benchmarks_lib_vs_M_Raw_skip_black(
                      s1x2),
                    s12,
                    s22,
                    self.alloc(
                      CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(
                        PhantomData)))
                },
                &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t8, s2x2, t9, t10) => {
                  self.CertiCoq_Benchmarks_lib_vs_M_Raw_compare_height(
                    self.CertiCoq_Benchmarks_lib_vs_M_Raw_skip_black(
                      s1x2),
                    s12,
                    s22,
                    self.CertiCoq_Benchmarks_lib_vs_M_Raw_skip_black(
                      s2x2))
                },
              }
            },
          }
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_compare_height__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> std::cmp::Ordering {
  self.closure(move |s1x| {
    self.closure(move |s1| {
      self.closure(move |s2| {
        self.closure(move |s2x| {
          self.CertiCoq_Benchmarks_lib_vs_M_Raw_compare_height(
            s1x,
            s1,
            s2,
            s2x)
        })
      })
    })
  })
}

fn Coq_Lists_List_rev_append<A: Copy>(&'a self, l: &'a Coq_Init_Datatypes_list<'a, A>, l2: &'a Coq_Init_Datatypes_list<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  match l {
    &Coq_Init_Datatypes_list::nil(_) => {
      l2
    },
    &Coq_Init_Datatypes_list::cons(_, a, l3) => {
      self.Coq_Lists_List_rev_append(
        l3,
        self.alloc(
          Coq_Init_Datatypes_list::cons(
            PhantomData,
            a,
            l2)))
    },
  }
}
fn Coq_Lists_List_rev_append__curried<A: Copy>(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> &'a Coq_Init_Datatypes_list<'a, A> {
  self.closure(move |l| {
    self.closure(move |l2| {
      self.Coq_Lists_List_rev_append(
        l,
        l2)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_union_list(&'a self, l1: &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>) -> &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>> {
  match l1 {
    &Coq_Init_Datatypes_list::nil(_) => {
      self.Coq_Lists_List_rev_append__curried()
    },
    &Coq_Init_Datatypes_list::cons(_, x, l12) => {
      let union_l1 = self.alloc(std::cell::Cell::new(None));
      union_l1.set(Some(
        self.closure(move |l2| {
          self.closure(move |acc| {
            match l2 {
              &Coq_Init_Datatypes_list::nil(_) => {
                self.Coq_Lists_List_rev_append(
                  l1,
                  acc)
              },
              &Coq_Init_Datatypes_list::cons(_, y, l22) => {
                match self.CertiCoq_Benchmarks_lib_vs_compare_clause_(
                        x,
                        y) {
                  std::cmp::Ordering::Equal => {
                    self.CertiCoq_Benchmarks_lib_vs_M_Raw_union_list(
                      l12)(
                      l22)(
                      self.alloc(
                        Coq_Init_Datatypes_list::cons(
                          PhantomData,
                          x,
                          acc)))
                  },
                  std::cmp::Ordering::Less => {
                    hint_app(hint_app(union_l1.get().unwrap())(l22))(self.alloc(
                                                                       Coq_Init_Datatypes_list::cons(
                                                                         PhantomData,
                                                                         y,
                                                                         acc)))
                  },
                  std::cmp::Ordering::Greater => {
                    self.CertiCoq_Benchmarks_lib_vs_M_Raw_union_list(
                      l12)(
                      l2)(
                      self.alloc(
                        Coq_Init_Datatypes_list::cons(
                          PhantomData,
                          x,
                          acc)))
                  },
                }
              },
            }
          })
        })));
      union_l1.get().unwrap()
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_union_list__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>>) -> &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>> {
  self.closure(move |l1| {
    self.CertiCoq_Benchmarks_lib_vs_M_Raw_union_list(
      l1)
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_rev_elements_aux(&'a self, acc: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>, s: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  match s {
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
      acc
    },
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t, l, x, r) => {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_rev_elements_aux(
        self.alloc(
          Coq_Init_Datatypes_list::cons(
            PhantomData,
            x,
            self.CertiCoq_Benchmarks_lib_vs_M_Raw_rev_elements_aux(
              acc,
              l))),
        r)
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_rev_elements_aux__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.closure(move |acc| {
    self.closure(move |s| {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_rev_elements_aux(
        acc,
        s)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_rev_elements(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.CertiCoq_Benchmarks_lib_vs_M_Raw_rev_elements_aux__curried()(
    self.alloc(
      Coq_Init_Datatypes_list::nil(
        PhantomData)))
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_linear_union(&'a self, s1: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, s2: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a> {
  self.CertiCoq_Benchmarks_lib_vs_M_Raw_treeify(
    self.CertiCoq_Benchmarks_lib_vs_M_Raw_union_list(
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_rev_elements()(
        s1))(
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_rev_elements()(
        s2))(
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))))
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_linear_union__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a> {
  self.closure(move |s1| {
    self.closure(move |s2| {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_linear_union(
        s1,
        s2)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_fold<A: Copy>(&'a self, A: (), f: &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>) -> &'a dyn Fn(A) -> A, t: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>, base: A) -> A {
  match t {
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
      base
    },
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t0, l, x, r) => {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_fold(
        (),
        f,
        r,
        hint_app(hint_app(f)(x))(self.CertiCoq_Benchmarks_lib_vs_M_Raw_fold(
                                   (),
                                   f,
                                   l,
                                   base)))
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_fold__curried<A: Copy>(&'a self) -> &'a dyn Fn(()) -> &'a dyn Fn(&'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>) -> &'a dyn Fn(A) -> A) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> &'a dyn Fn(A) -> A {
  self.closure(move |A| {
    self.closure(move |f| {
      self.closure(move |t| {
        self.closure(move |base| {
          self.CertiCoq_Benchmarks_lib_vs_M_Raw_fold(
            A,
            f,
            t,
            base)
        })
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_union(&'a self, t1: CertiCoq_Benchmarks_lib_vs_M_Raw_t<'a>, t2: CertiCoq_Benchmarks_lib_vs_M_Raw_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_Raw_t<'a> {
  match self.CertiCoq_Benchmarks_lib_vs_M_Raw_compare_height(
          t1,
          t1,
          t2,
          t2) {
    std::cmp::Ordering::Equal => {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_linear_union(
        t1,
        t2)
    },
    std::cmp::Ordering::Less => {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_fold(
        (),
        self.CertiCoq_Benchmarks_lib_vs_M_Raw_add__curried(),
        t1,
        t2)
    },
    std::cmp::Ordering::Greater => {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_fold(
        (),
        self.CertiCoq_Benchmarks_lib_vs_M_Raw_add__curried(),
        t2,
        t1)
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_union__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_Raw_t<'a>) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_Raw_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_Raw_t<'a> {
  self.closure(move |t1| {
    self.closure(move |t2| {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_union(
        t1,
        t2)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_union(&'a self, s: CertiCoq_Benchmarks_lib_vs_M_t<'a>, s2: CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.alloc(
    CertiCoq_Benchmarks_lib_vs_M_t_::Mkt(
      PhantomData,
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_union(
        self.CertiCoq_Benchmarks_lib_vs_M_this(
          s),
        self.CertiCoq_Benchmarks_lib_vs_M_this(
          s2))))
}
fn CertiCoq_Benchmarks_lib_vs_M_union__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.closure(move |s| {
    self.closure(move |s2| {
      self.CertiCoq_Benchmarks_lib_vs_M_union(
        s,
        s2)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_fold<A: Copy>(&'a self, f: &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_elt<'a>) -> &'a dyn Fn(A) -> A, s: CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> &'a dyn Fn(A) -> A {
  self.CertiCoq_Benchmarks_lib_vs_M_Raw_fold__curried()(
    ())(
    f)(
    self.CertiCoq_Benchmarks_lib_vs_M_this(
      s))
}
fn CertiCoq_Benchmarks_lib_vs_M_fold__curried<A: Copy>(&'a self) -> &'a dyn Fn(&'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_elt<'a>) -> &'a dyn Fn(A) -> A) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> &'a dyn Fn(A) -> A {
  self.closure(move |f| {
    self.closure(move |s| {
      self.CertiCoq_Benchmarks_lib_vs_M_fold(
        f,
        s)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_VeriStar_sublistg<A: Copy>(&'a self, cmp: &'a dyn Fn(A) -> &'a dyn Fn(A) -> std::cmp::Ordering, l1: &'a Coq_Init_Datatypes_list<'a, A>, l2: &'a Coq_Init_Datatypes_list<'a, A>) -> bool {
  match l1 {
    &Coq_Init_Datatypes_list::nil(_) => {
      true
    },
    &Coq_Init_Datatypes_list::cons(_, a, l12) => {
      match l2 {
        &Coq_Init_Datatypes_list::nil(_) => {
          false
        },
        &Coq_Init_Datatypes_list::cons(_, b, l22) => {
          __andb!(
            self.CertiCoq_Benchmarks_lib_vs_isEq(
              hint_app(hint_app(cmp)(a))(b)),
            self.CertiCoq_Benchmarks_lib_vs_VeriStar_sublistg(
              cmp,
              l12,
              l22))
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_VeriStar_sublistg__curried<A: Copy>(&'a self) -> &'a dyn Fn(&'a dyn Fn(A) -> &'a dyn Fn(A) -> std::cmp::Ordering) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> bool {
  self.closure(move |cmp| {
    self.closure(move |l1| {
      self.closure(move |l2| {
        self.CertiCoq_Benchmarks_lib_vs_VeriStar_sublistg(
          cmp,
          l1,
          l2)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_VeriStar_sublist<A: Copy>(&'a self, cmp: &'a dyn Fn(A) -> &'a dyn Fn(A) -> std::cmp::Ordering, l1: &'a Coq_Init_Datatypes_list<'a, A>, l2: &'a Coq_Init_Datatypes_list<'a, A>) -> bool {
  match l1 {
    &Coq_Init_Datatypes_list::nil(_) => {
      true
    },
    &Coq_Init_Datatypes_list::cons(_, a, l12) => {
      match l2 {
        &Coq_Init_Datatypes_list::nil(_) => {
          false
        },
        &Coq_Init_Datatypes_list::cons(_, b, l22) => {
          match self.CertiCoq_Benchmarks_lib_vs_isEq(
                  hint_app(hint_app(cmp)(a))(b)) {
            true => {
              self.CertiCoq_Benchmarks_lib_vs_VeriStar_sublistg(
                cmp,
                l12,
                l22)
            },
            false => {
              self.CertiCoq_Benchmarks_lib_vs_VeriStar_sublist(
                cmp,
                l1,
                l22)
            },
          }
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_VeriStar_sublist__curried<A: Copy>(&'a self) -> &'a dyn Fn(&'a dyn Fn(A) -> &'a dyn Fn(A) -> std::cmp::Ordering) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, A>) -> bool {
  self.closure(move |cmp| {
    self.closure(move |l1| {
      self.closure(move |l2| {
        self.CertiCoq_Benchmarks_lib_vs_VeriStar_sublist(
          cmp,
          l1,
          l2)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_VeriStar_impl_pure_clause(&'a self, c: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, d: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> bool {
  match c {
    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma, delta, priority) => {
      match d {
        &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma2, delta2, priority0) => {
          __andb!(
            self.CertiCoq_Benchmarks_lib_vs_VeriStar_sublist(
              self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
              gamma,
              gamma2),
            self.CertiCoq_Benchmarks_lib_vs_VeriStar_sublist(
              self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
              delta,
              delta2))
        },
        &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma0, delta0, sigma) => {
          false
        },
        &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma0, sigma, delta0) => {
          false
        },
      }
    },
    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
      false
    },
    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
      false
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_VeriStar_impl_pure_clause__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> bool {
  self.closure(move |c| {
    self.closure(move |d| {
      self.CertiCoq_Benchmarks_lib_vs_VeriStar_impl_pure_clause(
        c,
        d)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_VeriStar_relim1(&'a self, c: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, s: CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.CertiCoq_Benchmarks_lib_vs_M_filter(
    self.closure(move |d| {
      self.Coq_Init_Datatypes_negb(
        self.CertiCoq_Benchmarks_lib_vs_VeriStar_impl_pure_clause(
          c,
          d))
    }),
    s)
}
fn CertiCoq_Benchmarks_lib_vs_VeriStar_relim1__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.closure(move |c| {
    self.closure(move |s| {
      self.CertiCoq_Benchmarks_lib_vs_VeriStar_relim1(
        c,
        s)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_VeriStar_incorp(&'a self, s: CertiCoq_Benchmarks_lib_vs_M_t<'a>, t: CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.CertiCoq_Benchmarks_lib_vs_M_union(
    s,
    self.CertiCoq_Benchmarks_lib_vs_M_fold(
      self.closure(move |c| {
        self.closure(move |t0| {
          self.CertiCoq_Benchmarks_lib_vs_VeriStar_relim1(
            c,
            t0)
        })
      }),
      s)(
      t))
}
fn CertiCoq_Benchmarks_lib_vs_VeriStar_incorp__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.closure(move |s| {
    self.closure(move |t| {
      self.CertiCoq_Benchmarks_lib_vs_VeriStar_incorp(
        s,
        t)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_wf_set(&'a self, s: CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  s
}
fn CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_wf_set__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.closure(move |s| {
    self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_wf_set(
      s)
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well1_2(&'a self, sc: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>> {
  match sc {
    &Coq_Init_Datatypes_list::nil(_) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
    &Coq_Init_Datatypes_list::cons(_, s, sc2) => {
      match s {
        &CertiCoq_Benchmarks_lib_vs_space_atom::Next(_, e, e0) => {
          match e {
            &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
              self.alloc(
                Coq_Init_Datatypes_list::cons(
                  PhantomData,
                  self.alloc(
                    Coq_Init_Datatypes_list::nil(
                      PhantomData)),
                  self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well1_2(
                    sc2)))
            },
            &CertiCoq_Benchmarks_lib_vs_expr::Var(_, v) => {
              self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well1_2(
                sc2)
            },
          }
        },
        &CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(_, e, y) => {
          match e {
            &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
              self.alloc(
                Coq_Init_Datatypes_list::cons(
                  PhantomData,
                  self.alloc(
                    Coq_Init_Datatypes_list::cons(
                      PhantomData,
                      self.alloc(
                        CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                          PhantomData,
                          y,
                          self.alloc(
                            CertiCoq_Benchmarks_lib_vs_expr::Nil(
                              PhantomData)))),
                      self.alloc(
                        Coq_Init_Datatypes_list::nil(
                          PhantomData)))),
                  self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well1_2(
                    sc2)))
            },
            &CertiCoq_Benchmarks_lib_vs_expr::Var(_, v) => {
              self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well1_2(
                sc2)
            },
          }
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well1_2__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>> {
  self.closure(move |sc| {
    self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well1_2(
      sc)
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom(&'a self, x: Coq_PArith_BinPosDef_Pos_t<'a>, sc: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> bool {
  match sc {
    &Coq_Init_Datatypes_list::nil(_) => {
      false
    },
    &Coq_Init_Datatypes_list::cons(_, s, sc2) => {
      match s {
        &CertiCoq_Benchmarks_lib_vs_space_atom::Next(_, e, y) => {
          match e {
            &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
              self.CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom(
                x,
                sc2)
            },
            &CertiCoq_Benchmarks_lib_vs_expr::Var(_, x2) => {
              match self.Coq_PArith_BinPos_Pos_eq_dec(
                      x,
                      x2) {
                &Coq_Init_Specif_sumbool::left(_) => {
                  true
                },
                &Coq_Init_Specif_sumbool::right(_) => {
                  self.CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom(
                    x,
                    sc2)
                },
              }
            },
          }
        },
        &CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(_, e, e0) => {
          self.CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom(
            x,
            sc2)
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom__curried(&'a self) -> &'a dyn Fn(Coq_PArith_BinPosDef_Pos_t<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> bool {
  self.closure(move |x| {
    self.closure(move |sc| {
      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom(
        x,
        sc)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well3(&'a self, sc: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>> {
  match sc {
    &Coq_Init_Datatypes_list::nil(_) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
    &Coq_Init_Datatypes_list::cons(_, s, sc2) => {
      match s {
        &CertiCoq_Benchmarks_lib_vs_space_atom::Next(_, e, y) => {
          match e {
            &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
              self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well3(
                sc2)
            },
            &CertiCoq_Benchmarks_lib_vs_expr::Var(_, x) => {
              match self.CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom(
                      x,
                      sc2) {
                true => {
                  self.alloc(
                    Coq_Init_Datatypes_list::cons(
                      PhantomData,
                      self.alloc(
                        Coq_Init_Datatypes_list::nil(
                          PhantomData)),
                      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well3(
                        sc2)))
                },
                false => {
                  self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well3(
                    sc2)
                },
              }
            },
          }
        },
        &CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(_, e, e0) => {
          self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well3(
            sc2)
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well3__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>> {
  self.closure(move |sc| {
    self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well3(
      sc)
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_lseg_in_dom_atoms(&'a self, x: Coq_PArith_BinPosDef_Pos_t<'a>, sc: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>> {
  match sc {
    &Coq_Init_Datatypes_list::nil(_) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
    &Coq_Init_Datatypes_list::cons(_, s, sc2) => {
      match s {
        &CertiCoq_Benchmarks_lib_vs_space_atom::Next(_, e, e0) => {
          self.CertiCoq_Benchmarks_lib_vs_HeapResolve_lseg_in_dom_atoms(
            x,
            sc2)
        },
        &CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(_, x0, y0) => {
          match x0 {
            &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
              self.CertiCoq_Benchmarks_lib_vs_HeapResolve_lseg_in_dom_atoms(
                x,
                sc2)
            },
            &CertiCoq_Benchmarks_lib_vs_expr::Var(_, x2) => {
              match self.Coq_PArith_BinPos_Pos_eq_dec(
                      x,
                      x2) {
                &Coq_Init_Specif_sumbool::left(_) => {
                  self.alloc(
                    Coq_Init_Datatypes_list::cons(
                      PhantomData,
                      self.CertiCoq_Benchmarks_lib_vs_order_eqv_pure_atom(
                        self.alloc(
                          CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                            PhantomData,
                            x0,
                            y0))),
                      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_lseg_in_dom_atoms(
                        x,
                        sc2)))
                },
                &Coq_Init_Specif_sumbool::right(_) => {
                  self.CertiCoq_Benchmarks_lib_vs_HeapResolve_lseg_in_dom_atoms(
                    x,
                    sc2)
                },
              }
            },
          }
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_lseg_in_dom_atoms__curried(&'a self) -> &'a dyn Fn(Coq_PArith_BinPosDef_Pos_t<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>> {
  self.closure(move |x| {
    self.closure(move |sc| {
      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_lseg_in_dom_atoms(
        x,
        sc)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well4_5(&'a self, sc: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>> {
  match sc {
    &Coq_Init_Datatypes_list::nil(_) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
    &Coq_Init_Datatypes_list::cons(_, a, sc2) => {
      match a {
        &CertiCoq_Benchmarks_lib_vs_space_atom::Next(_, e, y) => {
          match e {
            &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
              self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well4_5(
                sc2)
            },
            &CertiCoq_Benchmarks_lib_vs_expr::Var(_, x) => {
              let atms =
                self.Coq_Lists_List_map(
                  self.closure(move |a2| {
                    self.alloc(
                      Coq_Init_Datatypes_list::cons(
                        PhantomData,
                        a2,
                        self.alloc(
                          Coq_Init_Datatypes_list::nil(
                            PhantomData))))
                  }),
                  self.CertiCoq_Benchmarks_lib_vs_HeapResolve_lseg_in_dom_atoms(
                    x,
                    sc2));
              self.Coq_Init_Datatypes_app(
                atms,
                self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well4_5(
                  sc2))
            },
          }
        },
        &CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(_, x0, y) => {
          match x0 {
            &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
              self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well4_5(
                sc2)
            },
            &CertiCoq_Benchmarks_lib_vs_expr::Var(_, x) => {
              let l0 =
                self.CertiCoq_Benchmarks_lib_vs_HeapResolve_lseg_in_dom_atoms(
                  x,
                  sc2);
              match l0 {
                &Coq_Init_Datatypes_list::nil(_) => {
                  self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well4_5(
                    sc2)
                },
                &Coq_Init_Datatypes_list::cons(_, p, l) => {
                  let atms =
                    self.Coq_Lists_List_map(
                      self.closure(move |a2| {
                        self.CertiCoq_Benchmarks_lib_vs_normalize_atoms(
                          self.alloc(
                            Coq_Init_Datatypes_list::cons(
                              PhantomData,
                              self.alloc(
                                CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                                  PhantomData,
                                  x0,
                                  y)),
                              self.alloc(
                                Coq_Init_Datatypes_list::cons(
                                  PhantomData,
                                  a2,
                                  self.alloc(
                                    Coq_Init_Datatypes_list::nil(
                                      PhantomData)))))))
                      }),
                      l0);
                  self.Coq_Init_Datatypes_app(
                    atms,
                    self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well4_5(
                      sc2))
                },
              }
            },
          }
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well4_5__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>> {
  self.closure(move |sc| {
    self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well4_5(
      sc)
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well(&'a self, sc: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>> {
  self.Coq_Init_Datatypes_app(
    self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well1_2(
      sc),
    self.Coq_Init_Datatypes_app(
      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well3(
        sc),
      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well4_5(
        sc)))
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>>> {
  self.closure(move |sc| {
    self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well(
      sc)
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_do_wellformed(&'a self, sc: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  match sc {
    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma, delta, priority) => {
      self.CertiCoq_Benchmarks_lib_vs_M_empty()
    },
    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
      let sigma2 =
        self.CertiCoq_Benchmarks_lib_vs_rsort(
          (),
          self.CertiCoq_Benchmarks_lib_vs_rev_cmp__curried()(
            self.CertiCoq_Benchmarks_lib_vs_compare_space_atom__curried()),
          sigma);
      self.CertiCoq_Benchmarks_lib_vs_clause_list2set(
        self.Coq_Lists_List_map(
          self.closure(move |ats| {
            self.CertiCoq_Benchmarks_lib_vs_mkPureClause(
              gamma,
              self.CertiCoq_Benchmarks_lib_vs_normalize_atoms(
                self.Coq_Init_Datatypes_app(
                  ats,
                  delta)))
          }),
          self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_well(
            sigma2)))
    },
    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
      self.CertiCoq_Benchmarks_lib_vs_M_empty()
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_do_wellformed__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.closure(move |sc| {
    self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_wellformed(
      sc)
  })
}

fn CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_spatial_model(&'a self, c: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_clause<'a> {
  c
}
fn CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_spatial_model__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_clause<'a> {
  self.closure(move |c| {
    self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_spatial_model(
      c)
  })
}

fn CertiCoq_Benchmarks_lib_vs_eq_var(&'a self, i: u64, j: u64) -> bool {
  self.CertiCoq_Benchmarks_lib_vs_isEq(
    self.Coq_PArith_BinPosDef_Pos_compare()(
      i)(
      j))
}
fn CertiCoq_Benchmarks_lib_vs_eq_var__curried(&'a self) -> &'a dyn Fn(u64) -> &'a dyn Fn(u64) -> bool {
  self.closure(move |i| {
    self.closure(move |j| {
      self.CertiCoq_Benchmarks_lib_vs_eq_var(
        i,
        j)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_drop_reflex_lseg(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>> {
  self.Coq_Lists_List_filter__curried()(
    self.closure(move |sa| {
      match sa {
        &CertiCoq_Benchmarks_lib_vs_space_atom::Next(_, e, e0) => {
          true
        },
        &CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(_, e, e0) => {
          match e {
            &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
              match e0 {
                &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
                  false
                },
                &CertiCoq_Benchmarks_lib_vs_expr::Var(_, v) => {
                  true
                },
              }
            },
            &CertiCoq_Benchmarks_lib_vs_expr::Var(_, x) => {
              match e0 {
                &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
                  true
                },
                &CertiCoq_Benchmarks_lib_vs_expr::Var(_, y) => {
                  self.Coq_Init_Datatypes_negb(
                    self.CertiCoq_Benchmarks_lib_vs_eq_var(
                      x,
                      y))
                },
              }
            },
          }
        },
      }
    }))
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_normalize2_4(&'a self, sc: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_clause<'a> {
  match sc {
    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma, delta, priority) => {
      sc
    },
    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
      self.alloc(
        CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(
          PhantomData,
          gamma,
          delta,
          self.CertiCoq_Benchmarks_lib_vs_drop_reflex_lseg()(
            sigma)))
    },
    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
      self.alloc(
        CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(
          PhantomData,
          gamma,
          self.CertiCoq_Benchmarks_lib_vs_drop_reflex_lseg()(
            sigma),
          delta))
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_normalize2_4__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_clause<'a> {
  self.closure(move |sc| {
    self.CertiCoq_Benchmarks_lib_vs_HeapResolve_normalize2_4(
      sc)
  })
}

fn CertiCoq_Benchmarks_lib_vs_subst_space(&'a self, i: CertiCoq_Benchmarks_lib_vs_var<'a>, t: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, a: &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a> {
  match a {
    &CertiCoq_Benchmarks_lib_vs_space_atom::Next(_, t1, t2) => {
      self.alloc(
        CertiCoq_Benchmarks_lib_vs_space_atom::Next(
          PhantomData,
          self.CertiCoq_Benchmarks_lib_vs_subst_expr(
            i,
            t,
            t1),
          self.CertiCoq_Benchmarks_lib_vs_subst_expr(
            i,
            t,
            t2)))
    },
    &CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(_, t1, t2) => {
      self.alloc(
        CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
          PhantomData,
          self.CertiCoq_Benchmarks_lib_vs_subst_expr(
            i,
            t,
            t1),
          self.CertiCoq_Benchmarks_lib_vs_subst_expr(
            i,
            t,
            t2)))
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_subst_space__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_var<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a> {
  self.closure(move |i| {
    self.closure(move |t| {
      self.closure(move |a| {
        self.CertiCoq_Benchmarks_lib_vs_subst_space(
          i,
          t,
          a)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_subst_spaces(&'a self, i: CertiCoq_Benchmarks_lib_vs_var<'a>, t: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>> {
  self.Coq_Lists_List_map__curried()(
    self.CertiCoq_Benchmarks_lib_vs_subst_space__curried()(
      i)(
      t))
}
fn CertiCoq_Benchmarks_lib_vs_subst_spaces__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_var<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>> {
  self.closure(move |i| {
    self.closure(move |t| {
      self.CertiCoq_Benchmarks_lib_vs_subst_spaces(
        i,
        t)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_normalize1_3(&'a self, pc: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, sc: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_clause<'a> {
  match pc {
    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma, delta0, priority) => {
      match delta0 {
        &Coq_Init_Datatypes_list::nil(_) => {
          sc
        },
        &Coq_Init_Datatypes_list::cons(_, p, delta) => {
          match p {
            &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, e, y) => {
              match e {
                &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
                  sc
                },
                &CertiCoq_Benchmarks_lib_vs_expr::Var(_, x) => {
                  match sc {
                    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma0, delta1, priority0) => {
                      sc
                    },
                    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma2, delta2, sigma) => {
                      self.alloc(
                        CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(
                          PhantomData,
                          self.CertiCoq_Benchmarks_lib_vs_rsort_uniq(
                            (),
                            self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
                            self.Coq_Init_Datatypes_app(
                              gamma,
                              gamma2)),
                          self.CertiCoq_Benchmarks_lib_vs_rsort_uniq(
                            (),
                            self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
                            self.Coq_Init_Datatypes_app(
                              delta,
                              delta2)),
                          self.CertiCoq_Benchmarks_lib_vs_subst_spaces(
                            x,
                            y)(
                            sigma)))
                    },
                    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma2, sigma, delta2) => {
                      self.alloc(
                        CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(
                          PhantomData,
                          self.CertiCoq_Benchmarks_lib_vs_rsort_uniq(
                            (),
                            self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
                            self.Coq_Init_Datatypes_app(
                              gamma,
                              gamma2)),
                          self.CertiCoq_Benchmarks_lib_vs_subst_spaces(
                            x,
                            y)(
                            sigma),
                          self.CertiCoq_Benchmarks_lib_vs_rsort_uniq(
                            (),
                            self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
                            self.Coq_Init_Datatypes_app(
                              delta,
                              delta2))))
                    },
                  }
                },
              }
            },
          }
        },
      }
    },
    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
      sc
    },
    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
      sc
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_normalize1_3__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_clause<'a> {
  self.closure(move |pc| {
    self.closure(move |sc| {
      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_normalize1_3(
        pc,
        sc)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_norm(&'a self, s: CertiCoq_Benchmarks_lib_vs_M_t<'a>, sc: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_clause<'a> {
  self.CertiCoq_Benchmarks_lib_vs_HeapResolve_normalize2_4(
    self.Coq_Lists_List_fold_right(
      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_normalize1_3__curried(),
      sc,
      self.CertiCoq_Benchmarks_lib_vs_rsort(
        (),
        self.CertiCoq_Benchmarks_lib_vs_rev_cmp__curried()(
          self.CertiCoq_Benchmarks_lib_vs_compare_clause2__curried()),
        self.CertiCoq_Benchmarks_lib_vs_M_elements(
          s))))
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_norm__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_clause<'a> {
  self.closure(move |s| {
    self.closure(move |sc| {
      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_norm(
        s,
        sc)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_clause_in_space(&'a self, c: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, atm: &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a> {
  match c {
    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma, delta, priority) => {
      match gamma {
        &Coq_Init_Datatypes_list::nil(_) => {
          match delta {
            &Coq_Init_Datatypes_list::nil(_) => {
              atm
            },
            &Coq_Init_Datatypes_list::cons(_, p, l) => {
              match p {
                &CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(_, s, t) => {
                  match l {
                    &Coq_Init_Datatypes_list::nil(_) => {
                      self.CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_in_space(
                        s,
                        t,
                        atm)
                    },
                    &Coq_Init_Datatypes_list::cons(_, p0, l0) => {
                      atm
                    },
                  }
                },
              }
            },
          }
        },
        &Coq_Init_Datatypes_list::cons(_, p, l) => {
          atm
        },
      }
    },
    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
      atm
    },
    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
      atm
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_clause_in_space__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a> {
  self.closure(move |c| {
    self.closure(move |atm| {
      self.CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_clause_in_space(
        c,
        atm)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_simplify_atoms(&'a self, l: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>, atms: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>> {
  self.Coq_Lists_List_fold_left(
    self.closure(move |atms2| {
      self.closure(move |d| {
        self.Coq_Lists_List_map(
          self.CertiCoq_Benchmarks_lib_vs_Superposition_rewrite_clause_in_space__curried()(
            d),
          atms2)
      })
    }),
    l,
    atms)
}
fn CertiCoq_Benchmarks_lib_vs_Superposition_simplify_atoms__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>> {
  self.closure(move |l| {
    self.closure(move |atms| {
      self.CertiCoq_Benchmarks_lib_vs_Superposition_simplify_atoms(
        l,
        atms)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_Superposition_is_model_of_PI(&'a self, R: CertiCoq_Benchmarks_lib_vs_Superposition_model<'a>, nc: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> bool {
  match nc {
    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma, delta, priority) => {
      false
    },
    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
      false
    },
    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, pi_plus, sigma, pi_minus) => {
      match self.Coq_Lists_List_fold_right(
              self.closure(move |ve| {
                self.CertiCoq_Benchmarks_lib_vs_subst_pures_delete(
                  self.Coq_Init_Datatypes_fst(
                    ve),
                  self.Coq_Init_Datatypes_snd(
                    ve))
              }),
              self.CertiCoq_Benchmarks_lib_vs_remove_trivial_atoms()(
                pi_plus),
              R) {
        &Coq_Init_Datatypes_list::nil(_) => {
          self.Coq_Lists_List_forallb(
            self.CertiCoq_Benchmarks_lib_vs_nonreflex_atom__curried(),
            self.Coq_Lists_List_fold_right(
              self.closure(move |ve| {
                self.CertiCoq_Benchmarks_lib_vs_subst_pures__curried()(
                  self.Coq_Init_Datatypes_fst(
                    ve))(
                  self.Coq_Init_Datatypes_snd(
                    ve))
              }),
              pi_minus,
              R))
        },
        &Coq_Init_Datatypes_list::cons(_, p, l) => {
          false
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_Superposition_is_model_of_PI__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_Superposition_model<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> bool {
  self.closure(move |R| {
    self.closure(move |nc| {
      self.CertiCoq_Benchmarks_lib_vs_Superposition_is_model_of_PI(
        R,
        nc)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_unfold_set(&'a self, s: CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  s
}
fn CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_unfold_set__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.closure(move |s| {
    self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_unfold_set(
      s)
  })
}

fn CertiCoq_Benchmarks_lib_vs_VeriStar_pures(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.CertiCoq_Benchmarks_lib_vs_M_filter__curried()(
    self.CertiCoq_Benchmarks_lib_vs_VeriStar_pureb__curried())
}

fn CertiCoq_Benchmarks_lib_vs_eq_space_atomlist(&'a self, a: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>, b: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> bool {
  self.CertiCoq_Benchmarks_lib_vs_isEq(
    self.CertiCoq_Benchmarks_lib_vs_compare_list(
      (),
      self.CertiCoq_Benchmarks_lib_vs_compare_space_atom__curried(),
      a,
      b))
}
fn CertiCoq_Benchmarks_lib_vs_eq_space_atomlist__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> bool {
  self.closure(move |a| {
    self.closure(move |b| {
      self.CertiCoq_Benchmarks_lib_vs_eq_space_atomlist(
        a,
        b)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_singleton(&'a self, k: CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a> {
  self.alloc(
    CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(
      PhantomData,
      self.alloc(
        Coq_MSets_MSetRBT_color::Black(
          PhantomData)),
      self.alloc(
        CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(
          PhantomData)),
      k,
      self.alloc(
        CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(
          PhantomData))))
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_singleton__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_Raw_elt<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a> {
  self.closure(move |k| {
    self.CertiCoq_Benchmarks_lib_vs_M_Raw_singleton(
      k)
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_singleton(&'a self, x: CertiCoq_Benchmarks_lib_vs_M_elt<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.alloc(
    CertiCoq_Benchmarks_lib_vs_M_t_::Mkt(
      PhantomData,
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_singleton(
        x)))
}
fn CertiCoq_Benchmarks_lib_vs_M_singleton__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_elt<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.closure(move |x| {
    self.CertiCoq_Benchmarks_lib_vs_M_singleton(
      x)
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_spatial_resolution(&'a self, pc: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, nc: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  match pc {
    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma, delta, priority) => {
      self.CertiCoq_Benchmarks_lib_vs_M_empty()
    },
    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma) => {
      match nc {
        &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma2, delta2, priority) => {
          self.CertiCoq_Benchmarks_lib_vs_M_empty()
        },
        &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma2, delta2, sigma2) => {
          self.CertiCoq_Benchmarks_lib_vs_M_empty()
        },
        &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma2, sigma2, delta2) => {
          match self.CertiCoq_Benchmarks_lib_vs_eq_space_atomlist(
                  self.CertiCoq_Benchmarks_lib_vs_rsort(
                    (),
                    self.CertiCoq_Benchmarks_lib_vs_compare_space_atom__curried(),
                    sigma2),
                  self.CertiCoq_Benchmarks_lib_vs_rsort(
                    (),
                    self.CertiCoq_Benchmarks_lib_vs_compare_space_atom__curried(),
                    sigma)) {
            true => {
              self.CertiCoq_Benchmarks_lib_vs_M_singleton(
                self.CertiCoq_Benchmarks_lib_vs_order_eqv_clause(
                  self.CertiCoq_Benchmarks_lib_vs_mkPureClause(
                    self.Coq_Init_Datatypes_app(
                      gamma2,
                      gamma),
                    self.Coq_Init_Datatypes_app(
                      delta2,
                      delta))))
            },
            false => {
              self.CertiCoq_Benchmarks_lib_vs_M_empty()
            },
          }
        },
      }
    },
    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
      self.CertiCoq_Benchmarks_lib_vs_M_empty()
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_spatial_resolution__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.closure(move |pc| {
    self.closure(move |nc| {
      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_spatial_resolution(
        pc,
        nc)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_Raw_mem(&'a self, x: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, t: &'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> bool {
  match t {
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Leaf(_) => {
      false
    },
    &CertiCoq_Benchmarks_lib_vs_M_Raw_tree::Node(_, t0, l, k, r) => {
      match self.CertiCoq_Benchmarks_lib_vs_compare_clause_(
              x,
              k) {
        std::cmp::Ordering::Equal => {
          true
        },
        std::cmp::Ordering::Less => {
          self.CertiCoq_Benchmarks_lib_vs_M_Raw_mem(
            x,
            l)
        },
        std::cmp::Ordering::Greater => {
          self.CertiCoq_Benchmarks_lib_vs_M_Raw_mem(
            x,
            r)
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_M_Raw_mem__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_M_Raw_tree<'a>) -> bool {
  self.closure(move |x| {
    self.closure(move |t| {
      self.CertiCoq_Benchmarks_lib_vs_M_Raw_mem(
        x,
        t)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_M_mem(&'a self, x: CertiCoq_Benchmarks_lib_vs_M_elt<'a>, s: CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> bool {
  self.CertiCoq_Benchmarks_lib_vs_M_Raw_mem(
    x,
    self.CertiCoq_Benchmarks_lib_vs_M_this(
      s))
}
fn CertiCoq_Benchmarks_lib_vs_M_mem__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_elt<'a>) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> bool {
  self.closure(move |x| {
    self.closure(move |s| {
      self.CertiCoq_Benchmarks_lib_vs_M_mem(
        x,
        s)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_mem_add(&'a self, x: CertiCoq_Benchmarks_lib_vs_M_elt<'a>, s: CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> Option<CertiCoq_Benchmarks_lib_vs_M_t<'a>> {
  match self.CertiCoq_Benchmarks_lib_vs_M_mem(
          x,
          s) {
    true => {
      None
    },
    false => {
      Some(
        self.CertiCoq_Benchmarks_lib_vs_M_add(
          x,
          s))
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_mem_add__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_elt<'a>) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> Option<CertiCoq_Benchmarks_lib_vs_M_t<'a>> {
  self.closure(move |x| {
    self.closure(move |s| {
      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_mem_add(
        x,
        s)
    })
  })
}

fn Coq_Program_Basics_flip<A: Copy, B: Copy, C: Copy>(&'a self, f: &'a dyn Fn(A) -> &'a dyn Fn(B) -> C, x: B, y: A) -> C {
  hint_app(hint_app(f)(y))(x)
}
fn Coq_Program_Basics_flip__curried<A: Copy, B: Copy, C: Copy>(&'a self) -> &'a dyn Fn(&'a dyn Fn(A) -> &'a dyn Fn(B) -> C) -> &'a dyn Fn(B) -> &'a dyn Fn(A) -> C {
  self.closure(move |f| {
    self.closure(move |x| {
      self.closure(move |y| {
        self.Coq_Program_Basics_flip(
          f,
          x,
          y)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_add_list_to_set_simple(&'a self, l: &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_elt<'a>>, s: CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.Coq_Lists_List_fold_left(
    self.Coq_Program_Basics_flip__curried()(
      self.CertiCoq_Benchmarks_lib_vs_M_add__curried()),
    l,
    s)
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_add_list_to_set_simple__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_elt<'a>>) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.closure(move |l| {
    self.closure(move |s| {
      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_add_list_to_set_simple(
        l,
        s)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_add_list_to_set(&'a self, l: &'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_elt<'a>>, s: CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> Option<CertiCoq_Benchmarks_lib_vs_M_t<'a>> {
  match l {
    &Coq_Init_Datatypes_list::nil(_) => {
      None
    },
    &Coq_Init_Datatypes_list::cons(_, x, xs) => {
      match self.CertiCoq_Benchmarks_lib_vs_HeapResolve_mem_add(
              x,
              s) {
        Some(s2) => {
          Some(
            self.CertiCoq_Benchmarks_lib_vs_HeapResolve_add_list_to_set_simple(
              xs,
              s2))
        },
        None => {
          self.CertiCoq_Benchmarks_lib_vs_HeapResolve_add_list_to_set(
            xs,
            s)
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_add_list_to_set__curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, CertiCoq_Benchmarks_lib_vs_M_elt<'a>>) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> Option<CertiCoq_Benchmarks_lib_vs_M_t<'a>> {
  self.closure(move |l| {
    self.closure(move |s| {
      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_add_list_to_set(
        l,
        s)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom1(&'a self, x: Coq_PArith_BinPosDef_Pos_t<'a>, y: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, sc: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> bool {
  match sc {
    &Coq_Init_Datatypes_list::nil(_) => {
      false
    },
    &Coq_Init_Datatypes_list::cons(_, s, sc2) => {
      match s {
        &CertiCoq_Benchmarks_lib_vs_space_atom::Next(_, e, y2) => {
          match e {
            &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
              self.CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom1(
                x,
                y,
                sc2)
            },
            &CertiCoq_Benchmarks_lib_vs_expr::Var(_, x2) => {
              match self.Coq_PArith_BinPos_Pos_eq_dec(
                      x,
                      x2) {
                &Coq_Init_Specif_sumbool::left(_) => {
                  match self.CertiCoq_Benchmarks_lib_vs_expr_eq(
                          y,
                          y2) {
                    true => {
                      true
                    },
                    false => {
                      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom1(
                        x,
                        y,
                        sc2)
                    },
                  }
                },
                &Coq_Init_Specif_sumbool::right(_) => {
                  self.CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom1(
                    x,
                    y,
                    sc2)
                },
              }
            },
          }
        },
        &CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(_, e, e0) => {
          self.CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom1(
            x,
            y,
            sc2)
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom1__curried(&'a self) -> &'a dyn Fn(Coq_PArith_BinPosDef_Pos_t<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> bool {
  self.closure(move |x| {
    self.closure(move |y| {
      self.closure(move |sc| {
        self.CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom1(
          x,
          y,
          sc)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding1_(&'a self, sigma0: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>, sigma1: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>, sigma2: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, __pair<&'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>>> {
  match sigma2 {
    &Coq_Init_Datatypes_list::nil(_) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
    &Coq_Init_Datatypes_list::cons(_, a, sigma22) => {
      match a {
        &CertiCoq_Benchmarks_lib_vs_space_atom::Next(_, e, e0) => {
          self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding1_(
            self.alloc(
              Coq_Init_Datatypes_list::cons(
                PhantomData,
                a,
                sigma0)),
            sigma1,
            sigma22)
        },
        &CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(_, x, z) => {
          match x {
            &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
              self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding1_(
                self.alloc(
                  Coq_Init_Datatypes_list::cons(
                    PhantomData,
                    a,
                    sigma0)),
                sigma1,
                sigma22)
            },
            &CertiCoq_Benchmarks_lib_vs_expr::Var(_, x2) => {
              match self.CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom1(
                      x2,
                      z,
                      sigma1) {
                true => {
                  self.alloc(
                    Coq_Init_Datatypes_list::cons(
                      PhantomData,
                      __mk_pair(
                        self.alloc(
                          CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                            PhantomData,
                            x,
                            z)),
                        self.CertiCoq_Benchmarks_lib_vs_insert(
                          (),
                          self.CertiCoq_Benchmarks_lib_vs_rev_cmp__curried()(
                            self.CertiCoq_Benchmarks_lib_vs_compare_space_atom__curried()),
                          self.alloc(
                            CertiCoq_Benchmarks_lib_vs_space_atom::Next(
                              PhantomData,
                              x,
                              z)),
                          self.Coq_Init_Datatypes_app(
                            self.Coq_Lists_List_rev(
                              sigma0),
                            sigma22))),
                      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding1_(
                        self.alloc(
                          Coq_Init_Datatypes_list::cons(
                            PhantomData,
                            self.alloc(
                              CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                                PhantomData,
                                x,
                                z)),
                            sigma0)),
                        sigma1,
                        sigma22)))
                },
                false => {
                  self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding1_(
                    self.alloc(
                      Coq_Init_Datatypes_list::cons(
                        PhantomData,
                        self.alloc(
                          CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                            PhantomData,
                            x,
                            z)),
                        sigma0)),
                    sigma1,
                    sigma22)
                },
              }
            },
          }
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding1___curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, __pair<&'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>>> {
  self.closure(move |sigma0| {
    self.closure(move |sigma1| {
      self.closure(move |sigma2| {
        self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding1_(
          sigma0,
          sigma1,
          sigma2)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding1(&'a self, sc1: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, sc2: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  match sc1 {
    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma, delta, priority) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma1) => {
      match sc2 {
        &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma0, delta0, priority) => {
          self.alloc(
            Coq_Init_Datatypes_list::nil(
              PhantomData))
        },
        &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma0, delta0, sigma) => {
          self.alloc(
            Coq_Init_Datatypes_list::nil(
              PhantomData))
        },
        &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma2, sigma2, delta2) => {
          let l0 =
            self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding1_(
              self.alloc(
                Coq_Init_Datatypes_list::nil(
                  PhantomData)),
              sigma1,
              sigma2);
          let build_clause =
            self.closure(move |p| {
              __pair_elim!(
                sigma22, atm, {
                  self.alloc(
                    CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(
                      PhantomData,
                      gamma2,
                      atm,
                      self.CertiCoq_Benchmarks_lib_vs_insert_uniq(
                        (),
                        self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
                        self.CertiCoq_Benchmarks_lib_vs_order_eqv_pure_atom(
                          sigma22),
                        delta2)))
                },
                p)
            });
          self.Coq_Lists_List_map(
            build_clause,
            l0)
        },
      }
    },
    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding1__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.closure(move |sc1| {
    self.closure(move |sc2| {
      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding1(
        sc1,
        sc2)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom2(&'a self, x: Coq_PArith_BinPosDef_Pos_t<'a>, y: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, sc: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> Option<&'a CertiCoq_Benchmarks_lib_vs_expr<'a>> {
  match sc {
    &Coq_Init_Datatypes_list::nil(_) => {
      None
    },
    &Coq_Init_Datatypes_list::cons(_, s, sc2) => {
      match s {
        &CertiCoq_Benchmarks_lib_vs_space_atom::Next(_, e, y2) => {
          match e {
            &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
              self.CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom2(
                x,
                y,
                sc2)
            },
            &CertiCoq_Benchmarks_lib_vs_expr::Var(_, x2) => {
              match self.Coq_PArith_BinPos_Pos_eq_dec(
                      x,
                      x2) {
                &Coq_Init_Specif_sumbool::left(_) => {
                  match self.CertiCoq_Benchmarks_lib_vs_expr_eq(
                          y,
                          y2) {
                    true => {
                      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom2(
                        x,
                        y,
                        sc2)
                    },
                    false => {
                      Some(
                        y2)
                    },
                  }
                },
                &Coq_Init_Specif_sumbool::right(_) => {
                  self.CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom2(
                    x,
                    y,
                    sc2)
                },
              }
            },
          }
        },
        &CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(_, e, e0) => {
          self.CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom2(
            x,
            y,
            sc2)
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom2__curried(&'a self) -> &'a dyn Fn(Coq_PArith_BinPosDef_Pos_t<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> Option<&'a CertiCoq_Benchmarks_lib_vs_expr<'a>> {
  self.closure(move |x| {
    self.closure(move |y| {
      self.closure(move |sc| {
        self.CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom2(
          x,
          y,
          sc)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding2_(&'a self, sigma0: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>, sigma1: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>, sigma2: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, __pair<&'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>>> {
  match sigma2 {
    &Coq_Init_Datatypes_list::nil(_) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
    &Coq_Init_Datatypes_list::cons(_, a, sigma22) => {
      match a {
        &CertiCoq_Benchmarks_lib_vs_space_atom::Next(_, e, e0) => {
          self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding2_(
            self.alloc(
              Coq_Init_Datatypes_list::cons(
                PhantomData,
                a,
                sigma0)),
            sigma1,
            sigma22)
        },
        &CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(_, x, z) => {
          match x {
            &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
              self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding2_(
                self.alloc(
                  Coq_Init_Datatypes_list::cons(
                    PhantomData,
                    a,
                    sigma0)),
                sigma1,
                sigma22)
            },
            &CertiCoq_Benchmarks_lib_vs_expr::Var(_, x2) => {
              match self.CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom2(
                      x2,
                      z,
                      sigma1) {
                Some(y) => {
                  self.alloc(
                    Coq_Init_Datatypes_list::cons(
                      PhantomData,
                      __mk_pair(
                        self.alloc(
                          CertiCoq_Benchmarks_lib_vs_pure_atom::Eqv(
                            PhantomData,
                            x,
                            z)),
                        self.CertiCoq_Benchmarks_lib_vs_insert(
                          (),
                          self.CertiCoq_Benchmarks_lib_vs_rev_cmp__curried()(
                            self.CertiCoq_Benchmarks_lib_vs_compare_space_atom__curried()),
                          self.alloc(
                            CertiCoq_Benchmarks_lib_vs_space_atom::Next(
                              PhantomData,
                              x,
                              y)),
                          self.CertiCoq_Benchmarks_lib_vs_insert(
                            (),
                            self.CertiCoq_Benchmarks_lib_vs_rev_cmp__curried()(
                              self.CertiCoq_Benchmarks_lib_vs_compare_space_atom__curried()),
                            self.alloc(
                              CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                                PhantomData,
                                y,
                                z)),
                            self.Coq_Init_Datatypes_app(
                              self.Coq_Lists_List_rev(
                                sigma0),
                              sigma22)))),
                      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding2_(
                        self.alloc(
                          Coq_Init_Datatypes_list::cons(
                            PhantomData,
                            self.alloc(
                              CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                                PhantomData,
                                x,
                                z)),
                            sigma0)),
                        sigma1,
                        sigma22)))
                },
                None => {
                  self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding2_(
                    self.alloc(
                      Coq_Init_Datatypes_list::cons(
                        PhantomData,
                        self.alloc(
                          CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                            PhantomData,
                            x,
                            z)),
                        sigma0)),
                    sigma1,
                    sigma22)
                },
              }
            },
          }
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding2___curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, __pair<&'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>>> {
  self.closure(move |sigma0| {
    self.closure(move |sigma1| {
      self.closure(move |sigma2| {
        self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding2_(
          sigma0,
          sigma1,
          sigma2)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding2(&'a self, sc1: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, sc2: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  match sc1 {
    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma, delta, priority) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma1) => {
      match sc2 {
        &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma0, delta0, priority) => {
          self.alloc(
            Coq_Init_Datatypes_list::nil(
              PhantomData))
        },
        &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma0, delta0, sigma) => {
          self.alloc(
            Coq_Init_Datatypes_list::nil(
              PhantomData))
        },
        &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma2, sigma2, delta2) => {
          let l0 =
            self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding2_(
              self.alloc(
                Coq_Init_Datatypes_list::nil(
                  PhantomData)),
              sigma1,
              sigma2);
          let build_clause =
            self.closure(move |p| {
              __pair_elim!(
                sigma22, atm, {
                  self.alloc(
                    CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(
                      PhantomData,
                      gamma2,
                      atm,
                      self.CertiCoq_Benchmarks_lib_vs_insert_uniq(
                        (),
                        self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
                        self.CertiCoq_Benchmarks_lib_vs_order_eqv_pure_atom(
                          sigma22),
                        delta2)))
                },
                p)
            });
          self.Coq_Lists_List_map(
            build_clause,
            l0)
        },
      }
    },
    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding2__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.closure(move |sc1| {
    self.closure(move |sc2| {
      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding2(
        sc1,
        sc2)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_lseg_in_dom2(&'a self, x: Coq_PArith_BinPosDef_Pos_t<'a>, y: &'a CertiCoq_Benchmarks_lib_vs_expr<'a>, sc: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> Option<&'a CertiCoq_Benchmarks_lib_vs_expr<'a>> {
  match sc {
    &Coq_Init_Datatypes_list::nil(_) => {
      None
    },
    &Coq_Init_Datatypes_list::cons(_, s, sc2) => {
      match s {
        &CertiCoq_Benchmarks_lib_vs_space_atom::Next(_, e, e0) => {
          self.CertiCoq_Benchmarks_lib_vs_HeapResolve_lseg_in_dom2(
            x,
            y,
            sc2)
        },
        &CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(_, x0, y0) => {
          match x0 {
            &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
              self.CertiCoq_Benchmarks_lib_vs_HeapResolve_lseg_in_dom2(
                x,
                y,
                sc2)
            },
            &CertiCoq_Benchmarks_lib_vs_expr::Var(_, x2) => {
              match self.Coq_PArith_BinPos_Pos_eq_dec(
                      x,
                      x2) {
                &Coq_Init_Specif_sumbool::left(_) => {
                  match self.Coq_Init_Datatypes_negb(
                          self.CertiCoq_Benchmarks_lib_vs_expr_eq(
                            y0,
                            y)) {
                    true => {
                      Some(
                        y0)
                    },
                    false => {
                      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_lseg_in_dom2(
                        x,
                        y,
                        sc2)
                    },
                  }
                },
                &Coq_Init_Specif_sumbool::right(_) => {
                  self.CertiCoq_Benchmarks_lib_vs_HeapResolve_lseg_in_dom2(
                    x,
                    y,
                    sc2)
                },
              }
            },
          }
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_lseg_in_dom2__curried(&'a self) -> &'a dyn Fn(Coq_PArith_BinPosDef_Pos_t<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_expr<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> Option<&'a CertiCoq_Benchmarks_lib_vs_expr<'a>> {
  self.closure(move |x| {
    self.closure(move |y| {
      self.closure(move |sc| {
        self.CertiCoq_Benchmarks_lib_vs_HeapResolve_lseg_in_dom2(
          x,
          y,
          sc)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding3_(&'a self, sigma0: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>, sigma1: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>, sigma2: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>> {
  match sigma2 {
    &Coq_Init_Datatypes_list::nil(_) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
    &Coq_Init_Datatypes_list::cons(_, a, sigma22) => {
      match a {
        &CertiCoq_Benchmarks_lib_vs_space_atom::Next(_, e, e0) => {
          self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding3_(
            self.alloc(
              Coq_Init_Datatypes_list::cons(
                PhantomData,
                a,
                sigma0)),
            sigma1,
            sigma22)
        },
        &CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(_, x, e) => {
          match x {
            &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
              self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding3_(
                self.alloc(
                  Coq_Init_Datatypes_list::cons(
                    PhantomData,
                    a,
                    sigma0)),
                sigma1,
                sigma22)
            },
            &CertiCoq_Benchmarks_lib_vs_expr::Var(_, x2) => {
              match e {
                &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
                  match self.CertiCoq_Benchmarks_lib_vs_HeapResolve_lseg_in_dom2(
                          x2,
                          self.alloc(
                            CertiCoq_Benchmarks_lib_vs_expr::Nil(
                              PhantomData)),
                          sigma1) {
                    Some(y) => {
                      self.alloc(
                        Coq_Init_Datatypes_list::cons(
                          PhantomData,
                          self.CertiCoq_Benchmarks_lib_vs_insert(
                            (),
                            self.CertiCoq_Benchmarks_lib_vs_rev_cmp__curried()(
                              self.CertiCoq_Benchmarks_lib_vs_compare_space_atom__curried()),
                            self.alloc(
                              CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                                PhantomData,
                                x,
                                y)),
                            self.CertiCoq_Benchmarks_lib_vs_insert(
                              (),
                              self.CertiCoq_Benchmarks_lib_vs_rev_cmp__curried()(
                                self.CertiCoq_Benchmarks_lib_vs_compare_space_atom__curried()),
                              self.alloc(
                                CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                                  PhantomData,
                                  y,
                                  self.alloc(
                                    CertiCoq_Benchmarks_lib_vs_expr::Nil(
                                      PhantomData)))),
                              self.Coq_Init_Datatypes_app(
                                self.Coq_Lists_List_rev(
                                  sigma0),
                                sigma22))),
                          self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding3_(
                            self.alloc(
                              Coq_Init_Datatypes_list::cons(
                                PhantomData,
                                self.alloc(
                                  CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                                    PhantomData,
                                    x,
                                    self.alloc(
                                      CertiCoq_Benchmarks_lib_vs_expr::Nil(
                                        PhantomData)))),
                                sigma0)),
                            sigma1,
                            sigma22)))
                    },
                    None => {
                      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding3_(
                        self.alloc(
                          Coq_Init_Datatypes_list::cons(
                            PhantomData,
                            self.alloc(
                              CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                                PhantomData,
                                x,
                                self.alloc(
                                  CertiCoq_Benchmarks_lib_vs_expr::Nil(
                                    PhantomData)))),
                            sigma0)),
                        sigma1,
                        sigma22)
                    },
                  }
                },
                &CertiCoq_Benchmarks_lib_vs_expr::Var(_, v) => {
                  self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding3_(
                    self.alloc(
                      Coq_Init_Datatypes_list::cons(
                        PhantomData,
                        a,
                        sigma0)),
                    sigma1,
                    sigma22)
                },
              }
            },
          }
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding3___curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>> {
  self.closure(move |sigma0| {
    self.closure(move |sigma1| {
      self.closure(move |sigma2| {
        self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding3_(
          sigma0,
          sigma1,
          sigma2)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding3(&'a self, sc1: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, sc2: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  match sc1 {
    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma, delta, priority) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma1) => {
      match sc2 {
        &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma0, delta0, priority) => {
          self.alloc(
            Coq_Init_Datatypes_list::nil(
              PhantomData))
        },
        &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma0, delta0, sigma) => {
          self.alloc(
            Coq_Init_Datatypes_list::nil(
              PhantomData))
        },
        &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma2, sigma2, delta2) => {
          let l0 =
            self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding3_(
              self.alloc(
                Coq_Init_Datatypes_list::nil(
                  PhantomData)),
              sigma1,
              sigma2);
          let build_clause =
            self.closure(move |sigma22| {
              self.alloc(
                CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(
                  PhantomData,
                  gamma2,
                  sigma22,
                  delta2))
            });
          self.Coq_Lists_List_map(
            build_clause,
            l0)
        },
      }
    },
    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding3__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.closure(move |sc1| {
    self.closure(move |sc2| {
      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding3(
        sc1,
        sc2)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding4NPR_(&'a self, sigma0: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>, sigma1: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>, sigma2: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>> {
  match sigma2 {
    &Coq_Init_Datatypes_list::nil(_) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
    &Coq_Init_Datatypes_list::cons(_, a, sigma22) => {
      match a {
        &CertiCoq_Benchmarks_lib_vs_space_atom::Next(_, e, e0) => {
          self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding4NPR_(
            self.alloc(
              Coq_Init_Datatypes_list::cons(
                PhantomData,
                a,
                sigma0)),
            sigma1,
            sigma22)
        },
        &CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(_, x, z) => {
          match x {
            &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
              self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding4NPR_(
                self.alloc(
                  Coq_Init_Datatypes_list::cons(
                    PhantomData,
                    a,
                    sigma0)),
                sigma1,
                sigma22)
            },
            &CertiCoq_Benchmarks_lib_vs_expr::Var(_, x2) => {
              match z {
                &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
                  self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding4NPR_(
                    self.alloc(
                      Coq_Init_Datatypes_list::cons(
                        PhantomData,
                        a,
                        sigma0)),
                    sigma1,
                    sigma22)
                },
                &CertiCoq_Benchmarks_lib_vs_expr::Var(_, z2) => {
                  match self.CertiCoq_Benchmarks_lib_vs_HeapResolve_lseg_in_dom2(
                          x2,
                          z,
                          sigma1) {
                    Some(y) => {
                      match self.CertiCoq_Benchmarks_lib_vs_HeapResolve_next_in_dom(
                              z2,
                              sigma1) {
                        true => {
                          self.alloc(
                            Coq_Init_Datatypes_list::cons(
                              PhantomData,
                              self.CertiCoq_Benchmarks_lib_vs_insert(
                                (),
                                self.CertiCoq_Benchmarks_lib_vs_rev_cmp__curried()(
                                  self.CertiCoq_Benchmarks_lib_vs_compare_space_atom__curried()),
                                self.alloc(
                                  CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                                    PhantomData,
                                    x,
                                    y)),
                                self.CertiCoq_Benchmarks_lib_vs_insert(
                                  (),
                                  self.CertiCoq_Benchmarks_lib_vs_rev_cmp__curried()(
                                    self.CertiCoq_Benchmarks_lib_vs_compare_space_atom__curried()),
                                  self.alloc(
                                    CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                                      PhantomData,
                                      y,
                                      z)),
                                  self.Coq_Init_Datatypes_app(
                                    self.Coq_Lists_List_rev(
                                      sigma0),
                                    sigma22))),
                              self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding4NPR_(
                                self.alloc(
                                  Coq_Init_Datatypes_list::cons(
                                    PhantomData,
                                    self.alloc(
                                      CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                                        PhantomData,
                                        x,
                                        z)),
                                    sigma0)),
                                sigma1,
                                sigma22)))
                        },
                        false => {
                          self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding4NPR_(
                            self.alloc(
                              Coq_Init_Datatypes_list::cons(
                                PhantomData,
                                self.alloc(
                                  CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                                    PhantomData,
                                    x,
                                    z)),
                                sigma0)),
                            sigma1,
                            sigma22)
                        },
                      }
                    },
                    None => {
                      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding4NPR_(
                        self.alloc(
                          Coq_Init_Datatypes_list::cons(
                            PhantomData,
                            self.alloc(
                              CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                                PhantomData,
                                x,
                                z)),
                            sigma0)),
                        sigma1,
                        sigma22)
                    },
                  }
                },
              }
            },
          }
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding4NPR___curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>> {
  self.closure(move |sigma0| {
    self.closure(move |sigma1| {
      self.closure(move |sigma2| {
        self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding4NPR_(
          sigma0,
          sigma1,
          sigma2)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding4(&'a self, sc1: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, sc2: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  match sc1 {
    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma, delta, priority) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma1) => {
      match sc2 {
        &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma0, delta0, priority) => {
          self.alloc(
            Coq_Init_Datatypes_list::nil(
              PhantomData))
        },
        &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma0, delta0, sigma) => {
          self.alloc(
            Coq_Init_Datatypes_list::nil(
              PhantomData))
        },
        &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma2, sigma2, delta2) => {
          let l0 =
            self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding4NPR_(
              self.alloc(
                Coq_Init_Datatypes_list::nil(
                  PhantomData)),
              sigma1,
              sigma2);
          let GG =
            self.CertiCoq_Benchmarks_lib_vs_rsort_uniq(
              (),
              self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
              self.Coq_Init_Datatypes_app(
                gamma,
                gamma2));
          let DD =
            self.CertiCoq_Benchmarks_lib_vs_rsort_uniq(
              (),
              self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
              self.Coq_Init_Datatypes_app(
                delta,
                delta2));
          let build_clause =
            self.closure(move |sigma22| {
              self.alloc(
                CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(
                  PhantomData,
                  GG,
                  sigma22,
                  DD))
            });
          self.Coq_Lists_List_map(
            build_clause,
            l0)
        },
      }
    },
    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding4__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.closure(move |sc1| {
    self.closure(move |sc2| {
      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding4(
        sc1,
        sc2)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding6NPR_(&'a self, sigma0: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>, sigma1: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>, sigma2: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, __pair<&'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>>> {
  match sigma2 {
    &Coq_Init_Datatypes_list::nil(_) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
    &Coq_Init_Datatypes_list::cons(_, a, sigma22) => {
      match a {
        &CertiCoq_Benchmarks_lib_vs_space_atom::Next(_, e, e0) => {
          self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding6NPR_(
            self.alloc(
              Coq_Init_Datatypes_list::cons(
                PhantomData,
                a,
                sigma0)),
            sigma1,
            sigma22)
        },
        &CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(_, x, z) => {
          match x {
            &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
              self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding6NPR_(
                self.alloc(
                  Coq_Init_Datatypes_list::cons(
                    PhantomData,
                    a,
                    sigma0)),
                sigma1,
                sigma22)
            },
            &CertiCoq_Benchmarks_lib_vs_expr::Var(_, x2) => {
              match z {
                &CertiCoq_Benchmarks_lib_vs_expr::Nil(_) => {
                  self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding6NPR_(
                    self.alloc(
                      Coq_Init_Datatypes_list::cons(
                        PhantomData,
                        a,
                        sigma0)),
                    sigma1,
                    sigma22)
                },
                &CertiCoq_Benchmarks_lib_vs_expr::Var(_, z2) => {
                  match self.Coq_PArith_BinPos_Pos_eq_dec(
                          x2,
                          z2) {
                    &Coq_Init_Specif_sumbool::left(_) => {
                      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding6NPR_(
                        sigma0,
                        sigma1,
                        sigma22)
                    },
                    &Coq_Init_Specif_sumbool::right(_) => {
                      match self.CertiCoq_Benchmarks_lib_vs_HeapResolve_lseg_in_dom2(
                              x2,
                              z,
                              sigma1) {
                        Some(y) => {
                          let atms =
                            self.CertiCoq_Benchmarks_lib_vs_HeapResolve_lseg_in_dom_atoms(
                              z2,
                              sigma1);
                          let build_res =
                            self.closure(move |atm| {
                              __mk_pair(
                                atm,
                                self.CertiCoq_Benchmarks_lib_vs_insert(
                                  (),
                                  self.CertiCoq_Benchmarks_lib_vs_rev_cmp__curried()(
                                    self.CertiCoq_Benchmarks_lib_vs_compare_space_atom__curried()),
                                  self.alloc(
                                    CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                                      PhantomData,
                                      x,
                                      y)),
                                  self.CertiCoq_Benchmarks_lib_vs_insert(
                                    (),
                                    self.CertiCoq_Benchmarks_lib_vs_rev_cmp__curried()(
                                      self.CertiCoq_Benchmarks_lib_vs_compare_space_atom__curried()),
                                    self.alloc(
                                      CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                                        PhantomData,
                                        y,
                                        z)),
                                    self.Coq_Init_Datatypes_app(
                                      self.Coq_Lists_List_rev(
                                        sigma0),
                                      sigma22))))
                            });
                          self.Coq_Init_Datatypes_app(
                            self.Coq_Lists_List_map(
                              build_res,
                              atms),
                            self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding6NPR_(
                              self.alloc(
                                Coq_Init_Datatypes_list::cons(
                                  PhantomData,
                                  self.alloc(
                                    CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                                      PhantomData,
                                      x,
                                      z)),
                                  sigma0)),
                              sigma1,
                              sigma22))
                        },
                        None => {
                          self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding6NPR_(
                            self.alloc(
                              Coq_Init_Datatypes_list::cons(
                                PhantomData,
                                self.alloc(
                                  CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                                    PhantomData,
                                    x,
                                    z)),
                                sigma0)),
                            sigma1,
                            sigma22)
                        },
                      }
                    },
                  }
                },
              }
            },
          }
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding6NPR___curried(&'a self) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a Coq_Init_Datatypes_list<'a, __pair<&'a CertiCoq_Benchmarks_lib_vs_pure_atom<'a>, &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>>> {
  self.closure(move |sigma0| {
    self.closure(move |sigma1| {
      self.closure(move |sigma2| {
        self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding6NPR_(
          sigma0,
          sigma1,
          sigma2)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding6(&'a self, sc1: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, sc2: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  match sc1 {
    &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma, delta, priority) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
    &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma, delta, sigma1) => {
      match sc2 {
        &CertiCoq_Benchmarks_lib_vs_clause::PureClause(_, gamma0, delta0, priority) => {
          self.alloc(
            Coq_Init_Datatypes_list::nil(
              PhantomData))
        },
        &CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(_, gamma0, delta0, sigma) => {
          self.alloc(
            Coq_Init_Datatypes_list::nil(
              PhantomData))
        },
        &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma2, sigma2, delta2) => {
          let l0 =
            self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding6NPR_(
              self.alloc(
                Coq_Init_Datatypes_list::nil(
                  PhantomData)),
              sigma1,
              sigma2);
          let GG =
            self.CertiCoq_Benchmarks_lib_vs_rsort_uniq(
              (),
              self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
              self.Coq_Init_Datatypes_app(
                gamma,
                gamma2));
          let DD =
            self.CertiCoq_Benchmarks_lib_vs_rsort_uniq(
              (),
              self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
              self.Coq_Init_Datatypes_app(
                delta,
                delta2));
          let build_clause =
            self.closure(move |p| {
              __pair_elim!(
                sigma22, atm, {
                  self.alloc(
                    CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(
                      PhantomData,
                      GG,
                      atm,
                      self.CertiCoq_Benchmarks_lib_vs_insert_uniq(
                        (),
                        self.CertiCoq_Benchmarks_lib_vs_pure_atom_cmp__curried(),
                        self.CertiCoq_Benchmarks_lib_vs_order_eqv_pure_atom(
                          sigma22),
                        DD)))
                },
                p)
            });
          self.Coq_Lists_List_map(
            build_clause,
            l0)
        },
      }
    },
    &CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(_, gamma, sigma, delta) => {
      self.alloc(
        Coq_Init_Datatypes_list::nil(
          PhantomData))
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding6__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.closure(move |sc1| {
    self.closure(move |sc2| {
      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding6(
        sc1,
        sc2)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_do_unfold_(&'a self, pc: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, nc: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, l: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.Coq_Init_Datatypes_app(
    self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding1(
      pc,
      nc),
    self.Coq_Init_Datatypes_app(
      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding2(
        pc,
        nc),
      self.Coq_Init_Datatypes_app(
        self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding3(
          pc,
          nc),
        self.Coq_Init_Datatypes_app(
          self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding4(
            pc,
            nc),
          self.Coq_Init_Datatypes_app(
            self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding6(
              pc,
              nc),
            l)))))
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_do_unfold___curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>>) -> &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_clause<'a>> {
  self.closure(move |pc| {
    self.closure(move |nc| {
      self.closure(move |l| {
        self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_unfold_(
          pc,
          nc,
          l)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_do_unfold(&'a self, n: u64, pc: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, s: CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  __nat_elim!(
    {
      s
    },
    n2, {
      match self.CertiCoq_Benchmarks_lib_vs_HeapResolve_add_list_to_set(
              self.CertiCoq_Benchmarks_lib_vs_M_fold(
                self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_unfold___curried()(
                  pc),
                s)(
                self.alloc(
                  Coq_Init_Datatypes_list::nil(
                    PhantomData))),
              s) {
        Some(s2) => {
          self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_unfold(
            n2,
            pc,
            s2)
        },
        None => {
          s
        },
      }
    },
    n)
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_do_unfold__curried(&'a self) -> &'a dyn Fn(u64) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.closure(move |n| {
    self.closure(move |pc| {
      self.closure(move |s| {
        self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_unfold(
          n,
          pc,
          s)
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding(&'a self, pc: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, nc: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.CertiCoq_Benchmarks_lib_vs_M_fold(
    self.closure(move |c| {
      self.CertiCoq_Benchmarks_lib_vs_M_union__curried()(
        self.CertiCoq_Benchmarks_lib_vs_HeapResolve_spatial_resolution(
          pc,
          c))
    }),
    self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_unfold(
      __nat_succ(
        __nat_succ(
          __nat_succ(
            __nat_succ(
              __nat_succ(
                __nat_succ(
                  __nat_succ(
                    __nat_succ(
                      __nat_succ(
                        __nat_succ(
                          __nat_succ(
                            __nat_succ(
                              __nat_succ(
                                __nat_succ(
                                  __nat_succ(
                                    __nat_succ(
                                      __nat_succ(
                                        __nat_succ(
                                          __nat_succ(
                                            __nat_succ(
                                              __nat_succ(
                                                __nat_succ(
                                                  __nat_succ(
                                                    __nat_succ(
                                                      __nat_succ(
                                                        __nat_succ(
                                                          __nat_succ(
                                                            __nat_succ(
                                                              __nat_succ(
                                                                __nat_succ(
                                                                  __nat_succ(
                                                                    __nat_succ(
                                                                      __nat_succ(
                                                                        __nat_succ(
                                                                          __nat_succ(
                                                                            __nat_succ(
                                                                              __nat_succ(
                                                                                __nat_succ(
                                                                                  __nat_succ(
                                                                                    __nat_succ(
                                                                                      __nat_succ(
                                                                                        __nat_succ(
                                                                                          __nat_succ(
                                                                                            __nat_succ(
                                                                                              __nat_succ(
                                                                                                __nat_succ(
                                                                                                  __nat_succ(
                                                                                                    __nat_succ(
                                                                                                      __nat_succ(
                                                                                                        __nat_succ(
                                                                                                          __nat_succ(
                                                                                                            __nat_succ(
                                                                                                              __nat_succ(
                                                                                                                __nat_succ(
                                                                                                                  __nat_succ(
                                                                                                                    __nat_succ(
                                                                                                                      __nat_succ(
                                                                                                                        __nat_succ(
                                                                                                                          __nat_succ(
                                                                                                                            __nat_succ(
                                                                                                                              __nat_succ(
                                                                                                                                __nat_succ(
                                                                                                                                  __nat_succ(
                                                                                                                                    __nat_succ(
                                                                                                                                      __nat_succ(
                                                                                                                                        __nat_succ(
                                                                                                                                          __nat_succ(
                                                                                                                                            __nat_succ(
                                                                                                                                              __nat_succ(
                                                                                                                                                __nat_succ(
                                                                                                                                                  __nat_succ(
                                                                                                                                                    __nat_succ(
                                                                                                                                                      __nat_succ(
                                                                                                                                                        __nat_succ(
                                                                                                                                                          __nat_succ(
                                                                                                                                                            __nat_succ(
                                                                                                                                                              __nat_succ(
                                                                                                                                                                __nat_succ(
                                                                                                                                                                  __nat_succ(
                                                                                                                                                                    __nat_succ(
                                                                                                                                                                      __nat_succ(
                                                                                                                                                                        __nat_succ(
                                                                                                                                                                          __nat_succ(
                                                                                                                                                                            __nat_succ(
                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            __nat_succ(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
      pc,
      self.CertiCoq_Benchmarks_lib_vs_M_add(
        nc,
        self.CertiCoq_Benchmarks_lib_vs_M_empty())))(
    self.CertiCoq_Benchmarks_lib_vs_M_empty())
}
fn CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.closure(move |pc| {
    self.closure(move |nc| {
      self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding(
        pc,
        nc)
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_spatial_model2(&'a self, c: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_clause<'a> {
  c
}
fn CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_spatial_model2__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_clause<'a> {
  self.closure(move |c| {
    self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_spatial_model2(
      c)
  })
}

fn Coq_Init_Logic_and_rect<P: Copy>(&'a self, f: &'a dyn Fn(()) -> &'a dyn Fn(()) -> P) -> P {
  hint_app(hint_app(f)(()))(())
}
fn Coq_Init_Logic_and_rect__curried<P: Copy>(&'a self) -> &'a dyn Fn(&'a dyn Fn(()) -> &'a dyn Fn(()) -> P) -> P {
  self.closure(move |f| {
    self.Coq_Init_Logic_and_rect(
      f)
  })
}

fn CertiCoq_Benchmarks_lib_vs_VeriStar_the_loop_terminate(&'a self) -> &'a dyn Fn(u64) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a Coq_Init_Specif_sig<'a, &'a CertiCoq_Benchmarks_lib_vs_VeriStar_veristar_result<'a>> {
  hint_app(self.closure(move |h| {
             let H =
               ();
             hint_app(self.closure(move |_TmpHyp| {
                        self.Coq_Init_Logic_and_rect(
                          self.closure(move |H2| {
                            self.closure(move |H0| {
                              self.closure(move |n| {
                                self.closure(move |sigma| {
                                  self.closure(move |nc| {
                                    self.closure(move |s| {
                                      self.closure(move |cl| {
                                        let Acc_n =
                                          ();
                                        hint_app(hint_app(hint_app(hint_app(hint_app(hint_app({ let hrec2 = self.alloc(std::cell::Cell::new(None));
                                                                                                hrec2.set(Some(
                                                                                                  self.closure(move |n2| {
                                                                                                    self.closure(move |sigma2| {
                                                                                                      self.closure(move |nc2| {
                                                                                                        self.closure(move |s2| {
                                                                                                          self.closure(move |cl2| {
                                                                                                            self.closure(move |Acc_n2| {
                                                                                                              hint_app(match self.Coq_PArith_BinPosDef_Pos_eqb(
                                                                                                                               n2,
                                                                                                                               1) {
                                                                                                                         true => {
                                                                                                                           self.closure(move |teq| {
                                                                                                                             self.alloc(
                                                                                                                               Coq_Init_Specif_sig::exist(
                                                                                                                                 PhantomData,
                                                                                                                                 self.alloc(
                                                                                                                                   CertiCoq_Benchmarks_lib_vs_VeriStar_veristar_result::Aborted(
                                                                                                                                     PhantomData,
                                                                                                                                     self.CertiCoq_Benchmarks_lib_vs_M_elements(
                                                                                                                                       s2),
                                                                                                                                     cl2))))
                                                                                                                           })
                                                                                                                         },
                                                                                                                         false => {
                                                                                                                           self.closure(move |teq| {
                                                                                                                             hint_app(__pair_elim!(
                                                                                                                                        b, a, {
                                                                                                                                          hint_app(hint_app(self.closure(move |p| {
                                                                                                                                                              self.closure(move |t| {
                                                                                                                                                                self.closure(move |teq0| {
                                                                                                                                                                  hint_app(hint_app(__pair_elim!(
                                                                                                                                                                                      b2, a2, {
                                                                                                                                                                                        hint_app(hint_app(self.closure(move |p0| {
                                                                                                                                                                                                            self.closure(move |s_star| {
                                                                                                                                                                                                              self.closure(move |teq1| {
                                                                                                                                                                                                                self.closure(move |teq02| {
                                                                                                                                                                                                                  hint_app(hint_app(hint_app(__pair_elim!(
                                                                                                                                                                                                                                               b3, a3, {
                                                                                                                                                                                                                                                 hint_app(hint_app(self.closure(move |s0| {
                                                                                                                                                                                                                                                                     self.closure(move |units| {
                                                                                                                                                                                                                                                                       self.closure(move |teq2| {
                                                                                                                                                                                                                                                                         self.closure(move |teq12| {
                                                                                                                                                                                                                                                                           self.closure(move |teq03| {
                                                                                                                                                                                                                                                                             hint_app(hint_app(hint_app(hint_app(match s0 {
                                                                                                                                                                                                                                                                                                                   &CertiCoq_Benchmarks_lib_vs_Superposition_superposition_result::Valid(_) => {
                                                                                                                                                                                                                                                                                                                     self.closure(move |teq3| {
                                                                                                                                                                                                                                                                                                                       self.closure(move |teq22| {
                                                                                                                                                                                                                                                                                                                         self.closure(move |teq13| {
                                                                                                                                                                                                                                                                                                                           self.closure(move |teq04| {
                                                                                                                                                                                                                                                                                                                             self.alloc(
                                                                                                                                                                                                                                                                                                                               Coq_Init_Specif_sig::exist(
                                                                                                                                                                                                                                                                                                                                 PhantomData,
                                                                                                                                                                                                                                                                                                                                 self.alloc(
                                                                                                                                                                                                                                                                                                                                   CertiCoq_Benchmarks_lib_vs_VeriStar_veristar_result::Valid(
                                                                                                                                                                                                                                                                                                                                     PhantomData))))
                                                                                                                                                                                                                                                                                                                           })
                                                                                                                                                                                                                                                                                                                         })
                                                                                                                                                                                                                                                                                                                       })
                                                                                                                                                                                                                                                                                                                     })
                                                                                                                                                                                                                                                                                                                   },
                                                                                                                                                                                                                                                                                                                   &CertiCoq_Benchmarks_lib_vs_Superposition_superposition_result::C_example(_, m, t2) => {
                                                                                                                                                                                                                                                                                                                     hint_app(hint_app(self.closure(move |R| {
                                                                                                                                                                                                                                                                                                                                         self.closure(move |selected| {
                                                                                                                                                                                                                                                                                                                                           self.closure(move |teq3| {
                                                                                                                                                                                                                                                                                                                                             self.closure(move |teq22| {
                                                                                                                                                                                                                                                                                                                                               self.closure(move |teq13| {
                                                                                                                                                                                                                                                                                                                                                 self.closure(move |teq04| {
                                                                                                                                                                                                                                                                                                                                                   hint_app(match self.CertiCoq_Benchmarks_lib_vs_isEq(
                                                                                                                                                                                                                                                                                                                                                                    self.CertiCoq_Benchmarks_lib_vs_M_compare(
                                                                                                                                                                                                                                                                                                                                                                      self.CertiCoq_Benchmarks_lib_vs_VeriStar_incorp(
                                                                                                                                                                                                                                                                                                                                                                        self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_wf_set(
                                                                                                                                                                                                                                                                                                                                                                          self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_wellformed(
                                                                                                                                                                                                                                                                                                                                                                            self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_spatial_model(
                                                                                                                                                                                                                                                                                                                                                                              self.CertiCoq_Benchmarks_lib_vs_HeapResolve_norm(
                                                                                                                                                                                                                                                                                                                                                                                self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_wf_set(
                                                                                                                                                                                                                                                                                                                                                                                  selected),
                                                                                                                                                                                                                                                                                                                                                                                self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                  CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(
                                                                                                                                                                                                                                                                                                                                                                                    PhantomData,
                                                                                                                                                                                                                                                                                                                                                                                    self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                      Coq_Init_Datatypes_list::nil(
                                                                                                                                                                                                                                                                                                                                                                                        PhantomData)),
                                                                                                                                                                                                                                                                                                                                                                                    self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                      Coq_Init_Datatypes_list::nil(
                                                                                                                                                                                                                                                                                                                                                                                        PhantomData)),
                                                                                                                                                                                                                                                                                                                                                                                    self.CertiCoq_Benchmarks_lib_vs_Superposition_simplify_atoms(
                                                                                                                                                                                                                                                                                                                                                                                      units,
                                                                                                                                                                                                                                                                                                                                                                                      sigma2))))))),
                                                                                                                                                                                                                                                                                                                                                                        s_star),
                                                                                                                                                                                                                                                                                                                                                                      s_star)) {
                                                                                                                                                                                                                                                                                                                                                              true => {
                                                                                                                                                                                                                                                                                                                                                                self.closure(move |teq4| {
                                                                                                                                                                                                                                                                                                                                                                  hint_app(match self.CertiCoq_Benchmarks_lib_vs_Superposition_is_model_of_PI(
                                                                                                                                                                                                                                                                                                                                                                                   self.Coq_Lists_List_rev(
                                                                                                                                                                                                                                                                                                                                                                                     R),
                                                                                                                                                                                                                                                                                                                                                                                   self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_spatial_model(
                                                                                                                                                                                                                                                                                                                                                                                     self.CertiCoq_Benchmarks_lib_vs_Superposition_simplify(
                                                                                                                                                                                                                                                                                                                                                                                       units,
                                                                                                                                                                                                                                                                                                                                                                                       nc2))) {
                                                                                                                                                                                                                                                                                                                                                                             true => {
                                                                                                                                                                                                                                                                                                                                                                               self.closure(move |teq5| {
                                                                                                                                                                                                                                                                                                                                                                                 hint_app(match self.CertiCoq_Benchmarks_lib_vs_isEq(
                                                                                                                                                                                                                                                                                                                                                                                                  self.CertiCoq_Benchmarks_lib_vs_M_compare(
                                                                                                                                                                                                                                                                                                                                                                                                    self.CertiCoq_Benchmarks_lib_vs_VeriStar_incorp(
                                                                                                                                                                                                                                                                                                                                                                                                      self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_wf_set(
                                                                                                                                                                                                                                                                                                                                                                                                        self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_wellformed(
                                                                                                                                                                                                                                                                                                                                                                                                          self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_spatial_model(
                                                                                                                                                                                                                                                                                                                                                                                                            self.CertiCoq_Benchmarks_lib_vs_HeapResolve_norm(
                                                                                                                                                                                                                                                                                                                                                                                                              self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_wf_set(
                                                                                                                                                                                                                                                                                                                                                                                                                selected),
                                                                                                                                                                                                                                                                                                                                                                                                              self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(
                                                                                                                                                                                                                                                                                                                                                                                                                  PhantomData,
                                                                                                                                                                                                                                                                                                                                                                                                                  self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                    Coq_Init_Datatypes_list::nil(
                                                                                                                                                                                                                                                                                                                                                                                                                      PhantomData)),
                                                                                                                                                                                                                                                                                                                                                                                                                  self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                    Coq_Init_Datatypes_list::nil(
                                                                                                                                                                                                                                                                                                                                                                                                                      PhantomData)),
                                                                                                                                                                                                                                                                                                                                                                                                                  self.CertiCoq_Benchmarks_lib_vs_Superposition_simplify_atoms(
                                                                                                                                                                                                                                                                                                                                                                                                                    units,
                                                                                                                                                                                                                                                                                                                                                                                                                    sigma2))))))),
                                                                                                                                                                                                                                                                                                                                                                                                      s_star),
                                                                                                                                                                                                                                                                                                                                                                                                    self.CertiCoq_Benchmarks_lib_vs_VeriStar_incorp(
                                                                                                                                                                                                                                                                                                                                                                                                      self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_unfold_set(
                                                                                                                                                                                                                                                                                                                                                                                                        self.CertiCoq_Benchmarks_lib_vs_VeriStar_pures()(
                                                                                                                                                                                                                                                                                                                                                                                                          self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding(
                                                                                                                                                                                                                                                                                                                                                                                                            self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_spatial_model(
                                                                                                                                                                                                                                                                                                                                                                                                              self.CertiCoq_Benchmarks_lib_vs_HeapResolve_norm(
                                                                                                                                                                                                                                                                                                                                                                                                                self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_wf_set(
                                                                                                                                                                                                                                                                                                                                                                                                                  selected),
                                                                                                                                                                                                                                                                                                                                                                                                                self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                  CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(
                                                                                                                                                                                                                                                                                                                                                                                                                    PhantomData,
                                                                                                                                                                                                                                                                                                                                                                                                                    self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                      Coq_Init_Datatypes_list::nil(
                                                                                                                                                                                                                                                                                                                                                                                                                        PhantomData)),
                                                                                                                                                                                                                                                                                                                                                                                                                    self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                      Coq_Init_Datatypes_list::nil(
                                                                                                                                                                                                                                                                                                                                                                                                                        PhantomData)),
                                                                                                                                                                                                                                                                                                                                                                                                                    self.CertiCoq_Benchmarks_lib_vs_Superposition_simplify_atoms(
                                                                                                                                                                                                                                                                                                                                                                                                                      units,
                                                                                                                                                                                                                                                                                                                                                                                                                      sigma2))))),
                                                                                                                                                                                                                                                                                                                                                                                                            self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_spatial_model2(
                                                                                                                                                                                                                                                                                                                                                                                                              self.CertiCoq_Benchmarks_lib_vs_HeapResolve_norm(
                                                                                                                                                                                                                                                                                                                                                                                                                selected,
                                                                                                                                                                                                                                                                                                                                                                                                                self.CertiCoq_Benchmarks_lib_vs_Superposition_simplify(
                                                                                                                                                                                                                                                                                                                                                                                                                  units,
                                                                                                                                                                                                                                                                                                                                                                                                                  nc2)))))),
                                                                                                                                                                                                                                                                                                                                                                                                      self.CertiCoq_Benchmarks_lib_vs_VeriStar_incorp(
                                                                                                                                                                                                                                                                                                                                                                                                        self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_wf_set(
                                                                                                                                                                                                                                                                                                                                                                                                          self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_wellformed(
                                                                                                                                                                                                                                                                                                                                                                                                            self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_spatial_model(
                                                                                                                                                                                                                                                                                                                                                                                                              self.CertiCoq_Benchmarks_lib_vs_HeapResolve_norm(
                                                                                                                                                                                                                                                                                                                                                                                                                self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_wf_set(
                                                                                                                                                                                                                                                                                                                                                                                                                  selected),
                                                                                                                                                                                                                                                                                                                                                                                                                self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                  CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(
                                                                                                                                                                                                                                                                                                                                                                                                                    PhantomData,
                                                                                                                                                                                                                                                                                                                                                                                                                    self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                      Coq_Init_Datatypes_list::nil(
                                                                                                                                                                                                                                                                                                                                                                                                                        PhantomData)),
                                                                                                                                                                                                                                                                                                                                                                                                                    self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                      Coq_Init_Datatypes_list::nil(
                                                                                                                                                                                                                                                                                                                                                                                                                        PhantomData)),
                                                                                                                                                                                                                                                                                                                                                                                                                    self.CertiCoq_Benchmarks_lib_vs_Superposition_simplify_atoms(
                                                                                                                                                                                                                                                                                                                                                                                                                      units,
                                                                                                                                                                                                                                                                                                                                                                                                                      sigma2))))))),
                                                                                                                                                                                                                                                                                                                                                                                                        s_star)))) {
                                                                                                                                                                                                                                                                                                                                                                                            true => {
                                                                                                                                                                                                                                                                                                                                                                                              self.closure(move |teq6| {
                                                                                                                                                                                                                                                                                                                                                                                                self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                  Coq_Init_Specif_sig::exist(
                                                                                                                                                                                                                                                                                                                                                                                                    PhantomData,
                                                                                                                                                                                                                                                                                                                                                                                                    self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                      CertiCoq_Benchmarks_lib_vs_VeriStar_veristar_result::C_example(
                                                                                                                                                                                                                                                                                                                                                                                                        PhantomData,
                                                                                                                                                                                                                                                                                                                                                                                                        R))))
                                                                                                                                                                                                                                                                                                                                                                                              })
                                                                                                                                                                                                                                                                                                                                                                                            },
                                                                                                                                                                                                                                                                                                                                                                                            false => {
                                                                                                                                                                                                                                                                                                                                                                                              self.closure(move |teq6| {
                                                                                                                                                                                                                                                                                                                                                                                                self.Coq_Init_Specif_sig_rect(
                                                                                                                                                                                                                                                                                                                                                                                                  self.closure(move |rec_res| {
                                                                                                                                                                                                                                                                                                                                                                                                    self.closure(move |p1| {
                                                                                                                                                                                                                                                                                                                                                                                                      self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                        Coq_Init_Specif_sig::exist(
                                                                                                                                                                                                                                                                                                                                                                                                          PhantomData,
                                                                                                                                                                                                                                                                                                                                                                                                          rec_res))
                                                                                                                                                                                                                                                                                                                                                                                                    })
                                                                                                                                                                                                                                                                                                                                                                                                  }),
                                                                                                                                                                                                                                                                                                                                                                                                  hint_app(hint_app(hint_app(hint_app(hint_app(hint_app(hrec2.get().unwrap())(self.Coq_PArith_BinPosDef_Pos_pred(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                n2)))(self.CertiCoq_Benchmarks_lib_vs_Superposition_simplify_atoms(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        units,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        sigma2)))(self.CertiCoq_Benchmarks_lib_vs_Superposition_simplify(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    units,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    nc2)))(self.CertiCoq_Benchmarks_lib_vs_VeriStar_incorp(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_unfold_set(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               self.CertiCoq_Benchmarks_lib_vs_VeriStar_pures()(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 self.CertiCoq_Benchmarks_lib_vs_HeapResolve_unfolding(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_spatial_model(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     self.CertiCoq_Benchmarks_lib_vs_HeapResolve_norm(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_wf_set(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         selected),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           PhantomData,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Coq_Init_Datatypes_list::nil(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               PhantomData)),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Coq_Init_Datatypes_list::nil(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               PhantomData)),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           self.CertiCoq_Benchmarks_lib_vs_Superposition_simplify_atoms(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             units,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             sigma2))))),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_spatial_model2(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     self.CertiCoq_Benchmarks_lib_vs_HeapResolve_norm(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       selected,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       self.CertiCoq_Benchmarks_lib_vs_Superposition_simplify(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         units,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         nc2)))))),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             self.CertiCoq_Benchmarks_lib_vs_VeriStar_incorp(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_wf_set(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_wellformed(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_spatial_model(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     self.CertiCoq_Benchmarks_lib_vs_HeapResolve_norm(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_wf_set(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         selected),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           PhantomData,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Coq_Init_Datatypes_list::nil(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               PhantomData)),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Coq_Init_Datatypes_list::nil(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               PhantomData)),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           self.CertiCoq_Benchmarks_lib_vs_Superposition_simplify_atoms(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             units,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             sigma2))))))),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               s_star))))(self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_spatial_model(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            self.CertiCoq_Benchmarks_lib_vs_HeapResolve_norm(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_wf_set(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                selected),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  PhantomData,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    Coq_Init_Datatypes_list::nil(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      PhantomData)),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    Coq_Init_Datatypes_list::nil(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      PhantomData)),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  self.CertiCoq_Benchmarks_lib_vs_Superposition_simplify_atoms(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    units,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    sigma2)))))))(()))
                                                                                                                                                                                                                                                                                                                                                                                              })
                                                                                                                                                                                                                                                                                                                                                                                            },
                                                                                                                                                                                                                                                                                                                                                                                          })(())
                                                                                                                                                                                                                                                                                                                                                                               })
                                                                                                                                                                                                                                                                                                                                                                             },
                                                                                                                                                                                                                                                                                                                                                                             false => {
                                                                                                                                                                                                                                                                                                                                                                               self.closure(move |teq5| {
                                                                                                                                                                                                                                                                                                                                                                                 self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                   Coq_Init_Specif_sig::exist(
                                                                                                                                                                                                                                                                                                                                                                                     PhantomData,
                                                                                                                                                                                                                                                                                                                                                                                     self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                       CertiCoq_Benchmarks_lib_vs_VeriStar_veristar_result::C_example(
                                                                                                                                                                                                                                                                                                                                                                                         PhantomData,
                                                                                                                                                                                                                                                                                                                                                                                         R))))
                                                                                                                                                                                                                                                                                                                                                                               })
                                                                                                                                                                                                                                                                                                                                                                             },
                                                                                                                                                                                                                                                                                                                                                                           })(())
                                                                                                                                                                                                                                                                                                                                                                })
                                                                                                                                                                                                                                                                                                                                                              },
                                                                                                                                                                                                                                                                                                                                                              false => {
                                                                                                                                                                                                                                                                                                                                                                self.closure(move |teq4| {
                                                                                                                                                                                                                                                                                                                                                                  self.Coq_Init_Specif_sig_rect(
                                                                                                                                                                                                                                                                                                                                                                    self.closure(move |rec_res| {
                                                                                                                                                                                                                                                                                                                                                                      self.closure(move |p1| {
                                                                                                                                                                                                                                                                                                                                                                        self.alloc(
                                                                                                                                                                                                                                                                                                                                                                          Coq_Init_Specif_sig::exist(
                                                                                                                                                                                                                                                                                                                                                                            PhantomData,
                                                                                                                                                                                                                                                                                                                                                                            rec_res))
                                                                                                                                                                                                                                                                                                                                                                      })
                                                                                                                                                                                                                                                                                                                                                                    }),
                                                                                                                                                                                                                                                                                                                                                                    hint_app(hint_app(hint_app(hint_app(hint_app(hint_app(hrec2.get().unwrap())(self.Coq_PArith_BinPosDef_Pos_pred(
                                                                                                                                                                                                                                                                                                                                                                                                                                                  n2)))(self.CertiCoq_Benchmarks_lib_vs_Superposition_simplify_atoms(
                                                                                                                                                                                                                                                                                                                                                                                                                                                          units,
                                                                                                                                                                                                                                                                                                                                                                                                                                                          sigma2)))(self.CertiCoq_Benchmarks_lib_vs_Superposition_simplify(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      units,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      nc2)))(self.CertiCoq_Benchmarks_lib_vs_VeriStar_incorp(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                               self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_wf_set(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 self.CertiCoq_Benchmarks_lib_vs_HeapResolve_do_wellformed(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_spatial_model(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     self.CertiCoq_Benchmarks_lib_vs_HeapResolve_norm(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_wf_set(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         selected),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           PhantomData,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Coq_Init_Datatypes_list::nil(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               PhantomData)),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             Coq_Init_Datatypes_list::nil(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               PhantomData)),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           self.CertiCoq_Benchmarks_lib_vs_Superposition_simplify_atoms(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             units,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             sigma2))))))),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                               s_star)))(self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_spatial_model(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           self.CertiCoq_Benchmarks_lib_vs_HeapResolve_norm(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_wf_set(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               selected),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               CertiCoq_Benchmarks_lib_vs_clause::PosSpaceClause(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 PhantomData,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   Coq_Init_Datatypes_list::nil(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     PhantomData)),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 self.alloc(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   Coq_Init_Datatypes_list::nil(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     PhantomData)),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 self.CertiCoq_Benchmarks_lib_vs_Superposition_simplify_atoms(
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   units,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   sigma2)))))))(()))
                                                                                                                                                                                                                                                                                                                                                                })
                                                                                                                                                                                                                                                                                                                                                              },
                                                                                                                                                                                                                                                                                                                                                            })(())
                                                                                                                                                                                                                                                                                                                                                 })
                                                                                                                                                                                                                                                                                                                                               })
                                                                                                                                                                                                                                                                                                                                             })
                                                                                                                                                                                                                                                                                                                                           })
                                                                                                                                                                                                                                                                                                                                         })
                                                                                                                                                                                                                                                                                                                                       }))(m))(t2)
                                                                                                                                                                                                                                                                                                                   },
                                                                                                                                                                                                                                                                                                                   &CertiCoq_Benchmarks_lib_vs_Superposition_superposition_result::Aborted(_, l) => {
                                                                                                                                                                                                                                                                                                                     hint_app(self.closure(move |l2| {
                                                                                                                                                                                                                                                                                                                                self.closure(move |teq3| {
                                                                                                                                                                                                                                                                                                                                  self.closure(move |teq22| {
                                                                                                                                                                                                                                                                                                                                    self.closure(move |teq13| {
                                                                                                                                                                                                                                                                                                                                      self.closure(move |teq04| {
                                                                                                                                                                                                                                                                                                                                        self.alloc(
                                                                                                                                                                                                                                                                                                                                          Coq_Init_Specif_sig::exist(
                                                                                                                                                                                                                                                                                                                                            PhantomData,
                                                                                                                                                                                                                                                                                                                                            self.alloc(
                                                                                                                                                                                                                                                                                                                                              CertiCoq_Benchmarks_lib_vs_VeriStar_veristar_result::Aborted(
                                                                                                                                                                                                                                                                                                                                                PhantomData,
                                                                                                                                                                                                                                                                                                                                                l2,
                                                                                                                                                                                                                                                                                                                                                cl2))))
                                                                                                                                                                                                                                                                                                                                      })
                                                                                                                                                                                                                                                                                                                                    })
                                                                                                                                                                                                                                                                                                                                  })
                                                                                                                                                                                                                                                                                                                                })
                                                                                                                                                                                                                                                                                                                              }))(l)
                                                                                                                                                                                                                                                                                                                   },
                                                                                                                                                                                                                                                                                                                 })(()))(()))(()))(())
                                                                                                                                                                                                                                                                           })
                                                                                                                                                                                                                                                                         })
                                                                                                                                                                                                                                                                       })
                                                                                                                                                                                                                                                                     })
                                                                                                                                                                                                                                                                   }))(b3))(a3)
                                                                                                                                                                                                                                               },
                                                                                                                                                                                                                                               p0))(()))(()))(())
                                                                                                                                                                                                                })
                                                                                                                                                                                                              })
                                                                                                                                                                                                            })
                                                                                                                                                                                                          }))(b2))(a2)
                                                                                                                                                                                      },
                                                                                                                                                                                      p))(()))(())
                                                                                                                                                                })
                                                                                                                                                              })
                                                                                                                                                            }))(b))(a)
                                                                                                                                        },
                                                                                                                                        self.CertiCoq_Benchmarks_lib_vs_Superposition_check_clauseset(
                                                                                                                                          s2)))(())
                                                                                                                           })
                                                                                                                         },
                                                                                                                       })(())
                                                                                                            })
                                                                                                          })
                                                                                                        })
                                                                                                      })
                                                                                                    })
                                                                                                  })));
                                                                                                hrec2.get().unwrap() })(n))(sigma))(nc))(s))(cl))(())
                                      })
                                    })
                                  })
                                })
                              })
                            })
                          }))
                      }))(())
           }))(())
}

fn CertiCoq_Benchmarks_lib_vs_VeriStar_the_loop(&'a self, x: u64, x0: &'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>, x1: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>, x2: CertiCoq_Benchmarks_lib_vs_M_t<'a>, x3: &'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_VeriStar_veristar_result<'a> {
  match self.CertiCoq_Benchmarks_lib_vs_VeriStar_the_loop_terminate()(
          x)(
          x0)(
          x1)(
          x2)(
          x3) {
    &Coq_Init_Specif_sig::exist(_, v) => {
      v
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_VeriStar_the_loop__curried(&'a self) -> &'a dyn Fn(u64) -> &'a dyn Fn(&'a Coq_Init_Datatypes_list<'a, &'a CertiCoq_Benchmarks_lib_vs_space_atom<'a>>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_clause<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_VeriStar_veristar_result<'a> {
  self.closure(move |x| {
    self.closure(move |x0| {
      self.closure(move |x1| {
        self.closure(move |x2| {
          self.closure(move |x3| {
            self.CertiCoq_Benchmarks_lib_vs_VeriStar_the_loop(
              x,
              x0,
              x1,
              x2,
              x3)
          })
        })
      })
    })
  })
}

fn CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_new_pures_set(&'a self, s: CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  s
}
fn CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_new_pures_set__curried(&'a self) -> &'a dyn Fn(CertiCoq_Benchmarks_lib_vs_M_t<'a>) -> CertiCoq_Benchmarks_lib_vs_M_t<'a> {
  self.closure(move |s| {
    self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_new_pures_set(
      s)
  })
}

fn CertiCoq_Benchmarks_lib_vs_empty_clause(&'a self) -> &'a CertiCoq_Benchmarks_lib_vs_clause<'a> {
  self.CertiCoq_Benchmarks_lib_vs_mkPureClause(
    self.alloc(
      Coq_Init_Datatypes_list::nil(
        PhantomData)),
    self.alloc(
      Coq_Init_Datatypes_list::nil(
        PhantomData)))
}

fn CertiCoq_Benchmarks_lib_vs_VeriStar_check_entailment(&'a self, ent: &'a CertiCoq_Benchmarks_lib_vs_entailment<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_VeriStar_veristar_result<'a> {
  let s =
    self.CertiCoq_Benchmarks_lib_vs_clause_list2set(
      self.CertiCoq_Benchmarks_lib_vs_VeriStar_pure_clauses()(
        self.Coq_Lists_List_map(
          self.CertiCoq_Benchmarks_lib_vs_order_eqv_clause__curried(),
          self.CertiCoq_Benchmarks_lib_vs_cnf(
            ent))));
  match ent {
    &CertiCoq_Benchmarks_lib_vs_entailment::Entailment(_, a, a0) => {
      match a {
        &CertiCoq_Benchmarks_lib_vs_assertion::Assertion(_, pi, sigma) => {
          match a0 {
            &CertiCoq_Benchmarks_lib_vs_assertion::Assertion(_, pi2, sigma2) => {
              __pair_elim!(
                piminus, piplus, {
                  __pair_elim!(
                    piminus2, piplus2, {
                      self.CertiCoq_Benchmarks_lib_vs_VeriStar_the_loop(
                        __pos_zerobit(
                          __pos_zerobit(
                            __pos_zerobit(
                              __pos_zerobit(
                                __pos_zerobit(
                                  __pos_zerobit(
                                    __pos_zerobit(
                                      __pos_zerobit(
                                        __pos_zerobit(
                                          __pos_onebit(
                                            __pos_zerobit(
                                              __pos_onebit(
                                                __pos_zerobit(
                                                  __pos_zerobit(
                                                    __pos_onebit(
                                                      __pos_onebit(
                                                        __pos_zerobit(
                                                          __pos_onebit(
                                                            __pos_zerobit(
                                                              __pos_onebit(
                                                                __pos_onebit(
                                                                  __pos_zerobit(
                                                                    __pos_zerobit(
                                                                      __pos_onebit(
                                                                        __pos_onebit(
                                                                          __pos_onebit(
                                                                            __pos_zerobit(
                                                                              __pos_onebit(
                                                                                __pos_onebit(
                                                                                  1))))))))))))))))))))))))))))),
                        sigma,
                        self.alloc(
                          CertiCoq_Benchmarks_lib_vs_clause::NegSpaceClause(
                            PhantomData,
                            piminus2,
                            sigma2,
                            piplus2)),
                        self.CertiCoq_Benchmarks_lib_vs_DebuggingHooks_print_new_pures_set(
                          s),
                        self.CertiCoq_Benchmarks_lib_vs_empty_clause())
                    },
                    self.CertiCoq_Benchmarks_lib_vs_mk_pureR(
                      pi2))
                },
                self.CertiCoq_Benchmarks_lib_vs_mk_pureR(
                  pi))
            },
          }
        },
      }
    },
  }
}
fn CertiCoq_Benchmarks_lib_vs_VeriStar_check_entailment__curried(&'a self) -> &'a dyn Fn(&'a CertiCoq_Benchmarks_lib_vs_entailment<'a>) -> &'a CertiCoq_Benchmarks_lib_vs_VeriStar_veristar_result<'a> {
  self.closure(move |ent| {
    self.CertiCoq_Benchmarks_lib_vs_VeriStar_check_entailment(
      ent)
  })
}

fn CertiCoq_Benchmarks_lib_vs_x(&'a self, p: u64) -> &'a CertiCoq_Benchmarks_lib_vs_expr<'a> {
  self.alloc(
    CertiCoq_Benchmarks_lib_vs_expr::Var(
      PhantomData,
      p))
}
fn CertiCoq_Benchmarks_lib_vs_x__curried(&'a self) -> &'a dyn Fn(u64) -> &'a CertiCoq_Benchmarks_lib_vs_expr<'a> {
  self.closure(move |p| {
    self.CertiCoq_Benchmarks_lib_vs_x(
      p)
  })
}

fn CertiCoq_Benchmarks_lib_vs_harder_ent(&'a self) -> &'a CertiCoq_Benchmarks_lib_vs_entailment<'a> {
  self.alloc(
    CertiCoq_Benchmarks_lib_vs_entailment::Entailment(
      PhantomData,
      self.alloc(
        CertiCoq_Benchmarks_lib_vs_assertion::Assertion(
          PhantomData,
          self.alloc(
            Coq_Init_Datatypes_list::nil(
              PhantomData)),
          self.alloc(
            Coq_Init_Datatypes_list::cons(
              PhantomData,
              self.alloc(
                CertiCoq_Benchmarks_lib_vs_space_atom::Next(
                  PhantomData,
                  self.CertiCoq_Benchmarks_lib_vs_x(
                    __pos_onebit(
                      __pos_zerobit(
                        __pos_zerobit(
                          1)))),
                  self.CertiCoq_Benchmarks_lib_vs_x(
                    __pos_onebit(
                      1)))),
              self.alloc(
                Coq_Init_Datatypes_list::cons(
                  PhantomData,
                  self.alloc(
                    CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                      PhantomData,
                      self.CertiCoq_Benchmarks_lib_vs_x(
                        __pos_onebit(
                          __pos_onebit(
                            1))),
                      self.CertiCoq_Benchmarks_lib_vs_x(
                        __pos_zerobit(
                          __pos_zerobit(
                            __pos_zerobit(
                              1)))))),
                  self.alloc(
                    Coq_Init_Datatypes_list::cons(
                      PhantomData,
                      self.alloc(
                        CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                          PhantomData,
                          self.CertiCoq_Benchmarks_lib_vs_x(
                            1),
                          self.CertiCoq_Benchmarks_lib_vs_x(
                            __pos_zerobit(
                              __pos_onebit(
                                1))))),
                      self.alloc(
                        Coq_Init_Datatypes_list::cons(
                          PhantomData,
                          self.alloc(
                            CertiCoq_Benchmarks_lib_vs_space_atom::Next(
                              PhantomData,
                              self.CertiCoq_Benchmarks_lib_vs_x(
                                __pos_zerobit(
                                  __pos_onebit(
                                    __pos_zerobit(
                                      1)))),
                              self.CertiCoq_Benchmarks_lib_vs_x(
                                __pos_zerobit(
                                  1)))),
                          self.alloc(
                            Coq_Init_Datatypes_list::cons(
                              PhantomData,
                              self.alloc(
                                CertiCoq_Benchmarks_lib_vs_space_atom::Next(
                                  PhantomData,
                                  self.CertiCoq_Benchmarks_lib_vs_x(
                                    __pos_onebit(
                                      1)),
                                  self.CertiCoq_Benchmarks_lib_vs_x(
                                    __pos_onebit(
                                      __pos_onebit(
                                        1))))),
                              self.alloc(
                                Coq_Init_Datatypes_list::cons(
                                  PhantomData,
                                  self.alloc(
                                    CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                                      PhantomData,
                                      self.CertiCoq_Benchmarks_lib_vs_x(
                                        __pos_onebit(
                                          __pos_zerobit(
                                            1))),
                                      self.CertiCoq_Benchmarks_lib_vs_x(
                                        __pos_zerobit(
                                          __pos_onebit(
                                            __pos_zerobit(
                                              1)))))),
                                  self.alloc(
                                    Coq_Init_Datatypes_list::cons(
                                      PhantomData,
                                      self.alloc(
                                        CertiCoq_Benchmarks_lib_vs_space_atom::Next(
                                          PhantomData,
                                          self.CertiCoq_Benchmarks_lib_vs_x(
                                            __pos_zerobit(
                                              __pos_zerobit(
                                                1))),
                                          self.CertiCoq_Benchmarks_lib_vs_x(
                                            __pos_onebit(
                                              __pos_zerobit(
                                                __pos_zerobit(
                                                  1)))))),
                                      self.alloc(
                                        Coq_Init_Datatypes_list::cons(
                                          PhantomData,
                                          self.alloc(
                                            CertiCoq_Benchmarks_lib_vs_space_atom::Next(
                                              PhantomData,
                                              self.CertiCoq_Benchmarks_lib_vs_x(
                                                __pos_onebit(
                                                  __pos_zerobit(
                                                    __pos_onebit(
                                                      1)))),
                                              self.CertiCoq_Benchmarks_lib_vs_x(
                                                __pos_onebit(
                                                  __pos_zerobit(
                                                    1))))),
                                          self.alloc(
                                            Coq_Init_Datatypes_list::cons(
                                              PhantomData,
                                              self.alloc(
                                                CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                                                  PhantomData,
                                                  self.CertiCoq_Benchmarks_lib_vs_x(
                                                    __pos_zerobit(
                                                      __pos_zerobit(
                                                        __pos_zerobit(
                                                          1)))),
                                                  self.CertiCoq_Benchmarks_lib_vs_x(
                                                    __pos_onebit(
                                                      __pos_zerobit(
                                                        1))))),
                                              self.alloc(
                                                Coq_Init_Datatypes_list::cons(
                                                  PhantomData,
                                                  self.alloc(
                                                    CertiCoq_Benchmarks_lib_vs_space_atom::Next(
                                                      PhantomData,
                                                      self.CertiCoq_Benchmarks_lib_vs_x(
                                                        __pos_onebit(
                                                          __pos_onebit(
                                                            __pos_zerobit(
                                                              1)))),
                                                      self.CertiCoq_Benchmarks_lib_vs_x(
                                                        __pos_zerobit(
                                                          __pos_zerobit(
                                                            __pos_onebit(
                                                              1)))))),
                                                  self.alloc(
                                                    Coq_Init_Datatypes_list::cons(
                                                      PhantomData,
                                                      self.alloc(
                                                        CertiCoq_Benchmarks_lib_vs_space_atom::Next(
                                                          PhantomData,
                                                          self.CertiCoq_Benchmarks_lib_vs_x(
                                                            __pos_zerobit(
                                                              __pos_zerobit(
                                                                __pos_onebit(
                                                                  1)))),
                                                          self.CertiCoq_Benchmarks_lib_vs_x(
                                                            __pos_onebit(
                                                              __pos_onebit(
                                                                __pos_zerobit(
                                                                  1)))))),
                                                      self.alloc(
                                                        Coq_Init_Datatypes_list::cons(
                                                          PhantomData,
                                                          self.alloc(
                                                            CertiCoq_Benchmarks_lib_vs_space_atom::Next(
                                                              PhantomData,
                                                              self.CertiCoq_Benchmarks_lib_vs_x(
                                                                __pos_zerobit(
                                                                  1)),
                                                              self.CertiCoq_Benchmarks_lib_vs_x(
                                                                __pos_zerobit(
                                                                  __pos_zerobit(
                                                                    1))))),
                                                          self.alloc(
                                                            Coq_Init_Datatypes_list::cons(
                                                              PhantomData,
                                                              self.alloc(
                                                                CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                                                                  PhantomData,
                                                                  self.CertiCoq_Benchmarks_lib_vs_x(
                                                                    __pos_zerobit(
                                                                      __pos_onebit(
                                                                        1))),
                                                                  self.CertiCoq_Benchmarks_lib_vs_x(
                                                                    __pos_onebit(
                                                                      1)))),
                                                              self.alloc(
                                                                Coq_Init_Datatypes_list::nil(
                                                                  PhantomData)))))))))))))))))))))))))))))),
      self.alloc(
        CertiCoq_Benchmarks_lib_vs_assertion::Assertion(
          PhantomData,
          self.alloc(
            Coq_Init_Datatypes_list::nil(
              PhantomData)),
          self.alloc(
            Coq_Init_Datatypes_list::cons(
              PhantomData,
              self.alloc(
                CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                  PhantomData,
                  self.CertiCoq_Benchmarks_lib_vs_x(
                    __pos_zerobit(
                      1)),
                  self.CertiCoq_Benchmarks_lib_vs_x(
                    __pos_zerobit(
                      __pos_onebit(
                        __pos_zerobit(
                          1)))))),
              self.alloc(
                Coq_Init_Datatypes_list::cons(
                  PhantomData,
                  self.alloc(
                    CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                      PhantomData,
                      self.CertiCoq_Benchmarks_lib_vs_x(
                        __pos_zerobit(
                          __pos_zerobit(
                            __pos_onebit(
                              1)))),
                      self.CertiCoq_Benchmarks_lib_vs_x(
                        __pos_onebit(
                          __pos_onebit(
                            __pos_zerobit(
                              1)))))),
                  self.alloc(
                    Coq_Init_Datatypes_list::cons(
                      PhantomData,
                      self.alloc(
                        CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                          PhantomData,
                          self.CertiCoq_Benchmarks_lib_vs_x(
                            __pos_onebit(
                              __pos_onebit(
                                __pos_zerobit(
                                  1)))),
                          self.CertiCoq_Benchmarks_lib_vs_x(
                            __pos_zerobit(
                              __pos_zerobit(
                                __pos_onebit(
                                  1)))))),
                      self.alloc(
                        Coq_Init_Datatypes_list::cons(
                          PhantomData,
                          self.alloc(
                            CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                              PhantomData,
                              self.CertiCoq_Benchmarks_lib_vs_x(
                                __pos_zerobit(
                                  __pos_onebit(
                                    1))),
                              self.CertiCoq_Benchmarks_lib_vs_x(
                                __pos_onebit(
                                  1)))),
                          self.alloc(
                            Coq_Init_Datatypes_list::cons(
                              PhantomData,
                              self.alloc(
                                CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                                  PhantomData,
                                  self.CertiCoq_Benchmarks_lib_vs_x(
                                    1),
                                  self.CertiCoq_Benchmarks_lib_vs_x(
                                    __pos_zerobit(
                                      __pos_onebit(
                                        1))))),
                              self.alloc(
                                Coq_Init_Datatypes_list::cons(
                                  PhantomData,
                                  self.alloc(
                                    CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                                      PhantomData,
                                      self.CertiCoq_Benchmarks_lib_vs_x(
                                        __pos_onebit(
                                          __pos_zerobit(
                                            __pos_onebit(
                                              1)))),
                                      self.CertiCoq_Benchmarks_lib_vs_x(
                                        __pos_onebit(
                                          __pos_zerobit(
                                            1))))),
                                  self.alloc(
                                    Coq_Init_Datatypes_list::cons(
                                      PhantomData,
                                      self.alloc(
                                        CertiCoq_Benchmarks_lib_vs_space_atom::Lseg(
                                          PhantomData,
                                          self.CertiCoq_Benchmarks_lib_vs_x(
                                            __pos_zerobit(
                                              __pos_onebit(
                                                __pos_zerobit(
                                                  1)))),
                                          self.CertiCoq_Benchmarks_lib_vs_x(
                                            __pos_zerobit(
                                              1)))),
                                      self.alloc(
                                        Coq_Init_Datatypes_list::nil(
                                          PhantomData))))))))))))))))))))
}

fn CertiCoq_Benchmarks_lib_vs_main_h(&'a self) -> &'a CertiCoq_Benchmarks_lib_vs_VeriStar_veristar_result<'a> {
  self.CertiCoq_Benchmarks_lib_vs_VeriStar_check_entailment(
    self.CertiCoq_Benchmarks_lib_vs_harder_ent())
}

fn CertiCoq_Benchmarks_tests_vs_hard(&'a self) -> bool {
  match self.CertiCoq_Benchmarks_lib_vs_main_h() {
    &CertiCoq_Benchmarks_lib_vs_VeriStar_veristar_result::Valid(_) => {
      true
    },
    &CertiCoq_Benchmarks_lib_vs_VeriStar_veristar_result::C_example(_, m) => {
      false
    },
    &CertiCoq_Benchmarks_lib_vs_VeriStar_veristar_result::Aborted(_, l, c) => {
      false
    },
  }
}
}
pub fn main() {
  Program::new().CertiCoq_Benchmarks_tests_vs_hard();
}
