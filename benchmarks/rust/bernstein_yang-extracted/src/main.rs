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

fn Coq_ZArith_BinIntDef_Z_mul(&'a self, a: i64, b: i64) -> i64 { a * b }
fn Coq_ZArith_BinIntDef_Z_mul__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> i64 {
  self.closure(move |x| {
    self.closure(move |y| {
      self.Coq_ZArith_BinIntDef_Z_mul(
        x,
        y)
    })
  })
}

fn Coq_ZArith_BinIntDef_Z_compare(&'a self, a: i64, b: i64) -> std::cmp::Ordering { a.cmp(&b) }
fn Coq_ZArith_BinIntDef_Z_compare__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> std::cmp::Ordering {
  self.closure(move |x| {
    self.closure(move |y| {
      self.Coq_ZArith_BinIntDef_Z_compare(
        x,
        y)
    })
  })
}

fn Coq_ZArith_BinIntDef_Z_ltb(&'a self, x: i64, y: i64) -> bool {
  match self.Coq_ZArith_BinIntDef_Z_compare(
          x,
          y) {
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
fn Coq_ZArith_BinIntDef_Z_ltb__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> bool {
  self.closure(move |x| {
    self.closure(move |y| {
      self.Coq_ZArith_BinIntDef_Z_ltb(
        x,
        y)
    })
  })
}

fn Coq_ZArith_BinIntDef_Z_add(&'a self, a: i64, b: i64) -> i64 { a + b }
fn Coq_ZArith_BinIntDef_Z_add__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> i64 {
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

fn Coq_ZArith_BinIntDef_Z_eqb(&'a self, a: i64, b: i64) -> bool { a == b }
fn Coq_ZArith_BinIntDef_Z_eqb__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> bool {
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

fn Coq_ZArith_BinIntDef_Z_odd(&'a self, z: i64) -> bool {
  __Z_elim!(
    {
      false
    },
    p, {
      __pos_elim!(
        p0, {
          true
        },
        p0, {
          false
        },
        {
          true
        },
        p)
    },
    p, {
      __pos_elim!(
        p0, {
          true
        },
        p0, {
          false
        },
        {
          true
        },
        p)
    },
    z)
}
fn Coq_ZArith_BinIntDef_Z_odd__curried(&'a self) -> &'a dyn Fn(i64) -> bool {
  self.closure(move |z| {
    self.Coq_ZArith_BinIntDef_Z_odd(
      z)
  })
}

fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_odd(&'a self) -> &'a dyn Fn(i64) -> bool {
  self.Coq_ZArith_BinIntDef_Z_odd__curried()
}

fn Coq_ZArith_BinIntDef_Z_opp(&'a self, a: i64) -> i64 { -a }
fn Coq_ZArith_BinIntDef_Z_opp__curried(&'a self) -> &'a dyn Fn(i64) -> i64 {
  self.closure(move |x| {
    self.Coq_ZArith_BinIntDef_Z_opp(
      x)
  })
}

fn Coq_ZArith_BinIntDef_Z_sub(&'a self, a: i64, b: i64) -> i64 { a - b }
fn Coq_ZArith_BinIntDef_Z_sub__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> i64 {
  self.closure(move |m| {
    self.closure(move |n| {
      self.Coq_ZArith_BinIntDef_Z_sub(
        m,
        n)
    })
  })
}

fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_shiftr(&'a self, a: i64, b: i64) -> i64 {
  __Z_elim!(
    {
      a
    },
    p, {
      hint_app(hint_app({ let iter_fix = self.alloc(std::cell::Cell::new(None));
                          iter_fix.set(Some(
                            self.closure(move |x| {
                              self.closure(move |n| {
                                __pos_elim!(
                                  n2, {
                                    __Z_elim!(
                                      {
                                        0
                                      },
                                      y, {
                                        __Z_frompos(
                                          __pos_zerobit(
                                            y))
                                      },
                                      y, {
                                        __Z_fromneg(
                                          __pos_zerobit(
                                            y))
                                      },
                                      hint_app(hint_app(iter_fix.get().unwrap())(hint_app(hint_app(iter_fix.get().unwrap())(x))(n2)))(n2))
                                  },
                                  n2, {
                                    hint_app(hint_app(iter_fix.get().unwrap())(hint_app(hint_app(iter_fix.get().unwrap())(x))(n2)))(n2)
                                  },
                                  {
                                    __Z_elim!(
                                      {
                                        0
                                      },
                                      y, {
                                        __Z_frompos(
                                          __pos_zerobit(
                                            y))
                                      },
                                      y, {
                                        __Z_fromneg(
                                          __pos_zerobit(
                                            y))
                                      },
                                      x)
                                  },
                                  n)
                              })
                            })));
                          iter_fix.get().unwrap() })(a))(p)
    },
    p, {
      hint_app(hint_app({ let iter_fix2 = self.alloc(std::cell::Cell::new(None));
                          iter_fix2.set(Some(
                            self.closure(move |x| {
                              self.closure(move |n| {
                                __pos_elim!(
                                  n2, {
                                    __Z_elim!(
                                      {
                                        0
                                      },
                                      p2, {
                                        __pos_elim!(
                                          p0, {
                                            __Z_frompos(
                                              __pos_elim!(
                                                p3, {
                                                  p3
                                                },
                                                p3, {
                                                  p3
                                                },
                                                {
                                                  1
                                                },
                                                p2))
                                          },
                                          p0, {
                                            __Z_frompos(
                                              __pos_elim!(
                                                p3, {
                                                  p3
                                                },
                                                p3, {
                                                  p3
                                                },
                                                {
                                                  1
                                                },
                                                p2))
                                          },
                                          {
                                            0
                                          },
                                          p2)
                                      },
                                      p2, {
                                        __Z_fromneg(
                                          __pos_elim!(
                                            p3, {
                                              hint_app({ let succ = self.alloc(std::cell::Cell::new(None));
                                                         succ.set(Some(
                                                           self.closure(move |x2| {
                                                             __pos_elim!(
                                                               p4, {
                                                                 __pos_zerobit(
                                                                   hint_app(succ.get().unwrap())(p4))
                                                               },
                                                               p4, {
                                                                 __pos_onebit(
                                                                   p4)
                                                               },
                                                               {
                                                                 __pos_zerobit(
                                                                   1)
                                                               },
                                                               x2)
                                                           })));
                                                         succ.get().unwrap() })(p3)
                                            },
                                            p3, {
                                              p3
                                            },
                                            {
                                              1
                                            },
                                            p2))
                                      },
                                      hint_app(hint_app(iter_fix2.get().unwrap())(hint_app(hint_app(iter_fix2.get().unwrap())(x))(n2)))(n2))
                                  },
                                  n2, {
                                    hint_app(hint_app(iter_fix2.get().unwrap())(hint_app(hint_app(iter_fix2.get().unwrap())(x))(n2)))(n2)
                                  },
                                  {
                                    __Z_elim!(
                                      {
                                        0
                                      },
                                      p2, {
                                        __pos_elim!(
                                          p0, {
                                            __Z_frompos(
                                              __pos_elim!(
                                                p3, {
                                                  p3
                                                },
                                                p3, {
                                                  p3
                                                },
                                                {
                                                  1
                                                },
                                                p2))
                                          },
                                          p0, {
                                            __Z_frompos(
                                              __pos_elim!(
                                                p3, {
                                                  p3
                                                },
                                                p3, {
                                                  p3
                                                },
                                                {
                                                  1
                                                },
                                                p2))
                                          },
                                          {
                                            0
                                          },
                                          p2)
                                      },
                                      p2, {
                                        __Z_fromneg(
                                          __pos_elim!(
                                            p3, {
                                              hint_app({ let succ2 = self.alloc(std::cell::Cell::new(None));
                                                         succ2.set(Some(
                                                           self.closure(move |x2| {
                                                             __pos_elim!(
                                                               p4, {
                                                                 __pos_zerobit(
                                                                   hint_app(succ2.get().unwrap())(p4))
                                                               },
                                                               p4, {
                                                                 __pos_onebit(
                                                                   p4)
                                                               },
                                                               {
                                                                 __pos_zerobit(
                                                                   1)
                                                               },
                                                               x2)
                                                           })));
                                                         succ2.get().unwrap() })(p3)
                                            },
                                            p3, {
                                              p3
                                            },
                                            {
                                              1
                                            },
                                            p2))
                                      },
                                      x)
                                  },
                                  n)
                              })
                            })));
                          iter_fix2.get().unwrap() })(a))(p)
    },
    __Z_elim!(
      {
        0
      },
      x, {
        __Z_fromneg(
          x)
      },
      x, {
        __Z_frompos(
          x)
      },
      b))
}
fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_shiftr__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> i64 {
  self.closure(move |a| {
    self.closure(move |b| {
      self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_shiftr(
        a,
        b)
    })
  })
}

fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_divstep(&'a self, d: i64, f: i64, g: i64) -> __pair<__pair<i64, i64>, i64> {
  match __andb!(
          self.Coq_ZArith_BinIntDef_Z_ltb(
            0,
            d),
          self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_odd()(
            g)) {
    true => {
      __mk_pair(
        __mk_pair(
          self.Coq_ZArith_BinIntDef_Z_sub(
            __Z_frompos(
              1),
            d),
          g),
        self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_shiftr(
          self.Coq_ZArith_BinIntDef_Z_sub(
            g,
            f),
          __Z_frompos(
            1)))
    },
    false => {
      __mk_pair(
        __mk_pair(
          self.Coq_ZArith_BinIntDef_Z_add(
            __Z_frompos(
              1),
            d),
          f),
        self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_shiftr(
          self.Coq_ZArith_BinIntDef_Z_add(
            g,
            self.Coq_ZArith_BinIntDef_Z_mul(
              match self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_odd()(
                      g) {
                true => {
                  __Z_frompos(
                    1)
                },
                false => {
                  0
                },
              },
              f)),
          __Z_frompos(
            1)))
    },
  }
}
fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_divstep__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> __pair<__pair<i64, i64>, i64> {
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

fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_needs_n_steps(&'a self, d: i64, a: i64, b: i64, n: u64) -> bool {
  __nat_elim!(
    {
      true
    },
    n2, {
      match self.Coq_ZArith_BinIntDef_Z_eqb(
              b,
              0) {
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
    n)
}
fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_needs_n_steps__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> &'a dyn Fn(u64) -> bool {
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

fn Coq_ZArith_BinIntDef_Z_min(&'a self, a: i64, b: i64) -> i64 { std::cmp::min(a, b) }
fn Coq_ZArith_BinIntDef_Z_min__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> i64 {
  self.closure(move |n| {
    self.closure(move |m| {
      self.Coq_ZArith_BinIntDef_Z_min(
        n,
        m)
    })
  })
}

fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_min_needs_n_steps_nat(&'a self, a: i64, b: i64, n: u64, acc: i64, fuel: u64) -> i64 {
  __nat_elim!(
    {
      0
    },
    fuel2, {
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
                  __Z_frompos(
                    __pos_zerobit(
                      1))),
                0,
                n,
                acc,
                fuel2)
            },
            false => {
              match __orb!(
                      self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_needs_n_steps(
                        __Z_frompos(
                          1),
                        a,
                        self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_shiftr(
                          b,
                          __Z_frompos(
                            1)),
                        n),
                      self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_needs_n_steps(
                        __Z_frompos(
                          1),
                        a,
                        self.Coq_ZArith_BinIntDef_Z_opp(
                          self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_shiftr(
                            b,
                            __Z_frompos(
                              1))),
                        n)) {
                true => {
                  self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_min_needs_n_steps_nat(
                    self.Coq_ZArith_BinIntDef_Z_add(
                      a,
                      __Z_frompos(
                        __pos_zerobit(
                          1))),
                    0,
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
                      __Z_frompos(
                        __pos_zerobit(
                          1))),
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
    fuel)
}
fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_min_needs_n_steps_nat__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> &'a dyn Fn(u64) -> &'a dyn Fn(i64) -> &'a dyn Fn(u64) -> i64 {
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

fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_shiftl(&'a self, a: i64, b: i64) -> i64 {
  __Z_elim!(
    {
      a
    },
    p, {
      hint_app(hint_app({ let iter_fix3 = self.alloc(std::cell::Cell::new(None));
                          iter_fix3.set(Some(
                            self.closure(move |x| {
                              self.closure(move |n| {
                                __pos_elim!(
                                  n2, {
                                    __Z_elim!(
                                      {
                                        0
                                      },
                                      y, {
                                        __Z_frompos(
                                          __pos_zerobit(
                                            y))
                                      },
                                      y, {
                                        __Z_fromneg(
                                          __pos_zerobit(
                                            y))
                                      },
                                      hint_app(hint_app(iter_fix3.get().unwrap())(hint_app(hint_app(iter_fix3.get().unwrap())(x))(n2)))(n2))
                                  },
                                  n2, {
                                    hint_app(hint_app(iter_fix3.get().unwrap())(hint_app(hint_app(iter_fix3.get().unwrap())(x))(n2)))(n2)
                                  },
                                  {
                                    __Z_elim!(
                                      {
                                        0
                                      },
                                      y, {
                                        __Z_frompos(
                                          __pos_zerobit(
                                            y))
                                      },
                                      y, {
                                        __Z_fromneg(
                                          __pos_zerobit(
                                            y))
                                      },
                                      x)
                                  },
                                  n)
                              })
                            })));
                          iter_fix3.get().unwrap() })(a))(p)
    },
    p, {
      hint_app(hint_app({ let iter_fix4 = self.alloc(std::cell::Cell::new(None));
                          iter_fix4.set(Some(
                            self.closure(move |x| {
                              self.closure(move |n| {
                                __pos_elim!(
                                  n2, {
                                    __Z_elim!(
                                      {
                                        0
                                      },
                                      p2, {
                                        __pos_elim!(
                                          p0, {
                                            __Z_frompos(
                                              __pos_elim!(
                                                p3, {
                                                  p3
                                                },
                                                p3, {
                                                  p3
                                                },
                                                {
                                                  1
                                                },
                                                p2))
                                          },
                                          p0, {
                                            __Z_frompos(
                                              __pos_elim!(
                                                p3, {
                                                  p3
                                                },
                                                p3, {
                                                  p3
                                                },
                                                {
                                                  1
                                                },
                                                p2))
                                          },
                                          {
                                            0
                                          },
                                          p2)
                                      },
                                      p2, {
                                        __Z_fromneg(
                                          __pos_elim!(
                                            p3, {
                                              hint_app({ let succ3 = self.alloc(std::cell::Cell::new(None));
                                                         succ3.set(Some(
                                                           self.closure(move |x2| {
                                                             __pos_elim!(
                                                               p4, {
                                                                 __pos_zerobit(
                                                                   hint_app(succ3.get().unwrap())(p4))
                                                               },
                                                               p4, {
                                                                 __pos_onebit(
                                                                   p4)
                                                               },
                                                               {
                                                                 __pos_zerobit(
                                                                   1)
                                                               },
                                                               x2)
                                                           })));
                                                         succ3.get().unwrap() })(p3)
                                            },
                                            p3, {
                                              p3
                                            },
                                            {
                                              1
                                            },
                                            p2))
                                      },
                                      hint_app(hint_app(iter_fix4.get().unwrap())(hint_app(hint_app(iter_fix4.get().unwrap())(x))(n2)))(n2))
                                  },
                                  n2, {
                                    hint_app(hint_app(iter_fix4.get().unwrap())(hint_app(hint_app(iter_fix4.get().unwrap())(x))(n2)))(n2)
                                  },
                                  {
                                    __Z_elim!(
                                      {
                                        0
                                      },
                                      p2, {
                                        __pos_elim!(
                                          p0, {
                                            __Z_frompos(
                                              __pos_elim!(
                                                p3, {
                                                  p3
                                                },
                                                p3, {
                                                  p3
                                                },
                                                {
                                                  1
                                                },
                                                p2))
                                          },
                                          p0, {
                                            __Z_frompos(
                                              __pos_elim!(
                                                p3, {
                                                  p3
                                                },
                                                p3, {
                                                  p3
                                                },
                                                {
                                                  1
                                                },
                                                p2))
                                          },
                                          {
                                            0
                                          },
                                          p2)
                                      },
                                      p2, {
                                        __Z_fromneg(
                                          __pos_elim!(
                                            p3, {
                                              hint_app({ let succ4 = self.alloc(std::cell::Cell::new(None));
                                                         succ4.set(Some(
                                                           self.closure(move |x2| {
                                                             __pos_elim!(
                                                               p4, {
                                                                 __pos_zerobit(
                                                                   hint_app(succ4.get().unwrap())(p4))
                                                               },
                                                               p4, {
                                                                 __pos_onebit(
                                                                   p4)
                                                               },
                                                               {
                                                                 __pos_zerobit(
                                                                   1)
                                                               },
                                                               x2)
                                                           })));
                                                         succ4.get().unwrap() })(p3)
                                            },
                                            p3, {
                                              p3
                                            },
                                            {
                                              1
                                            },
                                            p2))
                                      },
                                      x)
                                  },
                                  n)
                              })
                            })));
                          iter_fix4.get().unwrap() })(a))(p)
    },
    b)
}
fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_shiftl__curried(&'a self) -> &'a dyn Fn(i64) -> &'a dyn Fn(i64) -> i64 {
  self.closure(move |a| {
    self.closure(move |b| {
      self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_shiftl(
        a,
        b)
    })
  })
}

fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_nat_shiftl(&'a self, a: u64, n: u64) -> u64 {
  __nat_elim!(
    {
      a
    },
    n2, {
      hint_app(hint_app({ let add = self.alloc(std::cell::Cell::new(None));
                          add.set(Some(
                            self.closure(move |n3| {
                              self.closure(move |m| {
                                __nat_elim!(
                                  {
                                    m
                                  },
                                  p, {
                                    __nat_succ(
                                      hint_app(hint_app(add.get().unwrap())(p))(m))
                                  },
                                  n3)
                              })
                            })));
                          add.get().unwrap() })(self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_nat_shiftl(
                                                  a,
                                                  n2)))(self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_nat_shiftl(
                                                          a,
                                                          n2))
    },
    n)
}
fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_nat_shiftl__curried(&'a self) -> &'a dyn Fn(u64) -> &'a dyn Fn(u64) -> u64 {
  self.closure(move |a| {
    self.closure(move |n| {
      self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_nat_shiftl(
        a,
        n)
    })
  })
}

fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_W(&'a self, n: u64) -> i64 {
  self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_min_needs_n_steps_nat(
    __Z_frompos(
      1),
    0,
    n,
    self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_shiftl(
      __Z_frompos(
        1),
      __Z_frompos(
        __pos_zerobit(
          __pos_onebit(
            __pos_onebit(
              __pos_onebit(
                __pos_onebit(
                  1))))))),
    self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_nat_shiftl(
      __nat_succ(
        0),
      __nat_succ(
        __nat_succ(
          __nat_succ(
            __nat_succ(
              __nat_succ(
                __nat_succ(
                  __nat_succ(
                    __nat_succ(
                      __nat_succ(
                        __nat_succ(
                          __nat_succ(
                            __nat_succ(
                              __nat_succ(
                                __nat_succ(
                                  __nat_succ(
                                    __nat_succ(
                                      __nat_succ(
                                        __nat_succ(
                                          __nat_succ(
                                            __nat_succ(
                                              __nat_succ(
                                                __nat_succ(
                                                  __nat_succ(
                                                    __nat_succ(
                                                      __nat_succ(
                                                        __nat_succ(
                                                          __nat_succ(
                                                            __nat_succ(
                                                              __nat_succ(
                                                                __nat_succ(
                                                                  __nat_succ(
                                                                    __nat_succ(
                                                                      __nat_succ(
                                                                        __nat_succ(
                                                                          __nat_succ(
                                                                            __nat_succ(
                                                                              __nat_succ(
                                                                                __nat_succ(
                                                                                  __nat_succ(
                                                                                    __nat_succ(
                                                                                      __nat_succ(
                                                                                        __nat_succ(
                                                                                          __nat_succ(
                                                                                            __nat_succ(
                                                                                              0))))))))))))))))))))))))))))))))))))))))))))))
}
fn CertiCoq_Benchmarks_lib_BernsteinYangTermination_W__curried(&'a self) -> &'a dyn Fn(u64) -> i64 {
  self.closure(move |n| {
    self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_W(
      n)
  })
}

fn CertiCoq_Benchmarks_tests_bernstein_yang(&'a self) -> i64 {
  self.CertiCoq_Benchmarks_lib_BernsteinYangTermination_W(
    __nat_succ(
      __nat_succ(
        __nat_succ(
          __nat_succ(
            __nat_succ(
              __nat_succ(
                __nat_succ(
                  __nat_succ(
                    __nat_succ(
                      __nat_succ(
                        0)))))))))))
}
}
pub fn main() {
  Program::new().CertiCoq_Benchmarks_tests_bernstein_yang();
}
