#![feature(get_mut_unchecked)]

mod aug_bnf_dyn;

use aug_bnf_dyn::{GrammarParser, Production};
use std::iter::Peekable;
use std::rc::Rc;

pub fn fmt2<T: std::fmt::Display>(v: &Vec<T>) {
  for (i, c) in v.iter().enumerate() {
    if i > 0 {
      print!(" ");
    }
    print!("{}", c);
  }
}

#[derive(Debug)]
enum Direction {
  AB,
  BA,
}

#[derive(Debug)]
struct ABNode {
  direction: Direction,
  children: Option<Vec<ABNode>>,
}

fn compose(
  dir: Direction,
  children: Option<Vec<ABNode>>,
  subseq: Option<Vec<ABNode>>,
) -> Vec<ABNode> {
  let node = ABNode {
    direction: Direction::AB,
    children,
  };

  match subseq {
    Some(mut subseq) => {
      subseq.insert(0, node);
      return subseq;
    }
    None => {
      return vec![node];
    }
  };
}

/*
I => Sㅓ { $S }

S1 => '' { () }
S2 => 'a' A 'b' S {
  compose(Direction::AB, $A, $S)
}
S3 => 'b' B 'a' S {
  compose(Direction::BA, $B, $S)
}

A1 => ''
A2 => aAbA
B1 => ''
B2 => bBaB
 */
enum States {
  // I -> Sㅓ
  I0,
  I1(Rc<Option<Vec<ABNode>>>),
  // I2(Rc<Option<Vec<ABNode>>>),

  // S1 -> e
  // S10,
  // S11,
  // S12,

  // S2 -> aAbS
  // S20,
  S21(Rc<Option<Vec<ABNode>>>, char),
  S22(Rc<Option<Vec<ABNode>>>, char, Rc<Option<Vec<ABNode>>>),
  S23(Rc<Option<Vec<ABNode>>>, char, Rc<Option<Vec<ABNode>>>, char),
  S24(
    Rc<Option<Vec<ABNode>>>,
    char,
    Rc<Option<Vec<ABNode>>>,
    char,
    Rc<Option<Vec<ABNode>>>,
  ),

  // S3 -> bBaS
  // S30,
  S31(Rc<Option<Vec<ABNode>>>, char),
  S32(Rc<Option<Vec<ABNode>>>, char, Rc<Option<Vec<ABNode>>>),
  S33(Rc<Option<Vec<ABNode>>>, char, Rc<Option<Vec<ABNode>>>, char),
  S34(
    Rc<Option<Vec<ABNode>>>,
    char,
    Rc<Option<Vec<ABNode>>>,
    char,
    Rc<Option<Vec<ABNode>>>,
  ),

  // A1 -> e
  // A10,
  // A11,

  // A2 -> aAbA
  // A20,
  A21(Rc<Option<Vec<ABNode>>>, char),
  A22(Rc<Option<Vec<ABNode>>>, char, Rc<Option<Vec<ABNode>>>),
  A23(Rc<Option<Vec<ABNode>>>, char, Rc<Option<Vec<ABNode>>>, char),
  A24(
    Rc<Option<Vec<ABNode>>>,
    char,
    Rc<Option<Vec<ABNode>>>,
    char,
    Rc<Option<Vec<ABNode>>>,
  ),

  // B1 -> e
  // B10,
  // B11,

  // B2 -> bBaB
  // B20,
  B21(Rc<Option<Vec<ABNode>>>, char),
  B22(Rc<Option<Vec<ABNode>>>, char, Rc<Option<Vec<ABNode>>>),
  B23(Rc<Option<Vec<ABNode>>>, char, Rc<Option<Vec<ABNode>>>, char),
  B24(
    Rc<Option<Vec<ABNode>>>,
    char,
    Rc<Option<Vec<ABNode>>>,
    char,
    Rc<Option<Vec<ABNode>>>,
  ),
}

#[allow(non_snake_case)]
fn parse_tree<I: Iterator<Item = char>>(mut i: I) -> Option<Vec<ABNode>> {
  let mut states = vec![States::I0];

  loop {
    let state = states.pop().unwrap();

    // Try matching against states which don't look at the next token, i.e.
    // don't push.
    match state {
      States::S24(mut res, _a, A, _b, S) => {
        let A = Rc::try_unwrap(A).unwrap();
        let S = Rc::try_unwrap(S).unwrap();
        unsafe {
          *Rc::get_mut_unchecked(&mut res) = Some({
            // closure from grammar
            compose(Direction::AB, A, S)
          });
        }
        // unwind.
        continue;
      }
      States::S34(mut res, _b, B, _a, S) => {
        let B = Rc::try_unwrap(B).unwrap();
        let S = Rc::try_unwrap(S).unwrap();
        unsafe {
          *Rc::get_mut_unchecked(&mut res) = Some({
            // closure from grammar
            compose(Direction::BA, B, S)
          });
        }
        // unwind.
        continue;
      }
      States::A24(mut res, _a, A, _b, S) => {
        let A = Rc::try_unwrap(A).unwrap();
        let S = Rc::try_unwrap(S).unwrap();
        unsafe {
          *Rc::get_mut_unchecked(&mut res) = Some({
            // closure from grammar
            compose(Direction::AB, A, S)
          });
        }
        // unwind.
        continue;
      }
      States::B24(mut res, _b, B, _a, S) => {
        let B = Rc::try_unwrap(B).unwrap();
        let S = Rc::try_unwrap(S).unwrap();
        unsafe {
          *Rc::get_mut_unchecked(&mut res) = Some({
            // closure from grammar
            compose(Direction::BA, B, S)
          });
        }
        // unwind.
        continue;
      }
      _ => {}
    }

    let peek_char = i.next().unwrap_or('$');
    match (state, peek_char) {
      (States::I0, '$') => {
        return None;
      }
      (States::I0, 'a') => {
        let res = Rc::new(None);
        states.push(States::I1(res.clone()));
        states.push(States::S21(res, 'a'));
      }
      (States::I0, 'b') => {
        let res = Rc::new(None);
        states.push(States::I1(res.clone()));
        states.push(States::S31(res, 'b'));
      }
      (States::I1(res), '$') => {
        let res = Rc::try_unwrap(res).unwrap();
        let res = {
          // closure from grammar
          res
        };
        return res;
      }

      (States::S21(res, a), 'a') => {
        let sub_res = Rc::new(None);
        states.push(States::S22(res, a, sub_res.clone()));
        states.push(States::A21(sub_res, 'a'));
      }
      (States::S21(res, a), 'b') => {
        states.push(States::S23(res, a, Rc::new(None), 'b'));
      }
      (States::S22(res, a, A), 'b') => {
        states.push(States::S23(res, a, A, 'b'));
      }
      (States::S23(mut res, _a, A, _b), '$') => {
        let A = Rc::try_unwrap(A).unwrap();
        let S = None;
        unsafe {
          *Rc::get_mut_unchecked(&mut res) = Some({
            // closure from grammar
            compose(Direction::AB, A, S)
          });
        }
        // unwind.
      }
      (States::S23(res, a, A, b), 'a') => {
        let sub_res = Rc::new(None);
        states.push(States::S24(res, a, A, b, sub_res.clone()));
        states.push(States::S21(sub_res, 'a'));
      }
      (States::S23(res, a, A, b), 'b') => {
        let sub_res = Rc::new(None);
        states.push(States::S24(res, a, A, b, sub_res.clone()));
        states.push(States::S31(sub_res, 'b'));
      }
      (States::S24(_res, _a, _A, _b, _S), _) => unreachable!(),

      (States::S31(res, b), 'a') => {
        states.push(States::S33(res, b, Rc::new(None), 'a'));
      }
      (States::S31(res, b), 'b') => {
        let sub_res = Rc::new(None);
        states.push(States::S32(res, b, sub_res.clone()));
        states.push(States::B21(sub_res, 'b'));
      }
      (States::S32(res, b, B), 'a') => {
        states.push(States::S33(res, b, B, 'a'));
      }
      (States::S33(mut res, _b, B, _a), '$') => {
        let B = Rc::try_unwrap(B).unwrap();
        unsafe {
          *Rc::get_mut_unchecked(&mut res) = Some({
            // closure from grammar
            compose(Direction::BA, B, None)
          });
        }
        // unwind.
      }
      (States::S33(res, b, B, a), 'a') => {
        let sub_res = Rc::new(None);
        states.push(States::S34(res, b, B, a, sub_res.clone()));
        states.push(States::S21(sub_res, 'a'));
      }
      (States::S33(res, b, B, a), 'b') => {
        let sub_res = Rc::new(None);
        states.push(States::S34(res, b, B, a, sub_res.clone()));
        states.push(States::S31(sub_res, 'b'));
      }
      (States::S34(_res, _b, _B, _a, _S), _) => unreachable!(),

      (States::A21(res, a), 'a') => {
        let sub_res = Rc::new(None);
        states.push(States::A22(res, a, sub_res.clone()));
        states.push(States::A21(sub_res, 'a'));
      }
      (States::A21(res, a), 'b') => {
        states.push(States::A23(res, a, Rc::new(None), 'b'));
      }
      (States::A22(res, a, A), 'b') => {
        states.push(States::A23(res, a, A, 'b'));
      }
      (States::A23(mut res, _a, A, _b), '$') => {
        let A = Rc::try_unwrap(A).unwrap();
        unsafe {
          *Rc::get_mut_unchecked(&mut res) = Some({
            // closure from grammar
            compose(Direction::AB, A, None)
          });
        }
        // unwind.
      }
      (States::A23(res, a, A, b), 'a') => {
        let sub_res = Rc::new(None);
        states.push(States::A24(res, a, A, b, sub_res.clone()));
        states.push(States::A21(sub_res, 'a'));
      }
      (States::A23(res, a, A, b), 'b') => {
        let sub_res = Rc::new(None);
        states.push(States::A24(res, a, A, b, sub_res.clone()));
        states.push(States::B21(sub_res, 'b'));
      }
      (States::A24(_res, _a, _A, _b, _S), _) => unreachable!(),

      (States::B21(res, b), 'a') => {
        states.push(States::B23(res, b, Rc::new(None), 'a'));
      }
      (States::B21(res, b), 'b') => {
        let sub_res = Rc::new(None);
        states.push(States::B22(res, b, sub_res.clone()));
        states.push(States::B21(sub_res, 'b'));
      }
      (States::B22(res, b, B), 'a') => {
        states.push(States::B23(res, b, B, 'a'));
      }
      (States::B23(mut res, _b, B, _a), '$') => {
        let B = Rc::try_unwrap(B).unwrap();
        unsafe {
          *Rc::get_mut_unchecked(&mut res) = Some({
            // closure from grammar
            compose(Direction::BA, B, None)
          });
        }
        // unwind.
      }
      (States::B23(res, b, B, a), 'a') => {
        let sub_res = Rc::new(None);
        states.push(States::B24(res, b, B, a, sub_res.clone()));
        states.push(States::A21(sub_res, 'a'));
      }
      (States::B23(res, b, B, a), 'b') => {
        let sub_res = Rc::new(None);
        states.push(States::B24(res, b, B, a, sub_res.clone()));
        states.push(States::B21(sub_res, 'b'));
      }
      (States::B24(_res, _b, _B, _a, _S), _) => unreachable!(),

      _ => panic!("Unexpected token '{}'", peek_char),
    }
  }
}

fn main() {
  let mut p = GrammarParser::<char>::new('I', '$');
  p.add_production(Production::new('I', vec!['S', '$']));
  p.add_production(Production::new('S', vec![]));
  p.add_production(Production::new('S', vec!['a', 'A', 'b', 'S']));
  p.add_production(Production::new('S', vec!['b', 'B', 'a', 'S']));
  p.add_production(Production::new('A', vec![]));
  p.add_production(Production::new('A', vec!['a', 'A', 'b', 'A']));
  p.add_production(Production::new('B', vec![]));
  p.add_production(Production::new('B', vec!['b', 'B', 'a', 'B']));

  println!("{}", p);

  parse_tree("abba".chars());

  aug_bnf_impl::aug_bnf! {
    <S> => <A> <alias: B> $;
    <A> => 'a' <B>;
    <B> => 'b';
  };

  let mut buffer: String = "".to_string();
  while let Ok(_) = std::io::stdin().read_line(&mut buffer) {
    buffer.remove(buffer.len() - 1);

    if buffer == "quit" {
      break;
    }

    let v: Vec<char> = buffer.chars().collect();
    if let Some(ast_node) = p.parse(v.iter()) {
      println!("{}:\n{}", buffer, ast_node);
    } else {
      println!("Failed to parse!");
    }
    buffer.clear();
  }
}
