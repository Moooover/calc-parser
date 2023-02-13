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
  direction: Direction,
  children: Option<Vec<ABNode>>,
  subseq: Option<Vec<ABNode>>,
) -> Vec<ABNode> {
  let node = ABNode {
    direction,
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
        println!("S24");
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
        println!("S34");
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
        println!("A24");
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
        println!("B24");
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
        println!("I0 '$'");
        return None;
      }
      (States::I0, 'a') => {
        println!("I0 'a'");
        let res = Rc::new(None);
        states.push(States::I1(res.clone()));
        states.push(States::S21(res, 'a'));
      }
      (States::I0, 'b') => {
        println!("I0 'b'");
        let res = Rc::new(None);
        states.push(States::I1(res.clone()));
        states.push(States::S31(res, 'b'));
      }
      (States::I1(res), '$') => {
        println!("I1 '$'");
        let res = Rc::try_unwrap(res).unwrap();
        let res = {
          // closure from grammar
          res
        };
        return res;
      }

      (States::S21(res, a), 'a') => {
        println!("S21 'a'");
        let sub_res = Rc::new(None);
        states.push(States::S22(res, a, sub_res.clone()));
        states.push(States::A21(sub_res, 'a'));
      }
      (States::S21(res, a), 'b') => {
        println!("S21 'b'");
        states.push(States::S23(res, a, Rc::new(None), 'b'));
      }
      (States::S22(res, a, A), 'b') => {
        println!("S22 'b'");
        states.push(States::S23(res, a, A, 'b'));
      }
      (States::S23(mut res, _a, A, _b), '$') => {
        println!("S23 '$'");
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
        println!("S23 'a'");
        let sub_res = Rc::new(None);
        states.push(States::S24(res, a, A, b, sub_res.clone()));
        states.push(States::S21(sub_res, 'a'));
      }
      (States::S23(res, a, A, b), 'b') => {
        println!("S23 'b'");
        let sub_res = Rc::new(None);
        states.push(States::S24(res, a, A, b, sub_res.clone()));
        states.push(States::S31(sub_res, 'b'));
      }
      (States::S24(_res, _a, _A, _b, _S), _) => unreachable!(),

      (States::S31(res, b), 'a') => {
        println!("S31 'a'");
        states.push(States::S33(res, b, Rc::new(None), 'a'));
      }
      (States::S31(res, b), 'b') => {
        println!("S31 'b'");
        let sub_res = Rc::new(None);
        states.push(States::S32(res, b, sub_res.clone()));
        states.push(States::B21(sub_res, 'b'));
      }
      (States::S32(res, b, B), 'a') => {
        println!("S32 'a'");
        states.push(States::S33(res, b, B, 'a'));
      }
      (States::S33(mut res, _b, B, _a), '$') => {
        println!("S33 '$'");
        let B = Rc::try_unwrap(B).unwrap();
        let S = None;
        unsafe {
          *Rc::get_mut_unchecked(&mut res) = Some({
            // closure from grammar
            compose(Direction::BA, B, S)
          });
        }
        // unwind.
      }
      (States::S33(res, b, B, a), 'a') => {
        println!("S33 'a'");
        let sub_res = Rc::new(None);
        states.push(States::S34(res, b, B, a, sub_res.clone()));
        states.push(States::S21(sub_res, 'a'));
      }
      (States::S33(res, b, B, a), 'b') => {
        println!("S33 'b'");
        let sub_res = Rc::new(None);
        states.push(States::S34(res, b, B, a, sub_res.clone()));
        states.push(States::S31(sub_res, 'b'));
      }
      (States::S34(_res, _b, _B, _a, _S), _) => unreachable!(),

      (States::A21(res, a), 'a') => {
        println!("A21 'a'");
        let sub_res = Rc::new(None);
        states.push(States::A22(res, a, sub_res.clone()));
        states.push(States::A21(sub_res, 'a'));
      }
      (States::A21(res, a), 'b') => {
        println!("A21 'b'");
        states.push(States::A23(res, a, Rc::new(None), 'b'));
      }
      (States::A22(res, a, A), 'b') => {
        println!("A22 'b'");
        states.push(States::A23(res, a, A, 'b'));
      }
      (States::A23(mut res, _a, A, _b), '$') => {
        println!("A23 '$'");
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
        println!("A23 'a'");
        let sub_res = Rc::new(None);
        states.push(States::A24(res, a, A, b, sub_res.clone()));
        states.push(States::A21(sub_res, 'a'));
      }
      (States::A23(res, a, A, b), 'b') => {
        println!("A23 'b'");
        let sub_res = Rc::new(None);
        states.push(States::A24(res, a, A, b, sub_res.clone()));
        states.push(States::B21(sub_res, 'b'));
      }
      (States::A24(_res, _a, _A, _b, _S), _) => unreachable!(),

      (States::B21(res, b), 'a') => {
        println!("B21 'a'");
        states.push(States::B23(res, b, Rc::new(None), 'a'));
      }
      (States::B21(res, b), 'b') => {
        println!("B21 'b'");
        let sub_res = Rc::new(None);
        states.push(States::B22(res, b, sub_res.clone()));
        states.push(States::B21(sub_res, 'b'));
      }
      (States::B22(res, b, B), 'a') => {
        println!("B22 'a'");
        states.push(States::B23(res, b, B, 'a'));
      }
      (States::B23(mut res, _b, B, _a), '$') => {
        println!("B23 '$'");
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
        println!("B23 'a'");
        let sub_res = Rc::new(None);
        states.push(States::B24(res, b, B, a, sub_res.clone()));
        states.push(States::A21(sub_res, 'a'));
      }
      (States::B23(res, b, B, a), 'b') => {
        println!("B23 'b'");
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

  println!("{:?}", parse_tree("abba".chars()));

  aug_bnf_impl::aug_bnf! {
    <S> => <A> <alias: B> $;
    <A> => 'a' <B>;
    <B> => 'b';
  };

  let mut buffer = "".to_string();
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
