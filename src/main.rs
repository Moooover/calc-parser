#![feature(get_mut_unchecked)]
#![allow(dead_code)]

mod aug_bnf_dyn;

// use std::rc::Rc;

// pub fn fmt2<T: std::fmt::Display>(v: &Vec<T>) {
//   for (i, c) in v.iter().enumerate() {
//     if i > 0 {
//       print!(" ");
//     }
//     print!("{}", c);
//   }
// }

// #[derive(Debug)]
// enum Direction {
//   AB,
//   BA,
// }

// #[derive(Debug)]
// struct ABNode {
//   direction: Direction,
//   children: Option<Vec<ABNode>>,
// }

// impl std::fmt::Display for ABNode {
//   fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
//     let children_str = match &self.children {
//       Some(vec) => vec
//         .iter()
//         .fold("".to_string(), |s, node| s + &format!("{}", node)),
//       None => "".to_string(),
//     };
//     match self.direction {
//       Direction::AB => write!(f, "a{}b", children_str),
//       Direction::BA => write!(f, "b{}a", children_str),
//     }
//   }
// }

// fn compose(
//   direction: Direction,
//   children: Option<Vec<ABNode>>,
//   subseq: Option<Vec<ABNode>>,
// ) -> Vec<ABNode> {
//   let node = ABNode {
//     direction,
//     children,
//   };

//   match subseq {
//     Some(mut subseq) => {
//       subseq.insert(0, node);
//       return subseq;
//     }
//     None => {
//       return vec![node];
//     }
//   };
// }

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
// enum States {
//   // I -> Sㅓ
//   I0,
//   I1(Rc<Option<Vec<ABNode>>>),
//   // I2,

//   // S1 -> e
//   // S10,
//   // S11,
//   // S12,

//   // S2 -> aAbS
//   // S20,
//   S21(Rc<Option<Vec<ABNode>>>, char),
//   S22(Rc<Option<Vec<ABNode>>>, char, Rc<Option<Vec<ABNode>>>),
//   S23(Rc<Option<Vec<ABNode>>>, char, Rc<Option<Vec<ABNode>>>, char),
//   S24(
//     Rc<Option<Vec<ABNode>>>,
//     char,
//     Rc<Option<Vec<ABNode>>>,
//     char,
//     Rc<Option<Vec<ABNode>>>,
//   ),

//   // S3 -> bBaS
//   // S30,
//   S31(Rc<Option<Vec<ABNode>>>, char),
//   S32(Rc<Option<Vec<ABNode>>>, char, Rc<Option<Vec<ABNode>>>),
//   S33(Rc<Option<Vec<ABNode>>>, char, Rc<Option<Vec<ABNode>>>, char),
//   S34(
//     Rc<Option<Vec<ABNode>>>,
//     char,
//     Rc<Option<Vec<ABNode>>>,
//     char,
//     Rc<Option<Vec<ABNode>>>,
//   ),

//   // A1 -> e
//   // A10,
//   // A11,

//   // A2 -> aAbA
//   // A20,
//   A21(Rc<Option<Vec<ABNode>>>, char),
//   A22(Rc<Option<Vec<ABNode>>>, char, Rc<Option<Vec<ABNode>>>),
//   A23(Rc<Option<Vec<ABNode>>>, char, Rc<Option<Vec<ABNode>>>, char),
//   A24(
//     Rc<Option<Vec<ABNode>>>,
//     char,
//     Rc<Option<Vec<ABNode>>>,
//     char,
//     Rc<Option<Vec<ABNode>>>,
//   ),

//   // B1 -> e
//   // B10,
//   // B11,

//   // B2 -> bBaB
//   // B20,
//   B21(Rc<Option<Vec<ABNode>>>, char),
//   B22(Rc<Option<Vec<ABNode>>>, char, Rc<Option<Vec<ABNode>>>),
//   B23(Rc<Option<Vec<ABNode>>>, char, Rc<Option<Vec<ABNode>>>, char),
//   B24(
//     Rc<Option<Vec<ABNode>>>,
//     char,
//     Rc<Option<Vec<ABNode>>>,
//     char,
//     Rc<Option<Vec<ABNode>>>,
//   ),
// }

// impl std::fmt::Display for States {
//   fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
//     write!(
//       f,
//       "{}",
//       match self {
//         States::I0 => "I0",
//         States::I1(_) => "I1",
//         States::S21(_, _) => "S21",
//         States::S22(_, _, _) => "S22",
//         States::S23(_, _, _, _) => "S23",
//         States::S24(_, _, _, _, _) => "S24",
//         States::S31(_, _) => "S31",
//         States::S32(_, _, _) => "S32",
//         States::S33(_, _, _, _) => "S33",
//         States::S34(_, _, _, _, _) => "S34",
//         States::A21(_, _) => "A21",
//         States::A22(_, _, _) => "A22",
//         States::A23(_, _, _, _) => "A23",
//         States::A24(_, _, _, _, _) => "A24",
//         States::B21(_, _) => "B21",
//         States::B22(_, _, _) => "B22",
//         States::B23(_, _, _, _) => "B23",
//         States::B24(_, _, _, _, _) => "B24",
//       }
//     )
//   }
// }

// #[allow(non_snake_case)]
// fn parse_tree<I: Iterator<Item = char>>(i: I) -> Option<Vec<ABNode>> {
//   let mut i = i.peekable();
//   let mut states = vec![States::I0];

//   loop {
//     println!(
//       "{}",
//       states
//         .iter()
//         .fold("".to_string(), |s, state| s + &format!("{} ", state))
//     );
//     let state = states.pop().unwrap();
//     let peek_char = i.peek().unwrap_or(&'$');

//     match (state, peek_char) {
//       (States::I0, '$') => {
//         println!("I0 '$'");
//         return None;
//       }
//       (States::I0, 'a') => {
//         println!("I0 'a'");
//         let res = Rc::new(None);
//         states.push(States::I1(res.clone()));
//         states.push(States::S21(res, 'a'));
//       }
//       (States::I0, 'b') => {
//         println!("I0 'b'");
//         let res = Rc::new(None);
//         states.push(States::I1(res.clone()));
//         states.push(States::S31(res, 'b'));
//       }
//       (States::I1(res), '$') => {
//         println!("I1 '$'");
//         let res = Rc::try_unwrap(res).unwrap();
//         let res = {
//           // closure from grammar
//           res
//         };
//         return res;
//       }

//       (States::S21(res, a), 'a') => {
//         println!("S21 'a'");
//         let sub_res = Rc::new(None);
//         states.push(States::S22(res, a, sub_res.clone()));
//         states.push(States::A21(sub_res, 'a'));
//       }
//       (States::S21(res, a), 'b') => {
//         println!("S21 'b'");
//         states.push(States::S23(res, a, Rc::new(None), 'b'));
//       }
//       (States::S22(res, a, A), 'b') => {
//         println!("S22 'b'");
//         states.push(States::S23(res, a, A, 'b'));
//       }
//       (States::S23(mut res, _a, A, _b), '$') => {
//         println!("S23 '$'");
//         let A = Rc::try_unwrap(A).unwrap();
//         let S = None;
//         unsafe {
//           *Rc::get_mut_unchecked(&mut res) = Some({
//             // closure from grammar
//             compose(Direction::AB, A, S)
//           });
//         }
//         // unwind.
//       }
//       (States::S23(res, a, A, b), 'a') => {
//         println!("S23 'a'");
//         let sub_res = Rc::new(None);
//         states.push(States::S24(res, a, A, b, sub_res.clone()));
//         states.push(States::S21(sub_res, 'a'));
//       }
//       (States::S23(res, a, A, b), 'b') => {
//         println!("S23 'b'");
//         let sub_res = Rc::new(None);
//         states.push(States::S24(res, a, A, b, sub_res.clone()));
//         states.push(States::S31(sub_res, 'b'));
//       }
//       (States::S24(mut res, _a, A, _b, S), _) => {
//         println!("S24 _");
//         let A = Rc::try_unwrap(A).unwrap();
//         let S = Rc::try_unwrap(S).unwrap();
//         unsafe {
//           *Rc::get_mut_unchecked(&mut res) = Some({
//             // closure from grammar
//             compose(Direction::AB, A, S)
//           });
//         }
//         // unwind, re-match against peek_char.
//         continue;
//       }

//       (States::S31(res, b), 'a') => {
//         println!("S31 'a'");
//         states.push(States::S33(res, b, Rc::new(None), 'a'));
//       }
//       (States::S31(res, b), 'b') => {
//         println!("S31 'b'");
//         let sub_res = Rc::new(None);
//         states.push(States::S32(res, b, sub_res.clone()));
//         states.push(States::B21(sub_res, 'b'));
//       }
//       (States::S32(res, b, B), 'a') => {
//         println!("S32 'a'");
//         states.push(States::S33(res, b, B, 'a'));
//       }
//       (States::S33(mut res, _b, B, _a), '$') => {
//         println!("S33 '$'");
//         let B = Rc::try_unwrap(B).unwrap();
//         let S = None;
//         unsafe {
//           *Rc::get_mut_unchecked(&mut res) = Some({
//             // closure from grammar
//             compose(Direction::BA, B, S)
//           });
//         }
//         // unwind.
//       }
//       (States::S33(res, b, B, a), 'a') => {
//         println!("S33 'a'");
//         let sub_res = Rc::new(None);
//         states.push(States::S34(res, b, B, a, sub_res.clone()));
//         states.push(States::S21(sub_res, 'a'));
//       }
//       (States::S33(res, b, B, a), 'b') => {
//         println!("S33 'b'");
//         let sub_res = Rc::new(None);
//         states.push(States::S34(res, b, B, a, sub_res.clone()));
//         states.push(States::S31(sub_res, 'b'));
//       }
//       (States::S34(mut res, _b, B, _a, S), _) => {
//         println!("S34 _");
//         let B = Rc::try_unwrap(B).unwrap();
//         let S = Rc::try_unwrap(S).unwrap();
//         unsafe {
//           *Rc::get_mut_unchecked(&mut res) = Some({
//             // closure from grammar
//             compose(Direction::BA, B, S)
//           });
//         }
//         // unwind, re-match against peek_char.
//         continue;
//       }

//       (States::A21(res, a), 'a') => {
//         println!("A21 'a'");
//         let sub_res = Rc::new(None);
//         states.push(States::A22(res, a, sub_res.clone()));
//         states.push(States::A21(sub_res, 'a'));
//       }
//       (States::A21(res, a), 'b') => {
//         println!("A21 'b'");
//         states.push(States::A23(res, a, Rc::new(None), 'b'));
//       }
//       (States::A22(res, a, A), 'b') => {
//         println!("A22 'b'");
//         states.push(States::A23(res, a, A, 'b'));
//       }
//       (States::A23(mut res, _a, A, _b), '$') => {
//         println!("A23 '$'");
//         let A = Rc::try_unwrap(A).unwrap();
//         unsafe {
//           *Rc::get_mut_unchecked(&mut res) = Some({
//             // closure from grammar
//             compose(Direction::AB, A, None)
//           });
//         }
//         // unwind.
//       }
//       (States::A23(res, a, A, b), 'a') => {
//         println!("A23 'a'");
//         let sub_res = Rc::new(None);
//         states.push(States::A24(res, a, A, b, sub_res.clone()));
//         states.push(States::A21(sub_res, 'a'));
//       }
//       (States::A23(mut res, _a, A, _b), 'b') => {
//         println!("A23 'b'");
//         let A = Rc::try_unwrap(A).unwrap();
//         let S = None;
//         unsafe {
//           *Rc::get_mut_unchecked(&mut res) = Some({
//             // closure from grammar
//             compose(Direction::AB, A, S)
//           });
//         }
//         // unwind, re-match against peek_char.
//         continue;
//       }
//       (States::A24(mut res, _a, A, _b, S), _) => {
//         println!("A24 _");
//         let A = Rc::try_unwrap(A).unwrap();
//         let S = Rc::try_unwrap(S).unwrap();
//         unsafe {
//           *Rc::get_mut_unchecked(&mut res) = Some({
//             // closure from grammar
//             compose(Direction::AB, A, S)
//           });
//         }
//         // unwind, re-match against peek_char.
//         continue;
//       }

//       (States::B21(res, b), 'a') => {
//         println!("B21 'a'");
//         states.push(States::B23(res, b, Rc::new(None), 'a'));
//       }
//       (States::B21(res, b), 'b') => {
//         println!("B21 'b'");
//         let sub_res = Rc::new(None);
//         states.push(States::B22(res, b, sub_res.clone()));
//         states.push(States::B21(sub_res, 'b'));
//       }
//       (States::B22(res, b, B), 'a') => {
//         println!("B22 'a'");
//         states.push(States::B23(res, b, B, 'a'));
//       }
//       (States::B23(mut res, _b, B, _a), '$') => {
//         println!("B23 '$'");
//         let B = Rc::try_unwrap(B).unwrap();
//         unsafe {
//           *Rc::get_mut_unchecked(&mut res) = Some({
//             // closure from grammar
//             compose(Direction::BA, B, None)
//           });
//         }
//         // unwind.
//       }
//       (States::B23(mut res, _b, B, _a), 'a') => {
//         println!("B23 'a'");
//         let B = Rc::try_unwrap(B).unwrap();
//         let S = None;
//         unsafe {
//           *Rc::get_mut_unchecked(&mut res) = Some({
//             // closure from grammar
//             compose(Direction::BA, B, S)
//           });
//         }
//         // unwind, re-match against peek_char.
//         continue;
//       }
//       (States::B23(res, b, B, a), 'b') => {
//         println!("B23 'b'");
//         let sub_res = Rc::new(None);
//         states.push(States::B24(res, b, B, a, sub_res.clone()));
//         states.push(States::B21(sub_res, 'b'));
//       }
//       (States::B24(mut res, _b, B, _a, S), _) => {
//         println!("B24 _");
//         let B = Rc::try_unwrap(B).unwrap();
//         let S = Rc::try_unwrap(S).unwrap();
//         unsafe {
//           *Rc::get_mut_unchecked(&mut res) = Some({
//             // closure from grammar
//             compose(Direction::BA, B, S)
//           });
//         }
//         // unwind, re-match against peek_char.
//         continue;
//       }

//       _ => panic!("Unexpected token '{}'", peek_char),
//     }

//     // If no continue was called, then consume this character.
//     i.next();
//   }
// }

fn main() {
  /*
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

  println!(
    "{}",
    parse_tree("abbbaaba".chars())
      .unwrap()
      .iter()
      .fold("".to_string(), |s, node| s + &format!("{}", node))
  );

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
  */

  // parser_generator_impl::grammar_def! {
  //   terminal: char;

  //   <S> => <A> $;
  //   <A> => <A> <B>;
  //   <A> => 'a' 'b';
  //   <B> => 'a' 'c';
  // };

  // parser_generator_impl::grammar_def! {
  //   terminal: char;

  //   <I> => <S>;
  //   <S> => 'a' <S> 'x'
  //        | 'c' <S> 'z'
  //        | <B>;
  //   <B> => <B> 'b'
  //        | !;
  // }

  // parser_generator_impl::grammar_def! {
  //   name: Test;
  //   terminal: char;

  //   <I>: u32 => <S> {
  //     #S + 3
  //   };
  //   <S>: u32 => 'x' <A> 'y' {
  //     7
  //   };
  //   <S>: u32 => 'z' <A> 'w' {
  //     if #A {
  //       2 * 4
  //     } else {
  //       1 * 10
  //     }
  //   };
  //   <A>: bool => 'a' {
  //     true
  //   } | 'b' {
  //     false
  //   };
  // }

  // let x = vec!['x', 'a', 'y'];
  // let res = Test::parse(x.iter());

  // match res {
  //   Some(i) => println!("Result: {}", i),
  //   None => println!("no match :("),
  // }

  parser_generator_impl::grammar_def! {
    name: Test;
    terminal: char;

    <S>: u32 => <A> { #A };
    <A>: u32 => <A> '+' <P> {
      #A + #P
    } | <P> {
      #P
    };
    <P>: u32 => <P> '*' <V> {
      #P * #V
    } | <V> {
      #V
    };
    <V>: u32 => '1' { 1 } | '2' { 2 };
  };

  let res = Test::parse("2*2+1".chars().into_iter().peekable());

  match res {
    Some((i, _)) => println!("Result: {}", i),
    None => println!("no match :("),
  }

  /*
  parser_generator_impl::grammar_def! {
    terminal: CToken;

    <program> => <declList>;
    <declList> => <declList> <decl> | <decl>;
    <decl> => <varDecl> | <funDecl>;
    <varDecl> => <typeSpec> <varDeclList> ';';
    <scopedVarDecl> => <static> <typeSpec> <varDeclList> ';' | <typeSpec> <varDeclList> ';';
    <varDeclList> => <varDeclList> ',' <varDeclInit> | <varDeclInit>;
    <varDeclInit> => <varDeclId> | <varDeclId> ':' <simpleExp>;
    <varDeclId> => <ID> | <ID> '[' <NUMCONST> ']';
    <typeSpec> => <int> | <bool> | <char>;
    <funDecl> => <typeSpec> <ID> '(' <parms> ')' <stmt> | <ID> '(' <parms> ')' <stmt>;
    <parms> => <parmList> | !;
    <parmList> => <parmList> ';' <parmTypeList> | <parmTypeList>;
    <parmTypeList> => <typeSpec> <parmIdList>;
    <parmIdList> => <parmIdList> ',' <parmId> | <parmId>;
    <parmId>=><ID> | <ID> '[' ']';
    <stmt> => <expStmt> | <compoundStmt> | <selectStmt> | <iterStmt> | <returnStmt> | <breakStmt>;
    <expStmt> => <exp> ';' | ';';
    <compoundStmt> => '{' <localDecls> <stmtList> '}';
    <localDecls> => <localDecls> <scopedVarDecl> | !;
    <stmtList> => <stmtList> <stmt> | !;
    <selectStmt> => <if> <simpleExp> <then> <stmt> | <if> <simpleExp> <then> <stmt> <else> <stmt>;
    <iterStmt> => <while> <simpleExp> <do> <stmt> | <for> <ID> '=' <iterRange> <do> <stmt>;
    <iterRange> => <simpleExp> <to> <simpleExp> | <simpleExp> <to> <simpleExp> <by> <simpleExp>;
    <returnStmt> => <return> ';' | <return> <exp> ';';
    <breakStmt> => <break> ';';
    <exp> => <mutable> '=' <exp>
           | <mutable> '+' '=' <exp>
           | <mutable> '-' '=' <exp>
           | <mutable> '*' '=' <exp>
           | <mutable> '/' '=' <exp>
           | <mutable> '+' '+'
           | <mutable> '-' '-'
           | <simpleExp>;
    <simpleExp> => <simpleExp> <or> <andExp> | <andExp>;
    <andExp> => <andExp> <and> <unaryRelExp> | <unaryRelExp>;
    <unaryRelExp> => <not> <unaryRelExp> | <relExp>;
    <relExp> => <minmaxExp> <relop> <minmaxExp> | <minmaxExp>;
    <relop> => '<' '=' | '<' | '>' | '>' '=' | 'q' | '!' '=';
    <minmaxExp> => <minmaxExp> <minmaxop> <sumExp> | <sumExp>;
    <minmaxop> => ':' '>' ':' | ':' '<' ':';
    <sumExp> => <sumExp> <sumop> <mulExp> | <mulExp>;
    <sumop>=> '+' | '-';
    <mulExp> => <mulExp> <mulop> <unaryExp> | <unaryExp>;
    <mulop> => '*' | '/' | '%';
    <unaryExp> => <unaryop> <unaryExp> | <factor>;
    <unaryop> => '-' | '*' | '?';
    <factor> => <immutable> | <mutable>;
    <mutable> => <ID> | <ID> '[' <exp> ']';
    <immutable> => '(' <exp> ')' | <call> | <constant>;
    <call>=> <ID> '(' <args> ')';
    <args> => <argList> | !;
    <argList> => <argList> ',' <exp> | <exp>;
    <constant> => <NUMCONST> | <CHARCONST> | <STRINGCONST> | <true> | <false>;

    <return> => 'a';
    <or> => '|';
    <and> => '&';
    <not> => '!';
    <ID> => 'x';
    <NUMCONST> => '1';
    <CHARCONST> => '\'';
    <if> => 'i';
    <else> => 'e';
    <for> => 'f';
    <while> => 'w';
    <do> => 'd';
    <break> => 'r';
    <then> => 't';
    <to> => '2';
    <by> => 'b';
    <static> => 's';
    <int> => '0';
    <bool> => '3';
    <char> => '4';
    <STRINGCONST> => '5';
    <true> => 'y';
    <false> => 'z';
  }
  */
}

// Regexes:
// ::std::io::_(e?)print\([\s\r]*format_args!\([\s\r]*(.+)[\s\r]*\)[\s\r]*\);
// $1print!($2);
// ::core::panicking::panic\("internal error: entered unreachable code"\)
// unreachable!()
// <\[_\]>::into_vec\([\s\r]*#\[rustc_box\][\s\r]*::alloc::boxed::Box::new\((\[[^\]]+\])\),[\s\r]*\)
// vec!$1
