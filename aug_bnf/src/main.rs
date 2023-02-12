mod aug_bnf_dyn;

use aug_bnf_dyn::{GrammarParser, Production};

pub fn fmt2<T: std::fmt::Display>(v: &Vec<T>) {
  for (i, c) in v.iter().enumerate() {
    if i > 0 {
      print!(" ");
    }
    print!("{}", c);
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

  aug_bnf_impl::aug_bnf! {
    <S> => <A> <B> ;
    <A> => 'a' <B> ;
    <B> => 'b' ;
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
