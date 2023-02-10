mod aug_bnf_dyn;

use aug_bnf_dyn::{GrammarParser, Production};

fn main() {
  let mut p = GrammarParser::<char>::new('I');
  p.add_production(Production::new('I', vec!['S']));
  p.add_production(Production::new('S', vec![]));
  p.add_production(Production::new('S', vec!['a', 'A', 'b', 'S']));
  p.add_production(Production::new('S', vec!['b', 'B', 'a', 'S']));
  p.add_production(Production::new('A', vec![]));
  p.add_production(Production::new('A', vec!['a', 'A', 'b', 'A']));
  p.add_production(Production::new('B', vec![]));
  p.add_production(Production::new('B', vec!['b', 'B', 'a', 'B']));

  println!("{}", p);

  let mut buffer: String = "".to_string();
  while let Ok(_) = std::io::stdin().read_line(&mut buffer) {
    buffer.remove(buffer.len() - 1);

    if buffer == "quit" {
      break;
    }

    let v: Vec<char> = buffer.chars().collect();
    println!("{}: {}", buffer, p.parse(v.iter()));
    buffer.clear();
  }
}
