extern crate futures;
extern crate tokio;

use std::net::{Ipv6Addr, SocketAddrV6};
use tokio::net::TcpListener;
use tokio::task::yield_now;

async fn handle_connection(socket: tokio::net::TcpStream) {
  println!("Connected to {}", socket.peer_addr().unwrap());
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
  const PORT: u16 = 2000;
  let addr = SocketAddrV6::new(Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 0), PORT, 0, 0);
  let listener = TcpListener::bind(&addr).await?;

  loop {
    let (socket, _) = listener.accept().await?;
    tokio::spawn(async move {
      yield_now().await;
      handle_connection(socket).await;
    });
  }
}
