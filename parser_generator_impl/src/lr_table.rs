fn finalize_table(lr_table_builder: HashSet<Rc<LRTableEntryBuilder>>) -> HashSet<Rc<LRState>> {
  let mut entry_map = HashMap::new();

  lr_table_builder
    .into_iter()
    .for_each(|lr_table_entry_builder| {
      let lr_state = Rc::new(lr_table_entry_builder.lr_state().clone());
      entry_map.insert(lr_table_entry_builder, lr_state);
    });
}
