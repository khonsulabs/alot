var searchIndex = JSON.parse('{\
"alot":{"doc":"alot","t":"FEENNNNNNNNNNNNCNNNNNCFFFFFNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNFFKFFFFFNNNNNNNNNNNNNNNNNNNNNNNNNNNMNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNN","n":["LotId","Lots","OrderedLots","as_bytes","borrow","borrow_mut","clone","clone_into","cmp","eq","fmt","from","from_bytes","hash","into","ordered","partial_cmp","to_owned","try_from","try_into","type_id","unordered","Drain","EntryIter","IntoIter","Iter","OrderedLots","borrow","borrow","borrow","borrow","borrow","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","clone","clone","clone","clone_into","clone_into","clone_into","default","drain","drain_filter","drop","entries","eq","eq","eq","eq","eq","first","first_mut","fmt","from","from","from","from","from","from_iter","get","get_by_index","get_mut","get_mut_by_index","id","index","index","index_mut","index_mut","index_of_id","insert","into","into","into","into","into","into_iter","into_iter","into_iter","into_iter","into_iter","into_iter","is_empty","iter","key","last","last_mut","len","new","next","next","next","next","pop","pop_entry","push","remove","remove_by_index","sort","sort_by","sort_by_cached_key","sort_by_key","sort_unstable","sort_unstable_by","sort_unstable_by_key","swap","to_owned","to_owned","to_owned","try_from","try_from","try_from","try_from","try_from","try_into","try_into","try_into","try_into","try_into","type_id","type_id","type_id","type_id","type_id","with_capacity","Drain","DrainAll","DrainFilter","EntryIter","IntoIter","Iter","IterMut","Lots","borrow","borrow","borrow","borrow","borrow","borrow","borrow","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","clear","clone","clone","clone","clone_into","clone_into","clone_into","default","drain","drain_filter","drop","entries","eq","filter","filter","fmt","from","from","from","from","from","from","from","from_iter","get","get_mut","index","index_mut","into","into","into","into","into","into","into","into_iter","into_iter","into_iter","into_iter","into_iter","into_iter","into_iter","into_iter","is_empty","iter","iter_mut","len","new","next","next","next","next","next","push","remove","to_owned","to_owned","to_owned","try_from","try_from","try_from","try_from","try_from","try_from","try_from","try_into","try_into","try_into","try_into","try_into","try_into","try_into","type_id","type_id","type_id","type_id","type_id","type_id","type_id","with_capacity"],"q":[[0,"alot"],[22,"alot::ordered"],[127,"alot::unordered"],[229,"core::cmp"],[230,"core::fmt"],[231,"core::fmt"],[232,"core::hash"],[233,"core::result"],[234,"core::any"],[235,"core::clone"],[236,"core::ops::function"],[237,"core::cmp"],[238,"core::cmp"]],"d":["A <code>LotId</code> is a single <code>usize</code>, encoding generation information …","","","Returns this ID as bytes. To decode the resulting bytes, …","","","","","","","","Returns the argument unchanged.","Decodes <code>bytes</code> that were previously encoded with <code>as_bytes()</code> …","","Calls <code>U::from(self)</code>.","An ordered collection of values, accessible by <code>LotId</code> or …","","","","","","An unordered collection of values, accessible by <code>LotId</code>.","An iterator over values being remoed from a <code>OrderedLots&lt;T&gt;</code>.","An iterator over an <code>OrderedLots&lt;T&gt;</code> that returns each …","An iterator that removes all values from the collection …","An iterator over all values contained in an <code>OrderedLots&lt;T&gt;</code>.","A collection of <code>T</code> values that maintains the order of …","","","","","","","","","","","","","","","","","","Returns an iterator that returns all the contained values …","Returns an iterator that invokes <code>filter</code> for each item in …","","Returns an <code>Iterator&lt;Item = (LotId, &amp;T)&gt;</code> for all contained …","","","","","","Returns the first entry in this collection, or None if the …","Returns a mutable reference to the first entry in this …","","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","","Looks up a previously stored value by its <code>LotId</code>. If the …","Looks up a value by index. If <code>index</code> is greater than or …","Looks up a previously stored value by its <code>LotId</code>. If the …","Looks up a mutable reference to a value by index. If <code>index</code> …","Returns the id of the entry at <code>index</code>, or None if <code>index</code> is …","","","","","Returns the index of <code>id</code>, or None if the id is not …","Inserts <code>value</code> at <code>offset</code> inside of the collection.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","","","","","","","Returns true if this collection has no values.","Returns an iterator of references to all contained values.","Returns the <code>LotId</code> associated with a given index. Returns …","Returns the last entry in this collection, or None if the …","Returns a mutable reference to the last entry in this …","Returns the number of values contained in this collection.","Returns a new, empty collection.","","","","","Removes the last element of the collection, if one is …","Removes the last element of the collection, if one is …","Adds <code>value</code> to the end of the collection, returning the …","Removes the value with the associated <code>LotId</code>, if found.","Removes the value at <code>index</code>, returning the <code>LotId</code> and value …","Orders the elements in this collection leveraging the …","Orders the elements in this collection leveraging the …","Orders the elements in this collection leveraging the …","Orders the elements in this collection leveraging the …","Orders the elements in this collection leveraging the …","Orders the elements in this collection leveraging the …","Orders the elements in this collection leveraging the …","Swaps the elements at index <code>a</code> and <code>b</code>.","","","","","","","","","","","","","","","","","","","Returns an empty collection that can hold <code>initial_capacity</code> …","An iterator over values being remoed from a <code>Lots&lt;T&gt;</code>.","A <code>DrainFilter</code> that drains all elements from a collection.","A filter for a <code>Drain</code> iterator.","An iterator over a <code>Lots&lt;T&gt;</code> that returns each contained …","An iterator that removes all values from the collection …","An iterator over all values contained in a <code>Lots&lt;T&gt;</code>.","An iterator providing exclusive access to all values …","A collection of <code>T</code>, organized by generational <code>LotId</code>s.","","","","","","","","","","","","","","","Removes all values from the collection.","","","","","","","","Returns an iterator that returns all the contained values …","Returns an iterator that invokes <code>filter</code> for each item in …","","Returns an <code>Iterator&lt;Item = (LotId, &amp;T)&gt;</code> for all contained …","","Return true if the value should be removed from the …","","","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","Returns the argument unchanged.","","Looks up a previously stored value by its <code>LotId</code>. If the …","Looks up a previously stored value by its <code>LotId</code>. If the …","","","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","Calls <code>U::from(self)</code>.","","","","","","","","","Returns true if this collection has no values.","Returns an iterator of references to all contained values.","Returns an iterator of exclusive references to all …","Returns the number of values contained in this collection.","Returns a new, empty collection.","","","","","","Adds <code>value</code> to the collection, returning the value’s …","Removes a previously stored value by its <code>LotId</code>. If the …","","","","","","","","","","","","","","","","","","","","","","","","","Returns an empty collection that can hold <code>initial_capacity</code> …"],"i":[0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,0,0,0,0,0,0,19,28,14,16,17,19,28,14,16,17,14,16,17,14,16,17,14,14,14,19,14,14,14,14,14,14,14,14,14,19,28,14,16,17,14,14,14,14,14,14,14,14,14,14,14,14,19,28,14,16,17,19,28,14,14,16,17,14,14,14,14,14,14,14,19,28,16,17,14,14,14,14,14,14,14,14,14,14,14,14,14,14,16,17,19,28,14,16,17,19,28,14,16,17,19,28,14,16,17,14,0,0,0,0,0,0,0,0,35,34,18,36,31,32,33,35,34,18,36,31,32,33,31,31,32,33,31,32,33,31,31,31,34,31,31,22,18,31,35,34,18,36,31,32,33,31,31,31,31,31,35,34,18,36,31,32,33,35,34,36,31,31,31,32,33,31,31,31,31,31,35,34,36,32,33,31,31,31,32,33,35,34,18,36,31,32,33,35,34,18,36,31,32,33,35,34,18,36,31,32,33,31],"f":[0,0,0,[1,[[3,[2]]]],[-1,-2,[],[]],[-1,-2,[],[]],[1,1],[[-1,-2],4,[],[]],[[1,1],5],[[1,1],6],[[1,7],8],[-1,-1,[]],[[[9,[2]]],[[10,[1]]]],[[1,-1],4,11],[-1,-2,[],[]],0,[[1,1],[[10,[5]]]],[-1,-2,[],[]],[-1,[[12,[-2]]],[],[]],[-1,[[12,[-2]]],[],[]],[-1,13,[]],0,0,0,0,0,0,[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[[[14,[-1]]],[[14,[-1]]],15],[[[16,[-1]]],[[16,[-1]]],15],[[[17,[-1]]],[[17,[-1]]],15],[[-1,-2],4,[],[]],[[-1,-2],4,[],[]],[[-1,-2],4,[],[]],[[],[[14,[-1]]],[]],[[[14,[-1]]],[[19,[-1,18]]],[]],[[[14,[-1]],-2],[[19,[-1,-2]]],[],[[21,[-1],[[20,[6]]]]]],[[[19,[-1,-2]]],4,[],[[22,[-1]]]],[[[14,[-1]]],[[17,[-1]]],[]],[[[14,[-1]],[3,[-1]]],6,23],[[[14,[-1]],[9,[-1]]],6,23],[[[14,[-1]],[14,[-1]]],6,23],[[[14,[-1]],[9,[-1]]],6,23],[[[14,[-1]],[3,[-1]]],6,23],[[[14,[-1]]],[[10,[-1]]],[]],[[[14,[-1]]],[[10,[-1]]],[]],[[[14,[-1]],7],8,24],[-1,-1,[]],[-1,-1,[]],[-1,-1,[]],[-1,-1,[]],[-1,-1,[]],[-2,[[14,[-1]]],[],[[26,[],[[25,[-1]]]]]],[[[14,[-1]],1],[[10,[-1]]],[]],[[[14,[-1]],27],[[10,[-1]]],[]],[[[14,[-1]],1],[[10,[-1]]],[]],[[[14,[-1]],27],[[10,[-1]]],[]],[[[14,[-1]],27],[[10,[1]]],[]],[[[14,[-1]],1],-2,[],[]],[[[14,[-1]],27],-2,[],[]],[[[14,[-1]],27],-2,[],[]],[[[14,[-1]],1],-2,[],[]],[[[14,[-1]],1],[[10,[27]]],[]],[[[14,[-1]],27,-1],1,[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[[[14,[-1]]],-2,[],[]],[[[14,[-1]]],-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[[[14,[-1]]],6,[]],[[[14,[-1]]],[[16,[-1]]],[]],[[[14,[-1]],27],[[10,[1]]],[]],[[[14,[-1]]],[[10,[-1]]],[]],[[[14,[-1]]],[[10,[-1]]],[]],[[[14,[-1]]],27,[]],[[],[[14,[-1]]],[]],[[[19,[-1,-2]]],[[10,[-3]]],[],[[22,[-1]]],[]],[[[28,[-1]]],[[10,[-2]]],[],[]],[[[16,[-1]]],[[10,[-2]]],[],[]],[[[17,[-1]]],[[10,[-2]]],[],[]],[[[14,[-1]]],[[10,[-1]]],[]],[[[14,[-1]]],[[10,[[4,[1,-1]]]]],[]],[[[14,[-1]],-1],1,[]],[[[14,[-1]],1],[[10,[-1]]],[]],[[[14,[-1]],27],[[10,[[4,[1,-1]]]]],[]],[[[14,[-1]]],4,29],[[[14,[-1]],-2],4,[],[[30,[-1,-1],[[20,[5]]]]]],[[[14,[-1]],-3],4,[],29,[[21,[-1],[[20,[-2]]]]]],[[[14,[-1]],-3],4,[],29,[[21,[-1],[[20,[-2]]]]]],[[[14,[-1]]],4,29],[[[14,[-1]],-2],4,[],[[30,[-1,-1],[[20,[5]]]]]],[[[14,[-1]],-3],4,[],29,[[21,[-1],[[20,[-2]]]]]],[[[14,[-1]],27,27],4,[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,[[12,[-2]]],[],[]],[-1,[[12,[-2]]],[],[]],[-1,[[12,[-2]]],[],[]],[-1,[[12,[-2]]],[],[]],[-1,[[12,[-2]]],[],[]],[-1,[[12,[-2]]],[],[]],[-1,[[12,[-2]]],[],[]],[-1,[[12,[-2]]],[],[]],[-1,[[12,[-2]]],[],[]],[-1,[[12,[-2]]],[],[]],[-1,13,[]],[-1,13,[]],[-1,13,[]],[-1,13,[]],[-1,13,[]],[27,[[14,[-1]]],[]],0,0,0,0,0,0,0,0,[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[[[31,[-1]]],4,[]],[[[31,[-1]]],[[31,[-1]]],15],[[[32,[-1]]],[[32,[-1]]],15],[[[33,[-1]]],[[33,[-1]]],15],[[-1,-2],4,[],[]],[[-1,-2],4,[],[]],[[-1,-2],4,[],[]],[[],[[31,[-1]]],[]],[[[31,[-1]]],[[34,[-1,18]]],[]],[[[31,[-1]],-2],[[34,[-1,-2]]],[],[[21,[-1],[[20,[6]]]]]],[[[34,[-1,-2]]],4,[],[[22,[-1]]]],[[[31,[-1]]],[[33,[-1]]],[]],[[[31,[-1]],[31,[-1]]],6,23],[[22,-1],6,[]],[[18,-1],6,[]],[[[31,[-1]],7],8,24],[-1,-1,[]],[-1,-1,[]],[-1,-1,[]],[-1,-1,[]],[-1,-1,[]],[-1,-1,[]],[-1,-1,[]],[-2,[[31,[-1]]],[],[[26,[],[[25,[-1]]]]]],[[[31,[-1]],1],[[10,[-1]]],[]],[[[31,[-1]],1],[[10,[-1]]],[]],[[[31,[-1]],1],-2,[],[]],[[[31,[-1]],1],-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[[[31,[-1]]],-2,[],[]],[[[31,[-1]]],-2,[],[]],[[[31,[-1]]],-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[[[31,[-1]]],6,[]],[[[31,[-1]]],[[32,[-1]]],[]],[[[31,[-1]]],[[35,[-1]]],[]],[[[31,[-1]]],27,[]],[[],[[31,[-1]]],[]],[[[35,[-1]]],[[10,[-2]]],[],[]],[[[34,[-1,-2]]],[[10,[-3]]],[],[[22,[-1]]],[]],[[[36,[-1]]],[[10,[-2]]],[],[]],[[[32,[-1]]],[[10,[-2]]],[],[]],[[[33,[-1]]],[[10,[-2]]],[],[]],[[[31,[-1]],-1],1,[]],[[[31,[-1]],1],[[10,[-1]]],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,-2,[],[]],[-1,[[12,[-2]]],[],[]],[-1,[[12,[-2]]],[],[]],[-1,[[12,[-2]]],[],[]],[-1,[[12,[-2]]],[],[]],[-1,[[12,[-2]]],[],[]],[-1,[[12,[-2]]],[],[]],[-1,[[12,[-2]]],[],[]],[-1,[[12,[-2]]],[],[]],[-1,[[12,[-2]]],[],[]],[-1,[[12,[-2]]],[],[]],[-1,[[12,[-2]]],[],[]],[-1,[[12,[-2]]],[],[]],[-1,[[12,[-2]]],[],[]],[-1,[[12,[-2]]],[],[]],[-1,13,[]],[-1,13,[]],[-1,13,[]],[-1,13,[]],[-1,13,[]],[-1,13,[]],[-1,13,[]],[27,[[31,[-1]]],[]]],"c":[],"p":[[5,"LotId",0],[1,"u8"],[1,"array"],[1,"tuple"],[6,"Ordering",229],[1,"bool"],[5,"Formatter",230],[8,"Result",230],[1,"slice"],[6,"Option",231],[10,"Hasher",232],[6,"Result",233],[5,"TypeId",234],[5,"OrderedLots",22],[10,"Clone",235],[5,"Iter",22],[5,"EntryIter",22],[5,"DrainAll",127],[5,"Drain",22],[17,"Output"],[10,"FnMut",236],[10,"DrainFilter",127],[10,"PartialEq",229],[10,"Debug",230],[17,"Item"],[10,"IntoIterator",237],[1,"usize"],[5,"IntoIter",22],[10,"Ord",229],[10,"Fn",236],[5,"Lots",127],[5,"Iter",127],[5,"EntryIter",127],[5,"Drain",127],[5,"IterMut",127],[5,"IntoIter",127]],"b":[[48,"impl-PartialEq%3C%5BT;+N%5D%3E-for-OrderedLots%3CT%3E"],[49,"impl-PartialEq%3C%5BT%5D%3E-for-OrderedLots%3CT%3E"],[50,"impl-PartialEq-for-OrderedLots%3CT%3E"],[51,"impl-PartialEq%3C%26%5BT%5D%3E-for-OrderedLots%3CT%3E"],[52,"impl-PartialEq%3C%26%5BT;+N%5D%3E-for-OrderedLots%3CT%3E"],[67,"impl-Index%3CLotId%3E-for-OrderedLots%3CT%3E"],[68,"impl-Index%3Cusize%3E-for-OrderedLots%3CT%3E"],[69,"impl-IndexMut%3Cusize%3E-for-OrderedLots%3CT%3E"],[70,"impl-IndexMut%3CLotId%3E-for-OrderedLots%3CT%3E"],[80,"impl-IntoIterator-for-OrderedLots%3CT%3E"],[81,"impl-IntoIterator-for-%26OrderedLots%3CT%3E"],[187,"impl-IntoIterator-for-%26mut+Lots%3CT%3E"],[188,"impl-IntoIterator-for-Lots%3CT%3E"],[189,"impl-IntoIterator-for-%26Lots%3CT%3E"]]}\
}');
if (typeof window !== 'undefined' && window.initSearch) {window.initSearch(searchIndex)};
if (typeof exports !== 'undefined') {exports.searchIndex = searchIndex};
