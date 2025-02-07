module IMapHelpers {
  ghost predicate IsKey(k: int) { true }  // a useless symbol for dafny to trigger on

  ghost function ZeroMap() : imap<int,int>
  {
    imap i | IsKey(i) :: 0
  }

  ghost function EmptyMap() : imap<int,int>
  {
    imap i | !IsKey(i) :: 0
  }

  ghost function MapUnionPreferLeft<K(!new),V>(a:map<K,V>, b:map<K,V>) : map<K,V>
  {
    map key | key in a.Keys + b.Keys :: if key in a then a[key] else b[key]
  }

  ghost function IMapUnionPreferLeft(a:imap<int,int>, b:imap<int,int>) : imap<int,int>
  {
    imap key | key in a || key in b :: if key in a then a[key] else b[key]
  }

  ghost function MapRemove(table:imap<int,int>, removeKeys:iset<int>) : imap<int,int>
    requires removeKeys <= table.Keys
  {
    imap key | key in table && key !in removeKeys :: table[key]
  }

  ghost predicate IsFull(m:imap<int, int>) {
    forall i :: i in m
  }
}
