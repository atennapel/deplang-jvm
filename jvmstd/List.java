package jvmstd;

public abstract class List {
  public final static List NIL = new Nil();
  public final static class Nil extends List {}

  public final static class Cons extends List {
    public final Object head;
    public final List tail;

    public Cons(Object head, List tail) {
      this.head = head;
      this.tail = tail;
    }
  }
}
