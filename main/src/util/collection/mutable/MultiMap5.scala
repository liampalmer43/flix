package util.collection.mutable

/**
 * Companion object for classes implementing [[MultiMap5]].
 */
object MultiMap5 {
  def empty[K1, K2, K3, K4, K5, V]: MultiMap5[K1, K2, K3, K4, K5, V] = new HashMultiMap5[K1, K2, K3, K4, K5, V]();
}

/**
 * Interface for util.collection.mutable multi maps with five keys.
 */
trait MultiMap5[K1, K2, K3, K4, K5, V] extends Traversable[(K1, K2, K3, K4, K5, Set[V])] {
  def keys: Traversable[K1];
  def get(k1: K1, k2: K2, k3: K3, k4: K4, k5: K5): Set[V];
  def has(k1: K1, k2: K2, k3: K3, k4: K4, k5: K5, v: V): Boolean;
  def hasNot(k1: K1, k2: K2, k3: K3, k4: K4, k5: K5, v: V): Boolean;
  def put(k1: K1, k2: K2, k3: K3, k4: K4, k5: K5, v: V): Boolean;
  def remove(k1: K1, k2: K2, k3: K3, k4: K4, k5: K5, v: V): Unit;
  def tuples: Traversable[(K1, K2, K3, K4, K5, V)];
}