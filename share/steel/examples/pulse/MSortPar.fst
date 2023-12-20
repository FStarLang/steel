module MSortPar

open FStar.Ghost
open Pulse.Lib.Pervasives
open TaskPool
module A = Pulse.Lib.Array
open ArraySplit
module S = FStar.Seq
open Pulse.Lib.Par.Pledge.Simple


assume val sort : Seq.seq int -> Seq.seq int
assume val sorted : Seq.seq int -> bool
assume val sort_is_sorted (s:Seq.seq int) : Lemma (sorted (sort s))
assume val sort_len (s:Seq.seq int)
  : Lemma (S.length (sort s) == S.length s)
          [SMTPat (S.length (sort s))]
          
assume val singl_is_sorted (s : S.seq int)
  : Lemma (requires S.length s < 2)
          (ensures s == sort s)

assume val merge : Seq.seq int -> Seq.seq int -> Seq.seq int
assume val merge_len (s1 s2 : S.seq int)
  : Lemma (ensures S.length (merge s1 s2) == S.length s1 + S.length s2)
          [SMTPat (merge s1 s2)]
assume val merge_sorted' (s1 s2 : S.seq int)
  : Lemma (ensures merge (sort s1) (sort s2) == sort (s1 `S.append` s2))
          [SMTPat (merge (sort s1) (sort s2))]

assume val merge_sorted (s1 s2 : S.seq int)
  : Lemma (requires sorted s1 /\ sorted s2)
          (ensures sorted (merge s1 s2))
          [SMTPat (sorted (merge s1 s2))]
          
assume val append_slice #a (s : S.seq a)
  (l1:nat) (l2 : nat{S.length s == l2 /\ l1 <= l2})
  : Lemma (S.append (S.slice s 0 l1) (S.slice s l1 l2) == s)
          [SMTPat (S.append (S.slice s 0 l1) (S.slice s l1 l2))]

```pulse
fn
merge_impl
  (a : A.array int) (lo mid hi : nat) (_:squash (lo <= mid /\ mid <= hi))
  (s1 : erased (S.lseq int (mid-lo)))
  (s2 : erased (S.lseq int (hi-mid)))
  requires pts_to_range a lo mid s1 ** pts_to_range a mid hi s2
  ensures pts_to_range a lo hi (merge s1 s2)
{
  admit()
}
```

assume // move to task pool
val join_alive
  (p:pool)   
  (e:perm)             
  : stt_ghost unit emp_inames 
              (pool_alive #(half_perm e) p ** pool_alive #(half_perm e) p) 
              (fun () -> pool_alive #e p) 
           
```pulse
fn lem1 (e:perm) (p:pool)
  requires pledge (pool_done p) (pool_alive #(half_perm e) p)
        ** pledge (pool_done p) (pool_alive #(half_perm e) p)
  ensures  pledge (pool_done p) (pool_alive #e p)
{
  join_pledge #(pool_done p)
    (pool_alive #(half_perm e) p)
    (pool_alive #(half_perm e) p);
  rewrite_pledge 
    (pool_alive #(half_perm e) p ** pool_alive #(half_perm e) p)
    (pool_alive #e p)
    (fun () -> join_alive p e);
  ()
}
// ```


//   q
//   ** pledge emp_inames (pool_done p) (pool_alive #(half_perm e) p)
//   ** pledge emp_inames (pool_done p) (pool_alive #(half_perm e) p)
//   ------------------------------------------------------------------
//   pledge emp_inames (pool_done p) (pool_alive #e p)
//   ** pledge emp_inames (pool_done p) phi

//   q **
//   pledge emp_inames (pool_done p) (pool_alive #(half_perm e) p)
//   ** pledge emp_inames (pool_done p) (pool_alive #(half_perm e) p)
//   ==> pledge emp_inames (pool_done p) (pool_alive #e p ** phi)
  
//   q **
//   pool_done p **
//   pledge emp_inames (pool_done p) (pool_alive #(half_perm e) p)
//   ** pledge emp_inames (pool_done p) (pool_alive #(half_perm e) p)
//   ==> (pool_done p) ** (pool_alive #e p ** phi)

//   q **
//   (pool_done p) **
//   (pool_alive #(half_perm e) p)
//   ** (pool_alive #(half_perm e) p)
//   ==> (pool_done p) ** (pool_alive #e p) ** phi
  

#push-options "--z3rlimit 50"

```pulse
fn
msort_par
  (a : A.array int)
  (p : pool)
  (cb : (
    (e : perm) ->
    (lo:nat) -> (hi : (hi:nat{lo <= hi})) ->
    (s : erased (s:Seq.seq int{S.length s == hi-lo})) ->
    stt unit (pool_alive #e p ** pts_to_range a lo hi (reveal s))
             (fun () -> pledge (pool_done p) (pool_alive #e p) ** pts_to_range a lo hi (sort (reveal s)))
  ))
  (e : perm)
  (lo:nat) (hi : (hi:nat{lo <= hi}))
  (s : erased (S.lseq int (hi-lo)))
  requires pool_alive #e p ** pts_to_range a lo hi (reveal s)
  ensures pledge (pool_done p) (pool_alive #e p)
       ** pts_to_range a lo hi (sort (reveal s))
{
  if (hi - lo < 2) {
    singl_is_sorted s;
    rewrite (pts_to_range a lo hi s)
         as (pts_to_range a lo hi (sort s));
    return_pledge (pool_done p) (pool_alive #e p);
    ()
  } else {
    let mid = (hi+lo) / 2;

    array_split a lo mid hi s ();

    with s1. assert (pts_to_range a lo mid s1);
    with s2. assert (pts_to_range a mid hi s2);

    // assert (pure ((hi-mid) + (mid-lo) == hi-lo));
    
    // assert (pure (s1 == S.slice s 0 (mid-lo)));
    // assert (pure (s2 == S.slice s (mid-lo) (hi-lo)));
    
    split_alive p e;

    let h1 = spawn #_ #_ #_ #(half_perm e) p (fun () -> cb (half_perm e) lo mid s1);

    // cb lo mid s1 ();
    cb (half_perm e) mid hi s2;
    
    join h1;
    
    lem1 e p;
    // assert (pool_alive #(half_perm e) p ** pledge emp_inames (pool_done p) (pool_alive #(half_perm e) p));

    // make_pledge emp_inames
    //   (pool_done p)
    //   (pool_alive #e p)
    //   (pool_alive #(half_perm e) p ** pledge emp_inames (pool_done p) (pool_alive #(half_perm e) p))
    //   (magic());
    
    // assert (pts_to_range a lo mid (sort s1));
    // assert (pts_to_range a mid hi (sort s2));

    merge_impl a lo mid hi () (sort s1) (sort s2);

    drop_ (Pulse.Lib.Par.Pledge.pledge emp_inames (joined h1) (handle_solved h1));
    
    // rewrite (pts_to_range a lo hi (merge (sort s1) (sort s2)))
    //      as (pts_to_range a lo hi (sort s));
  }
}
```
