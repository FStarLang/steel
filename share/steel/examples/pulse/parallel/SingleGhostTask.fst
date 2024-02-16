module SingleGhostTasks

open Pulse.Lib.Pervasives
module GR = Pulse.Lib.GhostReference

let guarded_inv (gb: GR.ref bool) (p: vprop) =
    exists* b. GR.pts_to gb #one_half b ** (if b then p else emp)

(* ghost can be used in unobs if result is non-informative
(singleton for observable code)
reveal x (if x is erased) --> becomes informative, but we enter ghost
ghost code cannot open invariants
*)
(* allocates with false and nothing *)
```pulse
unobservable fn allocate_empty_guarded_inv_ (p: vprop)
requires emp
returns r: (gb: GR.ref bool & inv (guarded_inv gb p))
ensures GR.pts_to r._1 #one_half false
{
    let gb: GR.ref bool = GR.alloc #bool false;
    GR.share2 gb;
    rewrite emp as (if false then p else emp);
    fold guarded_inv gb p;
    let i: inv (guarded_inv gb p) = new_invariant (guarded_inv gb p);
    let r: (gb: GR.ref bool & inv (guarded_inv gb p)) = Mkdtuple2 #(GR.ref bool) #(fun gb -> inv (guarded_inv gb p)) gb i;
    rewrite each gb as r._1;
    r
}
```

let allocate_empty_guarded_inv = allocate_empty_guarded_inv_


```pulse
unobservable fn put_in_guarded_inv_ (#gb: GR.ref bool) (#p: vprop) (i: inv (guarded_inv gb p))
requires p ** GR.pts_to gb #one_half false
ensures GR.pts_to gb #one_half true
opens (singleton i)
{
    with_invariants i {
        unfold guarded_inv gb p;
        GR.gather2 gb;
        GR.write gb true;
        GR.share2 gb;
        rewrite (if false then p else emp) as emp;
        fold guarded_inv gb p
    }
}
```

let put_in_guarded_inv = put_in_guarded_inv_

```pulse
unobservable fn take_from_guarded_inv_ (#gb: GR.ref bool) (#p: vprop) (i: inv (guarded_inv gb p))
requires GR.pts_to gb #one_half true
ensures GR.pts_to gb #one_half false ** p
opens (singleton i)
{
    with_invariants i {
        unfold guarded_inv gb p;
        GR.gather2 gb;
        GR.write gb false;
        GR.share2 gb;
        rewrite emp as (if false then p else emp);
        fold guarded_inv gb p
    }
}
```

let take_from_guarded_inv = take_from_guarded_inv_

let done_condition #a (t: extended_task a) =
    GR.pts_to t._3 #one_half false ** (exists* claimed. GR.pts_to t._4 #one_half claimed ** GR.pts_to t._5 #one_half (not claimed))

let task_res #a (t: extended_task a): vprop =
    match t._2 with
    | Todo -> GR.pts_to t._3 #one_half true ** GR.pts_to t._4 #one_half false ** GR.pts_to t._5 #one_half false
    | Ongoing -> GR.pts_to t._3 #one_half false ** GR.pts_to t._4 #one_half false ** GR.pts_to t._5 #one_half false
    | Done -> done_condition t

```pulse
unobservable fn from_todo_to_ongoing_ #a #pre (t: extended_task a{t._2 == Todo}) (i: inv (guarded_inv t._3 pre))
requires task_res t
ensures task_res (t._1, Ongoing, t._3, t._4, t._5) ** pre
opens (singleton i)
{
    rewrite task_res t as (GR.pts_to t._3 #one_half true ** GR.pts_to t._4 #one_half false ** GR.pts_to t._5 #one_half false);
    take_from_guarded_inv i;
    rewrite (GR.pts_to t._3 #one_half false ** GR.pts_to t._4 #one_half false ** GR.pts_to t._5 #one_half false) as
        (task_res (t._1, Ongoing, t._3, t._4, t._5));
    ()
}
```

let from_todo_to_ongoing = from_todo_to_ongoing_

```pulse
unobservable fn from_ongoing_to_done_ #a #post (t: extended_task a{t._2 == Ongoing}) (i: inv (guarded_inv t._4 post))
requires task_res t ** post
ensures task_res (t._1, Done, t._3, t._4, t._5)
opens (singleton i)
{
    rewrite task_res t as (GR.pts_to t._3 #one_half false ** GR.pts_to t._4 #one_half false ** GR.pts_to t._5 #one_half false);
    put_in_guarded_inv i;
    assert (GR.pts_to t._3 #one_half false ** (exists* claimed. GR.pts_to t._4 #one_half claimed ** GR.pts_to t._5 #one_half (not claimed)));
    rewrite (GR.pts_to t._3 #one_half false ** (exists* claimed. GR.pts_to t._4 #one_half claimed ** GR.pts_to t._5 #one_half (not claimed)))
        as task_res (t._1, Done, t._3, t._4, t._5);
    ()
}
```

let from_ongoing_to_done = from_ongoing_to_done_

```pulse
unobservable fn unfold_done #a (t: extended_task a{t._2 == Done})
requires task_res t
ensures done_condition t
{
    rewrite (task_res t) as (done_condition t);
    ()
}
```

```pulse
unobservable fn fold_done #a (t: extended_task a{t._2 == Done})
requires done_condition t
ensures task_res t
{
    rewrite done_condition t as task_res t;
    ()
}
```

//#push-options "--print_implicits --print_full_names"
```pulse
unobservable fn claim_post_ #a #post (t: extended_task a{t._2 == Done}) (i: inv (guarded_inv t._4 post))
requires task_res t ** GR.pts_to t._5 #one_half false
ensures task_res t ** post ** GR.pts_to t._5 #one_half true
opens (singleton i)
{
    unfold_done t;
    unfold done_condition t;
    with claimed. assert GR.pts_to t._4 #one_half claimed ** GR.pts_to t._5 #one_half (not claimed);
   
    //(GR.pts_to t._5 #one_half claimed ** (if not claimed then GR.pts_to t._4 #one_half true else emp));
    GR.pts_to_injective_eq t._5;
    take_from_guarded_inv i;
    GR.gather2 t._5;
    GR.write t._5 true;
    GR.share2 t._5;
    fold done_condition t;
    rewrite done_condition t as task_res t;
    ()
}
```

let claim_post = claim_post_

