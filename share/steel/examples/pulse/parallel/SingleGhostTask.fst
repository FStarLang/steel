module SingleGhostTask

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


```pulse
fn create_thunk
(#pre #post: vprop) (f: (unit -> stt unit pre (fun () -> post)))
(bpre bpost: GR.ref bool)
(ipre: inv (guarded_inv bpre pre))
(ipost: inv (guarded_inv bpost post))
(_: unit)
requires GR.pts_to bpre #one_half true ** GR.pts_to bpost #one_half false
ensures GR.pts_to bpre #one_half false ** GR.pts_to bpost #one_half true
{
    take_from_guarded_inv ipre;
    f ();
    put_in_guarded_inv ipost;
    ()
}
```
//#push-options "--print_implicits --print_full_names"

(*
let mk_res (#pre #post: vprop) (#bpre #bpost: GR.ref bool) (ipre: inv (guarded_inv bpre pre))
    (ipost: inv (guarded_inv bpost post)) (th: thunk bpre bpost)
: (bpre: GR.ref bool & bpost: GR.ref bool & inv (guarded_inv bpre pre) & inv (guarded_inv bpost post) & thunk bpre bpost)
= (| bpre, bpost, ipre, ipost, th |)
*)
let mk_res #post (bpre bpost: GR.ref bool) (th: thunk bpre bpost) (bdone: ref bool) (bclaimed: GR.ref bool) (ipost: inv (guarded_inv bpost post)):
    t:task & inv (guarded_inv t._2 post)
= (| (| bpre, bpost, th, bdone, bclaimed |), ipost|)
(*
    stt (t: task & inv (guarded_inv t._2 post))
    pre
    (fun r -> GR.pts_to r._1._1 #one_half true ** GR.pts_to r._1._2 #one_half false)
 
*)



```pulse
fn create_task_ (#pre #post: vprop) (f: (unit -> stt unit pre (fun () -> post)))
requires pre
returns r: (t: task & inv (guarded_inv t._2 post))
(*
        bpre: GR.ref bool &
        bpost: GR.ref bool &
        inv (guarded_inv bpre pre) &
        inv (guarded_inv bpost post) &
        thunk bpre bpost
        *)
ensures GR.pts_to r._1._1 #one_half true ** GR.pts_to r._1._2 #one_half false ** pts_to r._1._4 false ** GR.pts_to r._1._5 false

{
    (* precondition *)
    let bipre = allocate_empty_guarded_inv pre;
    let bpre: GR.ref bool = bipre._1;
    let ipre: inv (guarded_inv bpre pre) = bipre._2;
    rewrite each bipre._1 as bpre;
    rewrite each bipre._2 as ipre;
    put_in_guarded_inv ipre;

    (* postcondition *)
    let bipost = allocate_empty_guarded_inv post;
    let bpost: GR.ref bool = bipost._1;
    let ipost: inv (guarded_inv bpost post) = bipost._2;
    rewrite each bipost._1 as bpost;
    rewrite each bipost._2 as ipost;

    let bclaimed = GR.alloc false;
    let bdone = alloc false;

    let th: thunk bpre bpost = create_thunk f bpre bpost ipre ipost;
    let r: (t: task & inv (guarded_inv t._2 post)) = mk_res bpre bpost th bdone bclaimed ipost;
    (*
    let r: (bpre: GR.ref bool & bpost: GR.ref bool & inv (guarded_inv bpre pre) & inv (guarded_inv bpost post) & thunk bpre bpost)
        = mk_res ipre ipost th;
    *)
    rewrite each bpre as r._1._1;
    rewrite each bpost as r._1._2;
    rewrite each bdone as r._1._4;
    rewrite each bclaimed as r._1._5;
    r
    //admit()
}
```

let create_task = create_task_

let ongoing_condition (t: extended_task) =
    pts_to t._1._4 #one_half false ** GR.pts_to t._1._5 #one_half false
    (* bpre, bpost, bdone, bclaimed *)

(*
let ongoing_condition_after (t: extended_task) =
    GR.pts_to t._1._1 #one_half true ** GR.pts_to t._1._2 #one_half false
    (* bpre, bpost, bdone, bclaimed *)
*)

let done_condition (t: extended_task) =
    GR.pts_to t._1._1 #one_half false ** (exists* f. pts_to t._1._4 #f true **
    (exists* claimed. GR.pts_to t._1._2 #one_half claimed ** GR.pts_to t._1._5 #one_half (not claimed)))

let task_res (t: extended_task): vprop =
    match t._2 with
    | Todo -> GR.pts_to t._1._1 #one_half true ** GR.pts_to t._1._2 #one_half false ** pts_to t._1._4 #one_half false ** GR.pts_to t._1._5 #one_half false
    | Ongoing -> emp//pts_to t._1._4 #one_half false ** GR.pts_to t._1._5 #one_half false
    //GR.pts_to t._1._2 #one_half false ** GR.pts_to t._1._3 #one_half false ** GR.pts_to t._1._4 #one_half false
    | Done -> done_condition t


```pulse
ghost fn get_task_res_todo_ (t: task)
requires GR.pts_to t._1 #one_half true ** GR.pts_to t._2 #one_half false ** pts_to t._4 #one_half false ** GR.pts_to t._5 #one_half false
ensures task_res (t, Todo)
{
    let r = (t, Todo);
    rewrite each t as r._1;
    rewrite (GR.pts_to r._1._1 #one_half true ** GR.pts_to r._1._2 #one_half false ** pts_to r._1._4 #one_half false ** GR.pts_to r._1._5 #one_half false)
        as task_res r;
    ()
}
```

let get_task_res_todo = get_task_res_todo_

(*
val get_task_res_todo (t: task):
stt_ghost unit
(GR.pts_to t._1 #one_half true ** GR.pts_to t._2 #one_half false ** pts_to t._4 false ** GR.pts_to t._5 false)
(fun () -> task_res (t, Todo))
*)




```pulse
ghost fn from_todo_to_ongoing_ (t: extended_task{t._2 == Todo})
requires task_res t
ensures task_res (t._1, Ongoing) ** GR.pts_to t._1._1 #one_half true ** GR.pts_to t._1._2 #one_half false ** ongoing_condition t
{
    rewrite task_res t as (GR.pts_to t._1._1 #one_half true ** GR.pts_to t._1._2 #one_half false ** pts_to t._1._4 #one_half false ** GR.pts_to t._1._5 #one_half false);
    //take_from_guarded_inv i;
//    rewrite (GR.pts_to t._1._2 #one_half false ** GR.pts_to t._1._3 #one_half false ** GR.pts_to t._1._4 #one_half false) as
    rewrite emp as (task_res (t._1, Ongoing));
    fold ongoing_condition t;
    ()
}
```

let from_todo_to_ongoing = from_todo_to_ongoing_

```pulse
ghost fn unfold_done (t: extended_task{t._2 == Done})
requires task_res t
ensures done_condition t
{
    rewrite (task_res t) as (done_condition t);
    ()
}
```

```pulse
ghost fn fold_done (t: extended_task{t._2 == Done})
requires done_condition t
ensures task_res t
{
    rewrite done_condition t as task_res t;
    ()
}
```

```pulse
ghost fn prove_ongoing (t: extended_task)
requires task_res t ** GR.pts_to t._1._1 #one_half false ** GR.pts_to t._1._2 #one_half true ** ongoing_condition t
ensures task_res t ** GR.pts_to t._1._1 #one_half false ** GR.pts_to t._1._2 #one_half true ** ongoing_condition t ** pure (t._2 == Ongoing)
{
    if (t._2 = Todo) {
        rewrite task_res t as (GR.pts_to t._1._1 #one_half true ** GR.pts_to t._1._2 #one_half false ** pts_to t._1._4 #one_half false ** GR.pts_to t._1._5 #one_half false);
        GR.pts_to_injective_eq t._1._1;
        assert pure false;
        rewrite (GR.pts_to t._1._1 #one_half true ** GR.pts_to t._1._2 #one_half false ** pts_to t._1._4 #one_half false ** GR.pts_to t._1._5 #one_half false)
            as task_res t;
        ()
    }
    else if (t._2 = Done) {
        unfold_done t;
        unfold done_condition t;
        unfold ongoing_condition t;
        pts_to_injective_eq t._1._4;
        fold ongoing_condition t;
        fold done_condition t;
        fold_done t;
        ()
    }
}
```

let task_done (t: task): vprop =
    exists* f. pts_to t._4 #f true


(* needs to update done... *)
```pulse
fn from_ongoing_to_done_ (t: extended_task)
requires task_res t ** GR.pts_to t._1._1 #one_half false ** GR.pts_to t._1._2 #one_half true ** ongoing_condition t ** (exists* v. pts_to t._1._4 #one_half v)
ensures task_res (t._1, Done) ** pts_to t._1._4 #one_half true ** task_done t._1
{
    prove_ongoing t;
    rewrite task_res t as emp;

    assert (GR.pts_to t._1._1 #one_half false ** GR.pts_to t._1._2 #one_half true ** ongoing_condition t);
    unfold ongoing_condition t;
    assert (GR.pts_to t._1._1 #one_half false ** GR.pts_to t._1._2 #one_half true **
        pts_to t._1._4 #one_half false ** GR.pts_to t._1._5 #one_half false);
    gather2 t._1._4;
    t._1._4 := true;
    share2 t._1._4;
    share t._1._4;
    assert (GR.pts_to t._1._1 #one_half false ** GR.pts_to t._1._2 #one_half true **
        (exists* f. pts_to t._1._4 #f true) ** GR.pts_to t._1._5 #one_half false);

    rewrite each t as (t._1, Done);
    fold done_condition (t._1, Done);
    fold_done (t._1, Done);

    rewrite (pts_to (t._1, Done)._1._4 #one_half true)
        as pts_to t._1._4 #one_half true;

    fold task_done (t._1, Done)._1;
    rewrite task_done (t._1, Done)._1 as task_done t._1;

    
    ()
}
```

let from_ongoing_to_done = from_ongoing_to_done_


//#push-options "--print_implicits --print_full_names"
```pulse
unobservable fn claim_post_ #post (t: extended_task{t._2 == Done}) (i: inv (guarded_inv t._1._2 post))
requires task_res t ** GR.pts_to t._1._5 #one_half false
ensures task_res t ** post ** GR.pts_to t._1._5 #one_half true
opens (singleton i)
{
    unfold_done t;
    unfold done_condition t;
    with claimed. assert GR.pts_to t._1._2 #one_half claimed ** GR.pts_to t._1._5 #one_half (not claimed);

    GR.pts_to_injective_eq t._1._5;
    take_from_guarded_inv i;
    GR.gather2 t._1._5;
    GR.write t._1._5 true;
    GR.share2 t._1._5;
    fold done_condition t;
    rewrite done_condition t as task_res t;
    ()
}
```

let claim_post = claim_post_

```pulse
ghost fn duplicate_task_done_ (t: task)
requires task_done t
ensures task_done t ** task_done t
{
    unfold task_done t;
    share t._4;
    fold task_done t;
    fold task_done t;
    ()
}
```

let duplicate_task_done = duplicate_task_done_

```pulse
unobservable fn claim_post_from_done_
(#post: vprop) (t: extended_task) (i: inv (guarded_inv t._1._2 post))
requires task_res t ** GR.pts_to t._1._5 #one_half false ** task_done t._1
ensures task_res t ** post ** GR.pts_to t._1._5 #one_half true ** task_done t._1
opens (singleton i)
{
    admit()
}
```


let claim_post_from_done = claim_post_from_done_