module TaskPoolInv

open Pulse.Lib.Pervasives
module GR = Pulse.Lib.GhostReference

let guarded_inv (gb: GR.ref bool) (p: vprop) =
    exists* b. GR.pts_to gb #one_half b ** (if b then p else emp)

#push-options "--print_implicits --print_full_names"

(* ghost can be used in unobs if result is non-informative
(singleton for observable code)
reveal x (if x is erased) --> becomes informative, but we enter ghost
ghost code cannot open invariants
*)
(* allocates with false and nothing *)
```pulse
unobservable fn allocate_empty_guarded_inv (p: vprop)
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

let singleton #p (i:inv p) = add_inv emp_inames i


```pulse
unobservable fn put_in_guarded_inv (gb: GR.ref bool) (p: vprop) (i: inv (guarded_inv gb p))
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

```pulse
unobservable fn take_from_guarded_inv (gb: GR.ref bool) (p: vprop) (i: inv (guarded_inv gb p))
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

type task_status = | Todo | Ongoing | Done
type task_with_status (a: Type) = a & task_status
type mono_list (a: Type) = list (task_with_status a)