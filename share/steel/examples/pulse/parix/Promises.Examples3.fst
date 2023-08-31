module Promises.Examples3

open Pulse.Lib.Pervasives
open Promises
module GR = Pulse.Lib.GhostReference

assume val done : ref bool
assume val res : ref (option int)
assume val claimed : GR.ref bool

let inv_p : vprop =
  exists_ (fun (v_done:bool) ->
  exists_ (fun (v_res:option int) ->
  exists_ (fun (v_claimed:bool) ->
       pts_to done #one_half v_done
    ** pts_to res #one_half v_res
    ** GR.pts_to claimed #one_half v_claimed
    ** (if not v_claimed then pts_to res #one_half v_res else emp)
    ** pure (v_claimed ==> v_done)
    ** pure (v_done ==> Some? v_res))))

let goal : vprop =
  exists_ (fun v_res -> pts_to res #one_half v_res ** pure (Some? v_res))


```pulse
ghost
fn proof
   (i : inv inv_p) (_:unit)
   requires pts_to done #one_half true ** GR.pts_to claimed #one_half false
   ensures pts_to done #one_half true ** goal
{
  with_invariants i {
    unfold inv_p;
    with v_done v_res v_claimed.
      assert (pts_to done #one_half v_done
              ** pts_to res #one_half v_res
              ** GR.pts_to claimed #one_half v_claimed
              ** `@(if not v_claimed then pts_to res #one_half v_res else emp)
              ** pure (v_claimed ==> v_done)
              ** pure (v_done ==> Some? v_res));

    pts_to_injective_eq #_ #one_half #one_half #v_done #true done;
    assert (pure (v_done == true));
    
    GR.gather2 #bool #emp_inames
      claimed
      #false #v_claimed;
    assert (pure (v_claimed == false));

    // NB: this step is very sensitive to ordering
    rewrite `@((if not v_claimed then pts_to res #one_half v_res else emp) ** emp)
         as `@(pts_to res #one_half v_res ** (if not true then pts_to res #one_half v_res else emp));

    GR.op_Colon_Equals claimed true;
    
    fold goal;
    
    GR.share2 #_ #emp_inames claimed;
    
    fold inv_p;
    
    drop_ (GR.pts_to claimed #one_half true);

    ()
  }
}
```

```pulse
fn setup (_:unit)
   requires pts_to done v_done ** pts_to res v_res ** GR.pts_to claimed v_claimed
   returns i:inv inv_p
   ensures pts_to done #one_half false ** promise (pts_to done #one_half true) goal
{
  done := false;
  res := None;
  GR.op_Colon_Equals claimed false;
  
  share2 #_ #emp_inames done;
  share2 #_ #emp_inames res;
  GR.share2 #_ #emp_inames claimed;
  
  rewrite (pts_to res #one_half None)
       as `@(if not false then  pts_to res #one_half None else emp);
       
  fold inv_p;
  
  let i = new_invariant' #emp_inames inv_p;
  
  make_promise
    (pts_to done #one_half true)
    goal
    (GR.pts_to claimed #one_half false)
    (proof i);

  i
}
```

```pulse
fn worker (i : inv inv_p) (_:unit)
   requires pts_to done #one_half false
   ensures pts_to done #one_half true
{
  with_invariants i {
    unfold inv_p;
    with v_done v_res v_claimed.
      assert (pts_to done #one_half v_done
              ** pts_to res #one_half v_res
              ** GR.pts_to claimed #one_half v_claimed
              ** `@(if not v_claimed then pts_to res #one_half v_res else emp)
              ** pure (v_claimed ==> v_done)
              ** pure (v_done ==> Some? v_res));

    gather2 #_ #emp_inames done #false #v_done;
    assert (pts_to done false);
    
    assert (pure (not v_claimed)); // contrapositive from v_done=false

    rewrite `@(if not v_claimed then pts_to res #one_half v_res else emp)
         as pts_to res #one_half v_res;
         
    gather2 #_ #emp_inames res #v_res #v_res;
    assert (pts_to res v_res);
    
    
    (* The main sketchy part here: two steps! But we see how
    to fix this by either:
      - Adding a lock and a ghost bool reference
      - Using a monotonic reference for the result, so once we
        set it to Some we know it must remain so. This allows
        to not have a lock for this. It would be two with_invariant
        steps.
    *)
    res := Some 42;
    done := true;
    
    share2 #_ #emp_inames res;

    rewrite (pts_to res #one_half (Some 42))
        as `@(if not v_claimed then pts_to res #one_half (Some 42) else emp);
        
    share2 #_ #emp_inames done;
    
    fold inv_p;

    ()
  };
}
```
