Inductive Tree (a : Set): Set := 
| Leaf: a -> Tree a
| Node: Tree a -> Tree a -> Tree a.

Definition s : Set := nat.
Definition Pre : Type := s -> Prop.
Definition Post (a : Set) : Type := s -> a -> s -> Prop.
Program Definition HoareState (pre: Pre) (a : Set) (post: Post a): Set := 
  forall i: {t:s| pre t}, {e: (a * s)| post i (fst e) (snd e)}.

Definition htop: Pre := fun s => True.

Program Definition hreturn (a : Set) : forall x, HoareState htop a (fun i y f => i = f /\ y = x) := 
  fun x s => (x, s).
Admit Obligations of hreturn.

Program Definition bind: forall a b P1 P2 Q1 Q2,
    (HoareState P1 a Q1) -> 
    (forall (x: a), HoareState (P2 x) b (Q2 x)) ->
    HoareState (fun s1 => P1 s1 /\ forall x s2, Q1 s1 x s2 -> P2 x s2)
               b
               (fun s1 y s3 => exists x, exists s2, Q1 s1 x s2 /\ Q2 x s2 y s3)
  := fun a b P1 P2 Q1 Q2 c1 c2 s1 =>
       match c1 s1 with (x, s2) => c2 x s2 end.
Admit Obligations of bind.

Program Definition get: HoareState htop s (fun i x f => i = f /\ x = i)
  := fun s => (s, s).
Admit Obligations of get.

Program Definition put (x : s): HoareState htop unit (fun _ _ f => f = x)
  := fun _ => (tt, x).
Admit Obligations of put.

Fixpoint size (a: Set) (t: Tree a): nat := 
  match t with 
  | Leaf _ x => 1
  | Node _ l r => size _ l + size _ r 
  end.

Fixpoint seq (x n: nat): list nat := 
  match n with 
  | 0 => nil
  | S k => x :: seq (S x) k
  end.

Fixpoint flatten (a : Set) (t : Tree a): list a :=
  match t with
  | Leaf _ x => x :: nil
  | Node _ l r => flatten _ l ++ flatten _ r
  end.

Notation "x >>= y" := (bind _ _ _ _ _ _ x y)
                       (at level 51, right associativity).

Notation "x >> y" := (bind _ _ _ _ _ _ x (fun _ => y))
                       (at level 51, right associativity).
  
Program Fixpoint relabel (a : Set) (t : Tree a):
    HoareState htop (Tree nat) (fun i t f => f = i + size _ t /\ flatten _ t = seq i (size _ t))
  := match t with
     | Leaf _ x => get >>= fun n =>
                   put (n + 1) >>
                   hreturn _ (Leaf _ n)
     | Node _ l r => relabel _ l >>= fun l' =>
                     relabel _ r >>= fun r' =>
                     hreturn _ (Node _ l' r')
     end.
Admit Obligations of relabel.
