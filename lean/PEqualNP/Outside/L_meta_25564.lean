import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25564
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Represents
open scoped BigOperators

private abbrev N (t : Nat) := 27 * t
private def bp {t : Nat} (p : Fin (N t)) : Fin 27 := ⟨p.val % 27, by omega⟩
private def sh {t : Nat} (p : Fin (N t)) : Nat := p.val / 27
private def lbl (p c : Fin 27) : Nat :=
  if c.val / 9 = 0 then p.val / 3 % 3 + 3 * (p.val / 9)
  else if c.val / 9 = 1 then p.val % 3 + 3 * (p.val / 9)
  else p.val % 3 + 3 * (p.val / 3 % 3)
private def Inc (p c : Fin 27) : Prop := c.val % 9 = lbl p c
private instance (p c : Fin 27) : Decidable (Inc p c) := inferInstanceAs (Decidable (_ = _))
private def nextSh (t : Nat) (p c : Fin 27) (s : Nat) : Nat :=
  if p.val = 0 ∧ c.val / 9 = 2 then (s+1) % t else s
private def G {t : Nat} (p c : Fin (N t)) : Prop :=
  sh c = nextSh t (bp p) (bp c) (sh p) ∧ Inc (bp p) (bp c)
private instance {t : Nat} (p c : Fin (N t)) : Decidable (G p c) :=
  inferInstanceAs (Decidable (_ = _ ∧ Inc _ _))
private def SameYZ (p q : Fin 27) : Prop := p.val / 3 = q.val / 3
private def SameXZ (p q : Fin 27) : Prop := p.val % 3 = q.val % 3 ∧ p.val / 9 = q.val / 9
private def SameXY (p q : Fin 27) : Prop := p.val % 9 = q.val % 9
private def Near (p q : Fin 27) : Prop := p ≠ q ∧ (SameYZ p q ∨ SameXZ p q ∨ SameXY p q)
private instance (p q : Fin 27) : Decidable (Near p q) := by
  unfold Near SameYZ SameXZ SameXY; infer_instance
private theorem baseNear {p q l : Fin 27} (ne : p ≠ q) (hp : Inc p l) (hq : Inc q l) : Near p q := by
  refine ⟨ne, ?_⟩
  unfold Inc lbl at hp hq
  unfold SameYZ SameXZ SameXY
  by_cases a : l.val / 9 = 0
  · simp only [a, ite_true] at hp hq; omega
  by_cases b : l.val / 9 = 1
  · simp [b] at hp hq; omega
  · simp only [a, b, ite_false] at hp hq; omega
private def Adj {t : Nat} (p q : Fin (N t)) : Prop := p ≠ q ∧ ∃ l, G p l ∧ G q l
private theorem baseLine (p q a b : Fin 27) (ne : p ≠ q)
    (ha : Inc p a) (ha' : Inc q a) (hb : Inc p b) (hb' : Inc q b) : a = b := by
  unfold Inc lbl at ha ha' hb hb'
  by_cases e : (a : Nat) / 9 = (b : Nat) / 9
  · apply Fin.ext
    have h : (a : Nat) % 9 = (b : Nat) % 9 := by rw [ha, hb, e]
    omega
  · exfalso
    apply ne
    apply Fin.ext
    by_cases a0 : a.val / 9 = 0 <;> by_cases a1 : a.val / 9 = 1 <;>
      by_cases b0 : b.val / 9 = 0 <;> by_cases b1 : b.val / 9 = 1 <;>
      simp [a0, a1, b0, b1] at ha ha' hb hb' <;> omega
private theorem baseCommon (p q : Fin 27) (ne : p ≠ q) :
    ((Finset.univ : Finset (Fin 27)).filter (fun w => Near p w ∧ Near q w)).card ≤ 2 := by
  revert q ne
  fin_cases p <;> decide +kernel
private theorem sh_lt {t : Nat} (p : Fin (N t)) : sh p < t := by
  have h := p.isLt
  unfold N at h
  unfold sh
  omega
private theorem reconstruct {t : Nat} {p q : Fin (N t)}
    (hb : bp p = bp q) (hs : sh p = sh q) : p = q := by
  apply Fin.ext
  have hv := congrArg Fin.val hb
  change p.val % 27 = q.val % 27 at hv
  unfold sh at hs
  omega
private theorem next_inj {t a b : Nat} (p c : Fin 27)
    (ha : a < t) (hb : b < t) (he : nextSh t p c a = nextSh t p c b) : a=b := by
  unfold nextSh at he
  split at he
  · have hm (s : Nat) (h : s < t) : (s+1)%t = if s+1=t then 0 else s+1 := by
      split
      · rename_i eq; rw [eq, Nat.mod_self]
      · apply Nat.mod_eq_of_lt; omega
    rw [hm a ha, hm b hb] at he
    split at he <;> split at he <;> omega
  · exact he
private theorem liftP_inj {t : Nat} {p q c : Fin (N t)}
    (hp : G p c) (hq : G q c) (he : bp p = bp q) : p = q := by
  apply reconstruct he
  apply next_inj (bp p) (bp c) (sh_lt p) (sh_lt q)
  rw [← hp.1, he, ← hq.1]
private theorem liftC_inj {t : Nat} {p a b : Fin (N t)}
    (ha : G p a) (hb : G p b) (he : bp a = bp b) : a = b := by
  exact reconstruct he (ha.1.trans (by rw [he, ← hb.1]))
private theorem near_of_adj {t : Nat} {p q : Fin (N t)} (h : Adj p q) : Near (bp p) (bp q) := by
  obtain ⟨ne,l,hp,hq⟩ := h
  exact baseNear (fun e => ne (liftP_inj hp hq e)) hp.2 hq.2
private theorem adj_inj {t : Nat} {p x y : Fin (N t)}
    (hx : Adj p x) (hy : Adj p y) (e : bp x = bp y) : x=y := by
  have ne := (near_of_adj hx).1
  obtain ⟨_,a,ha,hxa⟩ := hx
  obtain ⟨_,b,hb,hyb⟩ := hy
  have eb : bp a = bp b := baseLine _ _ _ _ ne ha.2 hxa.2 hb.2 (by simpa only [e] using hyb.2)
  have el : a=b := liftC_inj ha hb eb
  subst b
  exact liftP_inj hxa hyb e
private theorem eq_base_forbids {t : Nat} {p q w : Fin (N t)} (ne : p ≠ q)
    (e : bp p = bp q) (hp : Adj p w) (hq : Adj q w) : False := by
  apply ne
  apply adj_inj (p := w) _ _ e
  · obtain ⟨ne,l,a,b⟩ := hp; exact ⟨ne.symm,l,b,a⟩
  · obtain ⟨ne,l,a,b⟩ := hq; exact ⟨ne.symm,l,b,a⟩
private def blockP {t : Nat} (b : Fin (3*t)) (x y : Fin 3) : Fin (N t) :=
  ⟨27*(b.val / 3) + 9*(b.val % 3) + 3*y.val + x.val, by unfold N; omega⟩
private def blockA {t : Nat} (b : Fin (3*t)) (y : Fin 3) : Fin (N t) :=
  ⟨27*(b.val / 3) + 3*(b.val % 3) + y.val, by unfold N; omega⟩
private def blockB {t : Nat} (b : Fin (3*t)) (x : Fin 3) : Fin (N t) :=
  ⟨27*(b.val / 3) + 9 + 3*(b.val % 3) + x.val, by unfold N; omega⟩
private theorem gridA {t : Nat} (b : Fin (3*t)) (x y : Fin 3) :
    G (blockP b x y) (blockA b y) := by
  constructor
  · unfold sh nextSh bp blockP blockA
    dsimp only
    split <;> omega
  · unfold Inc lbl bp blockP blockA
    dsimp only
    (split <;> try split) <;> omega
private theorem gridB {t : Nat} (b : Fin (3*t)) (x y : Fin 3) :
    G (blockP b x y) (blockB b x) := by
  constructor
  · unfold sh nextSh bp blockP blockB
    dsimp only
    split <;> omega
  · have hp : (bp (blockP b x y)).val = 9*(b.val % 3)+3*y.val+x.val := by
      change (27*(b.val / 3)+9*(b.val % 3)+3*y.val+x.val)%27 = _
      omega
    have hc : (bp (blockB b x)).val = 9+3*(b.val % 3)+x.val := by
      change (27*(b.val / 3)+9+3*(b.val % 3)+x.val)%27 = _
      omega
    unfold Inc lbl
    rw [hp,hc]
    (split <;> try split) <;> omega
private def blockMap {t : Nat} (a : Fin (3*t) × Fin 15) : Fin (N t) ⊕ Fin (N t) :=
  if h : a.2.val < 9 then
    .inl ⟨27*(a.1.val / 3)+9*(a.1.val % 3)+a.2.val, by have := a.1.isLt; unfold N; omega⟩
  else if h : a.2.val < 12 then
    .inr ⟨27*(a.1.val / 3)+3*(a.1.val % 3)+(a.2.val-9), by have := a.1.isLt; unfold N; omega⟩
  else
    .inr ⟨27*(a.1.val / 3)+9+3*(a.1.val % 3)+(a.2.val-12), by have := a.1.isLt; unfold N; omega⟩
private theorem blockInj {t : Nat} : Function.Injective (@blockMap t) := by
  intro ⟨a,x⟩ ⟨b,y⟩ e
  unfold blockMap at e
  dsimp only [Prod.fst,Prod.snd] at e
  by_cases hx : x.val < 9 <;> by_cases hy : y.val < 9 <;>
    by_cases hx' : x.val < 12 <;> by_cases hy' : y.val < 12 <;>
    simp [hx, hy, hx', hy', Fin.mk.injEq] at e <;>
    exact Prod.ext (Fin.ext (by dsimp only; omega)) (Fin.ext (by dsimp only; omega))
private def ptSlot (x y : Fin 3) : Fin 15 := ⟨x.val+3*y.val, by omega⟩
private def aSlot (y : Fin 3) : Fin 15 := ⟨9+y.val, by omega⟩
private def bSlot (x : Fin 3) : Fin 15 := ⟨12+x.val, by omega⟩
private theorem slotP {t : Nat} (b : Fin (3*t)) (x y : Fin 3) :
    blockMap (b,ptSlot x y) = .inl (blockP b x y) := by
  have h : 3*y.val + x.val < 9 := by omega
  simp [blockMap, ptSlot, blockP, h, Nat.add_comm x.val (3*y.val), Nat.add_assoc]
private theorem slotA {t : Nat} (b : Fin (3*t)) (y : Fin 3) :
    blockMap (b,aSlot y) = .inr (blockA b y) := by
  have h : ¬ (9+y.val < 9) := by omega
  have h' : 9+y.val < 12 := by omega
  simp [blockMap, aSlot, blockA, h, h']
private theorem slotB {t : Nat} (b : Fin (3*t)) (x : Fin 3) :
    blockMap (b,bSlot x) = .inr (blockB b x) := by
  have h : ¬ (12+x.val < 9) := by omega
  have h' : ¬ (12+x.val < 12) := by omega
  simp [blockMap, bSlot, blockB, h, h']
private theorem blankSlots (k : Fin 15) :
    (∃ y z : Fin 3, y ≠ z ∧ aSlot y ≠ k ∧ aSlot z ≠ k ∧
      (∀ x : Fin 3, bSlot x ≠ k ∧ ptSlot x y ≠ k ∧ ptSlot x z ≠ k)) ∨
    (∃ x z : Fin 3, x ≠ z ∧ bSlot x ≠ k ∧ bSlot z ≠ k ∧
      (∀ y : Fin 3, aSlot y ≠ k ∧ ptSlot x y ≠ k ∧ ptSlot z y ≠ k)) := by
  have e : ∀ k : Fin 15,
    (∃ y z : Fin 3, y ≠ z ∧ aSlot y ≠ k ∧ aSlot z ≠ k ∧
      (∀ x : Fin 3, bSlot x ≠ k ∧ ptSlot x y ≠ k ∧ ptSlot x z ≠ k)) ∨
    (∃ x z : Fin 3, x ≠ z ∧ bSlot x ≠ k ∧ bSlot z ≠ k ∧
      (∀ y : Fin 3, aSlot y ≠ k ∧ ptSlot x y ≠ k ∧ ptSlot z y ≠ k)) := by decide +kernel
  exact e k
private theorem noThree {t : Nat} {p q : Fin (N t)} (ne : p ≠ q)
    (w : Fin 3 → Fin (N t)) (hw : Function.Injective w)
    (hp : ∀ k, Adj p (w k)) (hq : ∀ k, Adj q (w k)) : False := by
  by_cases e : bp p = bp q
  · exact eq_base_forbids ne e (hp 0) (hq 0)
  let S := (Finset.univ : Finset (Fin 27)).filter (fun x => Near (bp p) x ∧ Near (bp q) x)
  have hin : ∀ k, bp (w k) ∈ S := by
    intro k
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, near_of_adj (hp k), near_of_adj (hq k)⟩
  let f : Fin 3 ↪ Fin 27 := ⟨fun k => bp (w k), fun i j h => hw (adj_inj (hp i) (hp j) h)⟩
  have hsub : (Finset.univ : Finset (Fin 3)).map f ⊆ S := by
    intro x hx
    obtain ⟨k,_,rfl⟩ := Finset.mem_map.mp hx
    exact hin k
  have hl := Finset.card_le_card hsub
  have hu := baseCommon (bp p) (bp q) e
  simpa [S] using (show False by
    simp only [Finset.card_map, Finset.card_univ, Fintype.card_fin] at hl
    change S.card ≤ 2 at hu
    omega)
private theorem forbiddenGrid {t : Nat} {K : Finset (Fin (N t))}
    (mate : Equiv.Perm (Fin (N t)))
    (hs : ∀ i ∈ K, ∀ j ∈ K, G i (mate j) ↔ G j (mate i))
    (L : Finset (Fin (N t))) (hL : L = K.map mate.toEmbedding)
    (u v : Fin (N t)) (hne : u ≠ v) (hu : u ∈ L) (hv : v ∈ L)
    (w : Fin 3 ↪ Fin (N t)) (hw : ∀ k, w k ∈ L ∧ w k ≠ u ∧ w k ≠ v)
    (a b : Fin 3 → Fin (N t))
    (ha : ∀ k, a k ∈ K ∧ G (a k) u ∧ G (a k) (w k))
    (hb : ∀ k, b k ∈ K ∧ G (b k) v ∧ G (b k) (w k)) : False := by
  have inv (c : Fin (N t)) (hc : c ∈ L) : mate.symm c ∈ K := by
    rw [hL, Finset.mem_map] at hc
    obtain ⟨p,hp,rfl⟩ := hc
    simpa using hp
  have move (c a : Fin (N t)) (hc : c ∈ L) (ha : a ∈ K) (h : G a c) :
      G (mate.symm c) (mate a) := by
    apply (hs a ha _ (inv c hc)).mp
    simpa using h
  apply noThree (p := mate.symm u) (q := mate.symm v) (mate.symm.injective.ne hne)
    (fun k => mate.symm (w k)) (mate.symm.injective.comp w.injective)
  · intro k
    exact ⟨mate.symm.injective.ne (hw k).2.1.symm, mate (a k),
      move u _ hu (ha k).1 (ha k).2.1, move _ _ (hw k).1 (ha k).1 (ha k).2.2⟩
  · intro k
    exact ⟨mate.symm.injective.ne (hw k).2.2.symm, mate (b k),
      move v _ hv (hb k).1 (hb k).2.1, move _ _ (hw k).1 (hb k).1 (hb k).2.2⟩
private def goodSlot {t : Nat} (K L : Finset (Fin (N t))) (b : Fin (3*t)) (k : Fin 15) : Prop :=
  match blockMap (b,k) with
  | .inl p => p ∈ K
  | .inr q => q ∈ L
private instance {t : Nat} (K L : Finset (Fin (N t))) (b : Fin (3*t)) (k : Fin 15) :
    Decidable (goodSlot K L b k) := by
  unfold goodSlot
  split <;> infer_instance
private theorem twoMissing {t : Nat} {K : Finset (Fin (N t))}
    (mate : Equiv.Perm (Fin (N t)))
    (hs : ∀ i ∈ K, ∀ j ∈ K, G i (mate j) ↔ G j (mate i))
    (b : Fin (3*t)) :
    2 ≤ ((Finset.univ : Finset (Fin 15)).filter
      (fun k => ¬ goodSlot K (K.map mate.toEmbedding) b k)).card := by
  classical
  let L := K.map mate.toEmbedding
  let S := (Finset.univ : Finset (Fin 15)).filter (fun k => ¬ goodSlot K L b k)
  change 2 ≤ S.card
  by_contra hh
  have he : S.card ≤ 1 := by omega
  have hone := Finset.card_le_one.mp he
  have hb : ∃ k : Fin 15, ∀ j ≠ k, goodSlot K L b j := by
    by_cases hs : S.Nonempty
    · obtain ⟨k,hk⟩ := hs
      refine ⟨k, fun j hj => ?_⟩
      by_contra h
      exact hj (hone j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩) k hk)
    · refine ⟨0, fun j _ => ?_⟩
      by_contra h
      exact hs ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
  obtain ⟨k,hk⟩ := hb
  have gp (x y : Fin 3) (h : ptSlot x y ≠ k) : blockP b x y ∈ K := by
    have e := hk _ h
    unfold goodSlot at e
    rwa [slotP] at e
  have ga (y : Fin 3) (h : aSlot y ≠ k) : blockA b y ∈ L := by
    have e := hk _ h
    unfold goodSlot at e
    rwa [slotA] at e
  have gb (x : Fin 3) (h : bSlot x ≠ k) : blockB b x ∈ L := by
    have e := hk _ h
    unfold goodSlot at e
    rwa [slotB] at e
  have aInj : Function.Injective (blockA b) := by
    intro x y e; have z := congrArg Fin.val e; simp only [blockA] at z; exact Fin.ext (by omega)
  have bInj : Function.Injective (blockB b) := by
    intro x y e; have z := congrArg Fin.val e; simp only [blockB] at z; exact Fin.ext (by omega)
  have ab (x y : Fin 3) : blockB b x ≠ blockA b y := by
    intro e; have z := congrArg Fin.val e; simp only [blockA,blockB] at z; omega
  rcases blankSlots k with ⟨y,z,ne,hey,hez,hx⟩ | ⟨x,z,ne,hex,hez,hy⟩
  · exact forbiddenGrid mate hs L rfl _ _ (aInj.ne ne) (ga _ hey) (ga _ hez)
      ⟨blockB b, bInj⟩ (fun j => ⟨gb _ (hx j).1, ab _ _, ab _ _⟩)
      (fun j => blockP b j y) (fun j => blockP b j z)
      (fun j => ⟨gp _ _ (hx j).2.1, gridA _ _ _, gridB _ _ _⟩)
      (fun j => ⟨gp _ _ (hx j).2.2, gridA _ _ _, gridB _ _ _⟩)
  · exact forbiddenGrid mate hs L rfl _ _ (bInj.ne ne) (gb _ hex) (gb _ hez)
      ⟨blockA b, aInj⟩ (fun j => ⟨ga _ (hy j).1, (ab _ _).symm, (ab _ _).symm⟩)
      (fun j => blockP b x j) (fun j => blockP b z j)
      (fun j => ⟨gp _ _ (hy j).2.1, gridB _ _ _, gridA _ _ _⟩)
      (fun j => ⟨gp _ _ (hy j).2.2, gridB _ _ _, gridA _ _ _⟩)
private theorem gridBound {t : Nat} {K : Finset (Fin (N t))}
    (mate : Equiv.Perm (Fin (N t)))
    (hs : ∀ i ∈ K, ∀ j ∈ K, G i (mate j) ↔ G j (mate i)) :
    3 * t ≤ N t - K.card := by
  classical
  let L := K.map mate.toEmbedding
  let missing := fun b : Fin (3*t) => (Finset.univ : Finset (Fin 15)).filter
    (fun k => ¬ goodSlot K L b k)
  let left : Finset (Fin (N t)) := Finset.univ \ K
  let right : Finset (Fin (N t)) := Finset.univ \ L
  let S := (Finset.univ : Finset (Fin (3*t))).sigma missing
  let f : (Sigma (fun _ : Fin (3*t) => Fin 15)) ↪ Fin (N t) ⊕ Fin (N t) :=
    ⟨fun a => blockMap (a.1,a.2), fun a b h => by
      have e := blockInj h
      cases a; cases b
      injection e with e1 e2
      subst_vars; rfl⟩
  have hsub : S.map f ⊆ left.disjSum right := by
    intro a ha
    obtain ⟨⟨b,k⟩,hb,rfl⟩ := Finset.mem_map.mp ha
    have e := (Finset.mem_filter.mp (Finset.mem_sigma.mp hb).2).2
    change blockMap (b,k) ∈ left.disjSum right
    unfold goodSlot at e
    split at e <;> rename_i z hz <;> rw [hz] <;> simp [left,right,e]
  have hu := Finset.card_le_card hsub
  have hl : ∑ b : Fin (3*t), 2 ≤ ∑ b : Fin (3*t), (missing b).card :=
    Finset.sum_le_sum (fun b _ => twoMissing mate hs b)
  simp only [Finset.card_map, Finset.card_disjSum, Finset.card_sdiff_of_subset
    (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, left, right, L] at hu
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hl
  rw [show S.card = ∑ b : Fin (3*t), (missing b).card from Finset.card_sigma _ _] at hu
  omega
private abbrev rd (C : Circuit) (w : Nat) := readsIn C (Finset.range C.size) w
private def Pair {n : Nat} (C : Circuit) (m : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  ∃ g ∈ C.gates, g.op = .or ∧
    (g.inputs = [i.val, n+(m i).val] ∨ g.inputs = [n+(m i).val,i.val])
private noncomputable def Kept {n : Nat} (C : Circuit) (m : Equiv.Perm (Fin n)) :=
  @Finset.filter (Fin n) (fun i => Pair C m i ∧ rd C i.val = 1 ∧ rd C (n+(m i).val) = 1)
    (fun _ => Classical.propDecidable _) Finset.univ
private theorem kept_mem {n : Nat} {C : Circuit} {m : Equiv.Perm (Fin n)} {i : Fin n}
    (h : i ∈ Kept C m) : Pair C m i ∧ rd C i.val = 1 ∧ rd C (n+(m i).val) = 1 := by
  simpa only [Kept,Finset.mem_filter,Finset.mem_univ,true_and] using h
private theorem gateAt_eq' (C : Circuit) (j : Nat) (h : j < C.size) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
private theorem rd_pos {C : Circuit} {g : Gate} {w : Nat} (hg : g ∈ C.gates)
    (h : w ∈ g.inputs) : 0 < rd C w := by
  obtain ⟨j,hj,e⟩ := List.mem_iff_getElem.mp hg
  have hle : (gateAt C j).inputs.count w ≤ rd C w :=
    Finset.single_le_sum (f := fun j => (gateAt C j).inputs.count w) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
  rw [gateAt_eq' C j hj,e] at hle
  exact lt_of_lt_of_le (List.count_pos_iff.mpr h) hle
private theorem sole_reader {C : Circuit} {u : Nat} {g h : Gate}
    (hg : g ∈ C.gates) (hh : h ∈ C.gates)
    (hu : u ∈ g.inputs) (hv : u ∈ h.inputs) (hr : rd C u = 1) : g = h := by
  obtain ⟨a,ha,hga⟩ := List.mem_iff_getElem.mp hg
  obtain ⟨b,hb,hgb⟩ := List.mem_iff_getElem.mp hh
  by_cases e : a=b
  · subst b; exact hga.symm.trans hgb
  let S := Finset.range C.size
  let f := fun j => (gateAt C j).inputs.count u
  have as : a ∈ S := Finset.mem_range.mpr ha
  have bs : b ∈ S.erase a := Finset.mem_erase.mpr ⟨Ne.symm e, Finset.mem_range.mpr hb⟩
  have c1 : 0 < f a := by
    dsimp [f]; rw [gateAt_eq' C a ha,hga]; exact List.count_pos_iff.mpr hu
  have c2 : 0 < f b := by
    dsimp [f]; rw [gateAt_eq' C b hb,hgb]; exact List.count_pos_iff.mpr hv
  have hh1 := Finset.sum_erase_add _ f as
  have hh2 : f b ≤ ∑ j ∈ S.erase a, f j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) bs
  change ∑ j ∈ S, f j = 1 at hr
  omega
private theorem getInput {n : Nat} (p q : Fin n) (w : Nat) :
    (oneEach p q).getD w false = (decide (w=p.val) || decide (w=n+q.val)) := by
  unfold oneEach
  rw [List.getD_eq_getElem?_getD]
  by_cases h : w < n
  · have hn : w < (List.ofFn (fun i : Fin n => decide (i=p))).length := by simpa
    have he : w ≠ n+q.val := by omega
    rw [List.getElem?_append_left hn, List.getElem?_ofFn, dite_eq_left h]
    simp [he, Fin.ext_iff]
  · have hn : (List.ofFn (fun i : Fin n => decide (i=p))).length ≤ w := by simpa using Nat.le_of_not_gt h
    have hp : w ≠ p.val := by have := p.isLt; omega
    rw [List.getElem?_append_right hn, List.length_ofFn, List.getElem?_ofFn]
    split
    · rename_i hw; have e : w - n = q.val ↔ w = n+q.val := by omega
      simp [hp, Fin.ext_iff, e]
    · rename_i hw; have e : w ≠ n+q.val := by have := q.isLt; omega
      simp [hp,e]
private theorem inputLen {n : Nat} (p q : Fin n) : (oneEach p q).length = n+n := by
  simp [oneEach]
private def stepVal (g : Gate) (a : List Bool) := g.op.eval (g.inputs.map (fun i => a.getD i false))
private def run (gs : List Gate) (a : List Bool) := gs.foldl (fun x g => x ++ [stepVal g x]) a
private theorem foldEqual {a b : List Bool} (gs : List Gate)
    (h : ∀ g ∈ gs, ∀ z : List Bool, stepVal g (a++z) = stepVal g (b++z)) (z : List Bool) :
    ∃ z', run gs (a++z) = a++z' ∧ run gs (b++z) = b++z' := by
  induction gs generalizing z with
  | nil => exact ⟨z,rfl,rfl⟩
  | cons g gs ih =>
    have e := h g (by simp) z
    obtain ⟨z',e1,e2⟩ := ih (fun g hg => h g (by simp [hg])) (z++[stepVal g (a++z)])
    refine ⟨z', ?_, ?_⟩
    · simpa only [run,List.foldl_cons,List.append_assoc] using e1
    · simpa only [run,List.foldl_cons,List.append_assoc, e] using e2
private theorem rawWires (C : Circuit) (a : List Bool) : ∃ z, C.wires a = a++z := by
  have h : ∀ g ∈ C.gates, ∀ z : List Bool, stepVal g (a++z) = stepVal g (a++z) := by simp
  obtain ⟨z,e,_⟩ := foldEqual C.gates h []
  refine ⟨z, ?_⟩
  change run C.gates a = a++z
  simpa only [List.append_nil] using e
private theorem output_not_raw {t : Nat} (ht : 1 ≤ t) {C : Circuit}
    (rep : Represents (fun p c : Fin (N t) => decide (G p c)) C) : 2*N t ≤ C.output := by
  by_contra! e
  let blk : Fin (3*t) := ⟨0,by omega⟩
  let p := blockP blk 0 0
  let p' := blockP blk 1 0
  let a := blockA blk 0
  let b := blockB blk 0
  have pp : p.val ≠ p'.val := by simp [p,p',blockP]
  have ab : a.val ≠ b.val := by simp [a,b,blockA,blockB,blk]
  have hh (x y : Fin (N t)) (hxy : G x y) : C.output = x.val ∨ C.output = N t+y.val := by
    have r : C.eval (oneEach x y) = decide (G x y) := rep x y
    rw [decide_eq_true hxy] at r
    obtain ⟨z,ez⟩ := rawWires C (oneEach x y)
    unfold Circuit.eval at r
    rw [ez,List.getD_append _ _ _ _ (by rw [inputLen]; omega),getInput] at r
    simpa using r
  rcases hh p a (gridA blk 0 0) with h | h
  · rcases hh p' a (gridA blk 1 0) with h₂ | h₂ <;> omega
  · rcases hh p b (gridB blk 0 0) with h₂ | h₂ <;> omega
private theorem pair_sym {n : Nat} {C : Circuit} (out : n+n ≤ C.output)
    (mate : Equiv.Perm (Fin n)) {i j : Fin n}
    (hi : i ∈ Kept C mate) (hj : j ∈ Kept C mate) :
    C.eval (oneEach i (mate j)) = C.eval (oneEach j (mate i)) := by
  by_cases e : i=j
  · subst j; rfl
  have ei : i.val ≠ j.val := fun eq => e (Fin.ext eq)
  have ej : (mate i).val ≠ (mate j).val := fun eq => e (mate.injective (Fin.ext eq))
  obtain ⟨⟨gi,hgi,opi,ini⟩,ri,si⟩ := kept_mem hi
  obtain ⟨⟨gj,hgj,opj,inj⟩,rj,sj⟩ := kept_mem hj
  let a := oneEach i (mate j)
  let b := oneEach j (mate i)
  have al : a.length=n+n := inputLen _ _
  have bl : b.length=n+n := inputLen _ _
  have hstep : ∀ g ∈ C.gates, ∀ z : List Bool, stepVal g (a++z) = stepVal g (b++z) := by
    intro g hg z
    have aBit (w : Nat) (hw : w < n+n) :
        (a++z).getD w false = (decide (w=i.val) || decide (w=n+(mate j).val)) := by
      rw [List.getD_append _ _ _ _ (by simpa only [al])]
      exact getInput _ _ _
    have bBit (w : Nat) (hw : w < n+n) :
        (b++z).getD w false = (decide (w=j.val) || decide (w=n+(mate i).val)) := by
      rw [List.getD_append _ _ _ _ (by simpa only [bl])]
      exact getInput _ _ _
    by_cases h₁ : g=gi
    · subst g
      have hik : i.val < n+n := by have := i.isLt; omega
      have him : n+(mate i).val < n+n := by have := (mate i).isLt; omega
      rcases ini with ini|ini <;>
        simp only [stepVal, opi, ini, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
          aBit _ hik, aBit _ him, bBit _ hik, bBit _ him] <;>
        simp [ ei, ei.symm, ej, ej.symm, show i.val ≠ n+(mate i).val by omega,
          show i.val ≠ n+(mate j).val by omega, show n+(mate i).val ≠ j.val by omega,
          show n+(mate i).val ≠ i.val by omega]
    by_cases h₂ : g=gj
    · subst g
      have hjk : j.val < n+n := by have := j.isLt; omega
      have hjm : n+(mate j).val < n+n := by have := (mate j).isLt; omega
      rcases inj with inj|inj <;>
        simp only [stepVal, opj, inj, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
          aBit _ hjk, aBit _ hjm, bBit _ hjk, bBit _ hjm] <;>
        simp [ ei, ei.symm, ej, ej.symm, show j.val ≠ n+(mate j).val by omega,
          show j.val ≠ n+(mate i).val by omega, show n+(mate j).val ≠ j.val by omega,
          show n+(mate j).val ≠ i.val by omega]
    unfold stepVal
    congr 1
    apply List.map_congr_left
    intro w hw
    by_cases hx : w < n+n
    · rw [aBit _ hx, bBit _ hx]
      have avoid (q : Nat) (hread : rd C q = 1) (g₀ : Gate) (hg₀ : g₀ ∈ C.gates)
          (in₀ : q ∈ g₀.inputs) (hneq : g ≠ g₀) : w ≠ q := by
        intro e; subst w; exact hneq (sole_reader hg hg₀ hw in₀ hread)
      have wi := avoid _ ri _ hgi (by rcases ini with h|h <;> simp [h]) h₁
      have wmi := avoid _ si _ hgi (by rcases ini with h|h <;> simp [h]) h₁
      have wj := avoid _ rj _ hgj (by rcases inj with h|h <;> simp [h]) h₂
      have wmj := avoid _ sj _ hgj (by rcases inj with h|h <;> simp [h]) h₂
      simp [wi,wmi,wj,wmj]
    · simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by simpa only [al] using Nat.le_of_not_gt hx),
        List.getElem?_append_right (by simpa only [bl] using Nat.le_of_not_gt hx), al, bl]
  obtain ⟨z,ha,hb⟩ := foldEqual C.gates hstep []
  rw [List.append_nil] at ha hb
  change run C.gates a = _ at ha
  change run C.gates b = _ at hb
  change (run C.gates a).getD C.output false = (run C.gates b).getD C.output false
  rw [ha,hb]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simpa only [al] using out),
    List.getElem?_append_right (by simpa only [bl] using out), al, bl]
private theorem slotBound {n : Nat} {C : Circuit} (mate : Equiv.Perm (Fin n))
    (pair : ∀ i, Pair C mate i) (fan : FanInTwo C) (back : ReadsBack (n+n) C)
    (live : ∀ i : Fin C.gates.length, n+n+i.val ≠ C.output → 0 < rd C (n+n+i.val)) :
    2*n + (n-(Kept C mate).card) ≤ C.size + 1 := by
  classical
  let K := Kept C mate
  let E := (Finset.univ : Finset (Fin n)) \ K
  have readPair (i : Fin n) : 0 < rd C i.val ∧ 0 < rd C (n+(mate i).val) := by
    obtain ⟨g,hg,_,e⟩ := pair i
    exact ⟨rd_pos hg (by rcases e with e|e <;> simp [e]),
      rd_pos hg (by rcases e with e|e <;> simp [e])⟩
  have cost (i : Fin n) : 2 + (if i∈E then 1 else 0) ≤ rd C i.val + rd C (n+(mate i).val) := by
    have reads := readPair i
    by_cases h : i ∈ K
    · have h' : i ∉ E := by simp [E,h]
      rw [ite_eq_right h']
      omega
    · have h' : i ∈ E := by simp [E,h]
      rw [ite_eq_left h']
      have hn : ¬ (rd C i.val = 1 ∧ rd C (n+(mate i).val) = 1) := by
        intro hr
        apply h
        change i ∈ Kept C mate
        simp only [Kept,Finset.mem_filter,Finset.mem_univ,true_and]
        exact ⟨pair i,hr⟩
      omega
  have hc : (∑ i : Fin n, (2 + (if i∈E then 1 else 0))) ≤ ∑ i : Fin n, (rd C i.val + rd C (n+(mate i).val)) :=
    Finset.sum_le_sum (fun i _ => cost i)
  have ec : (∑ i : Fin n, if i∈E then 1 else 0) = E.card := by
    rw [← Finset.sum_filter]
    simp
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,ec] at hc
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hc
  have ecard : E.card = n-K.card := by simp [E, Finset.card_sdiff]
  rw [ecard] at hc
  have raw₁ : ∑ i : Fin n, rd C i.val = ∑ v ∈ Finset.range n, rd C v :=
    Fin.sum_univ_eq_sum_range _ _
  have raw₂ : ∑ i : Fin n, rd C (n+(mate i).val) = ∑ v ∈ Finset.range n, rd C (n+v) := by
    rw [Equiv.sum_comp mate (fun i => rd C (n+i.val))]
    exact Fin.sum_univ_eq_sum_range (fun v : Nat => rd C (n+v)) n
  rw [raw₁,raw₂] at hc
  have raw : 2*n + (n-K.card) ≤ ∑ v ∈ Finset.range (n+n), rd C v := by
    rw [Finset.sum_range_add]
    omega
  let s := C.size
  let J := (Finset.range s).erase (C.output-(n+n))
  have ilive : J.card ≤ ∑ v ∈ Finset.range s, rd C (n+n+v) := by
    calc
      J.card = ∑ v ∈ J, (1 : Nat) := by simp
      _ ≤ ∑ v ∈ J, rd C (n+n+v) := by
        apply Finset.sum_le_sum
        intro v hv
        have h' := Finset.mem_erase.mp hv
        have hlt : v < C.gates.length := Finset.mem_range.mp h'.2
        have ne : n+n+v ≠ C.output := by
          intro e
          apply h'.1
          omega
        exact live ⟨v,hlt⟩ ne
      _ ≤ ∑ v ∈ Finset.range s, rd C (n+n+v) := Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
  have jcard : s ≤ J.card+1 := by
    by_cases h : C.output-(n+n) ∈ Finset.range s
    · simpa [J] using (Finset.card_erase_add_one h).ge
    · simp [J,Finset.erase_eq_of_notMem h]
  have total : (∑ v ∈ Finset.range (n+n+s), rd C v) ≤ 2*s := by
    simp only [rd, readsIn]
    rw [Finset.sum_comm]
    have exactSlots (j : Nat) (hj : j ∈ Finset.range C.size) :
        (∑ v ∈ Finset.range (n+n+s), (gateAt C j).inputs.count v) = (gateAt C j).inputs.length := by
      have hj' : j < C.gates.length := Finset.mem_range.mp hj
      have bound : ∀ v ∈ ((gateAt C j).inputs : Multiset Nat), v ∈ Finset.range (n+n+s) := by
        intro v hv
        have hv' := back j hj' v hv
        change j < s at hj'
        exact Finset.mem_range.mpr (by omega)
      simpa only [Multiset.coe_count, Multiset.coe_card] using Multiset.sum_count_eq_card bound
    calc
      (∑ j ∈ Finset.range C.size, ∑ v ∈ Finset.range (n+n+s), (gateAt C j).inputs.count v) =
          ∑ j ∈ Finset.range C.size, (gateAt C j).inputs.length := Finset.sum_congr rfl exactSlots
      _ ≤ ∑ _j ∈ Finset.range C.size, (2 : Nat) := by
        refine Finset.sum_le_sum ?_
        intro j hj
        have hj' := Finset.mem_range.mp hj
        rw [gateAt_eq' C j hj']
        exact (fan _ (List.getElem_mem _)).2
      _ = 2*s := by simp [s,Nat.mul_comm]
  rw [Finset.sum_range_add] at total
  change 2*n + (n-K.card) ≤ s+1
  omega
private theorem solve {t : Nat} (ht : 1 ≤ t) (C : Circuit) (mate : Equiv.Perm (Fin (N t)))
    (back : ReadsBack (2*N t) C)
    (rep : Represents (fun p c : Fin (N t) => decide (G p c)) C) :
    3 * t ≤ N t - (Kept C mate).card ∧
    ((∀ i, Pair C mate i) → FanInTwo C →
      (∀ i : Fin C.gates.length, 2*N t+i.val ≠ C.output → 0 < rd C (2*N t+i.val)) →
      57 * t ≤ C.size + 1) := by
  have hout := output_not_raw ht rep
  have sym : ∀ i ∈ Kept C mate, ∀ j ∈ Kept C mate, G i (mate j) ↔ G j (mate i) := by
    intro i hi j hj
    have h : (decide (G i (mate j))) = decide (G j (mate i)) :=
      (rep i (mate j)).symm.trans ((pair_sym (by omega) mate hi hj).trans (rep j (mate i)))
    exact decide_eq_decide.mp h
  have h := gridBound mate sym
  refine ⟨h,?_⟩
  intro pair fan live
  have cost := slotBound mate pair fan (by simpa only [two_mul] using back)
    (by simpa only [two_mul] using live)
  unfold N at *
  omega
end PEqualNP.Outside.L_meta_25564

theorem PEqualNP.Outside.L_meta_25564 : (∀ (t : ℕ), 1 ≤ t →
  let n := 27 * t
  let G := fun (p c : Fin n) =>
    let point := p.val % 27
    let x := point % 3
    let y := point / 3 % 3
    let z := point / 9
    let axis := (c.val % 27) / 9
    let label := c.val % 9
    let sheet := p.val / 27
    let target := if point = 0 ∧ axis = 2 then (sheet + 1) % t else sheet
    decide (c.val / 27 = target ∧
      label = (if axis = 0 then y + 3 * z else if axis = 1 then x + 3 * z else x + 3 * y))
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (mate : Equiv.Perm (Fin n)),
    let reads := PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size)
    let pairGate := fun (i : Fin n) =>
      ∃ g ∈ C.gates, g.op = .or ∧
        (g.inputs = [i.val, n + (mate i).val] ∨ g.inputs = [n + (mate i).val, i.val])
    let kept := @Finset.filter (Fin n)
      (fun idx => pairGate idx ∧ reads idx.val = 1 ∧ reads (n + (mate idx).val) = 1)
      (fun _ => Classical.propDecidable _) Finset.univ
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * n) C →
    PEqualNP.Represents.Represents G C →
    3 * t ≤ n - kept.card ∧
      ((∀ i, pairGate i) → PEqualNP.MetaComplexity.FanInTwo C →
       (∀ i : Fin C.gates.length, 2 * n + i.val ≠ C.output → 0 < reads (2 * n + i.val)) →
       57 * t ≤ C.size + 1)) := by
  intro t ht
  dsimp only
  intro C mate hb hr
  apply PEqualNP.Outside.L_meta_25564.solve ht C mate hb
  intro p c
  refine (hr p c).trans ?_
  apply Bool.decide_congr
  simp only [PEqualNP.Outside.L_meta_25564.G, PEqualNP.Outside.L_meta_25564.sh,
    PEqualNP.Outside.L_meta_25564.nextSh, PEqualNP.Outside.L_meta_25564.bp, PEqualNP.Outside.L_meta_25564.Inc,
    PEqualNP.Outside.L_meta_25564.lbl, Nat.mod_mod_of_dvd _ (show 9 ∣ 27 by decide)]
  rfl

