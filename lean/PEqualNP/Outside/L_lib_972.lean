import Mathlib

namespace PEqualNP.Outside.L_lib_972_aux

private noncomputable def subEquiv {U V : Type*} (e : U ≃ V) (p : U → Prop)
    (q : V → Prop) (h : ∀ u, p u ↔ q (e u)) : Subtype p ≃ Subtype q where
  toFun u := ⟨e u, (h u).mp u.property⟩
  invFun v := ⟨e.symm v, (h _).mpr (by simpa using v.property)⟩
  left_inv u := Subtype.ext (e.symm_apply_apply u)
  right_inv v := Subtype.ext (e.apply_symm_apply v)

private def subProd {U V : Type*} (p : U → V → Prop) :
    {w : U × V // p w.1 w.2} ≃ Σ u, {v : V // p u v} where
  toFun w := ⟨w.val.1, w.val.2, w.property⟩
  invFun w := ⟨(w.1, w.2.val), w.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def swapSub {U V : Type*} (p : U → V → Prop) :
    (Σ u, {v : V // p u v}) ≃ Σ v, {u : U // p u v} where
  toFun w := ⟨w.2.val, w.1, w.2.property⟩
  invFun w := ⟨w.2.val, w.1, w.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem shiftEmbed {U : Type*} [AddGroup U] (p q : U → Prop)
    (h : ∀ u v, p u → p v → q (u - v)) : Nonempty (Subtype p ↪ Subtype q) := by
  classical
  by_cases hp : Nonempty (Subtype p)
  · let r := Classical.choice hp
    exact ⟨⟨fun u => ⟨u.val - r.val, h u r u.property r.property⟩,
      fun u v huv => Subtype.ext (sub_left_inj.mp (congrArg Subtype.val huv))⟩⟩
  · exact ⟨⟨fun u => (hp ⟨u⟩).elim, fun u _ _ => (hp ⟨u⟩).elim⟩⟩

private theorem sigmaMono {U : Type*} {p q : U → Type*} [Finite (Σ u, q u)]
    (h : ∀ u, Nonempty (p u ↪ q u)) : Nat.card (Σ u, p u) ≤ Nat.card (Σ u, q u) := by
  classical
  let f (u : U) := Classical.choice (h u)
  refine Nat.card_le_card_of_injective (fun w : Σ u, p u => ⟨w.1, f w.1 w.2⟩) ?_
  rintro ⟨u, a⟩ ⟨v, b⟩ he
  have huv : u = v := congrArg Sigma.fst he
  subst v
  congr 1
  exact (f u).injective (by simpa using he)

section Leaf
variable {X Y : Type*} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

private abbrev proj (S : Submodule (ZMod 2) (X × Y)) :=
  S.map (LinearMap.fst (ZMod 2) X Y)
private abbrev vert (S : Submodule (ZMod 2) (X × Y)) :=
  S.comap (LinearMap.inr (ZMod 2) X Y)

private noncomputable def lift (S : Submodule (ZMod 2) (X × Y)) (p : proj S) : S :=
  ⟨Classical.choose p.property, (Classical.choose_spec p.property).1⟩

private theorem lift_fst (S : Submodule (ZMod 2) (X × Y)) (p : proj S) :
    (lift S p).val.1 = p.val := (Classical.choose_spec p.property).2

private noncomputable def leafEquiv (S : Submodule (ZMod 2) (X × Y)) :
    S ≃ proj S × vert S where
  toFun s := by
    let p : proj S := ⟨s.val.1, ⟨s.val, s.property, rfl⟩⟩
    exact (p, ⟨s.val.2 - (lift S p).val.2, by
      change (0, s.val.2 - (lift S p).val.2) ∈ S
      have h := S.sub_mem s.property (lift S p).property
      change (s.val.1 - (lift S p).val.1, s.val.2 - (lift S p).val.2) ∈ S at h
      simpa [lift_fst, p] using h⟩)
  invFun w := ⟨(lift S w.1).val + (0, w.2.val),
    S.add_mem (lift S w.1).property w.2.property⟩
  left_inv s := by
    apply Subtype.ext
    apply Prod.ext
    · simp [lift_fst]
    · change (lift S ⟨s.val.1, _⟩).val.2 + (s.val.2 - (lift S ⟨s.val.1, _⟩).val.2) = _
      abel
  right_inv w := by
    have hp : (⟨((lift S w.1).val + (0, w.2.val)).1, by
        exact ⟨_, S.add_mem (lift S w.1).property w.2.property, rfl⟩⟩ : proj S) = w.1 := by
      apply Subtype.ext
      change (lift S w.1).val.1 + 0 = _
      simp [lift_fst]
    apply Prod.ext
    · exact hp
    · apply Subtype.ext
      change (lift S w.1).val.2 + w.2.val - (lift S _).val.2 = _
      rw [hp]
      abel

private theorem cardLeaf [Finite X] [Finite Y] (S : Submodule (ZMod 2) (X × Y)) :
    Nat.card S = Nat.card (proj S) * Nat.card (vert S) :=
  (Nat.card_congr (leafEquiv S)).trans (Nat.card_prod _ _)

variable {Z : Type*} [AddCommGroup Z] [Module (ZMod 2) Z]

private theorem leafBound [Finite X] [Finite Y] (B : X →ₗ[ZMod 2] Y →ₗ[ZMod 2] Z)
    (S : Submodule (ZMod 2) (X × Y)) (o : X × Y) (A : (X × Y) →ₗ[ZMod 2] Z) (c : Z) :
    Nat.card {s : S // B (o + s.val).1 (o + s.val).2 = A (o + s.val) + c} ≤
    Nat.card {w : X × Y // w.1 ∈ proj S ∧ w.2 ∈ vert S ∧ B w.1 w.2 = 0} := by
  classical
  let P := proj S
  let Q := vert S
  let C (p : P) (q : Q) : Prop :=
    B (o.1 + p.val) (o.2 + (lift S p).val.2 + q.val) =
      A (o + (lift S p).val) + c + A (0, q.val)
  let D (p : P) (q : Q) : Prop := B (p : X) (q : Y) = A (0, q.val) - B o.1 q.val
  let E (p : P) (q : Q) : Prop := B (p : X) (q : Y) = 0
  have hC (p : P) : Nonempty ({q // C p q} ↪ {q // D p q}) := by
    apply shiftEmbed
    intro u v hu hv
    let x := o.1 + p.val
    let y := o.2 + (lift S p).val.2
    let z := A (o + (lift S p).val) + c
    have hh (q : Q) (hq : C p q) : B x y + B x q.val = z + A (0, q.val) := by
      change B x (y + q.val) = z + A (0, q.val) at hq
      rwa [map_add] at hq
    have hd : B x u.val - B x v.val = A (0, u.val) - A (0, v.val) := calc
      _ = (B x y + B x u.val) - (B x y + B x v.val) := by abel
      _ = (z + A (0, u.val)) - (z + A (0, v.val)) := congrArg₂ Sub.sub (hh u hu) (hh v hv)
      _ = _ := by abel
    have hg : ((0 : X), u.val - v.val) = (0, u.val) - (0, v.val) := by simp
    rw [← map_sub, ← map_sub, ← hg] at hd
    dsimp only [x] at hd
    rw [map_add B, LinearMap.add_apply] at hd
    exact eq_sub_of_add_eq (by rw [add_comm]; exact hd)
  have hD (q : Q) : Nonempty ({p // D p q} ↪ {p // E p q}) := by
    apply shiftEmbed
    intro u v hu hv
    change B (u.val - v.val) q.val = 0
    simp only [map_sub, LinearMap.sub_apply, sub_eq_zero]
    exact hu.trans hv.symm
  have hstart : Nat.card {s : S // B (o + s.val).1 (o + s.val).2 = A (o + s.val) + c} =
      Nat.card (Σ p, {q // C p q}) := by
    apply Nat.card_congr
    refine (subEquiv (leafEquiv S).symm (fun w => C w.1 w.2) _ ?_).symm.trans (subProd C)
    intro w
    change C w.1 w.2 ↔ B (o.1 + ((lift S w.1).val.1 + 0))
      (o.2 + ((lift S w.1).val.2 + w.2.val)) = A (o + ((lift S w.1).val + (0, w.2.val))) + c
    simp [C, lift_fst, add_comm, add_left_comm]
  have hend : Nat.card (Σ q, {p // E p q}) =
      Nat.card {w : X × Y // w.1 ∈ P ∧ w.2 ∈ Q ∧ B w.1 w.2 = 0} := by
    apply Nat.card_congr
    refine (swapSub E).symm.trans ((subProd E).symm.trans ?_)
    exact {
      toFun := fun w => ⟨(w.val.1.val, w.val.2.val), w.val.1.property, w.val.2.property, w.property⟩
      invFun := fun w => ⟨(⟨w.val.1, w.property.1⟩, ⟨w.val.2, w.property.2.1⟩), w.property.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    _ = Nat.card (Σ p, {q // C p q}) := hstart
    _ ≤ Nat.card (Σ p, {q // D p q}) := sigmaMono hC
    _ = Nat.card (Σ q, {p // D p q}) := Nat.card_congr (swapSub D)
    _ ≤ Nat.card (Σ q, {p // E p q}) := sigmaMono hD
    _ = _ := hend

end Leaf

open scoped BigOperators

section ForwardPath

variable {W ι : Type*} [AddCommGroup W] [Module (ZMod 2) W]

private def forwardRun (ask : ι → ℕ → W →ₗ[ZMod 2] ZMod 2) (is : List ι) (w : W) : ℕ :=
  is.foldl (fun z i => 2*z + (if ask i z w = 0 then 0 else 1)) 0

/-- The direction of the path leaf through `o`, intersecting one kernel per query. -/
private def forwardDir (ask : ι → ℕ → W →ₗ[ZMod 2] ZMod 2) (o : W) (is : List ι) :
    Submodule (ZMod 2) W :=
  (is.foldl (fun (z, S) i =>
    (2*z + (if ask i z o = 0 then 0 else 1), S ⊓ (ask i z).ker)) (0, ⊤)).2

private theorem forwardState (ask : ι → ℕ → W →ₗ[ZMod 2] ZMod 2) (o : W) (is : List ι) :
    (is.foldl (fun (z, S) i =>
      (2*z + (if ask i z o = 0 then 0 else 1), S ⊓ (ask i z).ker))
      (0, ⊤)).1 = forwardRun ask is o := by
  induction is using List.reverseRecOn with
  | nil => rfl
  | append_singleton is i ih =>
    simp only [forwardRun, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [ih]

private theorem forwardDir_append (ask : ι → ℕ → W →ₗ[ZMod 2] ZMod 2) (o : W)
    (is : List ι) (i : ι) :
    forwardDir ask o (is ++ [i]) = forwardDir ask o is ⊓ (ask i (forwardRun ask is o)).ker := by
  unfold forwardDir
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [forwardState]

private theorem forwardBitEq (a b : ZMod 2) :
    (if a = 0 then (0 : ℕ) else 1) = (if b = 0 then 0 else 1) ↔ a = b := by
  have cases₂ : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases cases₂ a with rfl | rfl <;> rcases cases₂ b with rfl | rfl <;> decide

private theorem forwardLeaf (ask : ι → ℕ → W →ₗ[ZMod 2] ZMod 2) (o w : W) (is : List ι) :
    forwardRun ask is w = forwardRun ask is o ↔ w - o ∈ forwardDir ask o is := by
  induction is using List.reverseRecOn with
  | nil => simp [forwardRun, forwardDir]
  | append_singleton is i ih =>
    rw [forwardDir_append, Submodule.mem_inf, ← ih, LinearMap.mem_ker, map_sub, sub_eq_zero]
    change (is ++ [i]).foldl _ 0 = (is ++ [i]).foldl _ 0 ↔ _
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    change 2 * forwardRun ask is w + (if ask i (forwardRun ask is w) w = 0 then 0 else 1) =
      2 * forwardRun ask is o + (if ask i (forwardRun ask is o) o = 0 then 0 else 1) ↔ _
    constructor
    · intro he
      have hz : forwardRun ask is w = forwardRun ask is o := by
        split at he <;> split at he <;> omega
      refine ⟨hz, (forwardBitEq _ _).mp ?_⟩
      rw [hz] at he
      exact Nat.add_left_cancel he
    · rintro ⟨hz, hb⟩
      rw [hz, hb]

variable [Module.Finite (ZMod 2) W]

private theorem forwardDim (ask : ι → ℕ → W →ₗ[ZMod 2] ZMod 2) (o : W) (is : List ι) :
    Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) (forwardDir ask o is) + is.length := by
  induction is using List.reverseRecOn with
  | nil =>
    change Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) ↥(⊤ : Submodule (ZMod 2) W) + 0
    rw [finrank_top, add_zero]
  | append_singleton is i ih =>
    rw [forwardDir_append, List.length_append, List.length_singleton]
    let S := forwardDir ask o is
    let f := ask i (forwardRun ask is o)
    have hn := f.finrank_range_add_finrank_ker
    have hr := Submodule.finrank_le f.range
    have hs := Submodule.finrank_sup_add_finrank_inf_eq S f.ker
    have hsup := Submodule.finrank_le (S ⊔ f.ker)
    change Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) S + is.length at ih
    change Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) ↥(S ⊓ f.ker) + (is.length + 1)
    have hf : Module.finrank (ZMod 2) (ZMod 2) = 1 := Module.finrank_self _
    omega

end ForwardPath

private theorem forwardPowCard (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
  let := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

private theorem forwardFilterCard {V : Type*} [Fintype V] (p : V → Prop) [DecidablePred p] :
    Nat.card {x : V // p x} = (Finset.univ.filter p).card := by
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_of_subtype _ (by simp)

private theorem forwardOptimizer (l r m h : ℕ) :
    let X := Fin l → ZMod 2
    let Y := Fin r → ZMod 2
    let Z := Fin m → ZMod 2
    let W := X × Y
    ∀ (B : X →ₗ[ZMod 2] Y →ₗ[ZMod 2] Z),
    (∀ (S : Submodule (ZMod 2) W) (o : W) (a : W →ₗ[ZMod 2] Z) (c : Z),
      let P := S.map (LinearMap.fst (ZMod 2) X Y)
      let Q := S.comap (LinearMap.inr (ZMod 2) X Y)
      Nat.card {s : S // B (o + (s : W)).1 (o + (s : W)).2 = a (o + (s : W)) + c} ≤
        Nat.card {w : W // w.1 ∈ P ∧ w.2 ∈ Q ∧ B w.1 w.2 = 0} ∧
      Nat.card S = Nat.card P * Nat.card Q) →
    ∀ (ask : Fin h → ℕ → W →ₗ[ZMod 2] ZMod 2) (A : ℕ → W →ₗ[ZMod 2] Z) (c : ℕ → Z),
    ∃ (P : Submodule (ZMod 2) X) (Q : Submodule (ZMod 2) Y),
      let cost := (l - Module.finrank (ZMod 2) P) + (r - Module.finrank (ZMod 2) Q)
      cost ≤ h ∧
      Nat.card {w : W // B w.1 w.2 = A (forwardRun ask (List.finRange h) w) w +
          c (forwardRun ask (List.finRange h) w)} ≤
        2^cost * Nat.card {w : W // w.1 ∈ P ∧ w.2 ∈ Q ∧ B w.1 w.2 = 0} := by
  classical
  dsimp only
  intro B leafBound ask A c
  let F := ZMod 2
  let X := Fin l → F
  let Y := Fin r → F
  let W := X × Y
  let run : W → ℕ := forwardRun ask (List.finRange h)
  let good : W → Prop := fun w => B w.1 w.2 = A (run w) w + c (run w)
  let L := Finset.univ.image run
  have hL : L.Nonempty := ⟨run 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  have originEx (j : L) : ∃ o, run o = j.val := by
    obtain ⟨o, _, ho⟩ := Finset.mem_image.mp j.property
    exact ⟨o, ho⟩
  choose o ho using originEx
  let S (j : L) := forwardDir ask (o j) (List.finRange h)
  let P (j : L) := (S j).map (LinearMap.fst F X Y)
  let Q (j : L) := (S j).comap (LinearMap.inr F X Y)
  let cost (j : L) := (l - Module.finrank F (P j)) + (r - Module.finrank F (Q j))
  let zeros (j : L) := Nat.card {w : W // w.1 ∈ P j ∧ w.2 ∈ Q j ∧ B w.1 w.2 = 0}
  let score (j : L) := 2^cost j * zeros j
  let cnt (j : ℕ) := (Finset.univ.filter fun w => run w = j).card
  let suc (j : ℕ) := ((Finset.univ.filter good).filter fun w => run w = j).card
  let emb (j : L) : S j ≃ {w : W // run w = j.val} :=
    { toFun := fun s => ⟨o j + s.val, by
        rw [← ho j]
        apply (forwardLeaf ask (o j) _ _).mpr
        simp [add_comm]⟩
      invFun := fun w => ⟨w.val - o j, (forwardLeaf ask (o j) _ _).mp
        (w.property.trans (ho j).symm)⟩
      left_inv := fun s => Subtype.ext (by simp [add_comm])
      right_inv := fun w => Subtype.ext (by simp) }
  have hsucc (j : L) : suc j.val ≤ zeros j := by
    have e : {s : S j // B (o j + s.val).1 (o j + s.val).2 =
          A j.val (o j + s.val) + c j.val} ≃ {w : W // good w ∧ run w = j.val} :=
      { toFun := fun s => ⟨(emb j s.val).val, by
          refine ⟨?_, (emb j s.val).property⟩
          change B _ _ = A (run (emb j s.val).val) _ + c (run (emb j s.val).val)
          rw [(emb j s.val).property]
          exact s.property⟩
        invFun := fun w => ⟨(emb j).symm ⟨w.val, w.property.2⟩, by
          have hw := congrArg Subtype.val ((emb j).apply_symm_apply ⟨w.val, w.property.2⟩)
          change o j + ((emb j).symm ⟨w.val, w.property.2⟩).val = w.val at hw
          rw [hw]
          simpa only [good, w.property.2] using w.property.1⟩
        left_inv := fun s => Subtype.ext ((emb j).symm_apply_apply s.val)
        right_inv := fun w => Subtype.ext <| congrArg
          (fun x : {w : W // run w = j.val} => x.val)
          ((emb j).apply_symm_apply ⟨w.val, w.property.2⟩) }
    have hb := (leafBound (S j) (o j) (A j.val) (c j.val)).1
    rw [Nat.card_congr e, forwardFilterCard] at hb
    change _ ≤ zeros j at hb
    simpa only [suc, Finset.filter_filter, and_comm] using hb
  have hcnt (j : L) : cnt j.val = Nat.card (S j) :=
    (forwardFilterCard _).symm.trans (Nat.card_congr (emb j)).symm
  have hx : Module.finrank F X = l := by simp [X]
  have hy : Module.finrank F Y = r := by simp [Y]
  have hw : Module.finrank F W = l + r := by rw [Module.finrank_prod, hx, hy]
  have numerics (j : L) : cost j ≤ h ∧ 2^cost j * cnt j.val = Nat.card W := by
    have hp := Submodule.finrank_le (P j)
    have hq := Submodule.finrank_le (Q j)
    rw [hx] at hp
    rw [hy] at hq
    have hd := forwardDim ask (o j) (List.finRange h)
    change Module.finrank F W ≤ Module.finrank F (S j) + (List.finRange h).length at hd
    rw [hw, List.length_finRange] at hd
    have hc : Nat.card (S j) = Nat.card (P j) * Nat.card (Q j) :=
      (leafBound (S j) (o j) (A j.val) (c j.val)).2
    rw [forwardPowCard (S j), forwardPowCard (P j), forwardPowCard (Q j), ← pow_add] at hc
    have he : Module.finrank F (S j) = Module.finrank F (P j) + Module.finrank F (Q j) :=
      (Nat.pow_right_injective (by decide : 2 ≤ 2)) hc
    have hcost : cost j + Module.finrank F (S j) = l + r := by
      dsimp [cost]
      omega
    refine ⟨by omega, ?_⟩
    rw [hcnt, forwardPowCard (S j), forwardPowCard W, hw, ← pow_add, hcost]
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image L.attach score (by simpa using hL)
  have hsums : (∑ j ∈ L, suc j) = Nat.card {w : W // good w} := by
    rw [forwardFilterCard]
    unfold suc
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    exact congrArg Finset.card (Finset.filter_true_of_mem fun w _ =>
      Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩)
  have hsumc : (∑ j ∈ L, cnt j) = Nat.card W := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    unfold cnt
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    exact congrArg Finset.card (Finset.filter_true_of_mem fun w _ =>
      Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩)
  have hterm (j : L) : Nat.card W * suc j.val ≤ cnt j.val * score j₀ := calc
    _ = cnt j.val * (2^cost j * suc j.val) := by rw [← (numerics j).2]; ac_rfl
    _ ≤ cnt j.val * score j := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hsucc j))
    _ ≤ _ := Nat.mul_le_mul_left _ (hj₀ j (Finset.mem_attach _ _))
  have hall : Nat.card W * Nat.card {w : W // good w} ≤ Nat.card W * score j₀ := by
    calc
      _ = ∑ j ∈ L, Nat.card W * suc j := by rw [← hsums, Finset.mul_sum]
      _ ≤ ∑ j ∈ L, cnt j * score j₀ := Finset.sum_le_sum fun j hj => hterm ⟨j, hj⟩
      _ = _ := by rw [← Finset.sum_mul, hsumc]
  exact ⟨P j₀, Q j₀, (numerics j₀).1, Nat.le_of_mul_le_mul_left hall Nat.card_pos⟩

private abbrev LowerVec (n : ℕ) := Fin n → ZMod 2

private noncomputable def lower_run {h : ℕ} {W : Type*} (q : Fin h → W → ZMod 2) (w : W) : ℕ :=
  (List.finRange h).foldl (fun z i => 2*z + (if q i w = 0 then 0 else 1)) 0

private theorem lower_fold_injective {I : Type*} (s : List I) (u v : I → ZMod 2) (a b : ℕ)
    (he : s.foldl (fun z i => 2*z + (if u i = 0 then 0 else 1)) a =
      s.foldl (fun z i => 2*z + (if v i = 0 then 0 else 1)) b) :
    a = b ∧ ∀ i ∈ s, u i = v i := by
  induction s generalizing a b with
  | nil => exact ⟨he, by simp⟩
  | cons i s ih =>
    simp only [List.foldl_cons] at he
    obtain ⟨he', ht⟩ := ih _ _ he
    have h01 (x : ZMod 2) : x = 0 ∨ x = 1 := by
      change x = (0 : Fin 2) ∨ x = (1 : Fin 2)
      by_cases hx : x = (0 : Fin 2)
      · exact Or.inl hx
      · exact Or.inr (Fin.eq_one_of_ne_zero x hx)
    have hab : a = b ∧ u i = v i := by
      rcases h01 (u i) with hu | hu <;> rcases h01 (v i) with hv | hv <;>
        simp [hu, hv] at he' ⊢ <;> omega
    exact ⟨hab.1, fun j hj => (List.mem_cons.mp hj).elim (fun e => e ▸ hab.2) (ht j)⟩

private theorem lower_compl_dim {n : ℕ} {S T : Submodule (ZMod 2) (LowerVec n)}
    (e : (S × T) ≃ₗ[ZMod 2] LowerVec n) :
    Module.finrank (ZMod 2) T = n - Module.finrank (ZMod 2) S := by
  have h := e.finrank_eq
  have hn : Module.finrank (ZMod 2) (LowerVec n) = n := by
    simp [LowerVec]
  rw [Module.finrank_prod, hn] at h
  omega

private theorem lower (l r m h : ℕ)
    (B : LowerVec l →ₗ[ZMod 2] (LowerVec r →ₗ[ZMod 2] LowerVec m))
    (P : Submodule (ZMod 2) (LowerVec l)) (Q : Submodule (ZMod 2) (LowerVec r)) :
    let cost := (l - Module.finrank (ZMod 2) P) + (r - Module.finrank (ZMod 2) Q)
    cost ≤ h → ∃ (q : Fin h → (LowerVec l × LowerVec r) →ₗ[ZMod 2] ZMod 2)
      (A : ℕ → (LowerVec l × LowerVec r) →ₗ[ZMod 2] LowerVec m) (c : ℕ → LowerVec m),
      (∀ i, (∀ y : LowerVec r, q i (0,y) = 0) ∨ (∀ x : LowerVec l, q i (x,0) = 0)) ∧
      (∀ w : LowerVec l × LowerVec r, (∀ i, q i w = 0) ↔ w.1 ∈ P ∧ w.2 ∈ Q) ∧
      Nat.card {w : LowerVec l × LowerVec r //
        B w.1 w.2 = A (lower_run (fun i => q i) w) w + c (lower_run (fun i => q i) w)} =
        2^cost * Nat.card {w : LowerVec l × LowerVec r // w.1 ∈ P ∧ w.2 ∈ Q ∧ B w.1 w.2 = 0} := by
  classical
  dsimp only
  intro hh
  let F := ZMod 2
  let X := LowerVec l
  let Y := LowerVec r
  let Z := LowerVec m
  let W := X × Y
  obtain ⟨U, hU⟩ := P.exists_isCompl
  obtain ⟨V, hV⟩ := Q.exists_isCompl
  let ex := P.prodEquivOfIsCompl U hU
  let ey := Q.prodEquivOfIsCompl V hV
  let a := Module.finrank F U
  let b := Module.finrank F V
  have ha : a = l - Module.finrank F P := lower_compl_dim ex
  have hb : b = r - Module.finrank F Q := lower_compl_dim ey
  change _ + _ ≤ h at hh
  rw [← ha, ← hb] at hh ⊢
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hh
  -- The transcript consists of the two complement coordinate vectors, padded with zeros.
  let bx := Module.finBasis F U
  let by' := Module.finBasis F V
  let sx : X →ₗ[F] U := (LinearMap.snd F P U).comp ex.symm.toLinearMap
  let sy : Y →ₗ[F] V := (LinearMap.snd F Q V).comp ey.symm.toLinearMap
  let fx : Fin a → W →ₗ[F] F := fun i => (bx.coord i).comp (sx.comp (LinearMap.fst F X Y))
  let fy : Fin b → W →ₗ[F] F := fun i => (by'.coord i).comp (sy.comp (LinearMap.snd F X Y))
  let q : Fin (a + b + t) → W →ₗ[F] F := Fin.addCases (Fin.addCases fx fy) (fun _ => 0)
  have hfx (i : Fin a) (w : W) : fx i w = bx.coord i (sx w.1) := rfl
  have hfy (i : Fin b) (w : W) : fy i w = by'.coord i (sy w.2) := rfl
  have hsx (p : P) (u : U) : sx ((p : X) + (u : X)) = u :=
    congrArg Prod.snd (ex.symm_apply_apply (p,u))
  have hsy (p : Q) (v : V) : sy ((p : Y) + (v : Y)) = v :=
    congrArg Prod.snd (ey.symm_apply_apply (p,v))
  have hsx' (u : U) : sx (u : X) = u := by simpa using hsx 0 u
  have hsy' (v : V) : sy (v : Y) = v := by simpa using hsy 0 v
  have htag_eq (w w' : W) (he : ∀ i, q i w = q i w') :
      lower_run (fun i => q i) w = lower_run (fun i => q i) w' := by
    unfold lower_run
    simp only [he]
  let tag : U × V → ℕ := fun uv => lower_run (fun i => q i) ((uv.1 : X), (uv.2 : Y))
  have htag_inj : Function.Injective tag := by
    intro uv uv' he
    have hbits := (lower_fold_injective (List.finRange (a + b + t))
      (fun i => q i ((uv.1 : X), (uv.2 : Y)))
      (fun i => q i ((uv'.1 : X), (uv'.2 : Y))) 0 0 he).2
    apply Prod.ext
    · apply bx.ext_elem
      intro i
      have hh := hbits ((i.castAdd b).castAdd t) (by simp)
      simpa [q, hfx, hsx', ← Module.Basis.coord_apply] using hh
    · apply by'.ext_elem
      intro i
      have hh := hbits ((i.natAdd a).castAdd t) (by simp)
      simpa [q, hfy, hsy', ← Module.Basis.coord_apply] using hh
  -- A leaf is labeled by the offsets in the two complementary subspaces.
  let decode := Function.invFun tag
  have hdecode (uv : U × V) : decode (tag uv) = uv := Function.leftInverse_invFun htag_inj uv
  let A : ℕ → W →ₗ[F] Z := fun z =>
    (B (decode z).1).comp (LinearMap.snd F X Y) +
    (B.flip ((decode z).2 : Y)).comp (LinearMap.fst F X Y)
  let c : ℕ → Z := fun z => -B (decode z).1 (decode z).2
  refine ⟨q, A, c, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => Fin.addCases
      (fun _ => Or.inl (by intro y; simp [q, hfx]))
      (fun _ => Or.inr (by intro x; simp [q, hfy])) j)
      (fun _ => Or.inl (by intro y; simp [q])) i
  · intro w
    have hpx : sx w.1 = 0 ↔ w.1 ∈ P :=
      Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero P U hU
    have hpy : sy w.2 = 0 ↔ w.2 ∈ Q :=
      Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero Q V hV
    rw [← hpx, ← hpy, ← bx.forall_coord_eq_zero_iff, ← by'.forall_coord_eq_zero_iff]
    constructor
    · intro e
      exact ⟨fun i => by simpa [q, hfx] using e ((i.castAdd b).castAdd t),
        fun i => by simpa [q, hfy] using e ((i.natAdd a).castAdd t)⟩
    · rintro ⟨eu, ev⟩ i
      refine Fin.addCases (fun j => Fin.addCases
        (fun jx => by simpa [q, hfx] using eu jx)
        (fun jy => by simpa [q, hfy] using ev jy) j)
        (fun _ => by simp [q]) i
  · have htranslate (p : P) (s : Q) (u : U) (v : V) :
      let w : W := ((p : X) + (u : X), (s : Y) + (v : Y))
      B w.1 w.2 = A (lower_run (fun i => q i) w) w + c (lower_run (fun i => q i) w) ↔
        B (p : X) (s : Y) = 0 := by
      let w : W := ((p : X) + (u : X), (s : Y) + (v : Y))
      change B w.1 w.2 = A (lower_run (fun i => q i) w) w + c (lower_run (fun i => q i) w) ↔ _
      have hw : lower_run (fun i => q i) w = tag (u,v) := by
        apply htag_eq
        intro i
        refine Fin.addCases (fun j => Fin.addCases
          (fun _ => by simp [q, w, hfx, hsx, hsx'])
          (fun _ => by simp [q, w, hfy, hsy, hsy']) j)
          (fun _ => by simp [q]) i
      rw [hw]
      simp only [A, c, hdecode, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.flip_apply, w]
      let z₀ := B (u : X) ((s : Y) + (v : Y)) +
        B ((p : X) + (u : X)) (v : Y) + -B (u : X) (v : Y)
      change B ((p : X) + (u : X)) ((s : Y) + (v : Y)) = z₀ ↔ _
      have expand : B ((p : X) + (u : X)) ((s : Y) + (v : Y)) =
          B (p : X) (s : Y) + z₀ := by
        simp only [z₀, map_add, LinearMap.add_apply]
        abel
      rw [expand]
      exact ⟨fun eq => add_right_cancel (eq.trans (zero_add z₀).symm),
        fun eq => by rw [eq, zero_add]⟩
    -- The accepted inputs are exactly a product of the rectangular zeros and the offsets.
    let E : ((P × Q) × (U × V)) ≃ W :=
      (Equiv.prodProdProdComm P Q U V).trans (Equiv.prodCongr ex.toEquiv ey.toEquiv)
    have e₁ : {w : (P × Q) × (U × V) // B (w.1.1 : X) (w.1.2 : Y) = 0} ≃
        {w : W // B w.1 w.2 = A (lower_run (fun i => q i) w) w + c (lower_run (fun i => q i) w)} :=
      E.subtypeEquiv fun ⟨⟨p,s⟩,⟨u,v⟩⟩ => (htranslate p s u v).symm
    have eprod : {w : (P × Q) × (U × V) // B (w.1.1 : X) (w.1.2 : Y) = 0} ≃
        {w : P × Q // B (w.1 : X) (w.2 : Y) = 0} × (U × V) :=
      Equiv.prodSubtypeFstEquivSubtypeProd (p := fun w : P × Q => B (w.1 : X) (w.2 : Y) = 0)
    let e₀ : {w : P × Q // B (w.1 : X) (w.2 : Y) = 0} ≃
        {w : W // w.1 ∈ P ∧ w.2 ∈ Q ∧ B w.1 w.2 = 0} :=
      { toFun := fun w => ⟨((w.1.1 : X), (w.1.2 : Y)), w.1.1.2, w.1.2.2, w.2⟩
        invFun := fun w => ⟨(⟨w.1.1, w.2.1⟩, ⟨w.1.2, w.2.2.1⟩), w.2.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hc : Nat.card (U × V) = 2^(a + b) := by
      rw [Module.natCard_eq_pow_finrank (K := F), Module.finrank_prod]
      simp [F, a, b]
    rw [← Nat.card_congr e₁, Nat.card_congr eprod,
      Nat.card_prod, Nat.card_congr e₀, hc, Nat.mul_comm]

end PEqualNP.Outside.L_lib_972_aux

theorem PEqualNP.Outside.L_lib_972 :
  ∀ l r m h : ℕ,
    let F := ZMod 2
    let X := Fin l → F
    let Y := Fin r → F
    let Z := Fin m → F
    let W := X × Y
    ∀ B : X →ₗ[F] (Y →ₗ[F] Z),
    let run := fun (ask : Fin h → ℕ → W →ₗ[F] F) (w : W) =>
      (List.finRange h).foldl (fun z i => 2*z + (if ask i z w = 0 then 0 else 1)) (0 : ℕ)
    (∀ k : ℕ, (∃ (ask : Fin h → ℕ → W →ₗ[F] F) (A : ℕ → W →ₗ[F] Z) (c : ℕ → Z),
        k ≤ Nat.card {w : W // B w.1 w.2 = A (run ask w) w + c (run ask w)}) ↔
      ∃ (P : Submodule F X) (Q : Submodule F Y),
        let cost := (l - Module.finrank F P) + (r - Module.finrank F Q)
        cost ≤ h ∧ k ≤ 2^cost * Nat.card {w : W // w.1 ∈ P ∧ w.2 ∈ Q ∧ B w.1 w.2 = 0}) ∧
    (∀ (P : Submodule F X) (Q : Submodule F Y),
      let cost := (l - Module.finrank F P) + (r - Module.finrank F Q)
      cost ≤ h → ∃ (q : Fin h → W →ₗ[F] F) (A : ℕ → W →ₗ[F] Z) (c : ℕ → Z),
        (∀ i, (∀ y : Y, q i (0,y) = 0) ∨ (∀ x : X, q i (x,0) = 0)) ∧
        (∀ w : W, (∀ i, q i w = 0) ↔ w.1 ∈ P ∧ w.2 ∈ Q) ∧
        Nat.card {w : W // B w.1 w.2 = A (run (fun i _ => q i) w) w + c (run (fun i _ => q i) w)} =
          2^cost * Nat.card {w : W // w.1 ∈ P ∧ w.2 ∈ Q ∧ B w.1 w.2 = 0}) := by
  intro l r m h F X Y Z W B run
  constructor
  · intro k
    constructor
    · rintro ⟨ask, A, c, hk⟩
      obtain ⟨P, Q, hcost, hscore⟩ := PEqualNP.Outside.L_lib_972_aux.forwardOptimizer l r m h B
        (fun S o a d => ⟨PEqualNP.Outside.L_lib_972_aux.leafBound B S o a d,
          PEqualNP.Outside.L_lib_972_aux.cardLeaf S⟩) ask A c
      exact ⟨P, Q, hcost, hk.trans hscore⟩
    · rintro ⟨P, Q, hc, hk⟩
      obtain ⟨q, A, c, _, _, he⟩ := PEqualNP.Outside.L_lib_972_aux.lower l r m h B P Q hc
      exact ⟨fun i _ => q i, A, c, he.symm ▸ hk⟩
  · exact PEqualNP.Outside.L_lib_972_aux.lower l r m h B
