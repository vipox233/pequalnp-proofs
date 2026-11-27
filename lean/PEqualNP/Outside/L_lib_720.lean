import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_720_aux

private abbrev F := ZMod 2

private lemma zmod2_out_eq_iff (xj aj xu au xv av dj du dv : F) :
    ((xj + dj) + (1 + (xu + du)) * (xv + dv) - (xj + (1 + xu) * xv) =
      (aj + dj) + (1 + (au + du)) * (av + dv) - (aj + (1 + au) * av)) ↔
    (xu + au) * dv + (xv + av) * du = 0 := by
  revert xj aj xu au xv av dj du dv; decide

private lemma zmod2_add_self (x : F) : x + x = 0 := by
  revert x; decide

private lemma zmod2_add_cancel (x y : F) : x + y + y = x := by
  revert x y; decide

private lemma zmod2_eq_zero_or_one (x : F) : x = 0 ∨ x = 1 := by
  revert x; decide

private lemma zmod2_eq_of_add_eq_zero {x y : F} (h : x + y = 0) : x = y := by
  revert x y h; decide

private lemma zmod2_bilinear_zero_iff {s : ℕ} (cu cv : Fin s → F) (yu yv : F) :
    (∀ p : Fin s, yu * cv p + yv * cu p = 0) ↔
      ((cu = cv ∧ cu ≠ 0 → yu = yv) ∧
       (cu ≠ cv → (cv ≠ 0 → yu = 0) ∧ (cu ≠ 0 → yv = 0))) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rintro ⟨heq, hne⟩
      have hex : ∃ p : Fin s, cu p ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hne (funext hall)
      rcases hex with ⟨p, hp⟩
      have h1 := h p
      rw [← heq] at h1
      have hcup : cu p = 1 := by
        rcases zmod2_eq_zero_or_one (cu p) with h0 | h1'
        · exact absurd h0 hp
        · exact h1'
      rw [hcup, mul_one, mul_one] at h1
      exact zmod2_eq_of_add_eq_zero h1
    · intro hne
      have hneq_ex : ∃ p : Fin s, cu p ≠ cv p := by
        by_contra hall
        push Not at hall
        exact hne (funext hall)
      constructor
      · intro hcv
        have hexv : ∃ p : Fin s, cv p ≠ 0 := by
          by_contra hall
          push Not at hall
          exact hcv (funext hall)
        rcases hexv with ⟨p1, hp1⟩
        rcases hneq_ex with ⟨p2, hp2⟩
        have e1 := h p1
        have e2 := h p2
        have hstep : ∀ a b c1 c2 d1 d2 : F,
            c2 ≠ 0 → d1 ≠ d2 → a * c2 + b * c1 = 0 → a * d2 + b * d1 = 0 → a = 0 := by decide
        exact hstep yu yv (cu p1) (cv p1) (cu p2) (cv p2) hp1 hp2 e1 e2
      · intro hcu
        have hexu : ∃ p : Fin s, cu p ≠ 0 := by
          by_contra hall
          push Not at hall
          exact hcu (funext hall)
        rcases hexu with ⟨p1, hp1⟩
        rcases hneq_ex with ⟨p2, hp2⟩
        have e1 := h p1
        have e2 := h p2
        have hstep : ∀ a b c1 c2 d1 d2 : F,
            c1 ≠ 0 → d1 ≠ d2 → a * c2 + b * c1 = 0 → a * d2 + b * d1 = 0 → b = 0 := by decide
        exact hstep yu yv (cu p1) (cv p1) (cu p2) (cv p2) hp1 hp2 e1 e2
  · rintro ⟨h1, h2⟩ p
    by_cases heq : cu = cv
    · by_cases h0 : cu = 0
      · have hcu : cu p = 0 := congrFun h0 p
        have hcv : cv p = 0 := by rw [← heq]; exact hcu
        simp [hcu, hcv]
      · have hy : yu = yv := h1 ⟨heq, h0⟩
        rw [heq, hy]
        exact zmod2_add_self _
    · rcases h2 heq with ⟨hu, hv⟩
      have hterm1 : yu * cv p = 0 := by
        by_cases hcv : cv = 0
        · simp [hcv]
        · rw [hu hcv, zero_mul]
      have hterm2 : yv * cu p = 0 := by
        by_cases hcu : cu = 0
        · simp [hcu]
        · rw [hv hcu, zero_mul]
      rw [hterm1, hterm2, add_zero]

private lemma eqvGen_const {k : ℕ} {edge : Fin k → Fin k → Prop} {y : Fin k → F}
    (he : ∀ u v, edge u v → y u = y v) {u v : Fin k} (h : Relation.EqvGen edge u v) :
    y u = y v := by
  induction h with
  | rel a b hab => exact he a b hab
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

private noncomputable def repOf {k : ℕ} (edge : Fin k → Fin k → Prop) (z : Fin k) : Fin k :=
  let joined := fun u v => @decide (Relation.EqvGen edge u v) (Classical.propDecidable _)
  let cls : Finset (Fin k) := Finset.univ.filter (fun w => joined z w = true)
  cls.min' ⟨z, by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ z, ?_⟩
    exact @decide_eq_true _ (Classical.propDecidable _) (Relation.EqvGen.refl z)⟩

private lemma repOf_joined {k : ℕ} (edge : Fin k → Fin k → Prop) (z : Fin k) :
    Relation.EqvGen edge (repOf edge z) z := by
  let joined := fun u v => @decide (Relation.EqvGen edge u v) (Classical.propDecidable _)
  let cls : Finset (Fin k) := Finset.univ.filter (fun w => joined z w = true)
  have hmem : repOf edge z ∈ cls := Finset.min'_mem cls _
  have hj : joined z (repOf edge z) = true := (Finset.mem_filter.1 hmem).2
  have hrel : Relation.EqvGen edge z (repOf edge z) :=
    @of_decide_eq_true _ (Classical.propDecidable _) hj
  exact Relation.EqvGen.symm _ _ hrel

private lemma repOf_le {k : ℕ} (edge : Fin k → Fin k → Prop) {z w : Fin k}
    (h : Relation.EqvGen edge (repOf edge z) w) :
    (repOf edge z).val ≤ w.val := by
  let joined := fun u v => @decide (Relation.EqvGen edge u v) (Classical.propDecidable _)
  let cls : Finset (Fin k) := Finset.univ.filter (fun w => joined z w = true)
  have hzw : Relation.EqvGen edge z w :=
    Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (repOf_joined edge z)) h
  have hw : w ∈ cls := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ w, ?_⟩
    exact @decide_eq_true _ (Classical.propDecidable _) hzw
  exact Finset.min'_le cls w hw

private lemma repOf_eq_of_eqvGen {k : ℕ} (edge : Fin k → Fin k → Prop) {u v : Fin k}
    (h : Relation.EqvGen edge u v) :
    repOf edge u = repOf edge v := by
  have h1 : (repOf edge u).val ≤ (repOf edge v).val :=
    repOf_le edge (Relation.EqvGen.trans _ _ _ (repOf_joined edge u)
      (Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.symm _ _ (repOf_joined edge v))))
  have h2 : (repOf edge v).val ≤ (repOf edge u).val :=
    repOf_le edge (Relation.EqvGen.trans _ _ _ (repOf_joined edge v)
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h)
        (Relation.EqvGen.symm _ _ (repOf_joined edge u))))
  exact Fin.ext (le_antisymm h1 h2)

end PEqualNP.Outside.L_lib_720_aux

theorem PEqualNP.Outside.L_lib_720 :
∀ (k s : Nat) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun t : Nat => (⟨t%k, Nat.mod_lt _ hk⟩ : Fin k)
  ∀ (D : Fin s → W) (test : Finset (Fin k)),
  let color := fun (j : Fin k) (p : Fin s) => D p j
  let chi := fun (x : W) (j : Fin k) => x j + (1+x (ix (j.val+1))) * x (ix (j.val+2))
  let out := fun (x : W) (p : Fin s) (j : Fin k) => chi (x+D p) j - chi x j
  let edge := fun (u v : Fin k) => ∃ j ∈ test,
    u = ix (j.val+1) ∧ v = ix (j.val+2) ∧ color u = color v ∧ color u ≠ 0
  let joined := fun u v => @decide (Relation.EqvGen edge u v) (Classical.propDecidable _)
  let pinned := fun (z : Fin k) => ∃ j ∈ test,
    let u := ix (j.val+1)
    let v := ix (j.val+2)
    color u ≠ color v ∧ ((z = u ∧ color v ≠ 0) ∨ (z = v ∧ color u ≠ 0))
  let free := (Finset.univ : Finset (Fin k)).filter (fun i =>
    (∀ j, joined i j = true → i.val ≤ j.val) ∧ (∀ j, joined i j = true → ¬pinned j))
  ∀ a : W,
    (∀ x : W, ((∀ p, ∀ j ∈ test, out x p j = out a p j) ↔
      ∃ amp : Fin k → F, ∀ z : Fin k, x z = a z +
        ∑ i ∈ free, (if joined i z = true then amp i else 0))) ∧
    ((Finset.univ : Finset W).filter
      (fun x => ∀ p, ∀ j ∈ test, out x p j = out a p j)).card = 2^free.card := by
  intro k s hk F W ix D test color chi out edge joined pinned free a
  have hjoined_iff : ∀ u v : Fin k, joined u v = true ↔ Relation.EqvGen edge u v := fun u v =>
    ⟨fun h => @of_decide_eq_true _ (Classical.propDecidable _) h,
     fun h => @decide_eq_true _ (Classical.propDecidable _) h⟩
  have hsum_collapse : ∀ (amp : Fin k → F) (z : Fin k),
      (∑ i ∈ free, (if joined i z = true then amp i else 0)) =
        if PEqualNP.Outside.L_lib_720_aux.repOf edge z ∈ free then
          amp (PEqualNP.Outside.L_lib_720_aux.repOf edge z)
        else 0 := by
    intro amp z
    let r := PEqualNP.Outside.L_lib_720_aux.repOf edge z
    have huniq : ∀ i ∈ free, joined i z = true ↔ i = r := by
      intro i hi
      have hmin := (Finset.mem_filter.1 hi).2.1
      constructor
      · intro hiz
        have hrel_iz : Relation.EqvGen edge i z := (hjoined_iff i z).1 hiz
        have hrel_ir : Relation.EqvGen edge i r :=
          Relation.EqvGen.trans _ _ _ hrel_iz
            (Relation.EqvGen.symm _ _ (PEqualNP.Outside.L_lib_720_aux.repOf_joined edge z))
        have hle1 : i.val ≤ r.val := hmin r ((hjoined_iff i r).2 hrel_ir)
        have hle2 : r.val ≤ i.val :=
          PEqualNP.Outside.L_lib_720_aux.repOf_le edge (Relation.EqvGen.symm _ _ hrel_ir)
        exact Fin.ext (le_antisymm hle1 hle2)
      · rintro rfl
        exact (hjoined_iff r z).2 (PEqualNP.Outside.L_lib_720_aux.repOf_joined edge z)
    by_cases hr : r ∈ free
    · simp only [r, hr, ↓reduceIte]
      rw [Finset.sum_eq_single r]
      · simp [(huniq r hr).2 rfl]; rfl
      · intro i hi hne
        have hnf : joined i z ≠ true := fun h => hne ((huniq i hi).1 h)
        simp [hnf]
      · intro h; exact absurd hr h
    · simp only [r, hr, ↓reduceIte]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hnf : joined i z ≠ true := fun h => hr ((huniq i hi).1 h ▸ hi)
      simp [hnf]
  have hout_char : ∀ x : W,
      (∀ p, ∀ j ∈ test, out x p j = out a p j) ↔
        ((∀ u v, edge u v → x u + a u = x v + a v) ∧ (∀ z, pinned z → x z + a z = 0)) := by
    intro x
    have hstep : ∀ j ∈ test,
        (∀ p : Fin s, out x p j = out a p j) ↔
          ((color (ix (j.val + 1)) = color (ix (j.val + 2)) ∧ color (ix (j.val + 1)) ≠ 0 →
              x (ix (j.val + 1)) + a (ix (j.val + 1)) = x (ix (j.val + 2)) + a (ix (j.val + 2))) ∧
           (color (ix (j.val + 1)) ≠ color (ix (j.val + 2)) →
              (color (ix (j.val + 2)) ≠ 0 → x (ix (j.val + 1)) + a (ix (j.val + 1)) = 0) ∧
              (color (ix (j.val + 1)) ≠ 0 → x (ix (j.val + 2)) + a (ix (j.val + 2)) = 0))) := by
      intro j _
      have heq : (∀ p : Fin s, out x p j = out a p j) ↔
          ∀ p : Fin s, (x (ix (j.val + 1)) + a (ix (j.val + 1))) * color (ix (j.val + 2)) p +
            (x (ix (j.val + 2)) + a (ix (j.val + 2))) * color (ix (j.val + 1)) p = 0 := by
        refine forall_congr' fun p => ?_
        exact PEqualNP.Outside.L_lib_720_aux.zmod2_out_eq_iff _ _ _ _ _ _ _ _ _
      rw [heq]
      exact PEqualNP.Outside.L_lib_720_aux.zmod2_bilinear_zero_iff
        (color (ix (j.val + 1))) (color (ix (j.val + 2))) _ _
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · rintro u v ⟨j, hj, rfl, rfl, hceq, hcne⟩
        exact ((hstep j hj).1 (fun p => h p j hj)).1 ⟨hceq, hcne⟩
      · rintro z ⟨j, hj, hcne, ⟨rfl, hcv⟩ | ⟨rfl, hcu⟩⟩
        · exact (((hstep j hj).1 (fun p => h p j hj)).2 hcne).1 hcv
        · exact (((hstep j hj).1 (fun p => h p j hj)).2 hcne).2 hcu
    · rintro ⟨hedge, hpin⟩ p j hj
      have h1 : ∀ p' : Fin s, out x p' j = out a p' j := by
        rw [hstep j hj]
        refine ⟨?_, ?_⟩
        · rintro ⟨hceq, hcne⟩
          exact hedge _ _ ⟨j, hj, rfl, rfl, hceq, hcne⟩
        · intro hcne
          refine ⟨fun hcv => hpin _ ⟨j, hj, hcne, Or.inl ⟨rfl, hcv⟩⟩,
            fun hcu => hpin _ ⟨j, hj, hcne, Or.inr ⟨rfl, hcu⟩⟩⟩
      exact h1 p
  have hpart1 : ∀ x : W,
      (∀ p, ∀ j ∈ test, out x p j = out a p j) ↔
        ∃ amp : Fin k → F, ∀ z : Fin k, x z = a z +
          ∑ i ∈ free, (if joined i z = true then amp i else 0) := by
    intro x
    rw [hout_char x]
    constructor
    · rintro ⟨hedge, hpin⟩
      refine ⟨fun z => x z + a z, fun z => ?_⟩
      rw [hsum_collapse]
      let r := PEqualNP.Outside.L_lib_720_aux.repOf edge z
      by_cases hr : r ∈ free
      · simp only [r, hr, ↓reduceIte]
        have hrel := PEqualNP.Outside.L_lib_720_aux.repOf_joined edge z
        have hy : x r + a r = x z + a z :=
          PEqualNP.Outside.L_lib_720_aux.eqvGen_const hedge hrel
        rw [hy, add_comm (x z) (a z), ← add_assoc, PEqualNP.Outside.L_lib_720_aux.zmod2_add_self,
          zero_add]
      · simp only [r, hr, ↓reduceIte, add_zero]
        have hmin : ∀ j, joined r j = true → r.val ≤ j.val := fun j hj =>
          PEqualNP.Outside.L_lib_720_aux.repOf_le edge ((hjoined_iff r j).1 hj)
        have hhas_pin : ∃ w, Relation.EqvGen edge r w ∧ pinned w := by
          by_contra hno
          push Not at hno
          apply hr
          refine Finset.mem_filter.2 ⟨Finset.mem_univ r, hmin, fun w hw => hno w ((hjoined_iff r w).1 hw)⟩
        rcases hhas_pin with ⟨w, hrw, hpw⟩
        have hzw : Relation.EqvGen edge z w :=
          Relation.EqvGen.trans _ _ _
            (Relation.EqvGen.symm _ _ (PEqualNP.Outside.L_lib_720_aux.repOf_joined edge z)) hrw
        have hyz : x z + a z = x w + a w :=
          PEqualNP.Outside.L_lib_720_aux.eqvGen_const hedge hzw
        rw [hpin w hpw] at hyz
        exact PEqualNP.Outside.L_lib_720_aux.zmod2_eq_of_add_eq_zero hyz
    · rintro ⟨amp, hamp⟩
      have hy : ∀ z : Fin k, x z + a z =
          if PEqualNP.Outside.L_lib_720_aux.repOf edge z ∈ free then
            amp (PEqualNP.Outside.L_lib_720_aux.repOf edge z)
          else 0 := by
        intro z
        have hz := hamp z
        rw [hsum_collapse] at hz
        rw [hz, add_comm (a z), add_assoc, PEqualNP.Outside.L_lib_720_aux.zmod2_add_self, add_zero]
      refine ⟨?_, ?_⟩
      · intro u v huv
        rw [hy u, hy v, PEqualNP.Outside.L_lib_720_aux.repOf_eq_of_eqvGen edge
          (Relation.EqvGen.rel u v huv)]
      · intro z hz
        rw [hy z]
        have hnr : PEqualNP.Outside.L_lib_720_aux.repOf edge z ∉ free := by
          intro hmem
          have hnp := (Finset.mem_filter.1 hmem).2.2 z
            ((hjoined_iff _ z).2 (PEqualNP.Outside.L_lib_720_aux.repOf_joined edge z))
          exact hnp hz
        simp [hnr]
  refine ⟨hpart1, ?_⟩
  rw [← Finset.card_powerset]
  refine Finset.card_bij (fun x _ => free.filter (fun i => x i + a i = 1)) ?_ ?_ ?_
  · intro x _
    exact Finset.mem_powerset.2 (Finset.filter_subset _ _)
  · intro x1 hx1 x2 hx2 heq
    rcases (hpart1 x1).1 (Finset.mem_filter.1 hx1).2 with ⟨amp1, hamp1⟩
    rcases (hpart1 x2).1 (Finset.mem_filter.1 hx2).2 with ⟨amp2, hamp2⟩
    have hrep_free : ∀ i ∈ free, PEqualNP.Outside.L_lib_720_aux.repOf edge i = i := by
      intro i hi
      have hmin := (Finset.mem_filter.1 hi).2.1
      have h1 : (PEqualNP.Outside.L_lib_720_aux.repOf edge i).val ≤ i.val :=
        PEqualNP.Outside.L_lib_720_aux.repOf_le edge (PEqualNP.Outside.L_lib_720_aux.repOf_joined edge i)
      have h2 : i.val ≤ (PEqualNP.Outside.L_lib_720_aux.repOf edge i).val :=
        hmin _ ((hjoined_iff _ _).2 (Relation.EqvGen.symm _ _
          (PEqualNP.Outside.L_lib_720_aux.repOf_joined edge i)))
      exact Fin.ext (le_antisymm h1 h2)
    have hamp_eq : ∀ i ∈ free, amp1 i = amp2 i := by
      intro i hi
      have h1 : x1 i + a i = amp1 i := by
        have hx := hamp1 i
        rw [hsum_collapse, hrep_free i hi] at hx
        simp only [hi, ↓reduceIte] at hx
        rw [hx, add_comm (a i), add_assoc, PEqualNP.Outside.L_lib_720_aux.zmod2_add_self, add_zero]
      have h2 : x2 i + a i = amp2 i := by
        have hx := hamp2 i
        rw [hsum_collapse, hrep_free i hi] at hx
        simp only [hi, ↓reduceIte] at hx
        rw [hx, add_comm (a i), add_assoc, PEqualNP.Outside.L_lib_720_aux.zmod2_add_self, add_zero]
      have hmem : i ∈ free.filter (fun j => x1 j + a j = 1) ↔
          i ∈ free.filter (fun j => x2 j + a j = 1) := by rw [heq]
      simp only [Finset.mem_filter, hi, true_and, h1, h2] at hmem
      have hz : ∀ p q : F, (p = 1 ↔ q = 1) → p = q := by decide
      exact hz (amp1 i) (amp2 i) hmem
    funext z
    rw [hamp1 z, hamp2 z, hsum_collapse, hsum_collapse]
    by_cases hr : PEqualNP.Outside.L_lib_720_aux.repOf edge z ∈ free
    · simp only [hr, ↓reduceIte, hamp_eq _ hr]
    · simp only [hr, ↓reduceIte]
  · intro T hT
    have hTf : T ⊆ free := Finset.mem_powerset.1 hT
    let amp : Fin k → F := fun i => if i ∈ T then 1 else 0
    let x : W := fun z => a z + ∑ i ∈ free, (if joined i z = true then amp i else 0)
    have hx_mem : x ∈ (Finset.univ : Finset W).filter
        (fun x => ∀ p, ∀ j ∈ test, out x p j = out a p j) := by
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, (hpart1 x).2 ⟨amp, fun _ => rfl⟩⟩
    refine ⟨x, hx_mem, ?_⟩
    have hrep_free : ∀ i ∈ free, PEqualNP.Outside.L_lib_720_aux.repOf edge i = i := by
      intro i hi
      have hmin := (Finset.mem_filter.1 hi).2.1
      have h1 : (PEqualNP.Outside.L_lib_720_aux.repOf edge i).val ≤ i.val :=
        PEqualNP.Outside.L_lib_720_aux.repOf_le edge (PEqualNP.Outside.L_lib_720_aux.repOf_joined edge i)
      have h2 : i.val ≤ (PEqualNP.Outside.L_lib_720_aux.repOf edge i).val :=
        hmin _ ((hjoined_iff _ _).2 (Relation.EqvGen.symm _ _
          (PEqualNP.Outside.L_lib_720_aux.repOf_joined edge i)))
      exact Fin.ext (le_antisymm h1 h2)
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi, hx1⟩
      have hxa : x i + a i = amp i := by
        dsimp only [x]
        rw [hsum_collapse, hrep_free i hi]
        simp only [hi, ↓reduceIte]
        rw [add_comm (a i), add_assoc, PEqualNP.Outside.L_lib_720_aux.zmod2_add_self, add_zero]
      rw [hxa] at hx1
      by_contra hni
      simp [amp, hni] at hx1
    · intro hiT
      have hi : i ∈ free := hTf hiT
      refine ⟨hi, ?_⟩
      dsimp only [x]
      rw [hsum_collapse, hrep_free i hi]
      simp only [hi, ↓reduceIte]
      rw [add_comm (a i), add_assoc, PEqualNP.Outside.L_lib_720_aux.zmod2_add_self, add_zero]
      simp [amp, hiT]
