import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_263_aux

open scoped BigOperators
open PEqualNP.ProofComplexity

def bx (b : Bool) : ZMod 2 := if b then 1 else 0

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

lemma bx_xor (a b : Bool) : bx (a ^^ b) = bx a + bx b := by
  cases a <;> cases b <;> decide

lemma zmod2_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

lemma bx_decide_eq_one (x : ZMod 2) : bx (decide (x = 1)) = x := by
  revert x; decide

lemma odd_iff_zmod2_eq_one (k : ℕ) : Odd k ↔ (k : ZMod 2) = 1 := by
  rw [Nat.odd_iff]
  have h2z : ((2 : ℕ) : ZMod 2) = 0 := by decide
  have h1 : (k : ZMod 2) = ((k % 2 : ℕ) : ZMod 2) := by
    have hdiv := Nat.div_add_mod k 2
    have h2 := congrArg (fun n : ℕ => (n : ZMod 2)) hdiv
    rw [Nat.cast_add, Nat.cast_mul, h2z, zero_mul, zero_add] at h2
    exact h2.symm
  rw [h1]
  have hlt : k % 2 < 2 := Nat.mod_lt k (by omega)
  interval_cases (k % 2) <;> decide

lemma even_iff_zmod2_eq_zero (k : ℕ) : Even k ↔ (k : ZMod 2) = 0 := by
  rw [Nat.even_iff]
  have h2z : ((2 : ℕ) : ZMod 2) = 0 := by decide
  have h1 : (k : ZMod 2) = ((k % 2 : ℕ) : ZMod 2) := by
    have hdiv := Nat.div_add_mod k 2
    have h2 := congrArg (fun n : ℕ => (n : ZMod 2)) hdiv
    rw [Nat.cast_add, Nat.cast_mul, h2z, zero_mul, zero_add] at h2
    exact h2.symm
  rw [h1]
  have hlt : k % 2 < 2 := Nat.mod_lt k (by omega)
  interval_cases (k % 2) <;> decide

lemma fredholm_zmod2 {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J (ZMod 2)) (rhs : I → ZMod 2)
    (horth : ∀ c : I → ZMod 2, M.transpose.mulVec c = 0 → dotProduct c rhs = 0) :
    ∃ x : J → ZMod 2, M.mulVec x = rhs := by
  classical
  let orth : Submodule (ZMod 2) (I → ZMod 2) :=
    { carrier := {y : I → ZMod 2 | ∀ c ∈ LinearMap.ker M.transpose.mulVecLin, dotProduct c y = 0}
      zero_mem' := fun c _ => dotProduct_zero c, add_mem' := fun {u v} hu hv c hc => by
        rw [dotProduct_add, hu c hc, hv c hc, add_zero]
      smul_mem' := fun a {u} hu c hc => by
        rw [dotProduct_smul, hu c hc, smul_zero] }
  have hle : LinearMap.range M.mulVecLin ≤ orth := by
    rintro y ⟨x, rfl⟩ c hc
    have hMt : M.transpose.mulVec c = 0 := hc
    have hdot : dotProduct c (M.mulVec x) = dotProduct (M.transpose.mulVec c) x := by
      simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    change dotProduct c (M.mulVec x) = 0
    rw [hdot, hMt, zero_dotProduct]
  have horth_dim : Module.finrank (ZMod 2) orth =
      Fintype.card I - Module.finrank (ZMod 2) (LinearMap.ker M.transpose.mulVecLin) := by
    let b := Module.finBasis (ZMod 2) (LinearMap.ker M.transpose.mulVecLin)
    let evalK : (I → ZMod 2) →ₗ[ZMod 2]
        (Fin (Module.finrank (ZMod 2) (LinearMap.ker M.transpose.mulVecLin)) → ZMod 2) :=
      { toFun := fun v j => dotProduct (b j).1 v
        map_add' := fun u v => by ext j; simp [dotProduct_add]
        map_smul' := fun a v => by ext j; simp [dotProduct_smul] }
    have hker_eq : LinearMap.ker evalK = orth := by
      ext v
      constructor
      · intro hv c hc
        have hc_eq : (⟨c, hc⟩ : LinearMap.ker M.transpose.mulVecLin) =
            ∑ j, b.repr ⟨c, hc⟩ j • b j := (b.sum_repr ⟨c, hc⟩).symm
        have hval : c = ∑ j, b.repr ⟨c, hc⟩ j • (b j).1 := by
          have h1 := congrArg Subtype.val hc_eq
          simp only [Submodule.coe_sum, SetLike.val_smul] at h1
          exact h1
        rw [hval, sum_dotProduct]
        refine Finset.sum_eq_zero fun j _ => ?_
        have hvj : dotProduct (b j).1 v = 0 := congrFun hv j
        rw [smul_dotProduct, smul_eq_mul, hvj, mul_zero]
      · intro hv; ext j; exact hv (b j).1 (b j).2
    have hsurj : Module.finrank (ZMod 2) (LinearMap.range evalK) =
        Module.finrank (ZMod 2) (LinearMap.ker M.transpose.mulVecLin) := by
      let B : Matrix I (Fin (Module.finrank (ZMod 2) (LinearMap.ker M.transpose.mulVecLin))) (ZMod 2) :=
        Matrix.of fun i j => (b j).1 i
      have hB_inj : Function.Injective B.mulVecLin := by
        rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
        intro c hc
        have hc' : (∑ j, c j • (b j).1) = 0 := by
          ext i
          have hi := congrFun hc i
          simp only [B, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
            Pi.zero_apply] at hi
          simpa [Finset.sum_apply, mul_comm] using hi
        have hcK : (∑ j, c j • b j) = 0 := by apply Subtype.ext; simpa using hc'
        exact funext (Fintype.linearIndependent_iff.mp b.linearIndependent c hcK)
      have hB_rank : B.rank = Module.finrank (ZMod 2) (LinearMap.ker M.transpose.mulVecLin) := by
        have hr := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
        rw [LinearMap.ker_eq_bot.mpr hB_inj] at hr
        simp at hr
        exact hr
      have hBt : B.transpose.mulVecLin = evalK := by
        apply LinearMap.ext; intro v; ext j
        simp [B, evalK, Matrix.mulVec, dotProduct]
      rw [← hBt]
      change B.transpose.rank = Module.finrank (ZMod 2) (LinearMap.ker M.transpose.mulVecLin)
      rw [Matrix.rank_transpose, hB_rank]
    have hr := LinearMap.finrank_range_add_finrank_ker evalK
    rw [hsurj, hker_eq] at hr
    have hd : Module.finrank (ZMod 2) (I → ZMod 2) = Fintype.card I := by simp
    rw [hd] at hr
    omega
  have hrMt := LinearMap.finrank_range_add_finrank_ker M.transpose.mulVecLin
  have hd : Module.finrank (ZMod 2) (I → ZMod 2) = Fintype.card I := by simp
  rw [hd] at hrMt
  have hrank_eq : Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) =
      Module.finrank (ZMod 2) (LinearMap.range M.transpose.mulVecLin) := by
    change M.rank = M.transpose.rank
    exact (Matrix.rank_transpose M).symm
  have heq : LinearMap.range M.mulVecLin = orth := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    omega
  have hrhs : rhs ∈ LinearMap.range M.mulVecLin := by
    rw [heq]
    intro c hc
    exact horth c hc
  rcases hrhs with ⟨x, hx⟩
  exact ⟨x, hx⟩

def oddSet {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (D : Finset (Fin m)) : Prop :=
  Odd ((D.filter (fun e => sign e = true)).card) ∧
  ∀ v : Fin n, Even ((D.filter (fun e => left e = v)).card +
    (D.filter (fun e => right e = v)).card)

lemma unsat_imp_oddSet {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (H : Finset (Fin m × Bool))
    (hunsat : ¬ ∃ x : Fin n → Bool, ∀ p ∈ H, x (left p.1) = p.2 →
      x (right p.1) = (p.2 ^^ sign p.1)) :
    ∃ D : Finset (Fin m), oddSet left right sign D ∧ 2 * D.card ≤ H.card := by
  classical
  have hHne : H.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    subst hemp
    exact hunsat ⟨fun _ => false, fun _ hp => absurd hp (Finset.notMem_empty _)⟩
  let M : Matrix H (Fin n) (ZMod 2) := Matrix.of fun p v =>
    (if left p.1.1 = v then (1 : ZMod 2) else 0) + (if right p.1.1 = v then 1 else 0)
  let rhs : H → ZMod 2 := fun p => bx (sign p.1.1)
  have hMmul : ∀ (x : Fin n → ZMod 2) (p : H),
      M.mulVec x p = x (left p.1.1) + x (right p.1.1) := by
    intro x p
    simp only [M, Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib]
    have h1 : (∑ v : Fin n, (if left p.1.1 = v then (1 : ZMod 2) else 0) * x v) = x (left p.1.1) := by
      rw [Finset.sum_eq_single (left p.1.1)]
      · simp
      · intro v _ hne; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have h2 : (∑ v : Fin n, (if right p.1.1 = v then (1 : ZMod 2) else 0) * x v) = x (right p.1.1) := by
      rw [Finset.sum_eq_single (right p.1.1)]
      · simp
      · intro v _ hne; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h1, h2]
  let S := LinearMap.ker M.transpose.mulVecLin
  have hzero_dep : ∀ p0 : H, ∃ c : S, c.1 p0 = 0 ∧ dotProduct c.1 rhs = 1 := by
    intro p0
    by_contra hno
    push Not at hno
    let H' := H.erase p0.1
    let M' : Matrix H' (Fin n) (ZMod 2) := Matrix.of fun p v =>
      (if left p.1.1 = v then (1 : ZMod 2) else 0) + (if right p.1.1 = v then 1 else 0)
    let rhs' : H' → ZMod 2 := fun p => bx (sign p.1.1)
    have hfred : ∃ x : Fin n → ZMod 2, M'.mulVec x = rhs' := by
      refine fredholm_zmod2 M' rhs' fun c' hc' => ?_
      let c : H → ZMod 2 := fun p =>
        if hp : p.1 ∈ H' then c' ⟨p.1, hp⟩ else 0
      have hc_ker : c ∈ S := by
        change M.transpose.mulVec c = 0
        ext v
        have hv := congrFun hc' v
        simp only [M, M', Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply,
          Pi.zero_apply] at hv ⊢
        conv_rhs => rw [← hv]
        have hsplit : (∑ p : H, ((if left p.1.1 = v then (1 : ZMod 2) else 0) +
            (if right p.1.1 = v then 1 else 0)) * c p) =
            ∑ p ∈ Finset.univ.filter (fun p : H => p.1 ∈ H'),
              ((if left p.1.1 = v then (1 : ZMod 2) else 0) +
                (if right p.1.1 = v then 1 else 0)) * c p := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : H => p.1 ∈ H')]
          have h0 : (∑ p ∈ Finset.univ.filter (fun p : H => ¬ p.1 ∈ H'),
              ((if left p.1.1 = v then (1 : ZMod 2) else 0) +
                (if right p.1.1 = v then 1 else 0)) * c p) = 0 := by
            refine Finset.sum_eq_zero fun p hp => ?_
            have hnot : ¬ p.1 ∈ H' := (Finset.mem_filter.mp hp).2
            simp [c, hnot]
          rw [h0, add_zero]
        rw [hsplit]
        refine Finset.sum_bij
          (fun p hp => (⟨p.1, (Finset.mem_filter.mp hp).2⟩ : H'))
          (fun _ _ => Finset.mem_univ _)
          (fun p1 _ p2 _ heq => Subtype.ext (congrArg (fun q : H' => q.1) heq))
          (fun q _ => ⟨⟨q.1, Finset.mem_of_mem_erase q.2⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.2⟩, rfl⟩)
          (fun p hp => by
            have hp' : p.1 ∈ H' := (Finset.mem_filter.mp hp).2
            simp [c, hp'])
      have hcp0 : c p0 = 0 := by
        have hnot : ¬ p0.1 ∈ H' := Finset.notMem_erase _ _
        simp [c, hnot]
      have hdot_eq : dotProduct c' rhs' = dotProduct c rhs := by
        simp only [dotProduct, rhs, rhs']
        have hsplit : (∑ p : H, c p * bx (sign p.1.1)) =
            ∑ p ∈ Finset.univ.filter (fun p : H => p.1 ∈ H'), c p * bx (sign p.1.1) := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : H => p.1 ∈ H')]
          have h0 : (∑ p ∈ Finset.univ.filter (fun p : H => ¬ p.1 ∈ H'), c p * bx (sign p.1.1)) = 0 := by
            refine Finset.sum_eq_zero fun p hp => ?_
            have hnot : ¬ p.1 ∈ H' := (Finset.mem_filter.mp hp).2
            simp [c, hnot]
          rw [h0, add_zero]
        rw [hsplit]
        symm
        refine Finset.sum_bij
          (fun p hp => (⟨p.1, (Finset.mem_filter.mp hp).2⟩ : H'))
          (fun _ _ => Finset.mem_univ _)
          (fun p1 _ p2 _ heq => Subtype.ext (congrArg (fun q : H' => q.1) heq))
          (fun q _ => ⟨⟨q.1, Finset.mem_of_mem_erase q.2⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.2⟩, rfl⟩)
          (fun p hp => by
            have hp' : p.1 ∈ H' := (Finset.mem_filter.mp hp).2
            simp [c, hp'])
      rw [hdot_eq]
      have hne1 := hno ⟨c, hc_ker⟩ hcp0
      rcases zmod2_zero_or_one (dotProduct c rhs) with hval | hval
      · exact hval
      · exact absurd hval hne1
    rcases hfred with ⟨x, hx⟩
    let flip : ZMod 2 := if x (left p0.1.1) = bx p0.1.2 then 1 else 0
    let xb : Fin n → Bool := fun v => decide (x v + flip = 1)
    apply hunsat
    refine ⟨xb, fun p hp hleft => ?_⟩
    by_cases hpeq : p = p0.1
    · subst hpeq
      have hxb_eq : bx (xb (left p0.1.1)) = bx p0.1.2 := congrArg bx hleft
      rw [show bx (xb (left p0.1.1)) = x (left p0.1.1) + flip from bx_decide_eq_one _] at hxb_eq
      dsimp only [flip] at hxb_eq
      by_cases he : x (left p0.1.1) = bx p0.1.2
      · simp only [he, ↓reduceIte] at hxb_eq
        have h1 : (1 : ZMod 2) = 0 := by
          have := congrArg (fun z : ZMod 2 => z + bx p0.1.2) hxb_eq
          have h2 : bx p0.1.2 + 1 + bx p0.1.2 = 1 := by
            calc
              bx p0.1.2 + 1 + bx p0.1.2 = 1 + (bx p0.1.2 + bx p0.1.2) := by ring
              _ = 1 := by rw [zmod2_add_self, add_zero]
          rw [h2, zmod2_add_self] at this
          exact this
        exact absurd h1 (by decide)
      · simp only [he, ↓reduceIte, add_zero] at hxb_eq
    · have hpH' : p ∈ H' := Finset.mem_erase.mpr ⟨hpeq, hp⟩
      have hrow := congrFun hx ⟨p, hpH'⟩
      have hrow' : x (left p.1) + x (right p.1) = bx (sign p.1) := by
        simp only [M', rhs', Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul,
          Finset.sum_add_distrib] at hrow
        have h1 : (∑ v : Fin n, (if left p.1 = v then (1 : ZMod 2) else 0) * x v) = x (left p.1) := by
          rw [Finset.sum_eq_single (left p.1)]
          · simp
          · intro v _ hne; simp [Ne.symm hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        have h2 : (∑ v : Fin n, (if right p.1 = v then (1 : ZMod 2) else 0) * x v) = x (right p.1) := by
          rw [Finset.sum_eq_single (right p.1)]
          · simp
          · intro v _ hne; simp [Ne.symm hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [h1, h2] at hrow
        exact hrow
      have hbx_l : bx (xb (left p.1)) = bx p.2 := congrArg bx hleft
      rw [show bx (xb (left p.1)) = x (left p.1) + flip from bx_decide_eq_one _] at hbx_l
      have hbx_r : bx (xb (right p.1)) = bx (p.2 ^^ sign p.1) := by
        rw [show bx (xb (right p.1)) = x (right p.1) + flip from bx_decide_eq_one _,
          bx_xor, ← hbx_l, ← hrow']
        calc
          x (right p.1) + flip = x (right p.1) + flip + (x (left p.1) + x (left p.1)) := by
            rw [zmod2_add_self, add_zero]
          _ = (x (left p.1) + flip) + (x (left p.1) + x (right p.1)) := by ring
      cases h1 : xb (right p.1) <;> cases h2 : (p.2 ^^ sign p.1)
      · rfl
      · rw [h1, h2] at hbx_r; exact absurd hbx_r (by decide)
      · rw [h1, h2] at hbx_r; exact absurd hbx_r (by decide)
      · rfl
  let S_odd : Finset S := Finset.univ.filter (fun c : S => dotProduct c.1 rhs = 1)
  have hSodd_ne : S_odd.Nonempty := by
    rcases hHne with ⟨p0, hp0⟩
    rcases hzero_dep ⟨p0, hp0⟩ with ⟨c, _, hc1⟩
    exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc1⟩⟩
  have hhalf : ∀ p : H, 2 * (S_odd.filter (fun c : S => c.1 p = 1)).card ≤ S_odd.card := by
    intro p
    by_cases hex : ∃ d : S, dotProduct d.1 rhs = 0 ∧ d.1 p = 1
    · rcases hex with ⟨d, hd0, hdp1⟩
      have hbij : (S_odd.filter (fun c : S => c.1 p = 1)).card =
          (S_odd.filter (fun c : S => ¬ c.1 p = 1)).card := by
        refine Finset.card_bij (fun c _ => c + d) ?_ ?_ ?_
        · intro c hc
          have hc_odd : dotProduct c.1 rhs = 1 :=
            (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).2
          have hcp1 : c.1 p = 1 := (Finset.mem_filter.mp hc).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · change dotProduct (c.1 + d.1) rhs = 1
            rw [add_dotProduct, hc_odd, hd0, add_zero]
          · change ¬ (c.1 p + d.1 p = 1)
            rw [hcp1, hdp1]; decide
        · intro c1 _ c2 _ heq
          have h1 := congrArg (fun z : S => z + d) heq
          have hdd : ∀ z : S, z + d + d = z := fun z => by
            apply Subtype.ext; ext q
            change z.1 q + d.1 q + d.1 q = z.1 q
            rw [add_assoc, zmod2_add_self, add_zero]
          rw [hdd c1, hdd c2] at h1
          exact h1
        · intro c hc
          have hc_odd : dotProduct c.1 rhs = 1 :=
            (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).2
          have hcp0 : c.1 p = 0 := by
            have hne := (Finset.mem_filter.mp hc).2
            rcases zmod2_zero_or_one (c.1 p) with hv | hv
            · exact hv
            · exact absurd hv hne
          refine ⟨c + d, ?_, ?_⟩
          · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
            · change dotProduct (c.1 + d.1) rhs = 1
              rw [add_dotProduct, hc_odd, hd0, add_zero]
            · change c.1 p + d.1 p = 1
              rw [hcp0, hdp1, zero_add]
          · apply Subtype.ext; ext q
            change c.1 q + d.1 q + d.1 q = c.1 q
            rw [add_assoc, zmod2_add_self, add_zero]
      have htot := Finset.card_filter_add_card_filter_not (s := S_odd) (p := fun c : S => c.1 p = 1)
      omega
    · push Not at hex
      rcases hzero_dep p with ⟨c0, hc0p, hc0odd⟩
      have hemp : S_odd.filter (fun c : S => c.1 p = 1) = ∅ := by
        ext c
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hc_odd hcp1
        have hdot0 : dotProduct (c + c0).1 rhs = 0 := by
          change dotProduct (c.1 + c0.1) rhs = 0
          rw [add_dotProduct, (Finset.mem_filter.mp hc_odd).2, hc0odd, zmod2_add_self]
        have hne1 := hex (c + c0) hdot0
        have heq1 : (c + c0).1 p = 1 := by
          change c.1 p + c0.1 p = 1
          rw [hcp1, hc0p, add_zero]
        exact hne1 heq1
      rw [hemp, Finset.card_empty]
      omega
  have hsum_le : (∑ c ∈ S_odd, 2 * (Finset.univ.filter (fun p : H => c.1 p = 1)).card) ≤
      S_odd.card * H.card := by
    have hswap : (∑ c ∈ S_odd, 2 * (Finset.univ.filter (fun p : H => c.1 p = 1)).card) =
        ∑ p : H, 2 * (S_odd.filter (fun c : S => c.1 p = 1)).card := by
      simp_rw [← Finset.mul_sum]
      congr 1
      have h1 : ∀ c ∈ S_odd, (Finset.univ.filter (fun p : H => c.1 p = 1)).card =
          ∑ p : H, if c.1 p = 1 then 1 else 0 := fun _ _ => by simp
      have h2 : ∀ p : H, (S_odd.filter (fun c : S => c.1 p = 1)).card =
          ∑ c ∈ S_odd, if c.1 p = 1 then 1 else 0 := fun _ => by simp
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      exact Finset.sum_congr rfl fun p _ => (h2 p).symm
    rw [hswap]
    calc
      (∑ p : H, 2 * (S_odd.filter (fun c : S => c.1 p = 1)).card)
          ≤ ∑ _p : H, S_odd.card := Finset.sum_le_sum fun p _ => hhalf p
      _ = S_odd.card * H.card := by simp [Finset.sum_const, mul_comm]
  rcases Finset.exists_min_image S_odd (fun c : S => 2 * (Finset.univ.filter (fun p : H => c.1 p = 1)).card)
    hSodd_ne with ⟨c, hc_mem, hc_min⟩
  have hc_bound : 2 * (Finset.univ.filter (fun p : H => c.1 p = 1)).card ≤ H.card := by
    have h1 : S_odd.card * (2 * (Finset.univ.filter (fun p : H => c.1 p = 1)).card) ≤
        ∑ c' ∈ S_odd, 2 * (Finset.univ.filter (fun p : H => c'.1 p = 1)).card := by
      calc
        S_odd.card * (2 * (Finset.univ.filter (fun p : H => c.1 p = 1)).card)
            = ∑ _c' ∈ S_odd, 2 * (Finset.univ.filter (fun p : H => c.1 p = 1)).card := by
              simp [Finset.sum_const]
        _ ≤ ∑ c' ∈ S_odd, 2 * (Finset.univ.filter (fun p : H => c'.1 p = 1)).card :=
            Finset.sum_le_sum fun c' hc' => hc_min c' hc'
    have hpos : 0 < S_odd.card := Finset.card_pos.mpr hSodd_ne
    have hle : S_odd.card * (2 * (Finset.univ.filter (fun p : H => c.1 p = 1)).card) ≤
        S_odd.card * H.card := le_trans h1 hsum_le
    exact Nat.le_of_mul_le_mul_left hle hpos
  let par : Fin m → ZMod 2 := fun e =>
    ∑ p ∈ (Finset.univ : Finset H).filter (fun p => p.1.1 = e), c.1 p
  let D : Finset (Fin m) := Finset.univ.filter (fun e => par e = 1)
  have hD_card : D.card ≤ (Finset.univ.filter (fun p : H => c.1 p = 1)).card := by
    have hex_p : ∀ e ∈ D, ∃ p : H, p.1.1 = e ∧ c.1 p = 1 := by
      intro e he
      have hpe1 : par e = 1 := (Finset.mem_filter.mp he).2
      by_contra hall
      push Not at hall
      have h0 : par e = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        have hpe : p.1.1 = e := (Finset.mem_filter.mp hp).2
        have hne1 := hall p hpe
        rcases zmod2_zero_or_one (c.1 p) with hv | hv
        · exact hv
        · exact absurd hv hne1
      rw [h0] at hpe1
      exact absurd hpe1 (by decide)
    let pick : Fin m → H := fun e =>
      if he : e ∈ D then Classical.choose (hex_p e he) else ⟨Classical.choose hHne, Classical.choose_spec hHne⟩
    refine Finset.card_le_card_of_injOn pick ?_ ?_
    · intro e he
      have he' : e ∈ D := Finset.mem_coe.mp he
      simp only [pick, he', ↓reduceDIte]
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Classical.choose_spec (hex_p e he')).2⟩)
    · intro e1 he1 e2 he2 heq
      have he1' : e1 ∈ D := Finset.mem_coe.mp he1
      have he2' : e2 ∈ D := Finset.mem_coe.mp he2
      simp only [pick, he1', he2', ↓reduceDIte] at heq
      have h1 := (Classical.choose_spec (hex_p e1 he1')).1
      have h2 := (Classical.choose_spec (hex_p e2 he2')).1
      rw [← h1, ← h2, heq]
  have hpar_ind : ∀ e : Fin m, (if e ∈ D then (1 : ZMod 2) else 0) = par e := by
    intro e
    by_cases h1 : par e = 1
    · simp [D, h1]
    · have h0 : par e = 0 := by
        rcases zmod2_zero_or_one (par e) with hv | hv
        · exact hv
        · exact absurd hv h1
      simp [D, h0]
  have hsum_par : ∀ f : Fin m → ZMod 2,
      (∑ e ∈ D, f e) = ∑ p : H, c.1 p * f p.1.1 := by
    intro f
    calc
      (∑ e ∈ D, f e) = ∑ e : Fin m, (if e ∈ D then (1 : ZMod 2) else 0) * f e := by
        have hfilt : Finset.univ.filter (fun e : Fin m => e ∈ D) = D := by ext e; simp
        have hterm : ∀ e : Fin m, (if e ∈ D then (1 : ZMod 2) else 0) * f e =
            if e ∈ D then f e else 0 := fun e => by split_ifs <;> ring
        rw [Finset.sum_congr rfl fun e _ => hterm e, ← Finset.sum_filter, hfilt]
      _ = ∑ e : Fin m, par e * f e := Finset.sum_congr rfl fun e _ => by rw [hpar_ind e]
      _ = ∑ e : Fin m, ∑ p ∈ (Finset.univ : Finset H).filter (fun p => p.1.1 = e), c.1 p * f e := by
        refine Finset.sum_congr rfl fun e _ => Finset.sum_mul _ _ _
      _ = ∑ e : Fin m, ∑ p ∈ (Finset.univ : Finset H).filter (fun p => p.1.1 = e), c.1 p * f p.1.1 := by
        refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun p hp => ?_
        rw [(Finset.mem_filter.mp hp).2]
      _ = ∑ p : H, c.1 p * f p.1.1 :=
        Finset.sum_fiberwise_of_maps_to (g := fun p : H => p.1.1) (t := Finset.univ)
          (fun _ _ => Finset.mem_univ _) _
  have hodd_sign : Odd ((D.filter (fun e => sign e = true)).card) := by
    rw [odd_iff_zmod2_eq_one]
    have h1 : ((D.filter (fun e => sign e = true)).card : ZMod 2) = ∑ e ∈ D, bx (sign e) := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun e _ => by cases sign e <;> decide
    rw [h1, hsum_par (fun e => bx (sign e))]
    exact (Finset.mem_filter.mp hc_mem).2
  have heven_deg : ∀ v : Fin n, Even ((D.filter (fun e => left e = v)).card +
      (D.filter (fun e => right e = v)).card) := by
    intro v
    rw [even_iff_zmod2_eq_zero, Nat.cast_add]
    have h1 : ((D.filter (fun e => left e = v)).card : ZMod 2) +
        ((D.filter (fun e => right e = v)).card : ZMod 2) =
        ∑ e ∈ D, ((if left e = v then (1 : ZMod 2) else 0) +
          (if right e = v then (1 : ZMod 2) else 0)) := by
      rw [Finset.sum_add_distrib, Finset.card_filter, Finset.card_filter, Nat.cast_sum, Nat.cast_sum]
      congr 1
      · refine Finset.sum_congr rfl fun e _ => by split_ifs <;> simp
      · refine Finset.sum_congr rfl fun e _ => by split_ifs <;> simp
    rw [h1, hsum_par]
    have hker : M.transpose.mulVec c.1 = 0 := c.2
    have hv := congrFun hker v
    simp only [M, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply,
      Pi.zero_apply] at hv
    conv_rhs => rw [← hv]
    refine Finset.sum_congr rfl fun p _ => mul_comm _ _
  exact ⟨D, ⟨hodd_sign, heven_deg⟩, by omega⟩

lemma trail_deg_parity {n m : ℕ} (left right : Fin m → Fin n)
    (t : ℕ) (v : ℕ → Fin n) (edge : ℕ → Fin m)
    (hinj : ∀ i < t, ∀ j < t, i ≠ j → edge i ≠ edge j)
    (hwalk : ∀ j < t, (v j = left (edge j) ∧ v (j + 1) = right (edge j)) ∨
      (v j = right (edge j) ∧ v (j + 1) = left (edge j))) :
    let E := (Finset.range t).image edge
    ∀ w : Fin n,
      (((E.filter (fun e => left e = w)).card + (E.filter (fun e => right e = w)).card : ℕ) : ZMod 2) =
      (if v 0 = w then (1 : ZMod 2) else 0) + (if v t = w then 1 else 0) := by
  intro E w
  have h1 : (((E.filter (fun e => left e = w)).card + (E.filter (fun e => right e = w)).card : ℕ) : ZMod 2) =
      ∑ e ∈ E, ((if left e = w then (1 : ZMod 2) else 0) + (if right e = w then 1 else 0)) := by
    rw [Nat.cast_add, Finset.card_filter, Finset.card_filter, Nat.cast_sum, Nat.cast_sum,
      Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun e _ => by split_ifs <;> simp
    · refine Finset.sum_congr rfl fun e _ => by split_ifs <;> simp
  rw [h1]
  have himg : (∑ e ∈ E, ((if left e = w then (1 : ZMod 2) else 0) + (if right e = w then 1 else 0))) =
      ∑ j ∈ Finset.range t, ((if v j = w then (1 : ZMod 2) else 0) + (if v (j + 1) = w then 1 else 0)) := by
    rw [Finset.sum_image fun i hi j hj heq => by
      by_contra hne
      exact hinj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hne heq]
    refine Finset.sum_congr rfl fun j hj => ?_
    rcases hwalk j (Finset.mem_range.mp hj) with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · rw [hl, hr]
    · rw [hl, hr, add_comm]
  rw [himg]
  clear himg h1 E hwalk hinj
  induction t with
  | zero => simp [zmod2_add_self]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    calc
      ((if v 0 = w then (1 : ZMod 2) else 0) + (if v k = w then 1 else 0)) +
          ((if v k = w then 1 else 0) + (if v (k + 1) = w then 1 else 0))
          = (if v 0 = w then (1 : ZMod 2) else 0) + (if v (k + 1) = w then 1 else 0) +
            ((if v k = w then 1 else 0) + (if v k = w then 1 else 0)) := by ring
      _ = (if v 0 = w then (1 : ZMod 2) else 0) + (if v (k + 1) = w then 1 else 0) := by
          rw [zmod2_add_self, add_zero]

lemma oddSet_imp_negative {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool) :
    ∀ (N : ℕ) (D : Finset (Fin m)), D.card = N → oddSet left right sign D →
      ∃ k ≤ N, ∃ (v : ℕ → Fin n) (edge : ℕ → Fin m), v 0 = v k ∧
        Odd (((Finset.range k).filter (fun j => sign (edge j) = true)).card) ∧
        ∀ j < k, (v j = left (edge j) ∧ v (j + 1) = right (edge j)) ∨
          (v j = right (edge j) ∧ v (j + 1) = left (edge j)) := by
  intro N
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    intro D hDcard hodd
    have hDne : D.Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      have h0 := hodd.1
      rw [hemp] at h0
      simp at h0
    let Trail (t : ℕ) : Prop :=
      ∃ (v : ℕ → Fin n) (edge : ℕ → Fin m),
        (∀ j < t, edge j ∈ D) ∧
        (∀ i < t, ∀ j < t, i ≠ j → edge i ≠ edge j) ∧
        (∀ j < t, (v j = left (edge j) ∧ v (j + 1) = right (edge j)) ∨
          (v j = right (edge j) ∧ v (j + 1) = left (edge j)))
    have hT1 : Trail 1 := by
      rcases hDne with ⟨e0, he0⟩
      refine ⟨fun j => if j = 0 then left e0 else right e0, fun _ => e0,
        fun j hj => by exact he0,
        fun i hi j hj hne => by omega,
        fun j hj => by
          have hj0 : j = 0 := by omega
          subst hj0; left; simp⟩
    have hTle : ∀ t, Trail t → t ≤ D.card := by
      intro t ⟨_, edge, hmem, hinj, _⟩
      have hsub : (Finset.range t).image edge ⊆ D := by
        intro e he
        rcases Finset.mem_image.mp he with ⟨j, hj, rfl⟩
        exact hmem j (Finset.mem_range.mp hj)
      have hcard : ((Finset.range t).image edge).card = t := by
        rw [Finset.card_image_of_injOn (fun i hi j hj heq => by
          by_contra hne
          exact hinj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hne heq),
          Finset.card_range]
      rw [← hcard]
      exact Finset.card_le_card hsub
    classical
    let Ts := (Finset.range (D.card + 1)).filter Trail
    have hTsne : Ts.Nonempty := by
      refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hT1⟩⟩
      have := hTle 1 hT1; omega
    rcases Finset.exists_max_image Ts id hTsne with ⟨t, htMem, htMax⟩
    have ht1 : 1 ≤ t := by
      have := htMax 1 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hTle 1 hT1; omega), hT1⟩)
      exact this
    have htT : Trail t := (Finset.mem_filter.mp htMem).2
    rcases htT with ⟨v, edge, hmem, hinj, hwalk⟩
    let E : Finset (Fin m) := (Finset.range t).image edge
    have hEsub : E ⊆ D := by
      intro e he
      rcases Finset.mem_image.mp he with ⟨j, hj, rfl⟩
      exact hmem j (Finset.mem_range.mp hj)
    have hEcard : E.card = t := by
      rw [Finset.card_image_of_injOn (fun i hi j hj heq => by
        by_contra hne
        exact hinj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hne heq),
        Finset.card_range]
    have hclosed : v 0 = v t := by
      by_contra hne
      have hdegE := trail_deg_parity left right t v edge hinj hwalk (v t)
      have hdegD : (((D.filter (fun e => left e = v t)).card +
          (D.filter (fun e => right e = v t)).card : ℕ) : ZMod 2) = 0 :=
        (even_iff_zmod2_eq_zero _).mp (hodd.2 (v t))
      have hsplitL : (D.filter (fun e => left e = v t)).card =
          (E.filter (fun e => left e = v t)).card +
          ((D \ E).filter (fun e => left e = v t)).card := by
        rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter Finset.disjoint_sdiff)]
        congr 1; ext e
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
        tauto
      have hsplitR : (D.filter (fun e => right e = v t)).card =
          (E.filter (fun e => right e = v t)).card +
          ((D \ E).filter (fun e => right e = v t)).card := by
        rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter Finset.disjoint_sdiff)]
        congr 1; ext e
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
        tauto
      have hdegE1 : (((E.filter (fun e => left e = v t)).card +
          (E.filter (fun e => right e = v t)).card : ℕ) : ZMod 2) = 1 := by
        rw [hdegE]; simp [hne]
      have hrem_odd : ((((D \ E).filter (fun e => left e = v t)).card +
          ((D \ E).filter (fun e => right e = v t)).card : ℕ) : ZMod 2) = 1 := by
        have hsum : (((D.filter (fun e => left e = v t)).card +
            (D.filter (fun e => right e = v t)).card : ℕ) : ZMod 2) =
            (((E.filter (fun e => left e = v t)).card +
              (E.filter (fun e => right e = v t)).card : ℕ) : ZMod 2) +
            ((((D \ E).filter (fun e => left e = v t)).card +
              ((D \ E).filter (fun e => right e = v t)).card : ℕ) : ZMod 2) := by
          rw [hsplitL, hsplitR]; push_cast; ring
        rw [hdegD, hdegE1] at hsum
        have := congrArg (fun z : ZMod 2 => z + 1) hsum
        simp only [zero_add, add_comm (1 : ZMod 2), add_assoc, zmod2_add_self, add_zero] at this
        exact this.symm
      have hrem_pos : 0 < ((D \ E).filter (fun e => left e = v t)).card +
          ((D \ E).filter (fun e => right e = v t)).card := by
        by_contra h0
        have h0' : ((D \ E).filter (fun e => left e = v t)).card +
            ((D \ E).filter (fun e => right e = v t)).card = 0 := by omega
        rw [h0', Nat.cast_zero] at hrem_odd
        exact absurd hrem_odd (by decide)
      have hex_e : ∃ e1 ∈ D \ E, left e1 = v t ∨ right e1 = v t := by
        by_cases hl : 0 < ((D \ E).filter (fun e => left e = v t)).card
        · rcases Finset.card_pos.mp hl with ⟨e1, he1⟩
          exact ⟨e1, (Finset.mem_filter.mp he1).1, Or.inl (Finset.mem_filter.mp he1).2⟩
        · have hr : 0 < ((D \ E).filter (fun e => right e = v t)).card := by omega
          rcases Finset.card_pos.mp hr with ⟨e1, he1⟩
          exact ⟨e1, (Finset.mem_filter.mp he1).1, Or.inr (Finset.mem_filter.mp he1).2⟩
      rcases hex_e with ⟨e1, he1DE, he1inc⟩
      have he1D : e1 ∈ D := (Finset.mem_sdiff.mp he1DE).1
      have he1notE : e1 ∉ E := (Finset.mem_sdiff.mp he1DE).2
      let v' : ℕ → Fin n := fun j =>
        if j ≤ t then v j else if left e1 = v t then right e1 else left e1
      let edge' : ℕ → Fin m := fun j => if j < t then edge j else e1
      have hTsucc : Trail (t + 1) := by
        refine ⟨v', edge', ?_, ?_, ?_⟩
        · intro j hj
          dsimp only [edge']
          split_ifs with hlt
          · exact hmem j hlt
          · exact he1D
        · intro i hi j hj hneq
          dsimp only [edge']
          by_cases hit : i < t
          · by_cases hjt : j < t
            · simp only [hit, hjt, ↓reduceIte]; exact hinj i hit j hjt hneq
            · simp only [hit, hjt, ↓reduceIte]
              intro heq; apply he1notE; rw [← heq]
              exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hit, rfl⟩
          · by_cases hjt : j < t
            · simp only [hit, hjt, ↓reduceIte]
              intro heq; apply he1notE; rw [heq]
              exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjt, rfl⟩
            · omega
        · intro j hj
          by_cases hjt : j < t
          · have hj1 : j ≤ t := by omega
            have hj2 : j + 1 ≤ t := by omega
            simp only [v', edge', hjt, hj1, hj2, ↓reduceIte]
            exact hwalk j hjt
          · have hjeq : j = t := by omega
            subst j
            have hnt : ¬ t < t := lt_irrefl t
            have hle : t ≤ t := le_refl t
            have hnt1 : ¬ t + 1 ≤ t := by omega
            simp only [v', edge', hnt, hle, hnt1, ↓reduceIte]
            by_cases hl : left e1 = v t
            · left; simp [hl]
            · right
              have hr : right e1 = v t := he1inc.resolve_left hl
              simp [hl, hr]
      have htleD : t + 1 ≤ D.card := hTle (t + 1) hTsucc
      have hmemTs : t + 1 ∈ Ts :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hTsucc⟩
      have hle_max := htMax (t + 1) hmemTs
      dsimp only [id] at hle_max
      omega
    have hEsign_card : ((Finset.range t).filter (fun j => sign (edge j) = true)).card =
        (E.filter (fun e => sign e = true)).card := by
      refine Finset.card_bij (fun j _ => edge j) ?_ ?_ ?_
      · intro j hj
        refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j, (Finset.mem_filter.mp hj).1, rfl⟩,
          (Finset.mem_filter.mp hj).2⟩
      · intro i hi j hj heq
        by_contra hne
        exact hinj i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
          j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1) hne heq
      · intro e he
        rcases Finset.mem_image.mp (Finset.mem_filter.mp he).1 with ⟨j, hj, rfl⟩
        exact ⟨j, Finset.mem_filter.mpr ⟨hj, (Finset.mem_filter.mp he).2⟩, rfl⟩
    by_cases hEodd : Odd (E.filter (fun e => sign e = true)).card
    · refine ⟨t, by have := hTle t ⟨v, edge, hmem, hinj, hwalk⟩; omega,
        v, edge, hclosed, ?_, hwalk⟩
      rw [hEsign_card]
      exact hEodd
    · have hEeven : Even (E.filter (fun e => sign e = true)).card := Nat.not_odd_iff_even.mp hEodd
      let D' := D \ E
      have hD'card : D'.card = D.card - t := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hEsub, hEcard]
      have hD'odd : oddSet left right sign D' := by
        constructor
        · have hsplit : (D.filter (fun e => sign e = true)).card =
              (E.filter (fun e => sign e = true)).card +
              (D'.filter (fun e => sign e = true)).card := by
            rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter Finset.disjoint_sdiff)]
            congr 1; ext e
            simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
            tauto
          rw [odd_iff_zmod2_eq_one]
          have h1 := (odd_iff_zmod2_eq_one _).mp hodd.1
          have h2 := (even_iff_zmod2_eq_zero _).mp hEeven
          rw [hsplit, Nat.cast_add, h2, zero_add] at h1
          exact h1
        · intro w
          rw [even_iff_zmod2_eq_zero]
          have hdegE := trail_deg_parity left right t v edge hinj hwalk w
          rw [← hclosed, zmod2_add_self] at hdegE
          have hdegD := (even_iff_zmod2_eq_zero _).mp (hodd.2 w)
          have hsplitL : (D.filter (fun e => left e = w)).card =
              (E.filter (fun e => left e = w)).card +
              (D'.filter (fun e => left e = w)).card := by
            rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter Finset.disjoint_sdiff)]
            congr 1; ext e
            simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
            tauto
          have hsplitR : (D.filter (fun e => right e = w)).card =
              (E.filter (fun e => right e = w)).card +
              (D'.filter (fun e => right e = w)).card := by
            rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter Finset.disjoint_sdiff)]
            congr 1; ext e
            simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
            tauto
          have hsum : (((D.filter (fun e => left e = w)).card +
              (D.filter (fun e => right e = w)).card : ℕ) : ZMod 2) =
              (((E.filter (fun e => left e = w)).card +
                (E.filter (fun e => right e = w)).card : ℕ) : ZMod 2) +
              (((D'.filter (fun e => left e = w)).card +
                (D'.filter (fun e => right e = w)).card : ℕ) : ZMod 2) := by
            rw [hsplitL, hsplitR]; push_cast; ring
          rw [hdegD, hdegE, zero_add] at hsum
          exact hsum.symm
      have htD : t ≤ D.card := by
        rw [← hEcard]
        exact Finset.card_le_card hEsub
      rcases ih D'.card (by omega) D' rfl hD'odd with ⟨k, hk, v2, edge2, hc2, ho2, hw2⟩
      exact ⟨k, by omega, v2, edge2, hc2, ho2, hw2⟩

lemma isResolvent_sat {V : Type} [DecidableEq V] {a : V → Bool} {C D R : Clause V}
    (hres : IsResolvent C D R) (hC : ClauseSat a C) (hD : ClauseSat a D) : ClauseSat a R := by
  rcases hres with ⟨v, _, _, rfl⟩
  cases hv : a v
  · rcases hC with ⟨l, hlC, hla⟩
    have hne : l ≠ (v, true) := by
      intro heq; subst heq; simp [hv] at hla
    exact ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hlC⟩), hla⟩
  · rcases hD with ⟨l, hlD, hla⟩
    have hne : l ≠ (v, false) := by
      intro heq; subst heq; simp [hv] at hla
    exact ⟨l, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, hlD⟩), hla⟩

lemma derivation_step_index {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π : List (Clause V)} (hπ : IsDerivation F π) :
    ∀ i : Fin π.length, π.get i ∈ F ∨
      ∃ a b : Fin π.length, i.val < a.val ∧ i.val < b.val ∧
        IsResolvent (π.get a) (π.get b) (π.get i) := by
  induction hπ with
  | nil => intro i; exact i.elim0
  | ax hπ' hC ih =>
    intro i
    cases i using Fin.cases with
    | zero => exact Or.inl hC
    | succ j =>
      rcases ih j with hax | ⟨a, b, ha, hb, hres⟩
      · exact Or.inl hax
      · exact Or.inr ⟨a.succ, b.succ, Nat.succ_lt_succ ha, Nat.succ_lt_succ hb, hres⟩
  | res hπ' hC hD hres ih =>
    intro i
    cases i using Fin.cases with
    | zero =>
      rcases List.mem_iff_get.mp hC with ⟨a, ha⟩
      rcases List.mem_iff_get.mp hD with ⟨b, hb⟩
      refine Or.inr ⟨a.succ, b.succ, Nat.zero_lt_succ _, Nat.zero_lt_succ _, ?_⟩
      rw [← ha, ← hb] at hres
      exact hres
    | succ j =>
      rcases ih j with hax | ⟨a, b, ha, hb, hres'⟩
      · exact Or.inl hax
      · exact Or.inr ⟨a.succ, b.succ, Nat.succ_lt_succ ha, Nat.succ_lt_succ hb, hres'⟩

lemma derivation_append {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π1 π2 : List (Clause V)} (h1 : IsDerivation F π1) (h2 : IsDerivation F π2) :
    IsDerivation F (π1 ++ π2) := by
  induction h1 with
  | nil => exact h2
  | ax _ hC ih => exact IsDerivation.ax ih hC
  | res _ hC hD hres ih =>
    exact IsDerivation.res ih (List.mem_append_left _ hC) (List.mem_append_left _ hD) hres

lemma refutation_ax_count_and_unsat {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π : List (Clause V)} (href : IsRefutation F π) :
    ∃ (ActAx : Finset (Fin π.length)),
      (∀ i ∈ ActAx, π.get i ∈ F) ∧
      2 * ActAx.card ≤ π.length + 1 ∧
      ¬ ∃ x : V → Bool, ∀ i ∈ ActAx, ClauseSat x (π.get i) := by
  classical
  rcases href with ⟨hder, hbot⟩
  rcases List.mem_iff_get.mp hbot with ⟨ibot, hibot⟩
  have hstep := derivation_step_index hder
  have hpar : ∀ i : Fin π.length, π.get i ∉ F →
      ∃ p : Fin π.length × Fin π.length, i.val < p.1.val ∧ i.val < p.2.val ∧
        IsResolvent (π.get p.1) (π.get p.2) (π.get i) := by
    intro i hnot
    rcases (hstep i).resolve_left hnot with ⟨a, b, ha, hb, hr⟩
    exact ⟨(a, b), ha, hb, hr⟩
  let p1 : Fin π.length → Fin π.length := fun i =>
    if h : π.get i ∉ F then (Classical.choose (hpar i h)).1 else i
  let p2 : Fin π.length → Fin π.length := fun i =>
    if h : π.get i ∉ F then (Classical.choose (hpar i h)).2 else i
  let closed (S : Finset (Fin π.length)) : Prop :=
    ibot ∈ S ∧ ∀ i ∈ S, π.get i ∉ F → p1 i ∈ S ∧ p2 i ∈ S
  let Act : Finset (Fin π.length) :=
    Finset.univ.filter (fun u : Fin π.length => ∀ S : Finset (Fin π.length), closed S → u ∈ S)
  have hAct_closed : closed Act := by
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun S hS => hS.1⟩, fun i hi hnot => ?_⟩
    have hi' := (Finset.mem_filter.mp hi).2
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun S hS => (hS.2 i (hi' S hS) hnot).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun S hS => (hS.2 i (hi' S hS) hnot).2⟩⟩
  let ActAx := Act.filter (fun i => π.get i ∈ F)
  let ActRes := Act.filter (fun i => π.get i ∉ F)
  have hsub_img : Act.erase ibot ⊆ ActRes.image p1 ∪ ActRes.image p2 := by
    intro u hu
    have hu_ne : u ≠ ibot := Finset.ne_of_mem_erase hu
    have hu_Act : u ∈ Act := Finset.mem_of_mem_erase hu
    by_contra hnot_img
    have hcl : closed (Act.erase u) := by
      refine ⟨Finset.mem_erase.mpr ⟨Ne.symm hu_ne, hAct_closed.1⟩, fun i hi hnotF => ?_⟩
      have hiRes : i ∈ ActRes := Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hi, hnotF⟩
      have hp1_ne : p1 i ≠ u := fun heq =>
        hnot_img (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hiRes, heq⟩))
      have hp2_ne : p2 i ≠ u := fun heq =>
        hnot_img (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hiRes, heq⟩))
      have hmem12 := hAct_closed.2 i (Finset.mem_of_mem_erase hi) hnotF
      exact ⟨Finset.mem_erase.mpr ⟨hp1_ne, hmem12.1⟩, Finset.mem_erase.mpr ⟨hp2_ne, hmem12.2⟩⟩
    have hu_er := (Finset.mem_filter.mp hu_Act).2 (Act.erase u) hcl
    exact (Finset.notMem_erase u Act) hu_er
  have hcard_er : Act.card - 1 ≤ 2 * ActRes.card := by
    calc
      Act.card - 1 = (Act.erase ibot).card := (Finset.card_erase_of_mem hAct_closed.1).symm
      _ ≤ (ActRes.image p1 ∪ ActRes.image p2).card := Finset.card_le_card hsub_img
      _ ≤ (ActRes.image p1).card + (ActRes.image p2).card := Finset.card_union_le _ _
      _ ≤ ActRes.card + ActRes.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = 2 * ActRes.card := by omega
  have hpart : ActAx.card + ActRes.card = Act.card :=
    Finset.card_filter_add_card_filter_not (s := Act) (p := fun i => π.get i ∈ F)
  have hAct_le : Act.card ≤ π.length := by
    have := Finset.card_le_univ Act
    simpa using this
  have hlen_bound : 2 * ActAx.card ≤ π.length + 1 := by omega
  have hunsat : ¬ ∃ x : V → Bool, ∀ i ∈ ActAx, ClauseSat x (π.get i) := by
    rintro ⟨x, hx⟩
    have hall : ∀ d : ℕ, ∀ i : Fin π.length, π.length - i.val = d → i ∈ Act → ClauseSat x (π.get i) := by
      intro d
      induction d using Nat.strong_induction_on with
      | ind d ih =>
        intro i hd hiAct
        by_cases hF : π.get i ∈ F
        · exact hx i (Finset.mem_filter.mpr ⟨hiAct, hF⟩)
        · have hspec := Classical.choose_spec (hpar i hF)
          have hp1_eq : p1 i = (Classical.choose (hpar i hF)).1 := by
            dsimp only [p1]; split_ifs; rfl
          have hp2_eq : p2 i = (Classical.choose (hpar i hF)).2 := by
            dsimp only [p2]; split_ifs; rfl
          have hmem12 := hAct_closed.2 i hiAct hF
          have h1 : ClauseSat x (π.get (p1 i)) :=
            ih (π.length - (p1 i).val) (by rw [hp1_eq]; have := i.2; omega) (p1 i) rfl hmem12.1
          have h2 : ClauseSat x (π.get (p2 i)) :=
            ih (π.length - (p2 i).val) (by rw [hp2_eq]; have := i.2; omega) (p2 i) rfl hmem12.2
          rw [hp1_eq] at h1
          rw [hp2_eq] at h2
          exact isResolvent_sat hspec.2.2 h1 h2
    have hbot_sat := hall (π.length - ibot.val) ibot rfl hAct_closed.1
    rw [hibot] at hbot_sat
    rcases hbot_sat with ⟨l, hl, _⟩
    exact Finset.notMem_empty l hl
  exact ⟨ActAx, fun i hi => (Finset.mem_filter.mp hi).2, hlen_bound, hunsat⟩

lemma bool_xor_cancel_left (a b : Bool) : (a ^^ (a ^^ b)) = b := by
  cases a <;> cases b <;> decide

lemma bool_not_xor_cancel (a b c : Bool) : (!(a ^^ (b ^^ c)) ^^ c) = !(a ^^ b) := by
  cases a <;> cases b <;> cases c <;> decide

end PEqualNP.Outside.L_pcx_263_aux

open PEqualNP.Outside.L_pcx_263_aux
open PEqualNP.ProofComplexity

theorem PEqualNP.Outside.L_pcx_263 :
    ∀ (n m : ℕ) (left right : Fin m → Fin n) (sign : Fin m → Bool),
      let cl := fun (e : Fin m) (a : Bool) =>
        ({(left e, !a), (right e, a ^^ sign e)} : PEqualNP.ProofComplexity.Clause (Fin n))
      let negative := fun k : ℕ =>
        ∃ (v : ℕ → Fin n) (edge : ℕ → Fin m), v 0 = v k ∧
          Odd (((Finset.range k).filter (fun j => sign (edge j) = true)).card) ∧
          ∀ j < k, (v j = left (edge j) ∧ v (j+1) = right (edge j)) ∨
            (v j = right (edge j) ∧ v (j+1) = left (edge j))
      let F : Set (PEqualNP.ProofComplexity.Clause (Fin n)) := {C | ∃ e a, C = cl e a}
      ∀ g : ℕ, negative g → (∀ k < g, ¬ negative k) →
        ∀ L w : ℕ,
          (∃ π : List (PEqualNP.ProofComplexity.Clause (Fin n)),
            PEqualNP.ProofComplexity.IsRefutation F π ∧ π.length ≤ L ∧
            ∀ C ∈ π, C.card ≤ w) ↔
          4*g ≤ L+1 ∧ (if g = 1 then 1 else 2) ≤ w := by
  intro n m left right sign cl negative F g hneg hmin L w
  classical
  have hg_pos : 1 ≤ g := by
    by_contra h0
    have hg0 : g = 0 := by omega
    subst hg0
    rcases hneg with ⟨_, _, _, hodd, _⟩
    simp at hodd
  constructor
  · rintro ⟨π, href, hlen, hwid⟩
    rcases refutation_ax_count_and_unsat href with ⟨ActAx, hAxF, hAxLen, hAxUnsat⟩
    have hex_ea : ∀ i : Fin π.length, i ∈ ActAx → ∃ p : Fin m × Bool, π.get i = cl p.1 p.2 := by
      intro i hi
      rcases hAxF i hi with ⟨e, a, hea⟩
      exact ⟨(e, a), hea⟩
    let pick : Fin π.length → Fin m × Bool := fun i =>
      if hi : i ∈ ActAx then Classical.choose (hex_ea i hi)
      else (⟨0, by rcases hneg with ⟨_, edge, _⟩; exact (edge 0).pos⟩, false)
    let H : Finset (Fin m × Bool) := ActAx.image pick
    have hH_card : H.card ≤ ActAx.card := Finset.card_image_le
    have hH_unsat : ¬ ∃ x : Fin n → Bool, ∀ p ∈ H, x (left p.1) = p.2 →
        x (right p.1) = (p.2 ^^ sign p.1) := by
      rintro ⟨x, hx⟩
      apply hAxUnsat
      refine ⟨x, fun i hi => ?_⟩
      have hpH : pick i ∈ H := Finset.mem_image.mpr ⟨i, hi, rfl⟩
      have hspec : π.get i = cl (pick i).1 (pick i).2 := by
        simp only [pick, hi, ↓reduceDIte]
        exact Classical.choose_spec (hex_ea i hi)
      rw [hspec]
      by_cases hl : x (left (pick i).1) = (pick i).2
      · refine ⟨(right (pick i).1, (pick i).2 ^^ sign (pick i).1), ?_, hx (pick i) hpH hl⟩
        simp [cl]
      · refine ⟨(left (pick i).1, !(pick i).2), ?_, ?_⟩
        · simp [cl]
        · cases h1 : x (left (pick i).1) <;> cases h2 : (pick i).2 <;> simp_all
    rcases unsat_imp_oddSet left right sign H hH_unsat with ⟨D, hDodd, hDcard⟩
    rcases oddSet_imp_negative left right sign D.card D rfl hDodd with ⟨k, hkD, v, edge, hc, ho, hw⟩
    have hgk : g ≤ k := by
      by_contra hlt
      exact hmin k (by omega) ⟨v, edge, hc, ho, hw⟩
    have h4g : 4 * g ≤ L + 1 := by omega
    have hAxNe : ActAx.Nonempty := Finset.card_pos.mp (by omega)
    rcases hAxNe with ⟨i0, hi0⟩
    have hi0_mem : π.get i0 ∈ π := List.get_mem π i0
    have hwi0 : (π.get i0).card ≤ w := hwid (π.get i0) hi0_mem
    rcases hAxF i0 hi0 with ⟨e0, a0, he0⟩
    rw [he0] at hwi0
    refine ⟨h4g, ?_⟩
    by_cases hg1 : g = 1
    · simp only [hg1, ↓reduceIte]
      have hne : (cl e0 a0).Nonempty := ⟨(left e0, !a0), by simp [cl]⟩
      have hpos : 1 ≤ (cl e0 a0).card := Finset.card_pos.mpr hne
      omega
    · simp only [hg1, ↓reduceIte]
      have hpair_ne : (left e0, !a0) ≠ (right e0, a0 ^^ sign e0) := by
        intro heq
        rcases Prod.mk.inj heq with ⟨hlr, hsign⟩
        have hst : sign e0 = true := by
          revert hsign
          cases a0 <;> cases sign e0 <;> decide
        have hneg1 : negative 1 := by
          refine ⟨fun _ => left e0, fun _ => e0, rfl, ?_, fun j hj => ?_⟩
          · have h1 : (Finset.range 1).filter (fun _ => sign e0 = true) = {0} := by
              ext j; simp [hst]
            rw [h1]; decide
          · left; exact ⟨rfl, hlr⟩
        exact hmin 1 (by omega) hneg1
      have hcard2 : (cl e0 a0).card = 2 := by
        dsimp only [cl]
        rw [Finset.card_pair hpair_ne]
      omega
  · rintro ⟨h4g, hw⟩
    rcases hneg with ⟨v, edge, hclosed, hodd, hwalk⟩
    by_cases hg1 : g = 1
    · subst hg1
      simp only [↓reduceIte] at hw
      have hst : sign (edge 0) = true := by
        by_contra hnot
        have hsf : sign (edge 0) = false := Bool.eq_false_iff.mpr hnot
        have h0 : (Finset.range 1).filter (fun j => sign (edge j) = true) = ∅ := by
          ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false,
            not_and]
          intro hj; have : j = 0 := by omega
          subst this; simp [hsf]
        rw [h0] at hodd
        simp at hodd
      have hlr : left (edge 0) = v 0 ∧ right (edge 0) = v 0 := by
        rcases hwalk 0 (by omega) with ⟨hl, hr⟩ | ⟨hr, hl⟩
        · exact ⟨hl.symm, (hclosed.trans hr).symm⟩
        · exact ⟨(hclosed.trans hl).symm, hr.symm⟩
      have hC0 : cl (edge 0) false = {(v 0, true)} := by
        simp [cl, hlr.1, hlr.2, hst]
      have hC1 : cl (edge 0) true = {(v 0, false)} := by
        simp [cl, hlr.1, hlr.2, hst]
      let π : List (Clause (Fin n)) := [∅, {(v 0, false)}, {(v 0, true)}]
      have hder : IsDerivation F π := by
        have h1 : IsDerivation F [{(v 0, true)}] :=
          IsDerivation.ax IsDerivation.nil ⟨edge 0, false, hC0.symm⟩
        have h2 : IsDerivation F [{(v 0, false)}, {(v 0, true)}] :=
          IsDerivation.ax h1 ⟨edge 0, true, hC1.symm⟩
        refine IsDerivation.res (C := {(v 0, true)}) (D := {(v 0, false)}) h2 (by simp) (by simp)
          ⟨v 0, by simp, by simp, by simp⟩
      refine ⟨π, ⟨hder, by simp [π]⟩, by simp [π]; omega, fun C hC => ?_⟩
      simp only [π, List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with rfl | rfl | rfl <;> simp <;> omega
    · simp only [hg1, ↓reduceIte] at hw
      have hg2 : 2 ≤ g := by omega
      have hne_v0 : ∀ j, 0 < j → j < g → v j ≠ v 0 := by
        intro j hj0 hjg heq
        have hsplit : ((Finset.range g).filter (fun i => sign (edge i) = true)).card =
            ((Finset.range j).filter (fun i => sign (edge i) = true)).card +
            ((Finset.range (g - j)).filter (fun i => sign (edge (j + i)) = true)).card := by
          have h1 : (Finset.range g).filter (fun i => sign (edge i) = true) =
              (Finset.range j).filter (fun i => sign (edge i) = true) ∪
              ((Finset.range (g - j)).filter (fun i => sign (edge (j + i)) = true)).image (fun i => j + i) := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image]
            constructor
            · rintro ⟨hig, hsi⟩
              by_cases hij : i < j
              · exact Or.inl ⟨hij, hsi⟩
              · right; refine ⟨i - j, ⟨by omega, ?_⟩, by omega⟩
                rw [show j + (i - j) = i by omega]; exact hsi
            · rintro (⟨hij, hsi⟩ | ⟨t, ⟨ht, hst⟩, rfl⟩)
              · exact ⟨by omega, hsi⟩
              · exact ⟨by omega, hst⟩
          rw [h1, Finset.card_union_of_disjoint]
          · rw [Finset.card_image_of_injective _ (fun a b h => by omega)]
          · rw [Finset.disjoint_left]
            intro i hi1 hi2
            have hij := (Finset.mem_range.mp (Finset.mem_filter.mp hi1).1)
            rcases Finset.mem_image.mp hi2 with ⟨t, _, rfl⟩
            omega
        by_cases ho1 : Odd ((Finset.range j).filter (fun i => sign (edge i) = true)).card
        · exact hmin j hjg ⟨v, edge, heq.symm, ho1, fun i hi => hwalk i (by omega)⟩
        · have he1 : Even ((Finset.range j).filter (fun i => sign (edge i) = true)).card :=
            Nat.not_odd_iff_even.mp ho1
          have ho2 : Odd ((Finset.range (g - j)).filter (fun i => sign (edge (j + i)) = true)).card := by
            rw [odd_iff_zmod2_eq_one]
            have h1 := (odd_iff_zmod2_eq_one _).mp hodd
            have h2 := (even_iff_zmod2_eq_zero _).mp he1
            rw [hsplit, Nat.cast_add, h2, zero_add] at h1
            exact h1
          refine hmin (g - j) (by omega) ⟨fun i => v (j + i), fun i => edge (j + i), ?_, ho2, fun i hi => ?_⟩
          · simp only [add_zero, show j + (g - j) = g by omega]
            exact heq.trans hclosed
          · have hwi := hwalk (j + i) (by omega)
            simpa only [add_assoc] using hwi
      have hne_adj : ∀ j < g, v j ≠ v (j + 1) := by
        intro j hj heq
        by_cases hsj : sign (edge j) = true
        · have hneg1 : negative 1 := by
            refine ⟨fun _ => v j, fun _ => edge j, rfl, ?_, fun i hi => ?_⟩
            · have h1 : (Finset.range 1).filter (fun _ => sign (edge j) = true) = {0} := by
                ext i; simp [hsj]
              rw [h1]; decide
            · have h0 := hwalk j hj
              rw [← heq] at h0; exact h0
          exact hmin 1 (by omega) hneg1
        · have hsf : sign (edge j) = false := Bool.eq_false_iff.mpr hsj
          let v' : ℕ → Fin n := fun i => if i ≤ j then v i else v (i + 1)
          let edge' : ℕ → Fin m := fun i => if i < j then edge i else edge (i + 1)
          have hodd' : Odd ((Finset.range (g - 1)).filter (fun i => sign (edge' i) = true)).card := by
            have hcard : ((Finset.range (g - 1)).filter (fun i => sign (edge' i) = true)).card =
                ((Finset.range g).filter (fun i => sign (edge i) = true)).card := by
              refine Finset.card_bij (fun i _ => if i < j then i else i + 1) ?_ ?_ ?_
              · intro i hi
                have hir := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
                have his := (Finset.mem_filter.mp hi).2
                dsimp only [edge'] at his
                split_ifs at his ⊢ with hlt
                · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), his⟩
                · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), his⟩
              · intro i1 _ i2 _ h12
                split_ifs at h12 <;> omega
              · intro i hi
                have hir := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
                have his := (Finset.mem_filter.mp hi).2
                have hij : i ≠ j := fun h => by subst h; simp [hsf] at his
                by_cases hlt : i < j
                · refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, by simp [hlt]⟩
                  simp [edge', hlt, his]
                · refine ⟨i - 1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, ?_⟩
                  · have hnlt : ¬ i - 1 < j := by omega
                    simp only [edge', hnlt, ↓reduceIte, show i - 1 + 1 = i by omega]
                    exact his
                  · have hnlt : ¬ i - 1 < j := by omega
                    simp only [hnlt, ↓reduceIte]; omega
            rw [hcard]; exact hodd
          refine hmin (g - 1) (by omega) ⟨v', edge', ?_, hodd', fun i hi => ?_⟩
          · have h0 : 0 ≤ j := Nat.zero_le j
            by_cases hgj : g - 1 ≤ j
            · have hjeq : j = g - 1 := by omega
              simp only [v', h0, hgj, ↓reduceIte]
              rw [← hjeq, heq, show j + 1 = g by omega]
              exact hclosed
            · simp only [v', h0, hgj, ↓reduceIte, show g - 1 + 1 = g by omega]
              exact hclosed
          · by_cases hilt : i < j
            · by_cases hi1 : i + 1 ≤ j
              · simp only [v', edge', hilt, show i ≤ j by omega, hi1, ↓reduceIte]
                exact hwalk i (by omega)
              · omega
            · have hige : j ≤ i := by omega
              have hni1 : ¬ i + 1 ≤ j := by omega
              by_cases hiej : i = j
              · subst hiej
                simp only [v', edge', lt_irrefl, le_refl, hni1, ↓reduceIte]
                rw [heq]
                exact hwalk (i + 1) (by omega)
              · have hnij : ¬ i ≤ j := by omega
                simp only [v', edge', hilt, hnij, hni1, ↓reduceIte]
                exact hwalk (i + 1) (by omega)
      let s : ℕ → Bool := fun t =>
        decide (Odd ((Finset.range t).filter (fun j => sign (edge j) = true)).card)
      have hs0 : s 0 = false := by simp [s]
      have hsg : s g = true := by simp [s, hodd]
      have hs_step : ∀ j, s (j + 1) = (s j ^^ sign (edge j)) := by
        intro j
        dsimp only [s]
        rw [Finset.range_add_one, Finset.filter_insert]
        by_cases h : sign (edge j) = true
        · have hnot : j ∉ (Finset.range j).filter (fun i => sign (edge i) = true) := by simp
          simp only [h, ↓reduceIte, Finset.card_insert_of_notMem hnot]
          by_cases ho : Odd ((Finset.range j).filter (fun i => sign (edge i) = true)).card
          · have he : ¬ Odd (((Finset.range j).filter (fun i => sign (edge i) = true)).card + 1) := by
              rcases ho with ⟨q, hq⟩; rw [hq]; intro ⟨r, hr⟩; omega
            simp [ho, he]
          · have ho' : Odd (((Finset.range j).filter (fun i => sign (edge i) = true)).card + 1) := by
              rcases Nat.not_odd_iff_even.mp ho with ⟨q, hq⟩
              exact ⟨q, by omega⟩
            simp [ho, ho']
        · simp [h]
      have hax_edge : ∀ (a0 : Bool) (j : ℕ), j < g →
          ({(v j, !(a0 ^^ s j)), (v (j + 1), a0 ^^ s (j + 1))} : Clause (Fin n)) ∈ F := by
        intro a0 j hj
        rcases hwalk j hj with ⟨hl, hr⟩ | ⟨hr, hl⟩
        · refine ⟨edge j, a0 ^^ s j, ?_⟩
          dsimp only [cl]
          rw [hl, hr, hs_step j, Bool.xor_assoc]
        · refine ⟨edge j, !(a0 ^^ s (j + 1)), ?_⟩
          dsimp only [cl]
          rw [hl, hr, Bool.not_not, hs_step j, bool_not_xor_cancel, Finset.pair_comm]
      have hchain : ∀ (a0 : Bool) (t : ℕ), 1 ≤ t → t ≤ g →
          ∃ π : List (Clause (Fin n)),
            IsDerivation F π ∧ π.length = 2 * t - 1 ∧
            ({(v 0, !a0), (v t, a0 ^^ s t)} : Clause (Fin n)) ∈ π ∧
            ∀ C ∈ π, C.card ≤ 2 := by
        intro a0 t
        induction t with
        | zero => intro h; omega
        | succ t ih =>
          intro _ htg
          by_cases ht0 : t = 0
          · subst ht0
            let C1 : Clause (Fin n) := {(v 0, !a0), (v 1, a0 ^^ s 1)}
            have hC1F : C1 ∈ F := by
              have h := hax_edge a0 0 (by omega)
              simpa [hs0] using h
            refine ⟨[C1], IsDerivation.ax IsDerivation.nil hC1F, rfl, by simp [C1], fun C hC => ?_⟩
            simp only [List.mem_singleton] at hC
            subst hC
            exact Finset.card_le_two
          · rcases ih (by omega) (by omega) with ⟨π, hder, hlen, hmem, hwid⟩
            let C1 : Clause (Fin n) := {(v 0, !a0), (v t, a0 ^^ s t)}
            let C2 : Clause (Fin n) := {(v t, !(a0 ^^ s t)), (v (t + 1), a0 ^^ s (t + 1))}
            let R : Clause (Fin n) := {(v 0, !a0), (v (t + 1), a0 ^^ s (t + 1))}
            have hC2F : C2 ∈ F := hax_edge a0 t (by omega)
            have hvt0 : v t ≠ v 0 := hne_v0 t (by omega) (by omega)
            have hvt1 : v t ≠ v (t + 1) := hne_adj t (by omega)
            have hder1 : IsDerivation F (C2 :: π) := IsDerivation.ax hder hC2F
            have hder2 : IsDerivation F (R :: C2 :: π) := by
              cases hbit : a0 ^^ s t
              · refine IsDerivation.res (C := C2) (D := C1) hder1 (by simp) (List.mem_cons_of_mem C2 hmem) ?_
                refine ⟨v t, by simp [C2, hbit], by simp [C1, hbit], ?_⟩
                ext l
                simp only [R, C1, C2, hbit, Bool.not_false, Finset.mem_union, Finset.mem_erase,
                  Finset.mem_insert, Finset.mem_singleton]
                constructor
                · rintro (rfl | rfl)
                  · right; exact ⟨fun h => hvt0 (congrArg Prod.fst h).symm, Or.inl rfl⟩
                  · left; exact ⟨fun h => hvt1 (congrArg Prod.fst h).symm, Or.inr rfl⟩
                · rintro (⟨hne, rfl | rfl⟩ | ⟨hne, rfl | rfl⟩)
                  · exact absurd rfl hne
                  · exact Or.inr rfl
                  · exact Or.inl rfl
                  · exact absurd rfl hne
              · refine IsDerivation.res (C := C1) (D := C2) hder1 (List.mem_cons_of_mem C2 hmem) (by simp) ?_
                refine ⟨v t, by simp [C1, hbit], by simp [C2, hbit], ?_⟩
                ext l
                simp only [R, C1, C2, hbit, Bool.not_true, Finset.mem_union, Finset.mem_erase,
                  Finset.mem_insert, Finset.mem_singleton]
                constructor
                · rintro (rfl | rfl)
                  · left; exact ⟨fun h => hvt0 (congrArg Prod.fst h).symm, Or.inl rfl⟩
                  · right; exact ⟨fun h => hvt1 (congrArg Prod.fst h).symm, Or.inr rfl⟩
                · rintro (⟨hne, rfl | rfl⟩ | ⟨hne, rfl | rfl⟩)
                  · exact Or.inl rfl
                  · exact absurd rfl hne
                  · exact absurd rfl hne
                  · exact Or.inr rfl
            refine ⟨R :: C2 :: π, hder2, by simp [hlen]; omega, by simp [R], fun C hC => ?_⟩
            simp only [List.mem_cons] at hC
            rcases hC with rfl | rfl | hCπ
            · exact Finset.card_le_two
            · exact Finset.card_le_two
            · exact hwid C hCπ
      rcases hchain false g hg_pos (le_refl g) with ⟨π0, hder0, hlen0, hmem0, hwid0⟩
      rcases hchain true g hg_pos (le_refl g) with ⟨π1, hder1, hlen1, hmem1, hwid1⟩
      have hunit0 : ({(v 0, true)} : Clause (Fin n)) ∈ π0 := by
        simpa [hclosed, hsg] using hmem0
      have hunit1 : ({(v 0, false)} : Clause (Fin n)) ∈ π1 := by
        simpa [hclosed, hsg] using hmem1
      let π : List (Clause (Fin n)) := ∅ :: (π0 ++ π1)
      have hder_app : IsDerivation F (π0 ++ π1) := derivation_append hder0 hder1
      have hder_all : IsDerivation F π :=
        IsDerivation.res hder_app (List.mem_append_left _ hunit0) (List.mem_append_right _ hunit1)
          ⟨v 0, by simp, by simp, by simp⟩
      refine ⟨π, ⟨hder_all, by simp [π]⟩, by simp [π, hlen0, hlen1]; omega, fun C hC => ?_⟩
      simp only [π, List.mem_cons, List.mem_append] at hC
      rcases hC with rfl | h0 | h1
      · simp
      · exact le_trans (hwid0 C h0) hw
      · exact le_trans (hwid1 C h1) hw
