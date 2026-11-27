import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_753

private lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> rfl

private lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  rcases zmod2_cases a with rfl | rfl
  · exact absurd rfl h
  · rfl

private lemma zmod2_eq_or_one_add (a b : ZMod 2) : b = a ∨ b = 1 + a := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · left; rfl
  · right; rfl
  · right; rfl
  · left; rfl

private def skipIdx {q : ℕ} (j0 : Fin q) (k : Fin (q - 1)) : Fin q :=
  if h : k.val < j0.val then ⟨k.val, by omega⟩ else ⟨k.val + 1, by omega⟩

private lemma exists_skipIdx {q : ℕ} (j0 j : Fin q) (hne : j ≠ j0) :
    ∃ k : Fin (q - 1), skipIdx j0 k = j := by
  have hval : j.val ≠ j0.val := fun h => hne (Fin.ext h)
  by_cases hlt : j.val < j0.val
  · refine ⟨⟨j.val, by omega⟩, ?_⟩
    simp [skipIdx, hlt]
  · refine ⟨⟨j.val - 1, by omega⟩, ?_⟩
    have hnot : ¬ j.val - 1 < j0.val := by omega
    ext
    simp only [skipIdx, hnot, dite_false]
    omega

private lemma exists_nonzero_mem_ker {n q : ℕ} (hqn : q < n)
    (L : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin q → ZMod 2)) :
    ∃ x : Fin n → ZMod 2, x ≠ 0 ∧ L x = 0 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker L
  have hdom : Module.finrank (ZMod 2) (Fin n → ZMod 2) = n := by simp
  have hrng : Module.finrank (ZMod 2) (LinearMap.range L) ≤ q := by
    calc Module.finrank (ZMod 2) (LinearMap.range L)
        ≤ Module.finrank (ZMod 2) (Fin q → ZMod 2) := Submodule.finrank_le _
      _ = q := by simp
  have hker_pos : 0 < Module.finrank (ZMod 2) (LinearMap.ker L) := by omega
  have hker_ne : LinearMap.ker L ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hker_pos
    omega
  by_contra h
  push Not at h
  apply hker_ne
  rw [Submodule.eq_bot_iff]
  intro x hx
  by_contra hx0
  exact h x hx0 (LinearMap.mem_ker.1 hx)

private lemma ker_finrank_ge {n q : ℕ} (hq : 0 < q) (hqn : q < n)
    (L : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin (q - 1) → ZMod 2)) :
    n + 1 - q ≤ Module.finrank (ZMod 2) (LinearMap.ker L) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker L
  have hdom : Module.finrank (ZMod 2) (Fin n → ZMod 2) = n := by simp
  have hrng : Module.finrank (ZMod 2) (LinearMap.range L) ≤ q - 1 := by
    calc Module.finrank (ZMod 2) (LinearMap.range L)
        ≤ Module.finrank (ZMod 2) (Fin (q - 1) → ZMod 2) := Submodule.finrank_le _
      _ = q - 1 := by simp
  omega

private lemma exists_submodule_of_finrank_le {n k : ℕ}
    (W : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hk : k ≤ Module.finrank (ZMod 2) W) :
    ∃ U : Submodule (ZMod 2) (Fin n → ZMod 2), U ≤ W ∧ Module.finrank (ZMod 2) U = k := by
  let b := Module.finBasis (ZMod 2) W
  let v : Fin k → (Fin n → ZMod 2) := fun i => (b (Fin.castLE hk i) : Fin n → ZMod 2)
  let U : Submodule (ZMod 2) (Fin n → ZMod 2) := Submodule.span (ZMod 2) (Set.range v)
  refine ⟨U, ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (b (Fin.castLE hk i)).2
  · have hv_ind : LinearIndependent (ZMod 2) v := by
      have h1 : LinearIndependent (ZMod 2) (fun i : Fin k => b (Fin.castLE hk i)) :=
        b.linearIndependent.comp (Fin.castLE hk) (Fin.castLE_injective hk)
      exact h1.map' W.subtype W.ker_subtype
    rw [finrank_span_eq_card hv_ind, Fintype.card_fin]

private lemma exists_linearMap_ker_eq {n q : ℕ} (hq : 0 < q) (hqn : q < n)
    (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hdim : Module.finrank (ZMod 2) U = n + 1 - q) :
    ∃ φ : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin (q - 1) → ZMod 2), LinearMap.ker φ = U := by
  have hquot := Submodule.finrank_quotient_add_finrank U
  have hdom : Module.finrank (ZMod 2) (Fin n → ZMod 2) = n := by simp
  have hqdim : Module.finrank (ZMod 2) ((Fin n → ZMod 2) ⧸ U) = q - 1 := by omega
  let e : ((Fin n → ZMod 2) ⧸ U) ≃ₗ[ZMod 2] (Fin (q - 1) → ZMod 2) :=
    (Module.finBasisOfFinrankEq (ZMod 2) ((Fin n → ZMod 2) ⧸ U) hqdim).equivFun
  refine ⟨e.toLinearMap.comp U.mkQ, ?_⟩
  ext x
  simp

end PEqualNP.Outside.L_lib_753

theorem PEqualNP.Outside.L_lib_753 : ∀ (n q : Nat), 0 < q → q < n →
  let F := ZMod 2
  let V := Fin n → F
  let P := F × V
  ∀ (available : V → Finset F), (∀ x : V, x ≠ 0 → (available x).Nonempty) →
    let hits := fun (out : P → Bool) =>
      (∀ b : F, out (b,0) = false) ∧
      (∀ x : V, x ≠ 0 → ∃ b ∈ available x, out (b,x) = true)
    let adaptive := ∃ (ask : (j : Fin q) → (Fin j.val → F) → (P →ₗ[F] F))
        (ans : P → Fin q → F) (decode : (Fin q → F) → Bool),
      (∀ (p : P) (j : Fin q), ans p j =
        ask j (fun earlier => ans p ⟨earlier.val, Nat.lt_trans earlier.isLt j.isLt⟩) p) ∧
      hits (fun p => decode (ans p))
    let fixed := ∃ (Q : P →ₗ[F] (Fin q → F)) (decode : (Fin q → F) → Bool),
      hits (fun p => decode (Q p))
    (¬fixed) ∧ (adaptive ↔
      ∃ (U T : Submodule F V) (mask : V →ₗ[F] F),
        Disjoint U T ∧ Module.finrank F U = n+1-q ∧ Module.finrank F T = n+1-q ∧
        (∀ x ∈ U, x ≠ 0 → 1 + mask x ∈ available x) ∧
        (∀ x ∈ T, x ≠ 0 → mask x ∈ available x)) := by
  intro n q hq hqn F V P available havail hits adaptive fixed
  constructor
  · rintro ⟨Q, decode, h0, h1⟩
    dsimp only at h0 h1
    let QV : V →ₗ[F] (Fin q → F) := Q.comp (LinearMap.inr F F V)
    obtain ⟨x, hx0, hQx⟩ := PEqualNP.Outside.L_lib_753.exists_nonzero_mem_ker hqn QV
    obtain ⟨b, _, htrue⟩ := h1 x hx0
    have hEq : Q (b, x) = Q (b, 0) := by
      have hsplit : ((b, x) : P) = (b, 0) + (0, x) := by ext <;> simp
      rw [hsplit, map_add]
      have h0x : Q (0, x) = 0 := hQx
      rw [h0x, add_zero]
    rw [hEq, h0 b] at htrue
    exact Bool.noConfusion htrue
  · constructor
    · rintro ⟨ask, ans, decode, hans, h0, h1⟩
      dsimp only at h0 h1
      let t0 : Fin q → F := ans (0, 0)
      let t1 : Fin q → F := ans (1, 0)
      have ht0 : ∀ j : Fin q, t0 j = 0 := by
        intro j
        change ans (0, 0) j = 0
        rw [hans (0, 0) j]
        exact map_zero _
      by_cases ht1_zero : ∀ j : Fin q, t1 j = 0
      · let L : V →ₗ[F] (Fin q → F) :=
          LinearMap.pi (fun j => (ask j (fun _ => 0)).comp (LinearMap.inr F F V))
        obtain ⟨x, hx0, hLx⟩ := PEqualNP.Outside.L_lib_753.exists_nonzero_mem_ker hqn L
        have hans_zero : ∀ (b : F) (m : ℕ) (hm : m < q), ans (b, x) ⟨m, hm⟩ = 0 := by
          intro b m
          induction m using Nat.strong_induction_on with
          | ind m ih =>
            intro hm
            rw [hans (b, x) ⟨m, hm⟩]
            have hear : (fun earlier : Fin m =>
                ans (b, x) ⟨earlier.val, Nat.lt_trans earlier.isLt hm⟩) = fun _ => 0 := by
              funext e
              exact ih e.val e.isLt (Nat.lt_trans e.isLt hm)
            rw [hear]
            have hsplit : ((b, x) : P) = (b, 0) + (0, x) := by ext <;> simp
            rw [hsplit, map_add]
            have h0x : ask ⟨m, hm⟩ (fun _ => 0) (0, x) = 0 := congrFun hLx ⟨m, hm⟩
            have hb0 : ask ⟨m, hm⟩ (fun _ => 0) (b, 0) = 0 := by
              rcases PEqualNP.Outside.L_lib_753.zmod2_cases b with rfl | rfl
              · exact map_zero _
              · have hear1 : (fun earlier : Fin m =>
                    ans (1, 0) ⟨earlier.val, Nat.lt_trans earlier.isLt hm⟩) = fun _ => 0 := by
                  funext e
                  exact ht1_zero ⟨e.val, Nat.lt_trans e.isLt hm⟩
                rw [← hear1, ← hans (1, 0) ⟨m, hm⟩]
                exact ht1_zero ⟨m, hm⟩
            rw [hb0, h0x, add_zero]
        obtain ⟨b, _, htrue⟩ := h1 x hx0
        have heq_t0 : ans (b, x) = t0 := by
          funext j
          rw [ht0 j]
          exact hans_zero b j.val j.isLt
        rw [heq_t0] at htrue
        have hf0 : decode t0 = false := h0 0
        rw [hf0] at htrue
        exact Bool.noConfusion htrue
      · push Not at ht1_zero
        have hex : ∃ m : ℕ, ∃ hm : m < q, t1 ⟨m, hm⟩ ≠ 0 := by
          obtain ⟨j, hj⟩ := ht1_zero
          exact ⟨j.val, j.isLt, hj⟩
        classical
        let m0 : ℕ := Nat.find hex
        have hm0_spec : ∃ hm : m0 < q, t1 ⟨m0, hm⟩ ≠ 0 := Nat.find_spec hex
        let hm0 : m0 < q := hm0_spec.1
        let j0 : Fin q := ⟨m0, hm0⟩
        have hj0_ne : t1 j0 ≠ 0 := hm0_spec.2
        have hj0_one : t1 j0 = 1 := PEqualNP.Outside.L_lib_753.zmod2_eq_one_of_ne_zero hj0_ne
        have hj0_lt : ∀ m < m0, ∀ hm : m < q, t1 ⟨m, hm⟩ = 0 := by
          intro m hlt hm
          by_contra hne
          exact Nat.find_min hex hlt ⟨hm, hne⟩
        let hsep : P →ₗ[F] F := ask j0 (fun _ => 0)
        have hsep_10 : hsep (1, 0) = 1 := by
          have hear1 : (fun e : Fin j0.val =>
              ans (1, 0) ⟨e.val, Nat.lt_trans e.isLt j0.isLt⟩) = fun _ => 0 := by
            funext e
            exact hj0_lt e.val e.isLt (Nat.lt_trans e.isLt j0.isLt)
          change ask j0 (fun _ => 0) (1, 0) = 1
          rw [← hear1, ← hans (1, 0) j0]
          exact hj0_one
        let mask : V →ₗ[F] F := hsep.comp (LinearMap.inr F F V)
        have hsep_eval : ∀ (b : F) (x : V), hsep (b, x) = b + mask x := by
          intro b x
          have hsplit : ((b, x) : P) = b • ((1, 0) : P) + (0, x) := by ext <;> simp
          rw [hsplit, map_add, map_smul, hsep_10, smul_eq_mul, mul_one]
          rfl
        let liftMask : V →ₗ[F] P := mask.prod LinearMap.id
        let L0 : V →ₗ[F] (Fin (q - 1) → F) :=
          LinearMap.pi (fun k => (ask (PEqualNP.Outside.L_lib_753.skipIdx j0 k) (fun _ => 0)).comp liftMask)
        let L1 : V →ₗ[F] (Fin (q - 1) → F) :=
          LinearMap.pi (fun k =>
            (ask (PEqualNP.Outside.L_lib_753.skipIdx j0 k)
              (fun e => t1 ⟨e.val, Nat.lt_trans e.isLt (PEqualNP.Outside.L_lib_753.skipIdx j0 k).isLt⟩)).comp liftMask)
        have hask_congr : ∀ (j1 j2 : Fin q), j1 = j2 → ∀ (f : Fin q → F) (p : P),
            ask j1 (fun e => f ⟨e.val, Nat.lt_trans e.isLt j1.isLt⟩) p =
            ask j2 (fun e => f ⟨e.val, Nat.lt_trans e.isLt j2.isLt⟩) p := by
          rintro j _ rfl _ _; rfl
        have hker0 : ∀ x ∈ LinearMap.ker L0, ans (mask x, x) = t0 := by
          intro x hx
          have hLx : L0 x = 0 := LinearMap.mem_ker.1 hx
          have hstep : ∀ (m : ℕ) (hm : m < q), ans (mask x, x) ⟨m, hm⟩ = 0 := by
            intro m
            induction m using Nat.strong_induction_on with
            | ind m ih =>
              intro hm
              rw [hans (mask x, x) ⟨m, hm⟩]
              have hear : (fun e : Fin m =>
                  ans (mask x, x) ⟨e.val, Nat.lt_trans e.isLt hm⟩) = fun _ => 0 := by
                funext e
                exact ih e.val e.isLt (Nat.lt_trans e.isLt hm)
              rw [hear]
              by_cases heq : (⟨m, hm⟩ : Fin q) = j0
              · rw [hask_congr ⟨m, hm⟩ j0 heq (fun _ => 0) (mask x, x)]
                change hsep (mask x, x) = 0
                rw [hsep_eval, PEqualNP.Outside.L_lib_753.zmod2_add_self]
              · obtain ⟨k, hk⟩ := PEqualNP.Outside.L_lib_753.exists_skipIdx j0 ⟨m, hm⟩ heq
                rw [hask_congr ⟨m, hm⟩ (PEqualNP.Outside.L_lib_753.skipIdx j0 k) hk.symm (fun _ => 0) (mask x, x)]
                exact congrFun hLx k
          funext j
          rw [ht0 j]
          exact hstep j.val j.isLt
        have hker1 : ∀ x ∈ LinearMap.ker L1, ans (1 + mask x, x) = t1 := by
          intro x hx
          have hLx : L1 x = 0 := LinearMap.mem_ker.1 hx
          have hstep : ∀ (m : ℕ) (hm : m < q), ans (1 + mask x, x) ⟨m, hm⟩ = t1 ⟨m, hm⟩ := by
            intro m
            induction m using Nat.strong_induction_on with
            | ind m ih =>
              intro hm
              rw [hans (1 + mask x, x) ⟨m, hm⟩]
              have hear : (fun e : Fin m =>
                  ans (1 + mask x, x) ⟨e.val, Nat.lt_trans e.isLt hm⟩) =
                  fun e : Fin m => t1 ⟨e.val, Nat.lt_trans e.isLt hm⟩ := by
                funext e
                exact ih e.val e.isLt (Nat.lt_trans e.isLt hm)
              rw [hear]
              by_cases heq : (⟨m, hm⟩ : Fin q) = j0
              · rw [hask_congr ⟨m, hm⟩ j0 heq t1 (1 + mask x, x), heq]
                have hear0 : (fun e : Fin j0.val => t1 ⟨e.val, Nat.lt_trans e.isLt j0.isLt⟩) = fun _ => 0 := by
                  funext e
                  exact hj0_lt e.val e.isLt (Nat.lt_trans e.isLt j0.isLt)
                rw [hear0]
                change hsep (1 + mask x, x) = t1 j0
                rw [hsep_eval, add_assoc, PEqualNP.Outside.L_lib_753.zmod2_add_self, add_zero, hj0_one]
              · obtain ⟨k, hk⟩ := PEqualNP.Outside.L_lib_753.exists_skipIdx j0 ⟨m, hm⟩ heq
                have hsplit : ((1 + mask x, x) : P) = (1, 0) + (mask x, x) := by ext <;> simp
                rw [hsplit, map_add]
                have hfirst : ask ⟨m, hm⟩ (fun e : Fin m => t1 ⟨e.val, Nat.lt_trans e.isLt hm⟩) (1, 0) = t1 ⟨m, hm⟩ := by
                  exact (hans (1, 0) ⟨m, hm⟩).symm
                have hsecond : ask ⟨m, hm⟩ (fun e : Fin m => t1 ⟨e.val, Nat.lt_trans e.isLt hm⟩) (mask x, x) = 0 := by
                  rw [hask_congr ⟨m, hm⟩ (PEqualNP.Outside.L_lib_753.skipIdx j0 k) hk.symm t1 (mask x, x)]
                  exact congrFun hLx k
                rw [hfirst, hsecond, add_zero]
          funext j
          exact hstep j.val j.isLt
        have hdisj_ker : Disjoint (LinearMap.ker L0) (LinearMap.ker L1) := by
          rw [Submodule.disjoint_def]
          intro x hx0 hx1
          by_contra hxne
          obtain ⟨b, _, htrue⟩ := h1 x hxne
          rcases PEqualNP.Outside.L_lib_753.zmod2_eq_or_one_add (mask x) b with rfl | rfl
          · rw [hker0 x hx0] at htrue
            have hf0 : decode t0 = false := h0 0
            rw [hf0] at htrue
            exact Bool.noConfusion htrue
          · rw [hker1 x hx1] at htrue
            have hf1 : decode t1 = false := h0 1
            rw [hf1] at htrue
            exact Bool.noConfusion htrue
        have hdim0 : n + 1 - q ≤ Module.finrank F (LinearMap.ker L0) :=
          PEqualNP.Outside.L_lib_753.ker_finrank_ge hq hqn L0
        have hdim1 : n + 1 - q ≤ Module.finrank F (LinearMap.ker L1) :=
          PEqualNP.Outside.L_lib_753.ker_finrank_ge hq hqn L1
        obtain ⟨U, hU_le, hU_dim⟩ :=
          PEqualNP.Outside.L_lib_753.exists_submodule_of_finrank_le (LinearMap.ker L0) hdim0
        obtain ⟨T, hT_le, hT_dim⟩ :=
          PEqualNP.Outside.L_lib_753.exists_submodule_of_finrank_le (LinearMap.ker L1) hdim1
        refine ⟨U, T, mask, hdisj_ker.mono hU_le hT_le, hU_dim, hT_dim, ?_, ?_⟩
        · intro x hxU hxne
          obtain ⟨b, hb_av, htrue⟩ := h1 x hxne
          rcases PEqualNP.Outside.L_lib_753.zmod2_eq_or_one_add (mask x) b with rfl | rfl
          · rw [hker0 x (hU_le hxU)] at htrue
            have hf0 : decode t0 = false := h0 0
            rw [hf0] at htrue
            exact Bool.noConfusion htrue
          · exact hb_av
        · intro x hxT hxne
          obtain ⟨b, hb_av, htrue⟩ := h1 x hxne
          rcases PEqualNP.Outside.L_lib_753.zmod2_eq_or_one_add (mask x) b with rfl | rfl
          · exact hb_av
          · rw [hker1 x (hT_le hxT)] at htrue
            have hf1 : decode t1 = false := h0 1
            rw [hf1] at htrue
            exact Bool.noConfusion htrue
    · rintro ⟨U, T, mask, hdisj, hU_dim, hT_dim, hU_av, hT_av⟩
      obtain ⟨φU, hkerU⟩ := PEqualNP.Outside.L_lib_753.exists_linearMap_ker_eq hq hqn U hU_dim
      obtain ⟨φT, hkerT⟩ := PEqualNP.Outside.L_lib_753.exists_linearMap_ker_eq hq hqn T hT_dim
      let ask : (j : Fin q) → (Fin j.val → F) → (P →ₗ[F] F) := fun j earlier =>
        if hj : j.val = 0 then
          LinearMap.fst F F V + mask.comp (LinearMap.snd F F V)
        else
          let k : Fin (q - 1) := ⟨j.val - 1, by omega⟩
          if earlier ⟨0, by omega⟩ = 0 then
            (LinearMap.proj k).comp (φU.comp (LinearMap.snd F F V))
          else
            (LinearMap.proj k).comp (φT.comp (LinearMap.snd F F V))
      let ans : P → Fin q → F := fun p j =>
        if hj : j.val = 0 then
          p.1 + mask p.2
        else
          let k : Fin (q - 1) := ⟨j.val - 1, by omega⟩
          if p.1 + mask p.2 = 0 then φU p.2 k else φT p.2 k
      let decode : (Fin q → F) → Bool := fun v =>
        decide (∃ k : Fin (q - 1), v ⟨k.val + 1, by omega⟩ ≠ 0)
      refine ⟨ask, ans, decode, ?_, ?_, ?_⟩
      · intro p j
        by_cases hj : j.val = 0
        · simp [ask, ans, hj]
          rfl
        · simp only [ask, ans, show ¬ j.val = 0 from hj, dite_false, dite_true]
          split_ifs <;> rfl
      · intro b
        simp only [decode, decide_eq_false_iff_not, not_exists, not_not]
        intro k
        simp only [ans, show k.val + 1 ≠ 0 by omega, dite_false, Nat.add_sub_cancel, map_zero,
          Pi.zero_apply, ite_self]
      · intro x hx0
        have hne_of_not_mem_U : x ∉ U → ∃ k : Fin (q - 1), φU x k ≠ 0 := by
          intro hnot
          have hne : φU x ≠ 0 := by
            intro h0
            apply hnot
            rw [← hkerU]
            exact LinearMap.mem_ker.2 h0
          by_contra hall
          push Not at hall
          exact hne (funext hall)
        have hne_of_not_mem_T : x ∉ T → ∃ k : Fin (q - 1), φT x k ≠ 0 := by
          intro hnot
          have hne : φT x ≠ 0 := by
            intro h0
            apply hnot
            rw [← hkerT]
            exact LinearMap.mem_ker.2 h0
          by_contra hall
          push Not at hall
          exact hne (funext hall)
        by_cases hxU : x ∈ U
        · have hxT : x ∉ T := by
            intro hxT
            exact hx0 ((Submodule.disjoint_def.1 hdisj) x hxU hxT)
          refine ⟨1 + mask x, hU_av x hxU hx0, ?_⟩
          simp only [decode, decide_eq_true_eq]
          obtain ⟨k, hk⟩ := hne_of_not_mem_T hxT
          refine ⟨k, ?_⟩
          have hbm : (1 : F) + mask x + mask x ≠ 0 := by
            rw [add_assoc, PEqualNP.Outside.L_lib_753.zmod2_add_self, add_zero]
            decide
          simpa [ans, hbm] using hk
        · by_cases hxT : x ∈ T
          · refine ⟨mask x, hT_av x hxT hx0, ?_⟩
            simp only [decode, decide_eq_true_eq]
            obtain ⟨k, hk⟩ := hne_of_not_mem_U hxU
            refine ⟨k, ?_⟩
            have hbm : mask x + mask x = 0 := PEqualNP.Outside.L_lib_753.zmod2_add_self (mask x)
            simpa [ans, hbm] using hk
          · obtain ⟨b, hb_av⟩ := havail x hx0
            refine ⟨b, hb_av, ?_⟩
            simp only [decode, decide_eq_true_eq]
            by_cases hbm : b + mask x = 0
            · obtain ⟨k, hk⟩ := hne_of_not_mem_U hxU
              exact ⟨k, by simpa [ans, hbm] using hk⟩
            · obtain ⟨k, hk⟩ := hne_of_not_mem_T hxT
              exact ⟨k, by simpa [ans, hbm] using hk⟩
