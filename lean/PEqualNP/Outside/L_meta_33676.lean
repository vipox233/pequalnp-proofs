import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33676_aux.Translation

abbrev F₂ := ZMod 2

section Periods

variable {V O : Type*} [AddCommGroup V] [Module F₂ V]

def periods (F : V → O) : Submodule F₂ V := by
  refine { carrier := {v | ∀ x, F (x + v) = F x}, zero_mem' := by simp, add_mem' := ?_, smul_mem' := ?_ }
  ·
    intro a b ha hb x
    change ∀ z, F (z + a) = F z at ha
    change ∀ z, F (z + b) = F z at hb
    rw [← add_assoc, hb, ha]
  ·
    intro c v hv
    change ∀ z, F (z + v) = F z at hv
    have two : ∀ t : F₂, t = 0 ∨ t = 1 := by decide
    rcases two c with rfl | rfl
    · change ∀ x, F (x + (0:F₂) • v) = F x
      simp
    · change ∀ x, F (x + (1:F₂) • v) = F x
      simpa using hv

def Good (F : V → O) (R : V →ₗ[F₂] V) (g : V) : Prop :=
  ∀ w, F (R w + g) = F (w + g)

def displacement (R : V →ₗ[F₂] V) : V →ₗ[F₂] V := LinearMap.id - R

@[simp] theorem displacement_apply (R : V →ₗ[F₂] V) (x : V) :
    displacement R x = x - R x := rfl

theorem good_iff_affine (F : V → O) (R : V →ₗ[F₂] V) (g : V) :
    Good F R g ↔ ∀ x, F (R x + displacement R g) = F x := by
  constructor
  · intro h x
    have e := h (x - g)
    rw [map_sub, sub_add_cancel] at e
    convert e using 2 <;> simp only [displacement_apply] <;> abel
  · intro h w
    have e := h (w+g)
    rw [map_add, displacement_apply] at e
    convert e using 2 <;> abel

def directions (F : V → O) (R : V →ₗ[F₂] V) : Submodule F₂ V :=
  (periods F).comap (displacement R)

theorem good_iff_sub_mem (F : V → O) (R : V →ₗ[F₂] V) (hR : Function.Surjective R)
    {g₀ : V} (h₀ : Good F R g₀) (g : V) :
    Good F R g ↔ g - g₀ ∈ directions F R := by
  rw [good_iff_affine] at h₀ ⊢
  change _ ↔ ∀ z, F (z + displacement R (g - g₀)) = F z
  rw [map_sub]
  constructor
  · intro h z
    obtain ⟨w,hw⟩ := hR (z - displacement R g₀)
    have he : R w + displacement R g₀ = z := by rw [hw]; abel
    have hd : R w + displacement R g = z + (displacement R g - displacement R g₀) := by rw [hw]; abel
    rw [← hd, ← he, h, h₀]
  · intro h w
    have e := h (R w + displacement R g₀)
    rw [show R w + displacement R g₀ + (displacement R g - displacement R g₀) = R w + displacement R g by abel] at e
    exact e.trans (h₀ w)

def goodEquiv (F : V → O) (R : V →ₗ[F₂] V) (hR : Function.Surjective R)
    {g₀ : V} (h₀ : Good F R g₀) : {g // Good F R g} ≃ directions F R where
  toFun g := ⟨g.1 - g₀, (good_iff_sub_mem F R hR h₀ _).1 g.2⟩
  invFun v := ⟨v.1 + g₀, (good_iff_sub_mem F R hR h₀ _).2 (by simpa using v.2)⟩
  left_inv _ := Subtype.ext (sub_add_cancel _ _)
  right_inv _ := Subtype.ext (add_sub_cancel_right _ _)

theorem good_count (F : V → O) (R : V →ₗ[F₂] V) (hR : Function.Surjective R)
    [Finite V] {g₀ : V} (h₀ : Good F R g₀) :
    Nat.card {g // Good F R g} = 2 ^ Module.finrank F₂ (directions F R) := by
  rw [Nat.card_congr (goodEquiv F R hR h₀), Module.natCard_eq_pow_finrank (K := F₂), Nat.card_zmod]

end Periods

section Words

abbrev Word (k : ℕ) := Fin (2^k)
abbrev Vector (k : ℕ) := Fin k → F₂

def encode {k : ℕ} (x : Word k) (i : Fin k) : F₂ := if x.val.testBit i.val then 1 else 0

theorem encode_inj {k : ℕ} : Function.Injective (encode (k := k)) := by
  intro a b h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · have hi' := congrFun h ⟨i,hi⟩
    change (if a.val.testBit i then (1:F₂) else 0) = (if b.val.testBit i then (1:F₂) else 0) at hi'
    cases ea : a.val.testBit i <;> cases eb : b.val.testBit i <;> simp_all
  · have hpow : 2^k ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (a.isLt.trans_le hpow), Nat.testBit_lt_two_pow (b.isLt.trans_le hpow)]

noncomputable def wordEquiv (k : ℕ) : Word k ≃ Vector k := Equiv.ofBijective encode <| by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨encode_inj, by simp [Vector,F₂]⟩

def plusWord {k} (a b : Word k) : Word k := ⟨a.val ^^^ b.val,Nat.xor_lt_two_pow a.isLt b.isLt⟩

theorem encode_plusWord {k} (a b : Word k) :
    encode (plusWord a b) = encode a + encode b := by
  funext i
  change (if (a.val ^^^ b.val).testBit i then (1:F₂) else 0) =
    (if a.val.testBit i then 1 else 0) + (if b.val.testBit i then 1 else 0)
  rw [Nat.testBit_xor]
  cases a.val.testBit i <;> cases b.val.testBit i <;> decide

def rawRot (k s w : ℕ) := ((w <<< (s % k)) ||| (w >>> (k - s % k))) % 2^k

def rotated {k} (s : ℕ) (w : Word k) : Word k := ⟨rawRot k s w.val, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

def rotIndex {k s : ℕ} (hs : s<k) : Fin k ≃ Fin k where
  toFun i := ⟨if i.val<s then k-s+i.val else i.val-s, by split <;> omega⟩
  invFun i := ⟨if (k - s) ≤ i.val then i.val-(k-s) else i.val+s, by split <;> omega⟩
  left_inv i := by apply Fin.ext; dsimp; split_ifs <;> omega
  right_inv i := by apply Fin.ext; dsimp; split_ifs <;> omega

def rotateLinear {k s : ℕ} (hs : s<k) : Vector k →ₗ[F₂] Vector k where
  toFun v i := v (rotIndex hs i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rotate_surj {k s : ℕ} (hs : s<k) : Function.Surjective (rotateLinear hs) := by
  intro v
  refine ⟨fun i => v ((rotIndex hs).symm i), ?_⟩
  funext i
  exact congrArg v ((rotIndex hs).symm_apply_apply i)

theorem encode_rotated {k s : ℕ} (hs : s<k) (w : Word k) :
    encode (rotated s w) = rotateLinear hs (encode w) := by
  funext j
  change (if (rawRot k s w.val).testBit j.val then (1:F₂) else 0) =
    (if w.val.testBit (if j.val<s then k-s+j.val else j.val-s) then 1 else 0)
  suffices (rawRot k s w.val).testBit j.val = w.val.testBit (if j.val<s then k-s+j.val else j.val-s) by rw [this]
  simp only [rawRot,Nat.mod_eq_of_lt hs,Nat.testBit_mod_two_pow,j.isLt,decide_true,Bool.true_and,
    Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_shiftRight]
  by_cases hj : j.val<s
  · simp [hj,Nat.not_le.mpr hj]
  · have big : w.val.testBit (k-s+j.val) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le w.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hj,Nat.le_of_not_gt hj,big]

def rawGood {k : ℕ} {O : Type*} (F : Nat → O) (s : ℕ) (g : Word k) : Prop :=
  ∀ w : Word k, F (rawRot k s w.val ^^^ g.val) = F (w.val ^^^ g.val)

noncomputable def view {k : ℕ} {O : Type*} (F : Nat → O) (v : Vector k) := F ((wordEquiv k).symm v).val

theorem rawGood_iff {k s : ℕ} {O : Type*} (F : Nat → O) (hs : s<k) (g : Word k) :
    rawGood F s g ↔ Good (view F) (rotateLinear hs) (encode g) := by
  have ea (x : Word k) : view F (encode x) = F x.val := by
    change F ((wordEquiv k).symm ((wordEquiv k) x)).val = _
    rw [Equiv.symm_apply_apply]
  have e (w : Word k) : view F (rotateLinear hs (encode w) + encode g) = F (rawRot k s w.val ^^^ g.val) := by
    rw [← encode_rotated, ← encode_plusWord, ea]; rfl
  have e' (w : Word k) : view F (encode w + encode g) = F (w.val ^^^ g.val) := by
    rw [← encode_plusWord, ea]; rfl
  constructor
  · intro h w
    obtain ⟨v,rfl⟩ := (wordEquiv k).surjective w
    exact (e v).trans ((h v).trans (e' v).symm)
  · exact fun h w => (e w).symm.trans ((h (encode w)).trans (e' w))

theorem rawGood_count {k s : ℕ} {O : Type*} (F : Nat → O) (hs : s<k) {g₀ : Word k}
    (hg : rawGood F s g₀) :
    Nat.card {g : Word k // rawGood F s g} =
      2 ^ Module.finrank F₂ (directions (view F) (rotateLinear hs)) := by
  let e : {g : Word k // rawGood F s g} ≃ {v // Good (view F) (rotateLinear hs) v} :=
    (wordEquiv k).subtypeEquiv (rawGood_iff F hs)
  rw [Nat.card_congr e]
  exact good_count _ _ (rotate_surj hs) ((rawGood_iff F hs g₀).mp hg)

theorem rawGood_count_bit {k s : ℕ} {O : Type*} (F : Nat → O) (hs : s<k)
    {g₀ : Word k} (hg : rawGood F s g₀) (j : ℕ) :
    (Nat.card {g : Word k // rawGood F s g}).testBit j = true ↔
      j = Module.finrank F₂ (directions (view F) (rotateLinear hs)) := by
  rw [rawGood_count F hs hg, Nat.testBit_two_pow, decide_eq_true_eq, eq_comm]

theorem rawGood_count_empty {k s : ℕ} {O : Type*} (F : Nat → O)
    (h : ¬∃ g : Word k, rawGood F s g) : Nat.card {g : Word k // rawGood F s g} = 0 := by
  letI : IsEmpty {g : Word k // rawGood F s g} := ⟨fun g => h ⟨g.val,g.property⟩⟩
  simp

end Words

section LocalTables

variable {V : Type*} [AddCommGroup V] [Module F₂ V]

def signedPeriods (G : V → F₂) : Submodule F₂ (V × F₂) := by
  refine { carrier := {z | ∀ x, G (x + z.1) = G x + z.2}, zero_mem' := by simp, add_mem' := ?_, smul_mem' := ?_ }
  ·
    intro z w hz hw x
    change ∀ x, G (x + z.1) = G x + z.2 at hz
    change ∀ x, G (x + w.1) = G x + w.2 at hw
    change G (x + (z.1 + w.1)) = G x + (z.2 + w.2)
    rw [← add_assoc, hw, hz, add_assoc]
  ·
    intro c z hz
    have two : ∀ t : F₂, t = 0 ∨ t = 1 := by decide
    rcases two c with rfl | rfl
    · change ∀ x, G (x + ((0:F₂) • z).1) = G x + ((0:F₂) • z).2
      simp
    · change ∀ x, G (x + ((1:F₂) • z).1) = G x + ((1:F₂) • z).2
      simpa using hz

def compatible (F G : V → F₂) (z : V × F₂) : Prop :=
  ∀ x, G (x + z.1) = F x + z.2

theorem compatible_iff_coset (F G : V → F₂) {base : V × F₂} (hbase : compatible F G base)
    (z : V × F₂) : compatible F G z ↔ z - base ∈ signedPeriods G := by
  change (∀ x, G (x + z.1) = F x + z.2) ↔ ∀ x, G (x + (z.1-base.1)) = G x + (z.2-base.2)
  constructor
  · intro h x
    have hb := hbase (x-base.1)
    rw [sub_add_cancel] at hb
    rw [show x+(z.1-base.1) = (x-base.1)+z.1 by abel, h, hb]
    abel
  · intro h x
    have hh := h (x+base.1)
    rw [show (x+base.1)+(z.1-base.1) = x+z.1 by abel, hbase] at hh
    convert hh using 1; abel

theorem tableSum_iff {I X : Type*} [Fintype I] (o : X) (δ : I → X → F₂) :
    (∀ x : I → X, ∑ i, δ i (x i) = 0) ↔
      (∑ i, δ i o = 0) ∧ ∀ i x, δ i x = δ i o := by
  classical
  constructor
  · intro h
    have hb := h (fun _ => o)
    refine ⟨hb,fun i t => ?_⟩
    have ht := h (Function.update (fun _ => o) i t)
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at ht hb
    have he : (∑ j ∈ Finset.univ.erase i, δ j (Function.update (fun _ => o) i t j)) =
        ∑ j ∈ Finset.univ.erase i, δ j o := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [he, Function.update_self] at ht
    exact add_left_cancel (ht.trans hb.symm)
  · rintro ⟨h,h'⟩ x
    simpa only [h'] using h

theorem parity_iff_compatible {I : Type*} [Fintype I]
    (F G : I → V → F₂) (t : I → V) :
    (∀ x : I → V, ∑ i, G i (x i + t i) = ∑ i, F i (x i)) ↔
      ∃ b : I → F₂, (∑ i, b i = 0) ∧ ∀ i, compatible (F i) (G i) (t i,b i) := by
  let δ := fun i v => G i (v + t i) - F i v
  have he : (∀ x : I → V, ∑ i, G i (x i + t i) = ∑ i, F i (x i)) ↔
      ∀ x : I → V, ∑ i, δ i (x i) = 0 := by
    simp only [δ, Finset.sum_sub_distrib,sub_eq_zero]
  rw [he, tableSum_iff (0:V) δ]
  constructor
  · rintro ⟨h₀,h₁⟩
    refine ⟨fun i => δ i 0,h₀,fun i x => ?_⟩
    have hi := h₁ i x
    change G i (x + t i) - F i x = δ i 0 at hi
    exact (sub_eq_iff_eq_add'.mp hi)
  · rintro ⟨b,hb,hc⟩
    have h i v : δ i v = b i := by
      change G i (v+t i) - F i v = b i
      rw [hc i v]; abel
    simpa [h] using hb

theorem compatible_constant_unique (F G : V → F₂) (t : V) {b b' : F₂}
    (h : compatible F G (t,b)) (h' : compatible F G (t,b')) : b = b' := by
  exact add_left_cancel ((h 0).symm.trans (h' 0))

theorem compatible_iff_equations (F G : V → F₂) {base : V × F₂} (hbase : compatible F G base)
    (z : V × F₂) : compatible F G z ↔
      ∀ ℓ ∈ (signedPeriods G).dualAnnihilator, ℓ z = ℓ base := by
  rw [compatible_iff_coset F G hbase]
  have he : (signedPeriods G).dualAnnihilator.dualCoannihilator = signedPeriods G :=
    Subspace.dualAnnihilator_dualCoannihilator_eq
  conv_lhs => rw [← he,Submodule.mem_dualCoannihilator]
  simp only [map_sub,sub_eq_zero]

def validEquation (F G : V → F₂) (ℓ : Module.Dual F₂ (V × F₂)) (c : F₂) : Prop :=
  ∀ w, compatible F G w → ℓ w = c

theorem compatible_iff_validEquations (F G : V → F₂) (z : V × F₂) :
    compatible F G z ↔ ∀ ℓ c, validEquation F G ℓ c → ℓ z = c := by
  constructor
  · exact fun hz ℓ c h => h z hz
  · intro h
    by_cases hb : ∃ w, compatible F G w
    · obtain ⟨base,hbase⟩ := hb
      apply (compatible_iff_equations F G hbase z).2
      intro ℓ hℓ
      apply h ℓ (ℓ base)
      intro w hw
      exact ((compatible_iff_equations F G hbase w).1 hw) ℓ hℓ
    · have impossible := h 0 1 (fun w hw => False.elim (hb ⟨w,hw⟩))
      simpa using impossible

theorem local_normals_card (d : ℕ) :
    Nat.card (Module.Dual F₂ ((Fin (d+1) → F₂) × F₂)) = 4*2^d := by
  rw [Module.natCard_eq_pow_finrank (K := F₂), Nat.card_zmod, Subspace.dual_finrank_eq,
    Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self]
  ring

end LocalTables

section Combined

variable {I J U V : Type*} [Fintype I]
  [AddCommGroup U] [Module F₂ U] [AddCommGroup V] [Module F₂ V]

def combinedGood (F G : J → I → U → F₂) (T : J → I → V →ₗ[F₂] U) (g : V) : Prop :=
  ∀ j (x : I → U), ∑ i, G j i (x i + T j i g) = ∑ i, F j i (x i)

def equations (F G : J → I → U → F₂) (T : J → I → V →ₗ[F₂] U)
    (v : V × (J → I → F₂)) : Prop :=
  ∀ j, (∑ i, v.2 j i = 0) ∧ ∀ i ℓ c, validEquation (F j i) (G j i) ℓ c →
    ℓ (T j i v.1,v.2 j i) = c

theorem combined_iff (F G : J → I → U → F₂) (T : J → I → V →ₗ[F₂] U) (g : V) :
    combinedGood F G T g ↔ ∃! b : J → I → F₂, equations F G T (g,b) := by
  classical
  constructor
  · intro hg
    have localE j := (parity_iff_compatible (F j) (G j) (fun i => T j i g)).1 (hg j)
    choose b hb hcomp using localE
    refine ⟨b,fun j => ⟨hb j,fun i => (compatible_iff_validEquations _ _ _).1 (hcomp j i)⟩,?_⟩
    intro other he
    funext j i
    exact compatible_constant_unique _ _ _ ((compatible_iff_validEquations _ _ _).2 ((he j).2 i)) (hcomp j i)
  · rintro ⟨b,hb,_⟩ j
    apply (parity_iff_compatible (F j) (G j) (fun i => T j i g)).2
    exact ⟨b j,(hb j).1,fun i => (compatible_iff_validEquations _ _ _).2 ((hb j).2 i)⟩

theorem goodOfEquations (F G : J → I → U → F₂) (T : J → I → V →ₗ[F₂] U)
    {v : V × (J → I → F₂)} (h : equations F G T v) : combinedGood F G T v.1 := by
  intro j
  apply (parity_iff_compatible (F j) (G j) (fun i => T j i v.1)).2
  exact ⟨v.2 j,(h j).1,fun i => (compatible_iff_validEquations _ _ _).2 ((h j).2 i)⟩

noncomputable def equationsEquiv (F G : J → I → U → F₂) (T : J → I → V →ₗ[F₂] U) :
    {g // combinedGood F G T g} ≃ {v // equations F G T v} where
  toFun g := ⟨(g.val,((combined_iff F G T _).mp g.property).choose),
      ((combined_iff F G T _).mp g.property).choose_spec.1⟩
  invFun v := ⟨v.val.1,goodOfEquations F G T v.property⟩
  left_inv _ := rfl
  right_inv v := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · rfl
    exact (((combined_iff F G T v.val.1).mp (goodOfEquations F G T v.property)).choose_spec.2 _ v.property).symm

end Combined

section Least

def descend (ask : ℕ → ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, base => base
  | j+1, base => descend ask j (if ask j base then base else base + 2^j)

def feasible (P : ℕ → Prop) (j base : ℕ) : Prop :=
  ∃ w, base ≤ w ∧ w < base+2^j ∧ P w

theorem descend_spec (ask : ℕ → ℕ → Bool) (P : ℕ → Prop)
    (hs : ∀ j b, ask j b = true ↔ feasible P j b) (j base : ℕ) (h : feasible P j base) :
    P (descend ask j base) ∧ base ≤ descend ask j base ∧ descend ask j base < base+2^j ∧
      ∀ w, base ≤ w → w < base+2^j → P w → descend ask j base ≤ w := by
  induction j generalizing base with
  | zero =>
    rcases h with ⟨w,h₁,h₂,h₃⟩
    simp only [pow_zero] at h₂
    simp only [descend,pow_zero]
    have e : w = base := by omega
    subst w
    exact ⟨h₃,le_rfl, by omega, fun _ h' _ _ => h'⟩
  | succ j ih =>
    simp only [descend, pow_succ]
    by_cases hq : feasible P j base
    · simp [(hs j base).2 hq]
      obtain ⟨h₁,h₂,h₃,h₄⟩ := ih base hq
      refine ⟨h₁,h₂,by omega,fun w hwa hwb hw => ?_⟩
      by_cases hl : w < base+2^j
      · exact h₄ w hwa hl hw
      · omega
    · have ha : ask j base = false := Bool.eq_false_iff.mpr (fun e => hq ((hs j base).1 e))
      simp [ha]
      have hm : ∀ w, base ≤ w → P w → base+2^j ≤ w := by
        intro w hw hw'
        by_contra! hf
        exact hq ⟨w,hw,hf,hw'⟩
      obtain ⟨w,hw₁,hw₂,hw₃⟩ := h
      rw [pow_succ] at hw₂
      have he : feasible P j (base+2^j) := ⟨w,hm w hw₁ hw₃,by omega,hw₃⟩
      obtain ⟨h₁,h₂,h₃,h₄⟩ := ih (base+2^j) he
      exact ⟨h₁,by omega,by omega,fun z za zb hc => h₄ z (hm z za hc) (by omega) hc⟩

def natPred {k : ℕ} (P : Word k → Prop) (a : ℕ) : Prop :=
  ∃ w : Word k, w.val = a ∧ P w

theorem leastWord_spec {k : ℕ} (P : Word k → Prop) (ask : ℕ → ℕ → Bool)
    (hs : ∀ j b, ask j b = true ↔ feasible (natPred P) j b) (hp : ∃ w, P w) :
    ∃ g : Word k, g.val = descend ask k 0 ∧ P g ∧ ∀ w, P w → g ≤ w := by
  obtain ⟨w,hw⟩ := hp
  have h : feasible (natPred P) k 0 := ⟨w.val,Nat.zero_le _,by simpa using w.isLt,w,rfl,hw⟩
  obtain ⟨⟨g,hg,hpg⟩,_,_,hmin⟩ := descend_spec ask (natPred P) hs k 0 h
  refine ⟨g,hg,hpg,fun z hz => ?_⟩
  change g.val ≤ z.val
  rw [hg]
  exact hmin _ (Nat.zero_le _) (by simpa using z.isLt) ⟨z,rfl,hz⟩

theorem leastWord_bit {k : ℕ} (P : Word k → Prop) (ask : ℕ → ℕ → Bool)
    (hs : ∀ j b, ask j b = true ↔ feasible (natPred P) j b) (j : ℕ) :
    (∃ g, P g ∧ (∀ w, P w → g ≤ w) ∧ (j=0 ∨ g.val.testBit (j-1) = true)) ↔
      (∃ g, P g) ∧ (j=0 ∨ (descend ask k 0).testBit (j-1) = true) := by
  constructor
  · rintro ⟨g,hg,hm,hb⟩
    obtain ⟨g',he,hg',hm'⟩ := leastWord_spec P ask hs ⟨g,hg⟩
    have eq : g = g' := le_antisymm (hm g' hg') (hm' g hg)
    exact ⟨⟨g,hg⟩, by simpa only [eq,he] using hb⟩
  · rintro ⟨hp,hb⟩
    obtain ⟨g,he,hg,hm⟩ := leastWord_spec P ask hs hp
    exact ⟨g,hg,hm,by simpa only [he] using hb⟩

end Least

end PEqualNP.Outside.L_meta_33676_aux.Translation

namespace PEqualNP.Outside.L_meta_33676_aux.Windows

def rotK (k offset x : Nat) : Nat :=
  ((x <<< (offset % k)) ||| (x >>> (k - offset % k))) % 2 ^ k

def mixK (k gap value : Nat) : Nat :=
  value ^^^ rotK k gap value ^^^ rotK k (k - gap) value

def chiK (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc site =>
    acc ||| ((xor (word.testBit site)
      (!(word.testBit ((site + 1) % k)) && word.testBit ((site + 2) % k))).toNat <<< site)) 0

def stepK (k r : Nat) (constants : Nat → Fin (2 ^ k)) (col : Bool) (raw prev t : Nat) : Nat :=
  chiK k (mixK k (if col then 2 else 1) prev) ^^^
    rotK k (if col then 3 * t + 1 else 2 * (t - 1)) raw ^^^
    (constants (if col then r + t else t)).val

def stateN (k r : Nat) (c : Nat → Fin (2 ^ k)) (side : Bool) (key name : Nat) (n : Nat) : Nat :=
  (List.range n).foldl (fun v tick => stepK k r c side key v (tick + 1))
    (rotK k (if side then 3 else 1) key ^^^ name)

lemma rotK_lt {k : Nat} (offset x : Nat) : rotK k offset x < 2 ^ k :=
  Nat.mod_lt _ (by positivity)

lemma rotK_testBit {k : Nat} (hk : 0 < k) {x : Nat} (hx : x < 2 ^ k)
    (offset i : Nat) (hi : i < k) :
    (rotK k offset x).testBit i = x.testBit ((i + k - offset % k) % k) := by
  dsimp only [rotK]
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and,
    Nat.testBit_lor, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hs : offset % k < k := Nat.mod_lt offset hk
  by_cases hle : offset % k ≤ i
  · have hhi : x.testBit (k - offset % k + i) = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)))
    have hidx : (i + k - offset % k) % k = i - offset % k := by
      have h1 : i + k - offset % k = (i - offset % k) + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [decide_eq_true hle, Bool.true_and, hhi, Bool.or_false, hidx]
  · have hidx : (i + k - offset % k) % k = k - offset % k + i := by
      have h1 : i + k - offset % k = k - offset % k + i := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega)]
    rw [decide_eq_false hle, Bool.false_and, Bool.false_or, hidx]

lemma chiK_spec (k word : Nat) :
    chiK k word < 2 ^ k ∧
    ∀ i < k, (chiK k word).testBit i =
      xor (word.testBit i) (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k)) := by
  let bitFn : Nat → Bool := fun site =>
    xor (word.testBit site) (!(word.testBit ((site + 1) % k)) && word.testBit ((site + 2) % k))
  have htake : ∀ m ≤ k,
      let v := (List.range m).foldl (fun acc b => acc ||| ((bitFn b).toNat <<< b)) 0
      (∀ j, m ≤ j → v.testBit j = false) ∧ (∀ b < m, v.testBit b = bitFn b) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨fun j _ => by simp, fun b hb => by omega⟩
    | succ m ih =>
      intro hm
      have hprev := ih (by omega)
      dsimp only
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      refine ⟨?_, ?_⟩
      · intro j hj
        rw [Nat.testBit_lor, Nat.testBit_shiftLeft, hprev.1 j (by omega)]
        have h1 : m ≤ j := by omega
        have hlt2 : (bitFn m).toNat < 2 ^ (j - m) := by
          have hle1 : (bitFn m).toNat ≤ 1 := by cases bitFn m <;> decide
          have hpow : 2 ≤ 2 ^ (j - m) := Nat.le_self_pow (by omega) 2
          omega
        rw [decide_eq_true h1, Bool.true_and, Nat.testBit_eq_false_of_lt hlt2]
        rfl
      · intro b hb
        rw [Nat.testBit_lor, Nat.testBit_shiftLeft]
        by_cases hbm : b = m
        · subst hbm
          rw [hprev.1 b le_rfl, decide_eq_true le_rfl, Bool.true_and, Bool.false_or, Nat.sub_self]
          cases bitFn b <;> decide
        · have hlt : b < m := by omega
          have hnot : ¬(m ≤ b) := by omega
          rw [decide_eq_false hnot, Bool.false_and, Bool.or_false, hprev.2 b hlt]
  have hfull := htake k le_rfl
  refine ⟨?_, hfull.2⟩
  by_contra hge
  have h1 : 2 ^ k ≤ chiK k word := by omega
  have hne : chiK k word ≠ 0 := by
    have hpos : 0 < 2 ^ k := by positivity
    omega
  have hlog : k ≤ Nat.log2 (chiK k word) := (Nat.le_log2 hne).mpr h1
  have htrue : (chiK k word).testBit (Nat.log2 (chiK k word)) = true := Nat.testBit_log2 hne
  have hfalse : (chiK k word).testBit (Nat.log2 (chiK k word)) = false := hfull.1 _ hlog
  rw [htrue] at hfalse
  exact Bool.noConfusion hfalse

lemma stateN_zero (k r : Nat) (c : Nat → Fin (2 ^ k)) (side : Bool) (key name : Nat) :
    stateN k r c side key name 0 = rotK k (if side then 3 else 1) key ^^^ name := rfl

lemma stateN_succ (k r : Nat) (c : Nat → Fin (2 ^ k)) (side : Bool) (key name n : Nat) :
    stateN k r c side key name (n + 1) =
    stepK k r c side key (stateN k r c side key name n) (n + 1) := by
  dsimp only [stateN]
  rw [List.range_succ, List.foldl_append]
  rfl

lemma stateN_lt {k r : Nat} (c : Nat → Fin (2 ^ k)) (side : Bool) (key : Nat)
    {name : Nat} (hname : name < 2 ^ k) :
    ∀ n : Nat, stateN k r c side key name n < 2 ^ k := by
  intro n
  cases n with
  | zero =>
    rw [stateN_zero]
    exact Nat.xor_lt_two_pow (rotK_lt _ _) hname
  | succ m =>
    rw [stateN_succ]
    dsimp only [stepK]
    exact Nat.xor_lt_two_pow
      (Nat.xor_lt_two_pow (chiK_spec k _).1 (rotK_lt _ _))
      (c _).isLt

def AgreeCyc (k x y lo len : Nat) : Prop :=
  ∀ d < len, x.testBit ((lo + d) % k) = y.testBit ((lo + d) % k)

lemma agreeCyc_rot {k : Nat} (hk : 0 < k) {x y : Nat} (hx : x < 2 ^ k) (hy : y < 2 ^ k)
    (s lo len : Nat) (h : AgreeCyc k x y (lo + k - s % k) len) :
    AgreeCyc k (rotK k s x) (rotK k s y) lo len := by
  intro d hd
  have hi : (lo + d) % k < k := Nat.mod_lt _ hk
  rw [rotK_testBit hk hx s _ hi, rotK_testBit hk hy s _ hi]
  have hs : s % k < k := Nat.mod_lt s hk
  have heq : ((lo + d) % k + k - s % k) % k = ((lo + k - s % k) + d) % k := by
    have h1 : (lo + d) % k + k - s % k = (lo + d) % k + (k - s % k) := by omega
    rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    congr 1
    omega
  rw [heq]
  exact h d hd

lemma agreeCyc_mix {k gap : Nat} (hgap0 : 0 < gap) (hgap : gap < k) {u v : Nat}
    (hu : u < 2 ^ k) (hv : v < 2 ^ k) (lo len : Nat)
    (h : AgreeCyc k u v (lo + k - gap) (len + 2 * gap)) :
    AgreeCyc k (mixK k gap u) (mixK k gap v) lo len := by
  have hk : 0 < k := by omega
  intro d hd
  dsimp only [mixK]
  rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor]
  have h1 : u.testBit ((lo + d) % k) = v.testBit ((lo + d) % k) := by
    have heq : (lo + d) % k = (lo + k - gap + (d + gap)) % k := by
      have hsum : lo + k - gap + (d + gap) = (lo + d) + k := by omega
      rw [hsum, Nat.add_mod_right]
    rw [heq]
    exact h (d + gap) (by omega)
  have h2 : (rotK k gap u).testBit ((lo + d) % k) = (rotK k gap v).testBit ((lo + d) % k) := by
    have hi : (lo + d) % k < k := Nat.mod_lt _ hk
    rw [rotK_testBit hk hu gap _ hi, rotK_testBit hk hv gap _ hi]
    have hmod : gap % k = gap := Nat.mod_eq_of_lt hgap
    rw [hmod]
    have heq : ((lo + d) % k + k - gap) % k = (lo + k - gap + d) % k := by
      have hsub : (lo + d) % k + k - gap = (lo + d) % k + (k - gap) := by omega
      rw [hsub, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      congr 1
      omega
    rw [heq]
    exact h d (by omega)
  have h3 : (rotK k (k - gap) u).testBit ((lo + d) % k) = (rotK k (k - gap) v).testBit ((lo + d) % k) := by
    have hi : (lo + d) % k < k := Nat.mod_lt _ hk
    rw [rotK_testBit hk hu (k - gap) _ hi, rotK_testBit hk hv (k - gap) _ hi,
      Nat.mod_eq_of_lt (by omega : k - gap < k)]
    have heq : ((lo + d) % k + k - (k - gap)) % k = (lo + k - gap + (d + 2 * gap)) % k := by
      have hsub : (lo + d) % k + k - (k - gap) = (lo + d) % k + gap := by omega
      rw [hsub, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have hsum : lo + k - gap + (d + 2 * gap) = (lo + d + gap) + k := by omega
      rw [hsum, Nat.add_mod_right]
    rw [heq]
    exact h (d + 2 * gap) (by omega)
  rw [h1, h2, h3]

lemma agreeCyc_chi {k : Nat} (hk : 0 < k) {u v : Nat} (lo len : Nat)
    (h : AgreeCyc k u v lo (len + 2)) :
    AgreeCyc k (chiK k u) (chiK k v) lo len := by
  intro d hd
  have hi : (lo + d) % k < k := Nat.mod_lt _ hk
  rw [(chiK_spec k u).2 _ hi, (chiK_spec k v).2 _ hi]
  have h0 : u.testBit ((lo + d) % k) = v.testBit ((lo + d) % k) := h d (by omega)
  have h1 : u.testBit (((lo + d) % k + 1) % k) = v.testBit (((lo + d) % k + 1) % k) := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have heq : lo + d + 1 = lo + (d + 1) := by omega
    rw [heq]
    exact h (d + 1) (by omega)
  have h2 : u.testBit (((lo + d) % k + 2) % k) = v.testBit (((lo + d) % k + 2) % k) := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have heq : lo + d + 2 = lo + (d + 2) := by omega
    rw [heq]
    exact h (d + 2) (by omega)
  rw [h0, h1, h2]

lemma agreeCyc_chi_mix {k gap : Nat} (hgap0 : 0 < gap) (hgap : gap < k) {u v : Nat}
    (hu : u < 2 ^ k) (hv : v < 2 ^ k) (lo len : Nat)
    (h : AgreeCyc k u v (lo + k - gap) (len + 2 * gap + 2)) :
    AgreeCyc k (chiK k (mixK k gap u)) (chiK k (mixK k gap v)) lo len := by
  have hk : 0 < k := by omega
  apply agreeCyc_chi hk lo len
  have h' : AgreeCyc k u v (lo + k - gap) ((len + 2) + 2 * gap) := by
    have heq : (len + 2) + 2 * gap = len + 2 * gap + 2 := by omega
    rw [heq]
    exact h
  exact agreeCyc_mix hgap0 hgap hu hv lo (len + 2) h'

def rowL (t : Nat) : Nat := max (t + 1) (2 * t - 2)

lemma row_stateN_congr {k r : Nat} (hr : 4 ≤ r) (hk : 5 * r - 2 ≤ k)
    (c : Nat → Fin (2 ^ k)) {row x y : Nat}
    (hrow : row < 2 ^ k) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    ∀ t ≤ r, ∀ lo len : Nat,
      AgreeCyc k x y (lo + k - rowL t) (len + rowL t + 3 * t - 1) →
      AgreeCyc k (stateN k r c false x row t) (stateN k r c false y row t) lo len := by
  have hkpos : 0 < k := by omega
  intro t
  induction t with
  | zero =>
    intro _ lo len h
    rw [stateN_zero, stateN_zero]
    intro d hd
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Nat.testBit_xor, Nat.testBit_xor]
    have hrot : (rotK k 1 x).testBit ((lo + d) % k) = (rotK k 1 y).testBit ((lo + d) % k) := by
      have h1 : AgreeCyc k x y (lo + k - 1 % k) len := by
        rw [Nat.mod_eq_of_lt (by omega : 1 < k)]
        intro e he
        exact h e (by dsimp only [rowL]; omega)
      exact agreeCyc_rot hkpos hx hy 1 lo len h1 d hd
    rw [hrot]
  | succ t ih =>
    intro ht lo len h
    have ht' : t ≤ r := by omega
    have hL_lt : rowL (t + 1) < k := by dsimp only [rowL]; omega
    have hLt_lt : rowL t < k := by dsimp only [rowL]; omega
    have hL_rec : rowL (t + 1) = max (rowL t + 1) (2 * t) := by dsimp only [rowL]; omega
    rw [stateN_succ, stateN_succ]
    have hprev_ag : AgreeCyc k x y ((lo + k - 1) + k - rowL t) ((len + 4) + rowL t + 3 * t - 1) := by
      intro d hd
      have hshift : ((lo + k - 1) + k - rowL t + d) % k =
          (lo + k - rowL (t + 1) + (d + (rowL (t + 1) - (rowL t + 1)))) % k := by
        have h1 : (lo + k - 1) + k - rowL t + d =
            (lo + k - rowL (t + 1) + (d + (rowL (t + 1) - (rowL t + 1)))) + k := by omega
        rw [h1, Nat.add_mod_right]
      rw [hshift]
      exact h (d + (rowL (t + 1) - (rowL t + 1))) (by omega)
    have hprev := ih ht' (lo + k - 1) (len + 4) hprev_ag
    have hchimix := agreeCyc_chi_mix (gap := 1) (by omega : 0 < 1) (by omega : 1 < k)
      (stateN_lt c false x hrow t) (stateN_lt c false y hrow t) lo len hprev
    have hrot_ag : AgreeCyc k x y (lo + k - (2 * t) % k) len := by
      rw [Nat.mod_eq_of_lt (by omega : 2 * t < k)]
      intro d hd
      have hshift : (lo + k - 2 * t + d) % k =
          (lo + k - rowL (t + 1) + (d + (rowL (t + 1) - 2 * t))) % k := by
        congr 1
        omega
      rw [hshift]
      exact h (d + (rowL (t + 1) - 2 * t)) (by omega)
    have hrot := agreeCyc_rot hkpos hx hy (2 * t) lo len hrot_ag
    intro d hd
    dsimp only [stepK]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel]
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor]
    rw [hchimix d hd, hrot d hd]

def colL (t : Nat) : Nat := max (2 * t + 3) (3 * t + 1)

lemma col_stateN_congr {k r : Nat} (hr : 4 ≤ r) (hk : 5 * r - 2 ≤ k)
    (c : Nat → Fin (2 ^ k)) {col x y : Nat}
    (hcol : col < 2 ^ k) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    ∀ t ≤ r, ∀ lo len : Nat,
      AgreeCyc k x y (lo + k - colL t) (len + colL t + 4 * t - 3) →
      AgreeCyc k (stateN k r c true x col t) (stateN k r c true y col t) lo len := by
  have hkpos : 0 < k := by omega
  intro t
  induction t with
  | zero =>
    intro _ lo len h
    rw [stateN_zero, stateN_zero]
    intro d hd
    simp only [↓reduceIte]
    rw [Nat.testBit_xor, Nat.testBit_xor]
    have hrot : (rotK k 3 x).testBit ((lo + d) % k) = (rotK k 3 y).testBit ((lo + d) % k) := by
      have h1 : AgreeCyc k x y (lo + k - 3 % k) len := by
        rw [Nat.mod_eq_of_lt (by omega : 3 < k)]
        intro e he
        exact h e (by dsimp only [colL]; omega)
      exact agreeCyc_rot hkpos hx hy 3 lo len h1 d hd
    rw [hrot]
  | succ t ih =>
    intro ht lo len h
    have ht' : t ≤ r := by omega
    have hL_lt : colL (t + 1) < k := by dsimp only [colL]; omega
    have hLt_lt : colL t < k := by dsimp only [colL]; omega
    have hL_rec : colL (t + 1) = max (colL t + 2) (3 * t + 4) := by dsimp only [colL]; omega
    rw [stateN_succ, stateN_succ]
    have hprev_ag : AgreeCyc k x y ((lo + k - 2) + k - colL t) ((len + 6) + colL t + 4 * t - 3) := by
      intro d hd
      have hshift : ((lo + k - 2) + k - colL t + d) % k =
          (lo + k - colL (t + 1) + (d + (colL (t + 1) - (colL t + 2)))) % k := by
        have h1 : (lo + k - 2) + k - colL t + d =
            (lo + k - colL (t + 1) + (d + (colL (t + 1) - (colL t + 2)))) + k := by omega
        rw [h1, Nat.add_mod_right]
      rw [hshift]
      exact h (d + (colL (t + 1) - (colL t + 2))) (by omega)
    have hprev := ih ht' (lo + k - 2) (len + 6) hprev_ag
    have hchimix := agreeCyc_chi_mix (gap := 2) (by omega : 0 < 2) (by omega : 2 < k)
      (stateN_lt c true x hcol t) (stateN_lt c true y hcol t) lo len hprev
    have hrot_ag : AgreeCyc k x y (lo + k - (3 * (t + 1) + 1) % k) len := by
      rw [Nat.mod_eq_of_lt (by omega : 3 * (t + 1) + 1 < k)]
      intro d hd
      have hshift : (lo + k - (3 * (t + 1) + 1) + d) % k =
          (lo + k - colL (t + 1) + (d + (colL (t + 1) - (3 * (t + 1) + 1)))) % k := by
        congr 1
        omega
      rw [hshift]
      exact h (d + (colL (t + 1) - (3 * (t + 1) + 1))) (by omega)
    have hrot := agreeCyc_rot hkpos hx hy (3 * (t + 1) + 1) lo len hrot_ag
    intro d hd
    dsimp only [stepK]
    simp only [↓reduceIte]
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor]
    rw [hchimix d hd, hrot d hd]

def sensorState (k r : Nat) (col : Bool) (w name : Nat) (c : Fin r → Fin (2^k)) : Nat :=
  let b := if col then 2 else 1
  (List.finRange r).foldl (fun x j =>
    chiK k (x ^^^ rotK k b x ^^^ rotK k (k-b) x) ^^^
      rotK k (if col then 3*(j.val+1)+1 else 2*j.val) w ^^^ (c j).val)
    (rotK k (if col then 3 else 1) w ^^^ name)

def delay (r : Nat) (col : Bool) := if col then 3*r+1 else 2*r-2
def reach (r : Nat) (col : Bool) := if col then 7*r-2 else 5*r-3

private def schedule (k r : Nat) (col : Bool) (c : Fin r → Fin (2^k)) (i : Nat) : Fin (2^k) :=
  let j := (if col then i-r else i)-1
  if h : j < r then c ⟨j,h⟩ else 0

theorem sensorState_eq (k r : Nat) (col : Bool) (w name : Nat) (c : Fin r → Fin (2^k)) :
    sensorState k r col w name c = stateN k r (schedule k r col c) col w name r := by
  have hmap : (List.finRange r).map Fin.val = List.range r := by
    apply List.ext_getElem <;> simp
  unfold sensorState stateN
  rw [← hmap,List.foldl_map]
  cases col <;> simp [stepK, mixK, schedule]

theorem sensor_window {k r d : Nat} (hr : 4 ≤ r) (hk : d < k) (col : Bool)
    (valid : reach r col ≤ d) (name x y : Fin (2^k)) (c : Fin r → Fin (2^k)) (pos : Nat)
    (hxy : AgreeCyc k x.val y.val pos (reach r col + 1)) :
    (sensorState k r col x.val name.val c).testBit ((pos+delay r col)%k) =
    (sensorState k r col y.val name.val c).testBit ((pos+delay r col)%k) := by
  rw [sensorState_eq,sensorState_eq]
  have hs (s : Nat) :
      AgreeCyc k x.val y.val (pos+s+k-s) (reach r col+1) := by
    intro i hi
    have e : pos+s+k-s+i = pos+i+k := by omega
    simpa only [e, Nat.add_mod_right] using hxy i hi
  cases col with
  | false =>
    have hL : rowL r = 2*r-2 := by unfold rowL; omega
    have he : 1+rowL r+3*r-1 = reach r false+1 := by simp [reach,hL]; omega
    have h := row_stateN_congr hr (by simp [reach] at valid; omega) (schedule k r false c)
      name.isLt x.isLt y.isLt r (by rfl) (pos+rowL r) 1 (by simpa only [he] using hs (rowL r))
    simpa [delay,hL] using h 0 (by decide)
  | true =>
    have hL : colL r = 3*r+1 := by unfold colL; omega
    have he : 1+colL r+4*r-3 = reach r true+1 := by simp [reach,hL]; omega
    have h := col_stateN_congr hr (by simp [reach] at valid; omega) (schedule k r true c)
      name.isLt x.isLt y.isLt r (by rfl) (pos+colL r) 1 (by simpa only [he] using hs (colL r))
    simpa [delay,hL] using h 0 (by decide)

def windowBits (k d pos w : Nat) : Fin (d+1) → Bool :=
  fun i => w.testBit ((pos+i.val)%k)

theorem exists_sensor_table {k r d : Nat} (hr : 4 ≤ r) (hk : d < k) (col : Bool)
    (valid : reach r col ≤ d) (name : Fin (2^k)) (c : Fin r → Fin (2^k)) (pos : Nat) :
    ∃ table : (Fin (d+1) → Bool) → Bool, ∀ w : Fin (2^k),
      table (windowBits k d pos w.val) =
        (sensorState k r col w.val name.val c).testBit ((pos+delay r col)%k) := by
  classical
  let f (w : Fin (2^k)) := (sensorState k r col w.val name.val c).testBit ((pos+delay r col)%k)
  refine ⟨fun b => decide (∃ w : Fin (2^k), windowBits k d pos w.val = b ∧ f w = true), ?_⟩
  intro w
  change decide (∃ z : Fin (2^k), windowBits k d pos z.val = windowBits k d pos w.val ∧ f z = true) = f w
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨z,hz,hf⟩
    have hv := sensor_window hr hk col valid name z w c pos (by
      intro i hi
      exact congrFun hz ⟨i,by omega⟩)
    exact hv.symm.trans hf
  · exact fun h => ⟨w,rfl,h⟩

def representative (k d pos : Nat) (a : Fin (2^(d+1))) : Fin (2^k) :=
  ⟨rotK k pos a.val, rotK_lt pos a.val⟩

theorem representative_bit {k d : Nat} (hk : d<k) (pos : Nat) (a : Fin (2^(d+1))) (i : Fin (d+1)) :
    (representative k d pos a).val.testBit ((pos+i.val)%k) = a.val.testBit i.val := by
  have hkp : 0<k := by omega
  have ia : i.val<k := by omega
  have hlt : a.val<2^k := lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) (by omega))
  unfold representative
  rw [rotK_testBit hkp hlt pos _ (Nat.mod_lt _ hkp)]
  have hpi : pos % k<k := Nat.mod_lt _ hkp
  have hm : ((pos+i.val)%k+k-pos % k)%k = i.val := by
    have e : (pos+i.val)%k+k-pos % k = (pos+i.val)%k+(k-pos % k) := by omega
    rw [e,Nat.mod_add_mod,Nat.add_assoc]
    rw [← Nat.mod_add_mod pos k (i.val + (k-pos % k))]
    rw [show pos % k + (i.val+(k-pos % k)) = i.val+k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt ia]
  rw [hm]

theorem sensor_at_representative {k r d : Nat} (hr : 4 ≤ r) (hk : d<k) (col : Bool)
    (valid : reach r col ≤ d) (name w : Fin (2^k)) (c : Fin r → Fin (2^k)) (pos : Nat)
    (a : Fin (2^(d+1)))
    (h : ∀ i : Fin (d+1), w.val.testBit ((pos+i.val)%k) = a.val.testBit i.val) :
    (sensorState k r col w.val name.val c).testBit ((pos+delay r col)%k) =
    (sensorState k r col (representative k d pos a).val name.val c).testBit ((pos+delay r col)%k) := by
  apply sensor_window hr hk col valid name w (representative k d pos a) c pos
  intro i hi
  let j : Fin (d+1) := ⟨i, by omega⟩
  exact (h j).trans (representative_bit hk pos a j).symm

theorem table_entries (d : Nat) : Fintype.card (Fin (d+1) → Bool) = 2*(2^d) := by
  simp [pow_succ,Nat.mul_comm]

end PEqualNP.Outside.L_meta_33676_aux.Windows

namespace PEqualNP.Outside.L_meta_33676_aux

def cyclicWindow {p n width : Nat} (hp : 0 < p) (hn : 0 < n) (offset : Nat)
    (t : Fin p × Fin width) : Fin (p*n) :=
  ⟨(offset + (t.1.val*n + t.2.val)) % (p*n), Nat.mod_lt _ (Nat.mul_pos hp hn)⟩

theorem cyclicWindow_injective {p n width : Nat} (hp : 0 < p) (hn : 0 < n)
    (hwidth : width ≤ n) (offset : Nat) :
    Function.Injective (cyclicWindow (width:=width) hp hn offset) := by
  intro a b h
  have bound (t : Fin p × Fin width) : t.1.val*n + t.2.val < p*n := by
    calc
      t.1.val*n + t.2.val < (t.1.val+1)*n := by
        rw [Nat.add_mul, Nat.one_mul]
        exact Nat.add_lt_add_left (t.2.isLt.trans_le hwidth) _
      _ ≤ p*n := Nat.mul_le_mul_right _ t.1.isLt
  have hm : offset+(a.1.val*n+a.2.val) ≡ offset+(b.1.val*n+b.2.val) [MOD p*n] :=
    congrArg Fin.val h
  have eq := (hm.add_left_cancel' offset).eq_of_lt_of_lt (bound a) (bound b)
  have div (t : Fin p × Fin width) : (t.1.val*n+t.2.val)/n = t.1.val := by
    rw [Nat.mul_comm t.1.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt (t.2.isLt.trans_le hwidth), Nat.add_zero]
  have first := congrArg (fun x : Nat => x/n) eq
  change (a.1.val*n+a.2.val)/n=(b.1.val*n+b.2.val)/n at first
  rw [div a, div b] at first
  apply Prod.ext (Fin.ext first)
  apply Fin.ext
  rw [first] at eq
  exact Nat.add_left_cancel eq

theorem programWindowBits {p n width : Nat} (hp : 0 < p) (hn : 0 < n)
    (hw : width ≤ n) (offset : Nat) (requested : Fin p → Fin width → Bool) :
    ∃ input : Fin (p*n) → Bool,
      ∀ a j, input (cyclicWindow hp hn offset (a,j)) = requested a j := by
  classical
  let w := cyclicWindow (width:=width) hp hn offset
  let input := fun i : Fin (p*n) =>
    if h : ∃ v, w v = i then requested h.choose.1 h.choose.2 else false
  refine ⟨input, ?_⟩
  intro a j
  have h : ∃ v, w v = w (a,j) := ⟨(a,j),rfl⟩
  have hv : h.choose = (a,j) := cyclicWindow_injective hp hn hw offset h.choose_spec
  change (if h : ∃ v, w v = w (a,j) then requested h.choose.1 h.choose.2 else false) = _
  rw [dif_pos h,hv]

end PEqualNP.Outside.L_meta_33676_aux

namespace PEqualNP.Outside.L_meta_33676_aux.ShiftCriterion

open Translation PEqualNP.Outside.L_meta_33676_aux.Windows

def blockNext {p : ℕ} (hp : 0 < p) : Fin p ≃ Fin p where
  toFun i := ⟨if i.val+1<p then i.val+1 else 0, by split <;> omega⟩
  invFun i := ⟨if i.val=0 then p-1 else i.val-1, by split <;> omega⟩
  left_inv i := by
    apply Fin.ext
    change (if (if i.val+1<p then i.val+1 else 0)=0 then p-1 else (if i.val+1<p then i.val+1 else 0)-1) = i.val
    by_cases h : i.val+1<p
    · simp [h]
    · simp [h]; omega
  right_inv i := by
    apply Fin.ext
    change (if (if i.val=0 then p-1 else i.val-1)+1<p then (if i.val=0 then p-1 else i.val-1)+1 else 0) = i.val
    by_cases h : i.val=0
    · simp [h]; omega
    · have hh : i.val-1+1=i.val := by omega
      simp [h,hh,i.isLt]

def windowMap {p n width : ℕ} (hp : 0<p) (hn : 0<n) (i : Fin n) (a : Fin p) :
    Vector (p*n) →ₗ[F₂] Vector width where
  toFun v j := v (cyclicWindow hp hn i.val (a,j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem window_surj {p n width : ℕ} (hp : 0<p) (hn : 0<n) (hw : width ≤ n) (i : Fin n) :
    Function.Surjective (fun v a => windowMap (width := width) hp hn i a v) := by
  intro z
  obtain ⟨b,hb⟩ := programWindowBits hp hn hw i.val (fun a j => decide (z a j = 1))
  refine ⟨fun i => if b i then 1 else 0,?_⟩
  funext a j
  change (if b (cyclicWindow hp hn i.val (a,j)) then 1 else 0) = z a j
  rw [hb]
  have two : ∀ t : F₂, t=0 ∨ t=1 := by decide
  rcases two (z a j) with h|h <;> simp [h]

theorem inverse_index {k s : ℕ} (hs : s<k) (i : Fin k) :
    ((rotIndex hs).symm i).val = (i.val+s)%k := by
  change (if k-s ≤ i.val then i.val-(k-s) else i.val+s) = _
  split_ifs with hc
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]

theorem window_rotate {p n width : ℕ} (hp : 0<p) (hn : 0<n) (hk : n<p*n)
    (i : Fin n) (a : Fin p) (v : Vector (p*n)) :
    windowMap (width:=width) hp hn i (blockNext hp a) (rotateLinear hk v) = windowMap hp hn i a v := by
  funext j
  let old := cyclicWindow hp hn i.val (a,j)
  have eq : cyclicWindow hp hn i.val (blockNext hp a,j) = (rotIndex hk).symm old := by
    apply Fin.ext
    rw [inverse_index]
    change (i.val + ((if a.val+1<p then a.val+1 else 0)*n+j.val))%(p*n) =
      (((i.val+(a.val*n+j.val))%(p*n))+n)%(p*n)
    rw [Nat.mod_add_mod]
    by_cases ha : a.val+1 < p
    · simp only [ha,ite_true,Nat.add_mul,Nat.one_mul]
      congr 1; omega
    · have hlast : a.val+1 = p := by omega
      have hprod : a.val*n+n = p*n := by simpa [Nat.add_mul] using congrArg (fun b : ℕ => b*n) hlast
      simp only [ha, ite_false, Nat.zero_mul, Nat.zero_add]
      rw [show i.val+(a.val*n+j.val)+n = i.val+j.val+(p*n) by omega, Nat.add_mod_right]
  change v (rotIndex hk (cyclicWindow hp hn i.val (blockNext hp a,j))) = v old
  rw [eq,(rotIndex hk).apply_symm_apply]

def relativeMap {p n width : ℕ} (hp : 0<p) (hn : 0<n) (i : Fin n) (a : Fin p) :
    Vector (p*n) →ₗ[F₂] Vector width :=
  windowMap hp hn i (blockNext hp a) - windowMap hp hn i a

def residueSum {p n width : ℕ} (hp : 0<p) (hn : 0<n)
    (T : Fin n → Fin p → Vector width → F₂) (v : Vector (p*n)) (i : Fin n) : F₂ :=
  ∑ a, T i a (windowMap hp hn i a v)

theorem sum_good_iff {p n width : ℕ} (hp : 0<p) (hn : 0<n) (hk : n<p*n) (hw : width≤n)
    (T : Fin n → Fin p → Vector width → F₂) (g : Vector (p*n)) :
    Good (residueSum hp hn T) (rotateLinear hk) g ↔ combinedGood T
      (fun i a => T i (blockNext hp a)) (relativeMap hp hn) g := by
  have reindex (i : Fin n) (v : Vector (p*n)) :
      residueSum hp hn T (rotateLinear hk v + g) i =
        ∑ a, T i (blockNext hp a) (windowMap hp hn i a v + windowMap hp hn i (blockNext hp a) g) := by
    unfold residueSum
    rw [← Equiv.sum_comp (blockNext hp)]
    apply Finset.sum_congr rfl
    intro a _
    rw [map_add,window_rotate]
  have localId (i : Fin n) (a : Fin p) (v : Vector (p*n)) :
      windowMap (width:=width) hp hn i a (v+g) + relativeMap hp hn i a g =
      windowMap hp hn i a v + windowMap hp hn i (blockNext hp a) g := by
    rw [map_add]
    simp only [relativeMap,LinearMap.sub_apply]
    abel
  constructor
  · intro h i z
    obtain ⟨v,hv⟩ := window_surj hp hn hw i z
    have e := congrFun (h (v-g)) i
    rw [reindex,sub_add_cancel] at e
    have hi (a : Fin p) : windowMap hp hn i a (v-g) + windowMap hp hn i (blockNext hp a) g =
        z a + relativeMap hp hn i a g := by
      rw [← localId,sub_add_cancel,← hv]
    simpa only [residueSum,hi,← hv] using e
  · intro h v
    funext i
    have e := h i (fun a => windowMap hp hn i a (v+g))
    rw [reindex]
    simpa only [localId,residueSum] using e

def scalar (b : Bool) : F₂ := if b then 1 else 0

theorem scalar_xor (a b : Bool) : scalar (xor a b) = scalar a + scalar b := by
  cases a <;> cases b <;> decide

theorem scalar_inj : Function.Injective scalar := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact False.elim (by revert h; decide)

theorem fold_xor {I : Type*} (l : List I) (f : I → Bool) (b : Bool) :
    scalar (l.foldl (fun t i => xor t (f i)) b) = scalar b + (l.map (fun i => scalar (f i))).sum := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih,scalar_xor,add_assoc]

def rawSensor {p n r : ℕ} (hp : 0<p) (hn : 0<n) (nr nc : Word (p*n))
    (cr cc : Fin r → Word (p*n)) (bank : Fin (p*n) → Bool) (i : Fin n) (a : Fin p)
    (w : ℕ) : Bool :=
  let pos := a.val*n+i.val
  let col := bank ⟨pos % (p*n),Nat.mod_lt _ (Nat.mul_pos hp hn)⟩
  (sensorState (p*n) r col w (if col then nc.val else nr.val) (if col then cc else cr)).testBit
    ((pos+delay r col)%(p*n))

def rawReport {p n r : ℕ} (hp : 0<p) (hn : 0<n) (nr nc : Word (p*n))
    (cr cc : Fin r → Word (p*n)) (bank : Fin (p*n) → Bool) (w : ℕ) (i : Fin n) : Bool :=
  (List.finRange p).foldl (fun b a => xor b (rawSensor hp hn nr nc cr cc bank i a w)) false

theorem existsReportTables {p n r d : ℕ} (hp : 0<p) (hn : 0<n) (hk : d<p*n)
    (hr : 4≤r) (nr nc : Word (p*n)) (cr cc : Fin r → Word (p*n)) (bank : Fin (p*n) → Bool)
    (hvalid : ∀ i, reach r (bank i) ≤ d) :
    ∃ T : Fin n → Fin p → Vector (d+1) → F₂, ∀ (w : Word (p*n)) i,
      scalar (rawReport hp hn nr nc cr cc bank w.val i) = residueSum hp hn T (encode w) i := by
  classical
  have table (i : Fin n) (a : Fin p) :
      ∃ t : (Fin (d+1) → Bool) → Bool, ∀ w : Word (p*n),
        t (windowBits (p*n) d (a.val*n+i.val) w.val) = rawSensor hp hn nr nc cr cc bank i a w.val := by
    let col := bank ⟨(a.val*n+i.val)%(p*n),Nat.mod_lt _ (Nat.mul_pos hp hn)⟩
    have ht := exists_sensor_table hr hk col (hvalid _) (if col then nc else nr) (if col then cc else cr) (a.val*n+i.val)
    have he : ((if col then nc else nr) : Word (p*n)).val = (if col then nc.val else nr.val) := by split <;> rfl
    rw [he] at ht
    exact ht
  choose T hT using table
  refine ⟨fun i a x => scalar (T i a (fun j => decide (x j=1))),?_⟩
  intro w i
  unfold rawReport
  rw [fold_xor]
  change 0 + _ = _
  rw [zero_add]
  unfold residueSum
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  apply Finset.sum_congr rfl
  intro a _
  rw [← hT i a w]
  congr 2
  funext j
  change w.val.testBit ((a.val*n+i.val+j.val)%(p*n)) =
    decide ((if w.val.testBit ((i.val+(a.val*n+j.val))%(p*n)) then (1:F₂) else 0) = 1)
  rw [show a.val*n+i.val+j.val = i.val+(a.val*n+j.val) by omega]
  cases w.val.testBit ((i.val+(a.val*n+j.val))%(p*n)) <;> decide

theorem good_with_tables {p n d : ℕ} (hp : 0<p) (hn : 0<n) (hk : n<p*n) (hd : d<n)
    (H : ℕ → Fin n → Bool) (T : Fin n → Fin p → Vector (d+1) → F₂)
    (hT : ∀ (w : Word (p*n)) i, scalar (H w.val i) = residueSum hp hn T (encode w) i) (g : Word (p*n)) :
    rawGood H n g ↔ combinedGood T (fun i a => T i (blockNext hp a)) (relativeMap hp hn) (encode g) := by
  let F := fun w i => scalar (H w i)
  have eqview : view F = residueSum hp hn T := by
    funext x i
    obtain ⟨w,rfl⟩ := (wordEquiv _).surjective x
    unfold view
    rw [Equiv.symm_apply_apply]
    change scalar (H w.val i) = residueSum hp hn T (encode w) i
    exact hT w i
  have he : rawGood H n g ↔ rawGood F n g := by
    constructor
    · intro h w
      funext i
      exact congrArg scalar (congrFun (h w) i)
    · intro h w
      funext i
      exact scalar_inj (congrFun (h w) i)
  rw [he,rawGood_iff F hk,eqview,sum_good_iff hp hn hk (by omega)]

theorem actualGood_iff {p n r d : ℕ} (hp : 0<p) (hn : 0<n) (hk : n<p*n) (hd : d<n)
    (hr : 4≤r) (nr nc : Word (p*n)) (cr cc : Fin r → Word (p*n)) (bank : Fin (p*n) → Bool)
    (hvalid : ∀ i, reach r (bank i) ≤ d) :
    ∃ T : Fin n → Fin p → Vector (d+1) → F₂, ∀ g : Word (p*n),
      rawGood (rawReport hp hn nr nc cr cc bank) n g ↔
        ∃! b : Fin n → Fin p → F₂, equations T (fun i a => T i (blockNext hp a))
            (relativeMap hp hn) (encode g,b) := by
  obtain ⟨T,hT⟩ := existsReportTables hp hn (hd.trans hk) hr nr nc cr cc bank hvalid
  exact ⟨T, fun g => (good_with_tables hp hn hk hd _ T hT g).trans (combined_iff _ _ _ _)⟩

section Matrix

variable {I J U V : Type*} [Fintype I]
  [AddCommGroup U] [Module F₂ U] [AddCommGroup V] [Module F₂ V]

abbrev EqIndex (I J U : Type*) [AddCommGroup U] [Module F₂ U] :=
  J ⊕ (J × I × Module.Dual F₂ (U × F₂) × F₂)

abbrev Source (I J V : Type*) := V × (J → I → F₂)

def coeffLabel (j : J) (i : I) : Source I J V →ₗ[F₂] F₂ where
  toFun v := v.2 j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coeffShift (T : J → I → V →ₗ[F₂] U) (j : J) (i : I) :
    Source I J V →ₗ[F₂] U := (T j i).comp (LinearMap.fst F₂ V _)

noncomputable def matrixRow (F G : J → I → U → F₂) (T : J → I → V →ₗ[F₂] U) :
    EqIndex I J U → Source I J V →ₗ[F₂] F₂ := by
  classical
  exact fun
    | .inl j => ∑ i, coeffLabel j i
    | .inr (j,i,ℓ,c) =>
      if validEquation (F j i) (G j i) ℓ c then ℓ.comp ((coeffShift T j i).prod (coeffLabel j i)) else 0

noncomputable def matrixRhs (F G : J → I → U → F₂) : EqIndex I J U → F₂ := by
  classical
  exact fun
    | .inl _ => 0
    | .inr (j,i,ℓ,c) => if validEquation (F j i) (G j i) ℓ c then c else 0

noncomputable def shiftMatrix (F G : J → I → U → F₂) (T : J → I → V →ₗ[F₂] U) :
    Source I J V →ₗ[F₂] (EqIndex I J U → F₂) := LinearMap.pi (matrixRow F G T)

theorem matrix_iff (F G : J → I → U → F₂) (T : J → I → V →ₗ[F₂] U) (v : Source I J V) :
    equations F G T v ↔ shiftMatrix F G T v = matrixRhs F G := by
  classical
  constructor
  · intro h
    funext ix
    rcases ix with j|⟨j,i,ℓ,c⟩
    · simpa [shiftMatrix,matrixRow,matrixRhs,coeffLabel,LinearMap.sum_apply] using (h j).1
    · by_cases ha : validEquation (F j i) (G j i) ℓ c
      · simpa [shiftMatrix,matrixRow,matrixRhs,ha,coeffShift,coeffLabel] using (h j).2 i ℓ c ha
      · simp [shiftMatrix,matrixRow,matrixRhs,ha]
  · intro h j
    constructor
    · have e := congrFun h (.inl j)
      simpa [shiftMatrix,matrixRow,matrixRhs,coeffLabel,LinearMap.sum_apply] using e
    · intro i ℓ c ha
      have e := congrFun h (.inr (j,i,ℓ,c))
      simpa [shiftMatrix,matrixRow,matrixRhs,ha,coeffShift,coeffLabel] using e

end Matrix

local instance (d : ℕ) : Finite (Module.Dual F₂ (Vector (d+1) × F₂)) :=
  Finite.of_injective (fun f : Module.Dual F₂ (Vector (d+1) × F₂) => (f : (Vector (d+1) × F₂) → F₂))
    DFunLike.coe_injective

theorem index_card (p n d : ℕ) :
    Nat.card (EqIndex (Fin p) (Fin n) (Vector (d+1))) = n + 8*(p*n)*2^d := by
  rw [Nat.card_sum,Nat.card_prod,Nat.card_prod,Nat.card_prod,
      local_normals_card,Nat.card_zmod,Nat.card_fin,Nat.card_fin]
  ring

theorem input_finrank (p n : ℕ) :
    Module.finrank F₂ (Source (Fin p) (Fin n) (Vector (p*n))) = 2*(p*n) := by
  rw [Module.finrank_prod,Module.finrank_fin_fun,Module.finrank_pi_fintype]
  simp; ring

theorem actualGood_matrix {p n r d : ℕ} (hp : 0<p) (hn : 0<n) (hk : n<p*n) (hd : d<n)
    (hr : 4≤r) (nr nc : Word (p*n)) (cr cc : Fin r → Word (p*n)) (bank : Fin (p*n) → Bool)
    (hvalid : ∀ i, reach r (bank i) ≤ d) :
    ∃ T : Fin n → Fin p → Vector (d+1) → F₂, ∀ g : Word (p*n),
      rawGood (rawReport hp hn nr nc cr cc bank) n g ↔
        ∃! b : Fin n → Fin p → F₂,
          shiftMatrix T (fun i a => T i (blockNext hp a)) (relativeMap hp hn) (encode g,b) =
            matrixRhs T (fun i a => T i (blockNext hp a)) := by
  obtain ⟨T,hT⟩ := actualGood_iff hp hn hk hd hr nr nc cr cc bank hvalid
  refine ⟨T,fun g => ?_⟩
  simpa only [← matrix_iff] using hT g

abbrev VarIndex (p n : ℕ) := Fin (p*n) ⊕ (Fin n × Fin p)

noncomputable def varOrder (p n : ℕ) : VarIndex p n ≃ Fin (2*(p*n)) :=
  Fintype.equivFinOfCardEq (by simp [VarIndex]; ring)

noncomputable def rowOrder (p n d : ℕ) :
    EqIndex (Fin p) (Fin n) (Vector (d+1)) ≃ Fin (n+8*(p*n)*2^d) := by
  classical
  letI := Fintype.ofFinite (EqIndex (Fin p) (Fin n) (Vector (d+1)))
  exact Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card.symm.trans (index_card p n d))

noncomputable def unflatten (p n : ℕ) :
    Vector (2*(p*n)) →ₗ[F₂] Source (Fin p) (Fin n) (Vector (p*n)) where
  toFun f := (fun i => f (varOrder p n (.inl i)),fun j i => f (varOrder p n (.inr (j,i))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def flatten {p n : ℕ} (v : Source (Fin p) (Fin n) (Vector (p*n))) :
    Vector (2*(p*n)) := fun i => Sum.elim v.1 (fun ji => v.2 ji.1 ji.2) ((varOrder p n).symm i)

@[simp] theorem unflatten_flatten {p n : ℕ} (v : Source (Fin p) (Fin n) (Vector (p*n))) :
    unflatten p n (flatten v) = v := by
  refine Prod.ext ?_ ?_
  · funext i
    simp [unflatten,flatten]
  · funext j i
    simp [unflatten,flatten]

@[simp] theorem flatten_unflatten {p n : ℕ} (v : Vector (2*(p*n))) :
    flatten (unflatten p n v) = v := by
  funext i
  obtain ⟨t,rfl⟩ := (varOrder p n).surjective i
  cases t <;> simp [flatten,unflatten]

abbrev Rows (m n : ℕ) := Fin m → Fin n → F₂

noncomputable def flatRows {p n d : ℕ} (F G : Fin n → Fin p → Vector (d+1) → F₂)
    (T : Fin n → Fin p → Vector (p*n) →ₗ[F₂] Vector (d+1)) :
    Rows (n+8*(p*n)*2^d) (2*(p*n)) := fun i j =>
  shiftMatrix F G T (unflatten p n (Pi.single j 1)) ((rowOrder p n d).symm i)

noncomputable def flatRhs {p n d : ℕ} (F G : Fin n → Fin p → Vector (d+1) → F₂) :
    Vector (n+8*(p*n)*2^d) := fun i => matrixRhs F G ((rowOrder p n d).symm i)

theorem lin_dot {N : ℕ} (L : Vector N →ₗ[F₂] F₂) (x : Vector N) :
    (∑ j, L (Pi.single j 1) * x j) = L x := by
  have e : (∑ j, x j • (Pi.single j 1 : Vector N)) = x := by
    funext i
    simp [Finset.sum_apply,Pi.single_apply, Pi.smul_apply,smul_eq_mul]
  calc
    (∑ j, L (Pi.single j 1) * x j) = L (∑ j, x j • (Pi.single j 1 : Vector N)) := by
      simp [map_sum, map_smul,smul_eq_mul,mul_comm]
    _ = _ := congrArg L e

theorem flatRows_eval {p n d : ℕ} (F G : Fin n → Fin p → Vector (d+1) → F₂)
    (T : Fin n → Fin p → Vector (p*n) →ₗ[F₂] Vector (d+1))
    (x : Vector (2*(p*n))) (i : Fin (n+8*(p*n)*2^d)) :
    (∑ j, flatRows F G T i j * x j) =
      shiftMatrix F G T (unflatten p n x) ((rowOrder p n d).symm i) :=
  lin_dot (((LinearMap.proj ((rowOrder p n d).symm i)).comp (shiftMatrix F G T)).comp (unflatten p n)) x

theorem equations_iff_rows {p n d : ℕ} (F G : Fin n → Fin p → Vector (d+1) → F₂)
    (T : Fin n → Fin p → Vector (p*n) →ₗ[F₂] Vector (d+1)) (v : Source (Fin p) (Fin n) (Vector (p*n))) :
    equations F G T v ↔ ∀ i, (∑ j, flatRows F G T i j * flatten v j) = flatRhs F G i := by
  rw [matrix_iff]
  simp only [flatRows_eval,unflatten_flatten,flatRhs]
  constructor
  · intro e i
    exact congrFun e _
  · intro h
    funext i
    simpa using h (rowOrder p n d i)

noncomputable def flatEquiv (p n : ℕ) : Source (Fin p) (Fin n) (Vector (p*n)) ≃ Vector (2*(p*n)) where
  toFun := flatten
  invFun := unflatten p n
  left_inv := unflatten_flatten
  right_inv := flatten_unflatten

def rowSatisfied {m q : ℕ} (A : Rows m q) (b : Vector m) (x : Vector q) : Prop :=
  ∀ i, (∑ j, A i j * x j) = b i

noncomputable def solutionEquiv {p n d : ℕ} (hp : 0<p) (hn : 0<n) (hk : n<p*n) (hd : d<n)
    (H : ℕ → Fin n → Bool) (T : Fin n → Fin p → Vector (d+1) → F₂)
    (hT : ∀ (w : Word (p*n)) i, scalar (H w.val i) = residueSum hp hn T (encode w) i) :
    {g : Word (p*n) // rawGood H n g} ≃
    {x // rowSatisfied (flatRows T (fun i a => T i (blockNext hp a)) (relativeMap hp hn))
      (flatRhs T (fun i a => T i (blockNext hp a))) x} :=
  let G := fun i a => T i (blockNext hp a)
  let R := relativeMap (width:=d+1) hp hn
  let e₁ := (wordEquiv (p*n)).subtypeEquiv (p:=rawGood H n) (q:=combinedGood T G R)
      (good_with_tables hp hn hk hd H T hT)
  let e₂ := equationsEquiv T G R
  let e₃ := (flatEquiv p n).subtypeEquiv (p:=equations T G R) (q:=rowSatisfied (flatRows T G R) (flatRhs T G))
      (equations_iff_rows T G R)
  e₁.trans (e₂.trans e₃)

theorem solution_projects {p n d : ℕ} (hp : 0<p) (hn : 0<n) (hk : n<p*n) (hd : d<n)
    (H : ℕ → Fin n → Bool) (T : Fin n → Fin p → Vector (d+1) → F₂)
    (hT : ∀ (w : Word (p*n)) i, scalar (H w.val i) = residueSum hp hn T (encode w) i)
    (g : {w : Word (p*n) // rawGood H n w}) :
    (unflatten p n (solutionEquiv hp hn hk hd H T hT g).val).1 = encode g.val := by
  change (unflatten p n (flatten (_, _))).1 = _
  rw [unflatten_flatten]
  rfl

theorem filtered_solution_count {p n d : ℕ} (hp : 0<p) (hn : 0<n) (hk : n<p*n) (hd : d<n)
    (H : ℕ → Fin n → Bool) (T : Fin n → Fin p → Vector (d+1) → F₂)
    (hT : ∀ (w : Word (p*n)) i, scalar (H w.val i) = residueSum hp hn T (encode w) i)
    (P : Vector (p*n) → Prop) :
    Nat.card {g : Word (p*n) // rawGood H n g ∧ P (encode g)} =
    Nat.card {x // rowSatisfied (flatRows T (fun i a => T i (blockNext hp a)) (relativeMap hp hn))
      (flatRhs T (fun i a => T i (blockNext hp a))) x ∧ P (unflatten p n x).1} := by
  let e := solutionEquiv hp hn hk hd H T hT
  have h (g : {g : Word (p*n) // rawGood H n g}) :
      P (encode g.val) ↔ P (unflatten p n (e g).val).1 := by
    rw [solution_projects hp hn hk hd H T hT g]
  exact Nat.card_congr <| (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans
    ((e.subtypeEquiv h).trans (Equiv.subtypeSubtypeEquivSubtypeInter _ _))

end PEqualNP.Outside.L_meta_33676_aux.ShiftCriterion

namespace PEqualNP.Outside.L_meta_33676_aux.SensorCircuit
namespace Builder
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

abbrev BitFn (n : Nat) := (Fin n → Bool) → Bool

structure Bank (n : Nat) where
  gates : List Gate
  fan : FanInTwo ⟨gates, 0⟩
  back : ReadsBack n ⟨gates, 0⟩

namespace Bank
variable {n : Nat}

def val (B : Bank n) (i : Nat) (x : Fin n → Bool) : Bool :=
  ((⟨B.gates, 0⟩ : Circuit).wires (List.ofFn x)).getD i false

def Has (B : Bank n) (f : BitFn n) : Prop :=
  ∃ i < n + B.gates.length, ∀ x, B.val i x = f x

def Ext (B D : Bank n) : Prop := ∀ {f}, B.Has f → D.Has f

def Grow (B : Bank n) (cost : Nat) (p : Bank n → Prop) : Prop :=
  ∃ D, B.Ext D ∧ D.gates.length ≤ B.gates.length + cost ∧ p D

def empty (n : Nat) : Bank n := ⟨[], by simp [FanInTwo], by simp [ReadsBack]⟩

lemma ext_refl (B : Bank n) : B.Ext B := fun h => h

lemma ext_trans {A B C : Bank n} (h1 : A.Ext B) (h2 : B.Ext C) : A.Ext C :=
  fun h => h2 (h1 h)

lemma input (i : Fin n) : (empty n).Has (fun x => x i) := by
  refine ⟨i, i.isLt, ?_⟩
  intro x
  simp [val, empty, Circuit.wires, List.getD_eq_getElem?_getD, i.isLt]

lemma Grow.pure (B : Bank n) {p : Bank n → Prop} (h : p B) : B.Grow 0 p :=
  ⟨B, fun h => h, by omega, h⟩

lemma Grow.weaken {B : Bank n} {p q : Bank n → Prop} {a b : Nat} (h : B.Grow a p)
    (hab : a ≤ b) (hpq : ∀ D, p D → q D) : B.Grow b q := by
  obtain ⟨D, e, c, t⟩ := h
  exact ⟨D, e, by omega, hpq D t⟩

lemma Grow.bind {B : Bank n} {p q : Bank n → Prop} {a b : Nat} (h : B.Grow a p)
    (f : ∀ D, B.Ext D → p D → D.Grow b q) : B.Grow (a + b) q := by
  obtain ⟨D, e, c, t⟩ := h
  obtain ⟨E, e', c', t'⟩ := f D e t
  exact ⟨E, fun h => e' (e h), by omega, t'⟩

private lemma wireLen (gs : List Gate) (x : List Bool) :
    ((⟨gs, 0⟩ : Circuit).wires x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simp [Circuit.wires, List.foldl_append] at ih ⊢
    omega

private lemma gate (B : Bank n) (g : Gate)
    (ok : g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (back : ∀ i ∈ g.inputs, i < n + B.gates.length) :
    B.Grow 1 (fun D => D.Has (fun x => g.op.eval (g.inputs.map fun i => B.val i x))) := by
  let D : Bank n :=
    { gates := B.gates ++ [g]
      fan := by
        intro g' h
        change g' ∈ B.gates ++ [g] at h
        rcases List.mem_append.mp h with h | h
        · exact B.fan g' h
        · simpa using (show g' = g from List.mem_singleton.mp h) ▸ ok
      back := by
        intro j hj w hw
        change j < (B.gates ++ [g]).length at hj
        change w ∈ ((B.gates ++ [g]).getD j _).inputs at hw
        by_cases h : j < B.gates.length
        · rw [List.getD_append _ _ _ _ h] at hw
          exact B.back j h w hw
        · have he : j = B.gates.length := by simp at hj; omega
          subst j
          simp at hw
          exact back w hw }
  have hv (x : Fin n → Bool) :
      ((⟨D.gates, 0⟩ : Circuit).wires (List.ofFn x)) =
        ((⟨B.gates, 0⟩ : Circuit).wires (List.ofFn x)) ++
        [g.op.eval (g.inputs.map fun i => B.val i x)] := by
    simp [D, val, Circuit.wires, List.foldl_append]
  have hl (x : Fin n → Bool) :
      ((⟨B.gates, 0⟩ : Circuit).wires (List.ofFn x)).length = n + B.gates.length := by
    simp [wireLen]
  refine ⟨D, ?_, by simp [D], n + B.gates.length, by simp [D], ?_⟩
  · intro f hf
    obtain ⟨i, hi, he⟩ := hf
    refine ⟨i, by simp [D]; omega, ?_⟩
    intro x
    unfold val
    rw [hv, List.getD_append _ _ _ _ (by rw [hl]; exact hi)]
    exact he x
  · intro x
    unfold val
    rw [hv, ← hl x]
    simp [val, List.getD_eq_getElem?_getD]

lemma const (B : Bank n) (b : Bool) : B.Grow 1 (fun D => D.Has (fun _ => b)) := by
  cases b with
  | false => simpa [GateOp.eval] using B.gate ⟨.or, []⟩ (by simp) (by simp)
  | true => simpa [GateOp.eval] using B.gate ⟨.and, []⟩ (by simp) (by simp)

lemma inv {B : Bank n} {f : BitFn n} (a : B.Has f) :
    B.Grow 1 (fun D => D.Has (fun x => !(f x))) := by
  obtain ⟨i, hi, he⟩ := a
  simpa [GateOp.eval, he] using B.gate ⟨.not, [i]⟩ (by simp) (by simpa using hi)

lemma meet {B : Bank n} {f g : BitFn n} (a : B.Has f) (b : B.Has g) :
    B.Grow 1 (fun D => D.Has (fun x => f x && g x)) := by
  obtain ⟨i, hi, he⟩ := a
  obtain ⟨j, hj, hf⟩ := b
  simpa [GateOp.eval, he, hf] using B.gate ⟨.and, [i, j]⟩ (by simp) (by simp [hi, hj])

lemma join {B : Bank n} {f g : BitFn n} (a : B.Has f) (b : B.Has g) :
    B.Grow 1 (fun D => D.Has (fun x => f x || g x)) := by
  obtain ⟨i, hi, he⟩ := a
  obtain ⟨j, hj, hf⟩ := b
  simpa [GateOp.eval, he, hf] using B.gate ⟨.or, [i, j]⟩ (by simp) (by simp [hi, hj])

lemma xor2 {B : Bank n} {f g : BitFn n} (a : B.Has f) (b : B.Has g) :
    B.Grow 4 (fun D => D.Has (fun x => xor (f x) (g x))) := by
  apply (meet a b).bind (b := 3)
  intro C e hab
  apply (inv hab).bind (b := 2)
  intro D e' hn
  apply (join (e' (e a)) (e' (e b))).bind (b := 1)
  intro E e'' hor
  apply (meet hor (e'' hn)).weaken (le_refl _)
  intro F h
  have eq (x) : ((f x || g x) && !(f x && g x)) = xor (f x) (g x) := by
    cases f x <;> cases g x <;> decide
  simpa only [eq] using h

lemma mux {B : Bank n} {c f g : BitFn n} (hc : B.Has c) (hf : B.Has f) (hg : B.Has g) :
    B.Grow 4 (fun D => D.Has (fun x => if c x then f x else g x)) := by
  apply (inv hc).bind (b := 3)
  intro C e hnc
  apply (meet (e hc) (e hf)).bind (b := 2)
  intro D e' h1
  apply (meet (e' hnc) (e' (e hg))).bind (b := 1)
  intro E e'' h2
  apply (join (e'' h1) h2).weaken (le_refl _)
  intro F h
  have eq (x) : ((c x && f x) || (!c x && g x)) = (if c x then f x else g x) := by
    cases c x <;> cases f x <;> cases g x <;> decide
  simpa only [eq] using h

lemma foldGrow {α σ : Type} (B : Bank n) (l : List α) (s0 : σ)
    (step : σ → α → σ) (Inv : σ → Bank n → Prop) (cost : Nat)
    (h0 : Inv s0 B)
    (hstep : ∀ D, B.Ext D → ∀ s a, a ∈ l → Inv s D → D.Grow cost (Inv (step s a))) :
    B.Grow (l.length * cost) (Inv (l.foldl step s0)) := by
  induction l generalizing B s0 with
  | nil => simpa using Grow.pure B h0
  | cons a l ih =>
    have h1 : B.Grow cost (Inv (step s0 a)) := hstep B (fun h => h) s0 a (by simp) h0
    have h2 := h1.bind (b := l.length * cost) (fun D e hInv =>
      ih D (step s0 a) hInv (fun E e' s x hx =>
        hstep E (fun h => e' (e h)) s x (by simp [hx])))
    simpa [List.foldl_cons, Nat.succ_mul, Nat.add_comm] using h2

lemma collect {α : Type} (B : Bank n) (l : List α) (f : α → BitFn n) (cost : Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i ∈ l, D.Grow cost (fun E => E.Has (f i))) :
    B.Grow (l.length * cost) (fun D => ∀ i ∈ l, D.Has (f i)) := by
  induction l with
  | nil => simpa using (Grow.pure B (p := fun D => ∀ i ∈ ([] : List α), D.Has (f i)) (by simp))
  | cons a l ih =>
    have t := ih (fun D e i hi => emit D e i (by simp [hi]))
    have out := t.bind (b := cost) (q := fun E => ∀ i ∈ a :: l, E.Has (f i)) (by
      intro D e haveL
      obtain ⟨E, e', c', ha⟩ := emit D e a (by simp)
      refine ⟨E, e', c', ?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | h
      · exact ha
      · exact e' (haveL i h))
    simpa [Nat.succ_mul] using out

lemma collectFin (B : Bank n) (m : Nat) (f : Fin m → BitFn n) (cost : Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i, D.Grow cost (fun E => E.Has (f i))) :
    B.Grow (m * cost) (fun D => ∀ i, D.Has (f i)) := by
  simpa using B.collect (List.finRange m) f cost (fun D e i _ => emit D e i)

end Bank
end Builder
end PEqualNP.Outside.L_meta_33676_aux.SensorCircuit

namespace PEqualNP.Outside.L_meta_33676_aux.SensorCircuit.Pivot.Word
def rot (k s word : Nat) : Nat :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def stepBit (k word i : Nat) : Bool :=
  xor (word.testBit i) (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))

def step (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc i =>
    acc ||| ((xor (word.testBit i)
      (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0

def roundStep (k : Nat) (col : Bool) (w : Nat) (x : Nat) (cj : Nat) (j : Nat) : Nat :=
  let g := if col then 2 else 1
  step k (x ^^^ rot k g x ^^^ rot k (k - g) x) ^^^
    rot k (if col then 3 * (j + 1) + 1 else 2 * j) w ^^^ cj

def state (k r : Nat) (col : Bool) (w u : Nat) (c : Fin r → Fin (2 ^ k)) : Nat :=
  let g := if col then 2 else 1
  (List.finRange r).foldl (fun x j =>
    step k (x ^^^ rot k g x ^^^ rot k (k - g) x) ^^^
      rot k (if col then 3 * (j.val + 1) + 1 else 2 * j.val) w ^^^ (c j).val)
    (rot k (if col then 3 else 1) w ^^^ u)

lemma rot_lt (k s word : Nat) : rot k s word < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma xor_lt {k a b : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : a ^^^ b < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  have hpow := Nat.pow_le_pow_right Nat.zero_lt_two hj
  simp [Nat.testBit_xor, Nat.testBit_lt_two_pow (ha.trans_le hpow),
    Nat.testBit_lt_two_pow (hb.trans_le hpow)]

lemma testBit_rot {k s word b : Nat} (hw : word < 2 ^ k) (hb : b < k) :
    (rot k s word).testBit b = word.testBit ((b + k - s % k) % k) := by
  have hk : 0 < k := by omega
  have hs : s % k < k := Nat.mod_lt _ hk
  simp only [rot, Nat.testBit_mod_two_pow, hb, decide_true, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : s % k ≤ b
  · have hz : word.testBit (k - s % k + b) = false :=
      Nat.testBit_lt_two_pow (hw.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
    have he : (b + k - s % k) % k = b - s % k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    simp [h, hz, he]
  · have he : (b + k - s % k) % k = k - s % k + b := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    simp [h, he]

lemma testBit_foldl_or (p : Nat → Bool) (xs : List Nat) (acc i : Nat) :
    (xs.foldl (fun a j => a ||| ((p j).toNat <<< j)) acc).testBit i =
      (acc.testBit i || (decide (i ∈ xs) && p i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons j xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hji : j = i
    · subst j; cases p i <;> simp
    · by_cases hle : j ≤ i
      · have hsub : 1 ≤ i - j := by omega
        have hbt : (p j).toNat.testBit (i - j) = false := by
          cases p j
          · simp
          · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega : 1 < 2 ^ 1)
              (Nat.pow_le_pow_right Nat.zero_lt_two hsub))
        simp [hle, hbt, Ne.symm hji]
      · simp [hle, Ne.symm hji]

lemma testBit_step_all (k word b : Nat) :
    (step k word).testBit b = (decide (b < k) && stepBit k word b) := by
  unfold step stepBit; rw [testBit_foldl_or]; simp

lemma testBit_step {k word b : Nat} (hb : b < k) :
    (step k word).testBit b = stepBit k word b := by
  simp [testBit_step_all, hb]

lemma step_lt (k word : Nat) : step k word < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro b hb
  simp [testBit_step_all, Nat.not_lt_of_ge hb]

end PEqualNP.Outside.L_meta_33676_aux.SensorCircuit.Pivot.Word

namespace PEqualNP.Outside.L_meta_33676_aux.SensorCircuit.SensorBuilder

open Builder Pivot.Word

private lemma foldl_apply' {α β γ : Type} (op : γ → α → β → γ) (init : β → γ)
    (l : List α) (x : β) :
    (l.foldl (fun acc a y => op (acc y) a y) init) x =
      l.foldl (fun acc a => op acc a x) (init x) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => simp only [List.foldl_cons, ih]

private lemma has_congr {n : Nat} {B : Bank n} {f g : BitFn n}
    (h : B.Has f) (heq : ∀ x, f x = g x) : B.Has g := by
  obtain ⟨i, hi, hf⟩ := h; exact ⟨i, hi, fun x => (hf x).trans (heq x)⟩

theorem grow_stateBits {n k r : Nat} (hk : 0 < k) (col : Bool) (B : Bank n)
    (w u : (Fin n → Bool) → Fin (2 ^ k)) (c : (Fin n → Bool) → Fin r → Fin (2 ^ k))
    (hw : ∀ i : Fin k, B.Has (fun x => (w x).val.testBit i.val))
    (hu : ∀ i : Fin k, B.Has (fun x => (u x).val.testBit i.val))
    (hc : ∀ (j : Fin r) (i : Fin k), B.Has (fun x => (c x j).val.testBit i.val)) :
    B.Grow (k * 4 + r * (k * 22))
      (fun D => ∀ i : Fin k, D.Has (fun x => (state k r col (w x).val (u x).val (c x)).testBit i.val)) := by
  let g := if col then 2 else 1
  let s0 : (Fin n → Bool) → Nat := fun x => rot k (if col then 3 else 1) (w x).val ^^^ (u x).val
  have hs0_lt : ∀ x, s0 x < 2 ^ k := fun x => xor_lt (rot_lt k _ _) (u x).isLt
  have hinit : B.Grow (k * 4) (fun D => ∀ i : Fin k, D.Has (fun x => (s0 x).testBit i.val)) := by
    apply B.collectFin k (fun i x => (s0 x).testBit i.val) 4
    intro D e i
    let idx : Fin k := ⟨(i.val + k - (if col then 3 else 1) % k) % k, Nat.mod_lt _ hk⟩
    apply (Bank.xor2 (e (hw idx)) (e (hu i))).weaken (le_refl _)
    intro E hE
    exact has_congr hE (fun x => by
      simp only [s0, Nat.testBit_xor, testBit_rot (w x).isLt i.isLt, idx])
  apply hinit.bind (b := r * (k * 22))
  intro D0 e0 hD0
  let stepFn : ((Fin n → Bool) → Nat) → Fin r → (Fin n → Bool) → Nat :=
    fun cur j x => step k (cur x ^^^ rot k g (cur x) ^^^ rot k (k - g) (cur x)) ^^^
      rot k (if col then 3 * (j.val + 1) + 1 else 2 * j.val) (w x).val ^^^ (c x j).val
  have hfold := Bank.foldGrow D0 (List.finRange r) s0 stepFn
    (fun cur D => (∀ x, cur x < 2 ^ k) ∧ ∀ i : Fin k, D.Has (fun x => (cur x).testBit i.val))
    (k * 22) ⟨hs0_lt, hD0⟩ (by
      intro D e cur j _ ⟨hcur_lt, hcur⟩
      let t1 : (Fin n → Bool) → Nat := fun x => cur x ^^^ rot k g (cur x)
      let t2 : (Fin n → Bool) → Nat := fun x => t1 x ^^^ rot k (k - g) (cur x)
      let t3 : (Fin n → Bool) → Nat := fun x => step k (t2 x)
      let t4 : (Fin n → Bool) → Nat := fun x => t3 x ^^^ rot k (if col then 3 * (j.val + 1) + 1 else 2 * j.val) (w x).val
      obtain ⟨E1, e1, c1, h1⟩ := D.collectFin k (fun i x => (t1 x).testBit i.val) 4 (fun E e' i => by
        let idx : Fin k := ⟨(i.val + k - g % k) % k, Nat.mod_lt _ hk⟩
        apply (Bank.xor2 (e' (hcur i)) (e' (hcur idx))).weaken (le_refl _)
        intro F hF
        exact has_congr hF (fun x => by simp only [t1, Nat.testBit_xor, testBit_rot (hcur_lt x) i.isLt, idx]))
      obtain ⟨E2, e2, c2, h2⟩ := E1.collectFin k (fun i x => (t2 x).testBit i.val) 4 (fun E e' i => by
        let idx : Fin k := ⟨(i.val + k - (k - g) % k) % k, Nat.mod_lt _ hk⟩
        apply (Bank.xor2 (e' (h1 i)) (e' (e1 (hcur idx)))).weaken (le_refl _)
        intro F hF
        exact has_congr hF (fun x => by simp only [t2, Nat.testBit_xor, testBit_rot (hcur_lt x) i.isLt, idx]))
      obtain ⟨E3, e3, c3, h3⟩ := E2.collectFin k (fun i x => (t3 x).testBit i.val) 6 (fun E e' i => by
        let i1 : Fin k := ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩
        let i2 : Fin k := ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩
        obtain ⟨F1, ef1, cf1, hnot⟩ := Bank.inv (e' (h2 i1))
        obtain ⟨F2, ef2, cf2, hand⟩ := Bank.meet hnot (ef1 (e' (h2 i2)))
        obtain ⟨F3, ef3, cf3, hxr⟩ := Bank.xor2 (ef2 (ef1 (e' (h2 i)))) hand
        exact ⟨F3, Bank.ext_trans ef1 (Bank.ext_trans ef2 ef3), by omega,
          has_congr hxr (fun x => by simp only [t3, testBit_step i.isLt, stepBit, i1, i2])⟩)
      obtain ⟨E4, e4, c4, h4⟩ := E3.collectFin k (fun i x => (t4 x).testBit i.val) 4 (fun E e' i => by
        let idx : Fin k := ⟨(i.val + k - (if col then 3 * (j.val + 1) + 1 else 2 * j.val) % k) % k, Nat.mod_lt _ hk⟩
        apply (Bank.xor2 (e' (h3 i)) (e' (e3 (e2 (e1 (e (e0 (hw idx)))))))).weaken (le_refl _)
        intro F hF
        exact has_congr hF (fun x => by simp only [t4, Nat.testBit_xor, testBit_rot (w x).isLt i.isLt, idx]))
      obtain ⟨E5, e5, c5, h5⟩ := E4.collectFin k (fun i x => (stepFn cur j x).testBit i.val) 4 (fun E e' i => by
        apply (Bank.xor2 (e' (h4 i)) (e' (e4 (e3 (e2 (e1 (e (e0 (hc j i))))))))).weaken (le_refl _)
        intro F hF
        exact has_congr hF (fun x => by simp only [stepFn, t4, t3, t2, t1, Nat.testBit_xor]))
      exact ⟨E5, Bank.ext_trans e1 (Bank.ext_trans e2 (Bank.ext_trans e3 (Bank.ext_trans e4 e5))),
        by omega, fun x => xor_lt (xor_lt (step_lt k _) (rot_lt k _ _)) (c x j).isLt, h5⟩)
  refine hfold.weaken (by simp) (fun D hD i => ?_)
  exact has_congr (hD.2 i) (fun x => by
    have hfl := foldl_apply' (fun acc j x => stepFn (fun _ => acc) j x) s0 (List.finRange r) x
    have hfeq : (List.finRange r).foldl stepFn s0 x = state k r col (w x).val (u x).val (c x) := by
      have : (List.finRange r).foldl stepFn s0 =
          (List.finRange r).foldl (fun acc j y => stepFn (fun _ => acc y) j y) s0 := by
        rfl
      rw [this, hfl]; rfl
    rw [hfeq])

theorem localSensor {n k r : ℕ} (hk : 0 < k) (B : Bank n)
    (w : Fin (2^k)) (nr nc : (Fin n → Bool) → Fin (2^k))
    (cr cc : (Fin n → Bool) → Fin r → Fin (2^k))
    (bank : BitFn n) (rowBit colBit : Fin k)
    (hw : ∀ i : Fin k, B.Has (fun _ => w.val.testBit i.val))
    (hr : ∀ i : Fin k, B.Has (fun x => (nr x).val.testBit i.val))
    (hc : ∀ i : Fin k, B.Has (fun x => (nc x).val.testBit i.val))
    (hsr : ∀ (j : Fin r) (i : Fin k), B.Has (fun x => (cr x j).val.testBit i.val))
    (hsc : ∀ (j : Fin r) (i : Fin k), B.Has (fun x => (cc x j).val.testBit i.val))
    (hb : B.Has bank) :
    B.Grow ((k*4+r*(k*22)) + ((k*4+r*(k*22)) + 4))
      (fun D => D.Has (fun x =>
        (state k r (bank x) w.val (if bank x then (nc x).val else (nr x).val)
          (if bank x then cc x else cr x)).testBit (if bank x then colBit.val else rowBit.val))) := by
  apply (grow_stateBits hk false B (fun _ => w) nr cr hw hr hsr).bind
  intro R eR rows
  apply (grow_stateBits hk true R (fun _ => w) nc cc (fun i => eR (hw i))
    (fun i => eR (hc i)) (fun j i => eR (hsc j i))).bind
  intro T eT cols
  apply (Bank.mux (eT (eR hb)) (cols colBit) (eT (rows rowBit))).weaken (le_refl _)
  intro D wire
  apply has_congr wire
  intro x
  cases bank x <;> simp

theorem collectType {n : ℕ} {A : Type} [Fintype A] (B : Bank n)
    (f : A → BitFn n) (cost : ℕ)
    (emit : ∀ D : Bank n, B.Ext D → ∀ a, D.Grow cost (fun E => E.Has (f a))) :
    B.Grow (Fintype.card A * cost) (fun D => ∀ a, D.Has (f a)) := by
  classical
  let e := Fintype.equivFin A
  apply (B.collectFin (Fintype.card A) (fun j => f (e.symm j)) cost
    (fun D h j => emit D h (e.symm j))).weaken (le_refl _)
  intro D h a
  simpa using h (e a)

end PEqualNP.Outside.L_meta_33676_aux.SensorCircuit.SensorBuilder

namespace PEqualNP.Outside.L_meta_33676_aux.SensorCircuit.Layout
open Builder
abbrev Env (n : ℕ) := Fin n → Bool
def HasWord {n : ℕ} (B : Bank n) (w : ℕ) (f : Env n → ℕ) := ∀ i : Fin w, B.Has (fun x => (f x).testBit i.val)

def bits (w a : ℕ) := (List.range w).map (fun i => a.testBit i)
def sched {r k : ℕ} (c : Fin r → Fin (2^k)) :=
  (List.finRange r).flatMap (fun j => bits k (c j).val)

@[simp] theorem bits_length (w a : ℕ) : (bits w a).length=w := by simp [bits]

private lemma flat_length {α β : Type} (l : List α) (f : α → List β) (k : ℕ)
    (hf : ∀ a, (f a).length=k) : (l.flatMap f).length=l.length*k := by
  induction l with
  | nil => simp
  | cons a l ih => simp [hf,ih,Nat.succ_mul,Nat.add_comm]

@[simp] theorem sched_length {r k : ℕ} (c : Fin r → Fin (2^k)) :
    (sched c).length = r*k := by
  unfold sched
  rw [flat_length _ _ k (fun _ => bits_length _ _), List.length_finRange]

def raw {n : ℕ} (x : Env n) (i : ℕ) := (List.ofFn x).getD i false

def readWord {n : ℕ} (w base : ℕ) (x : Env n) : Fin (2^w) :=
  ⟨(List.range w).foldl (fun z i => z ||| ((raw x (base+i)).toNat <<< i)) 0, by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    rw [Pivot.Word.testBit_foldl_or]
    simp [Nat.not_lt_of_ge hi]⟩

theorem readWord_bit {n : ℕ} (w base : ℕ) (x : Env n) (i : Fin w) :
    (readWord w base x).val.testBit i.val = raw x (base+i.val) := by
  simp only [readWord, Pivot.Word.testBit_foldl_or, List.mem_range, i.isLt,
    decide_true, Bool.true_and, Nat.zero_testBit, Bool.false_or]

theorem empty_raw {n : ℕ} (B : Bank n) (ext : (Bank.empty n).Ext B)
    (hz : B.Has (fun _ => false)) (i : ℕ) : B.Has (fun x => raw x i) := by
  by_cases hi : i < n
  · have h := ext (Bank.input ⟨i,hi⟩)
    simpa [raw,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,hi] using h
  · simpa [raw,List.getD_eq_getElem?_getD,hi] using hz

theorem readWord_wires {n : ℕ} (B : Bank n) (ext : (Bank.empty n).Ext B)
    (hz : B.Has (fun _ => false)) (w base : ℕ) :
    HasWord B w (fun x => (readWord w base x).val) := by
  intro i
  simpa only [readWord_bit] using empty_raw B ext hz (base+i.val)

private theorem get_bounded (pre field post : List Bool) (j : ℕ) (hj : j < field.length) :
    (pre++field++post).getD (pre.length+j) false = field.getD j false := by
  rw [List.getD_append _ _ _ _ (by simp; omega),
    List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

private theorem bits_get (w x j : ℕ) (hj : j<w) : (bits w x).getD j false=x.testBit j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hj)]
  simp [bits]

private lemma get_flat {α β : Type} (l : List α) (f : α → List β) (k : ℕ)
    (hf : ∀ z, (f z).length=k) {j i : ℕ} (hj : j<l.length) (hi : i<k)
    (hidx : j*k+i<(l.flatMap f).length) :
    (l.flatMap f)[j*k+i]'hidx = (f (l[j]'hj))[i]'(by rw [hf]; exact hi) := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a l ih =>
    cases j with
    | zero =>
      simp only [Nat.zero_mul,Nat.zero_add,List.flatMap_cons,List.getElem_cons_zero]
      rw [List.getElem_append_left (by rw [hf]; exact hi)]
    | succ j =>
      simp only [List.flatMap_cons,List.getElem_cons_succ]
      have hh : (f a).length ≤ (j+1)*k+i := by rw [hf, Nat.succ_mul]; omega
      rw [List.getElem_append_right hh]
      have he : (j+1)*k+i-(f a).length=j*k+i := by rw [hf,Nat.succ_mul]; omega
      simp only [he]
      exact ih (by simpa using hj) _

private theorem sched_get {k r : ℕ} (c : Fin r → Fin (2^k)) (j : Fin r) (i : Fin k) :
    (sched c).getD (j.val*k+i.val) false = (c j).val.testBit i.val := by
  have hidx : j.val*k+i.val < (sched c).length := by
    have h := Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.isLt)
    rw [Nat.succ_mul] at h
    rw [sched_length]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]
  change ((List.finRange r).flatMap (fun j => bits k (c j).val))[j.val*k+i.val] = _
  rw [get_flat _ _ k (fun _ => bits_length _ _) (by simp [j.isLt]) i.isLt hidx]
  simp [bits,List.getElem_finRange]

private theorem word_ext {w : ℕ} (a b : Fin (2^w))
    (h : ∀ i : Fin w, a.val.testBit i.val = b.val.testBit i.val) : a=b := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < w
  · exact h ⟨i,hi⟩
  · rw [Nat.testBit_lt_two_pow (a.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))),
      Nat.testBit_lt_two_pow (b.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))]

end PEqualNP.Outside.L_meta_33676_aux.SensorCircuit.Layout
namespace PEqualNP.Outside.L_meta_33676_aux.SensorCircuit.Layout
open Builder Pivot.Word

def inLen (k r trailing : ℕ) := 3*k + 2*r*k + trailing

def cfg {k r : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k)) (bank : Fin k → Bool) :=
  bits k nr.val ++ bits k nc.val ++ sched cr ++ sched cc ++ List.ofFn bank

@[simp] theorem cfg_length {k r : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (bank : Fin k → Bool) : (cfg nr nc cr cc bank).length = 3*k+2*r*k := by
  simp [cfg]
  ring

def encoded {k r trailing : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (bank : Fin k → Bool) (extra : List Bool) (_ : extra.length = trailing) :
    Env (inLen k r trailing) := fun i => (cfg nr nc cr cc bank ++ extra).getD i.val false

theorem ofFn_encoded {k r trailing : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (bank : Fin k → Bool) (extra : List Bool) (ht : extra.length = trailing) :
    List.ofFn (encoded nr nc cr cc bank extra ht) = cfg nr nc cr cc bank ++ extra := by
  apply List.ext_getElem
  · rw [List.length_ofFn, List.length_append, cfg_length, ht]
    rfl
  · intro i h₁ h₂
    simp only [List.getElem_ofFn, encoded, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h₂, Option.getD_some]

def rowName {n : ℕ} (k : ℕ) (x : Env n) := readWord k 0 x
def colName {n : ℕ} (k : ℕ) (x : Env n) := readWord k k x
def rowSchedule {n r : ℕ} (k : ℕ) (x : Env n) (j : Fin r) := readWord k (2*k+j.val*k) x
def colSchedule {n r : ℕ} (k : ℕ) (x : Env n) (j : Fin r) := readWord k (2*k+r*k+j.val*k) x
def bankBit {n k : ℕ} (r : ℕ) (x : Env n) (j : Fin k) := raw x (2*k+2*r*k+j.val)

theorem decode_encoded {k r trailing : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (bank : Fin k → Bool) (extra : List Bool) (ht : extra.length = trailing) :
    let x := encoded nr nc cr cc bank extra ht
    rowName k x=nr ∧ colName k x=nc ∧ rowSchedule k x=cr ∧ colSchedule k x=cc ∧ bankBit r x=bank := by
  let x := encoded nr nc cr cc bank extra ht
  have pick (pre field post : List Bool) (a : ℕ)
      (hlist : cfg nr nc cr cc bank ++ extra = pre++field++post) (hsize : pre.length=a)
      (i : ℕ) (hi : i<field.length) : raw x (a+i)=field.getD i false := by
    unfold x raw
    rw [ofFn_encoded,hlist,← hsize]
    exact get_bounded pre field post i hi
  have get0 (j : ℕ) (hj : j < k) : raw x (0+j) = (bits k nr.val).getD j false := by
    exact pick [] _ (bits k nc.val ++ sched cr ++ sched cc ++ List.ofFn bank ++ extra) 0
      (by simp [cfg,List.append_assoc]) (by simp) j (by simpa using hj)
  have get1 (j : ℕ) (hj : j < k) : raw x (k+j) = (bits k nc.val).getD j false := by
    exact pick (bits k nr.val) _ (sched cr ++ sched cc ++ List.ofFn bank ++ extra) k
      (by simp [cfg,List.append_assoc]) (by simp) j (by simpa using hj)
  have get2 (j : ℕ) (hj : j < r*k) : raw x (2*k+j) = (sched cr).getD j false := by
    exact pick (bits k nr.val ++ bits k nc.val) _ (sched cc ++ List.ofFn bank ++ extra) (2*k)
      (by simp [cfg,List.append_assoc]) (by simp; ring) j (by simpa using hj)
  have get3 (j : ℕ) (hj : j < r*k) : raw x (2*k+r*k+j) = (sched cc).getD j false := by
    exact pick (bits k nr.val ++ bits k nc.val ++ sched cr) _ (List.ofFn bank ++ extra) (2*k+r*k)
      (by simp [cfg,List.append_assoc]) (by simp; ring) j (by simpa using hj)
  have get4 (j : ℕ) (hj : j < k) : raw x (2*k+2*r*k+j) = (List.ofFn bank).getD j false := by
    exact pick (bits k nr.val ++ bits k nc.val ++ sched cr ++ sched cc) _ extra (2*k+2*r*k)
      (by simp [cfg,List.append_assoc]) (by simp; ring) j (by simpa using hj)
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply word_ext; intro i
    exact (readWord_bit k _ x i).trans ((get0 i.val i.isLt).trans (bits_get k _ _ i.isLt))
  · apply word_ext; intro i
    exact (readWord_bit k _ x i).trans ((get1 i.val i.isLt).trans (bits_get k _ _ i.isLt))
  · funext j
    apply word_ext; intro i
    have hb : j.val*k+i.val < r*k := by
      have H := Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.isLt)
      rw [Nat.succ_mul] at H; omega
    simpa only [rowSchedule,readWord_bit,Nat.add_assoc] using (get2 _ hb).trans (sched_get cr j i)
  · funext j
    apply word_ext; intro i
    have hb : j.val*k+i.val < r*k := by
      have H := Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.isLt)
      rw [Nat.succ_mul] at H; omega
    simpa only [colSchedule,readWord_bit,Nat.add_assoc] using (get3 _ hb).trans (sched_get cc j i)
  · funext j
    simpa [bankBit,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,j.isLt] using get4 j.val j.isLt

def rep (k d : ℕ) (i : Fin k) (a : Fin (2^(d+1))) : Fin (2^k) :=
  ⟨rot k i.val a.val, rot_lt _ _ _⟩

def tableSignal {k n : ℕ} (r d : ℕ) (i : Fin k) (a : Fin (2^(d+1))) (x : Env n) : Bool :=
  let col := bankBit r x i
  (state k r col (rep k d i a).val (if col then (colName k x).val else (rowName k x).val)
    (if col then colSchedule k x else rowSchedule k x)).testBit
    (if col then (i.val+(3*r+1))%k else (i.val+(2*r-2))%k)

def unitCost (k r : ℕ) := (k*4+r*(k*22)) + ((k*4+r*(k*22)) + 4)

theorem buildSensorBank {k : ℕ} (hk : 0<k) (r d trailing : ℕ) :
    (Bank.empty (inLen k r trailing)).Grow (2 + k*2^(d+1)*unitCost k r)
      (fun D => ∀ (i : Fin k) (a : Fin (2^(d+1))), D.Has (tableSignal r d i a)) := by
  let n := inLen k r trailing
  obtain ⟨C,hC,kC,hz⟩ := (Bank.empty n).const false
  obtain ⟨B,hB,kB,ho⟩ := C.const true
  have hconst (b : Bool) : B.Has (fun _ => b) := by cases b; exact hB hz; exact ho
  have ext : (Bank.empty n).Ext B := Bank.ext_trans hC hB
  obtain ⟨D,hD,kD,all⟩ := SensorBuilder.collectType B
    (fun z : Fin k × Fin (2^(d+1)) => tableSignal r d z.1 z.2) (unitCost k r) (by
      intro E e z
      exact SensorBuilder.localSensor hk E (rep k d z.1 z.2) (rowName k) (colName k)
        (rowSchedule k) (colSchedule k) (fun x => bankBit r x z.1)
        ⟨(z.1.val+(2*r-2))%k, Nat.mod_lt _ hk⟩ ⟨(z.1.val+(3*r+1))%k, Nat.mod_lt _ hk⟩
        (fun j => e (hconst _)) (fun j => e (readWord_wires B ext (hB hz) k 0 j))
        (fun j => e (readWord_wires B ext (hB hz) k k j))
        (fun j i => e (readWord_wires B ext (hB hz) k (2*k+j.val*k) i))
        (fun j i => e (readWord_wires B ext (hB hz) k (2*k+r*k+j.val*k) i))
        (e (empty_raw B ext (hB hz) _)))
  refine ⟨D,Bank.ext_trans ext hD, ?_, fun i a => all (i,a)⟩
  simp only [Fintype.card_prod,Fintype.card_fin] at kD
  dsimp [Bank.empty] at kC ⊢
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem sharedSensorCircuit {k : ℕ} (hk : 0<k) (r d trailing : ℕ) :
    ∃ (gs : List Gate) (out : Fin k → Fin (2^(d+1)) → ℕ),
      FanInTwo (⟨gs,0⟩ : Circuit) ∧ ReadsBack (inLen k r trailing) ⟨gs,0⟩ ∧
      gs.length ≤ 2 + k*(2*2^d)*(2*(4*k+22*r*k)+4) ∧
      (∀ i a, out i a < inLen k r trailing + gs.length) ∧
      ∀ (i : Fin k) (a : Fin (2^(d+1))) (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
        (bank : Fin k → Bool) (extra : List Bool), extra.length = trailing →
        (⟨gs,out i a⟩ : Circuit).eval (cfg nr nc cr cc bank ++ extra) =
          let col := bank i
          (state k r col (rep k d i a).val (if col then nc.val else nr.val)
            (if col then cc else cr)).testBit ((i.val+(if col then 3*r+1 else 2*r-2))%k) := by
  classical
  obtain ⟨D,_,cost,hs⟩ := buildSensorBank hk r d trailing
  choose out hbound hval using hs
  refine ⟨D.gates,out,D.fan,D.back,?_,hbound,?_⟩
  · simpa [Bank.empty,unitCost,pow_succ,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc,
      Nat.add_assoc,two_mul] using cost
  · intro i a nr nc cr cc bank extra ht
    let x := encoded nr nc cr cc bank extra ht
    obtain ⟨hnr,hnc,hcr,hcc,hbank⟩ := decode_encoded nr nc cr cc bank extra ht
    have ans := hval i a x
    change (⟨D.gates,out i a⟩ : Circuit).eval (List.ofFn x) = tableSignal r d i a x at ans
    rw [show List.ofFn x = _ from ofFn_encoded nr nc cr cc bank extra ht] at ans
    rw [ans]
    unfold tableSignal
    change rowName k x = nr at hnr
    change colName k x = nc at hnc
    change rowSchedule k x = cr at hcr
    change colSchedule k x = cc at hcc
    change bankBit r x = bank at hbank
    rw [hbank,hnr,hnc,hcr,hcc]
    cases bank i <;> rfl

end PEqualNP.Outside.L_meta_33676_aux.SensorCircuit.Layout

namespace PEqualNP.Outside.L_meta_33676_aux.Elimination

abbrev Bit := ZMod 2
abbrev Rows (m n : Nat) := Fin m → Fin n → Bit
abbrev Bits (n : Nat) := Fin n → Bit

def dot {n : Nat} (a x : Bits n) : Bit := ∑ j, a j * x j

def solution {m n : Nat} (a : Rows m n) (b : Bits m) (x : Bits n) : Prop :=
  ∀ i, dot (a i) x = b i

def tailRows {m n : Nat} (a : Rows m (n+1)) : Rows m n :=
  fun i j => a i j.succ

def reducedRows {m n : Nat} (a : Rows m (n+1)) (v : Fin m) : Rows m n :=
  fun i j => a i j.succ - a i 0 * a v j.succ

def reducedRhs {m n : Nat} (a : Rows m (n+1)) (b : Bits m) (v : Fin m) : Bits m :=
  fun i => b i - a i 0 * b v

def recover {m n : Nat} (a : Rows m (n+1)) (b : Bits m) (v : Fin m) (x : Bits n) : Bit :=
  b v - dot (tailRows a v) x

theorem dot_cons {m n : Nat} (a : Rows m (n+1)) (i : Fin m) (u : Bit) (x : Bits n) :
    dot (a i) (Fin.cons u x) = a i 0 * u + dot (tailRows a i) x := by
  simp [dot, Fin.sum_univ_succ, tailRows]

theorem dot_reduced {m n : Nat} (a : Rows m (n+1)) (i v : Fin m) (x : Bits n) :
    dot (reducedRows a v i) x = dot (tailRows a i) x - a i 0 * dot (tailRows a v) x := by
  simp [dot, reducedRows, tailRows, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

theorem pivot_step {m n : Nat} (a : Rows m (n+1)) (b : Bits m) (v : Fin m)
    (hv : a v 0 = 1) (u : Bit) (x : Bits n) :
    solution a b (Fin.cons u x) ↔
      u = recover a b v x ∧ solution (reducedRows a v) (reducedRhs a b v) x := by
  constructor
  · intro h
    have hp := h v
    rw [dot_cons, hv, one_mul] at hp
    constructor
    · unfold recover
      linear_combination hp
    · intro i
      have hi := h i
      rw [dot_cons] at hi
      rw [dot_reduced]
      unfold reducedRhs
      linear_combination hi - a i 0 * hp
  · rintro ⟨rfl, h⟩ i
    have hi := h i
    rw [dot_reduced] at hi
    unfold reducedRhs at hi
    rw [dot_cons]
    unfold recover
    linear_combination hi

theorem free_step {m n : Nat} (a : Rows m (n+1)) (b : Bits m)
    (h : ∀ i, a i 0 = 0) (u : Bit) (x : Bits n) :
    solution a b (Fin.cons u x) ↔ solution (tailRows a) b x := by
  simp [solution, dot_cons, h]

def Satisfying {m n : Nat} (a : Rows m n) (b : Bits m) := { x : Bits n // solution a b x }

theorem free_card {m n : Nat} (a : Rows m (n+1)) (b : Bits m)
    (h : ∀ i, a i 0 = 0) :
    Nat.card (Satisfying a b) = 2 * Nat.card (Satisfying (tailRows a) b) := by
  let e : Satisfying a b ≃ Bit × Satisfying (tailRows a) b := {
    toFun := fun x => (x.val 0, ⟨Fin.tail x.val, (free_step a b h _ _).mp (Fin.cons_self_tail x.val ▸ x.property)⟩)
    invFun := fun ux => ⟨Fin.cons ux.1 ux.2.val, (free_step a b h _ _).mpr ux.2.property⟩
    left_inv := fun x => Subtype.ext (Fin.cons_self_tail _)
    right_inv := fun ux => Prod.ext rfl (Subtype.ext (Fin.tail_cons (α := fun _ : Fin (n+1) => Bit) ux.1 ux.2.val)) }
  rw [Nat.card_congr e, Nat.card_prod]
  simp [Bit]

theorem pivot_card {m n : Nat} (a : Rows m (n+1)) (b : Bits m) (v : Fin m)
    (hv : a v 0 = 1) :
    Nat.card (Satisfying a b) = Nat.card (Satisfying (reducedRows a v) (reducedRhs a b v)) := by
  have dec (x : Satisfying a b) := (pivot_step a b v hv (x.val 0) (Fin.tail x.val)).mp
    (Fin.cons_self_tail x.val ▸ x.property)
  let e : Satisfying a b ≃ Satisfying (reducedRows a v) (reducedRhs a b v) := {
    toFun := fun x => ⟨Fin.tail x.val, (dec x).2⟩
    invFun := fun x => ⟨Fin.cons (recover a b v x.val) x.val, (pivot_step a b v hv _ _).mpr ⟨rfl, x.property⟩⟩
    left_inv := fun x => Subtype.ext ((congrArg (fun t => Fin.cons t (Fin.tail x.val)) (dec x).1.symm).trans (Fin.cons_self_tail x.val))
    right_inv := fun x => Subtype.ext (Fin.tail_cons (α := fun _ : Fin (n+1) => Bit) (recover a b v x.val) x.val) }
  exact Nat.card_congr e

def count (m : Nat) : (n : Nat) → Rows m n → Bits m → Nat
  | 0, _, b => if ∀ i, b i = 0 then 1 else 0
  | n+1, a, b =>
    let candidates := Finset.univ.filter (fun i : Fin m => a i 0 = 1)
    if h : candidates.Nonempty then
      let v := candidates.min' h
      count m n (reducedRows a v) (reducedRhs a b v)
    else
      2 * count m n (tailRows a) b

theorem count_correct (m n : Nat) (a : Rows m n) (b : Bits m) :
    count m n a b = Nat.card (Satisfying a b) := by
  induction n generalizing b with
  | zero =>
    simp only [count]
    split
    next h =>
      have hsol : solution a b (fun _ => 0) := by intro i; simp [dot, h]
      have : Nonempty (Satisfying a b) := ⟨⟨_, hsol⟩⟩
      have : Subsingleton (Satisfying a b) := inferInstanceAs (Subsingleton { x : Bits 0 // solution a b x })
      exact (Nat.card_unique (α := Satisfying a b)).symm
    next h =>
      have : IsEmpty (Satisfying a b) := ⟨fun x => h (fun i => by simpa [dot] using (x.property i).symm)⟩
      exact (Nat.card_of_isEmpty (α := Satisfying a b)).symm
  | succ n ih =>
    simp only [count]
    split
    next h =>
      let c := Finset.univ.filter (fun i : Fin m => a i 0 = 1)
      have hv : a (c.min' h) 0 = 1 := (Finset.mem_filter.mp (c.min'_mem h)).2
      exact (ih _ _).trans (pivot_card a b _ hv).symm
    next h =>
      have hz (i : Fin m) : a i 0 = 0 := by
        have hu : a i 0 ≠ 1 := fun e => h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e⟩⟩
        have decideBit : ∀ x : Bit, x ≠ 1 → x = 0 := by decide
        exact decideBit _ hu
      rw [ih, free_card a b hz]

end PEqualNP.Outside.L_meta_33676_aux.Elimination

namespace PEqualNP.Outside.L_meta_33676_aux.EliminationCircuit

open Elimination
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit Builder

def bit (x : Bit) : Bool := decide (x=1)

def pivot? {m n : ℕ} (a : Rows m (n+1)) : Option (Fin m) :=
  (List.ofFn (id : Fin m → Fin m)).find? (fun i => bit (a i 0))

theorem pivot_some_iff {m n : ℕ} (a : Rows m (n+1)) (v : Fin m) :
    pivot? a = some v ↔ a v 0=1 ∧ ∀ j<v, a j 0≠1 := by
  simpa only [pivot?,bit,id_eq,decide_eq_true_eq] using
    (List.find?_ofFn_eq_some_of_injective (f := (id : Fin m → Fin m))
      (p := fun i => bit (a i 0)) (i := v) Function.injective_id)

def candidates {m n : ℕ} (a : Rows m (n+1)) :=
  Finset.univ.filter (fun i => a i 0=1)

theorem pivot_min {m n : ℕ} (a : Rows m (n+1)) (h : (candidates a).Nonempty) :
    pivot? a = some ((candidates a).min' h) := by
  apply (pivot_some_iff _ _).mpr
  refine ⟨(Finset.mem_filter.mp ((candidates a).min'_mem h)).2,?_⟩
  intro i hi ha
  exact (not_le_of_gt hi) ((candidates a).min'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩))

theorem pivot_none {m n : ℕ} (a : Rows m (n+1)) (h : ¬(candidates a).Nonempty) :
    pivot? a = none := by
  cases hv : pivot? a with
  | none => rfl
  | some v => exact False.elim (h ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,((pivot_some_iff _ _).mp hv).1⟩⟩)

def afterRows {m n : ℕ} (a : Rows m (n+1)) : Rows m n :=
  match pivot? a with
  | none => tailRows a
  | some v => reducedRows a v

def afterRhs {m n : ℕ} (a : Rows m (n+1)) (b : Bits m) : Bits m :=
  match pivot? a with
  | none => b
  | some v => reducedRhs a b v

def rowFields {m n : ℕ} (a : Rows m (n+1)) (b : Bits m) (i : Fin m) : Fin (n+1) → Bit :=
  Fin.cons (b i) (fun j => a i j.succ)

def selected {m n : ℕ} (a : Rows m (n+1)) (b : Bits m) (field : Fin (n+1)) : Bit :=
  ((pivot? a).map (fun i => rowFields a b i field)).getD 0

theorem row_update {m n : ℕ} (a : Rows m (n+1)) (b : Bits m) (i : Fin m) (j : Fin n) :
    a i j.succ - a i 0 * selected a b j.succ = afterRows a i j := by
  cases h : pivot? a <;> simp [afterRows,selected,h,rowFields,tailRows,reducedRows]

theorem rhs_update {m n : ℕ} (a : Rows m (n+1)) (b : Bits m) (i : Fin m) :
    b i - a i 0 * selected a b 0 = afterRhs a b i := by
  cases h : pivot? a <;> simp [afterRhs,selected,h,rowFields,reducedRhs]

private theorem has_eq {s} {B : Bank s} {f g : BitFn s} (h : B.Has f) (eq : ∀ x, f x=g x) :
    B.Has g := by
  obtain ⟨i,hi,h⟩ := h
  exact ⟨i,hi,fun x => (h x).trans (eq x)⟩

theorem firstWire {s : ℕ} {I : Type} (l : List I) (B : Bank s)
    (ctl dat : I → BitFn s) (hc : ∀ i, B.Has (ctl i)) (hd : ∀ i, B.Has (dat i))
    (hz : B.Has (fun _ => false)) :
    B.Grow (l.length*4) (fun E => E.Has (fun x =>
      ((l.find? (fun i => ctl i x)).map (fun i => dat i x)).getD false)) := by
  induction l with
  | nil => exact Bank.Grow.pure B hz
  | cons i l ih =>
    obtain ⟨D,e,c,hd'⟩ := ih
    obtain ⟨E,e',c',hh⟩ := Bank.mux (e (hc i)) (e (hd i)) hd'
    refine ⟨E,Bank.ext_trans e e',?_,has_eq hh (fun x => ?_)⟩
    · simp [Nat.succ_mul]; omega
    · cases h : ctl i x <;> simp [h]

private def readout {m n : ℕ} (a : Rows m (n+1)) (b : Bits m) (opt : Option (Fin (n+1)))
    (i : Fin m) : Bool :=
  match opt with
  | none => true
  | some j => bit (rowFields a b i j)

private def payload {m n : ℕ} (a : Rows m (n+1)) (b : Bits m) (opt : Option (Fin (n+1))) : Bool :=
  ((pivot? a).map (readout a b opt)).getD false

private theorem payload_flag {m n : ℕ} (a : Rows m (n+1)) (b : Bits m) :
    payload a b none = (pivot? a).isSome := by
  cases h : pivot? a <;> simp [payload,h,readout]

private theorem payload_field {m n : ℕ} (a : Rows m (n+1)) (b : Bits m) (j : Fin (n+1)) :
    payload a b (some j) = bit (selected a b j) := by
  cases h : pivot? a <;> simp [payload,selected,h,readout,bit]

def columnCost (m n : ℕ) := 2 + (n+2)*(m*4) + (m*(n+1))*5

theorem eliminateColumn {s m n : ℕ} (B : Bank s)
    (a : (Fin s → Bool) → Rows m (n+1)) (b : (Fin s → Bool) → Bits m)
    (ha : ∀ i j, B.Has (fun x => bit (a x i j)))
    (hb : ∀ i, B.Has (fun x => bit (b x i))) :
    B.Grow (columnCost m n) (fun E =>
      E.Has (fun x => (pivot? (a x)).isSome) ∧
      (∀ j, E.Has (fun x => bit (selected (a x) (b x) j))) ∧
      (∀ i j, E.Has (fun x => bit (afterRows (a x) i j))) ∧
      (∀ i, E.Has (fun x => bit (afterRhs (a x) (b x) i)))) := by
  have fields : ∀ i j, B.Has (fun x => bit (rowFields (a x) (b x) i j)) := by
    intro i j
    refine Fin.cases ?_ (fun j => ?_) j
    · exact hb i
    · exact ha i j.succ
  obtain ⟨C,eC,cC,hz⟩ := B.const false
  obtain ⟨D,eD,cD,ho⟩ := C.const true
  have eBD : B.Ext D := Bank.ext_trans eC eD
  obtain ⟨T,eT,cT,hT⟩ := SensorBuilder.collectType D
    (fun j : Option (Fin (n+1)) => fun x => payload (a x) (b x) j) (m*4) (by
      intro F eF j
      have data (i : Fin m) : F.Has (fun x => readout (a x) (b x) j i) := by
        cases j with
        | none => exact eF ho
        | some j => exact eF (eBD (fields i j))
      simpa [payload,pivot?] using firstWire (List.ofFn (id : Fin m → Fin m)) F
        (fun i x => bit (a x i 0)) (fun i x => readout (a x) (b x) j i)
        (fun i => eF (eBD (ha i 0))) data (eF (eD hz)))
  have selectedWire (j : Fin (n+1)) : T.Has (fun x => bit (selected (a x) (b x) j)) :=
    has_eq (hT (some j)) (fun _ => payload_field _ _ _)
  have eBT : B.Ext T := Bank.ext_trans eBD eT
  have bool_update : ∀ q p y : Bit, xor (bit q) (bit p && bit y) = bit (q-p*y) := by decide
  obtain ⟨F,eF,cF,hF⟩ := SensorBuilder.collectType T
    (fun z : Fin m × Fin (n+1) => fun x => bit (rowFields (a x) (b x) z.1 z.2 -
      a x z.1 0 * selected (a x) (b x) z.2)) 5 (by
      intro E e z
      obtain ⟨U,eU,cU,product⟩ := Bank.meet (e (eBT (ha z.1 0))) (e (selectedWire z.2))
      obtain ⟨V,eV,cV,sum⟩ := Bank.xor2 (eU (e (eBT (fields z.1 z.2)))) product
      exact ⟨V,Bank.ext_trans eU eV,by omega,has_eq sum (fun _ => bool_update _ _ _)⟩)
  refine ⟨F,Bank.ext_trans eBT eF,?_,eF (has_eq (hT none) (fun _ => payload_flag _ _)),
    fun j => eF (selectedWire j),?_,?_⟩
  · simp only [Fintype.card_option,Fintype.card_prod,Fintype.card_fin] at cT cF
    rw [show n+1+1 = n+2 by omega] at cT
    unfold columnCost
    omega
  · intro i j
    exact has_eq (hF (i,j.succ)) (fun x => congrArg bit (row_update (a x) (b x) i j))
  · intro i
    exact has_eq (hF (i,0)) (fun x => congrArg bit (rhs_update (a x) (b x) i))

end PEqualNP.Outside.L_meta_33676_aux.EliminationCircuit

namespace PEqualNP.Outside.L_meta_33676_aux.MatrixCircuit

open Translation ShiftCriterion
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit Builder SensorBuilder
open EliminationCircuit (bit)

abbrev Env (s : ℕ) := Fin s → Bool

noncomputable def truth (P : Prop) : Bool := @decide P (Classical.propDecidable _)

@[simp] theorem truth_true (P : Prop) : truth P = true ↔ P := by
  classical
  simp [truth]

theorem truth_eq {P Q : Prop} (h : P ↔ Q) : truth P = truth Q := by rw [propext h]

theorem has_iff {s} {B : Bank s} {f g : BitFn s} (hf : B.Has f) (h : ∀ x, f x = g x) : B.Has g :=
  ⟨hf.choose,hf.choose_spec.1,fun x => (hf.choose_spec.2 x).trans (h x)⟩

theorem allListWire {s : ℕ} {I : Type} (B : Bank s) (l : List I) (P : I → Env s → Prop) (c : ℕ)
    (emit : ∀ C : Bank s, B.Ext C → ∀ i, C.Grow c (fun E => E.Has (fun x => truth (P i x)))) :
    B.Grow (1+l.length*(c+1)) (fun E => E.Has (fun x => truth (∀ i ∈ l, P i x))) := by
  classical
  induction l with
  | nil =>
    obtain ⟨E,he,hle,hw⟩ := B.const true
    exact ⟨E,he,by simpa using hle,has_iff hw (fun _ => by simp [truth])⟩
  | cons i l ih =>
    obtain ⟨C,hC,kC,hw⟩ := ih
    obtain ⟨D,hD,kD,hp⟩ := emit C hC i
    obtain ⟨E,hE,kE,hh⟩ := Bank.meet hp (hD hw)
    refine ⟨E, Bank.ext_trans hC (Bank.ext_trans hD hE),?_,has_iff hh (fun x => ?_)⟩
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]; omega
    · apply Bool.eq_iff_iff.mpr
      simp

theorem allWire {s : ℕ} {I : Type} [Fintype I] (B : Bank s) (P : I → Env s → Prop) (c : ℕ)
    (emit : ∀ C : Bank s, B.Ext C → ∀ i, C.Grow c (fun E => E.Has (fun x => truth (P i x)))) :
    B.Grow (1+Fintype.card I*(c+1)) (fun E => E.Has (fun x => truth (∀ i, P i x))) := by
  classical
  simpa using allListWire B Finset.univ.toList P c emit

private theorem comparison (a b c : F₂) :
    (if c=1 then xor (bit a) (bit b) else !(xor (bit a) (bit b))) = truth (a=b+c) := by
  have ha : (if c=1 then xor (bit a) (bit b) else !(xor (bit a) (bit b))) = decide (a=b+c) := by
    revert a b c; decide
  rw [ha]
  exact Bool.eq_iff_iff.mpr (by simp)

theorem compareWire {s} (B : Bank s) (f g : Env s → F₂) (c : F₂)
    (hf : B.Has (fun x => bit (f x))) (hg : B.Has (fun x => bit (g x))) :
    B.Grow 5 (fun E => E.Has (fun x => truth (f x = g x + c))) := by
  obtain ⟨D,e,k,hw⟩ := Bank.xor2 hf hg
  by_cases hc : c=1
  · exact ⟨D,e,by omega,has_iff hw (fun x => by simpa [hc] using comparison (f x) (g x) c)⟩
  · obtain ⟨E,e',k',hh⟩ := Bank.inv hw
    exact ⟨E,Bank.ext_trans e e',by omega,has_iff hh (fun x => by simpa [hc] using comparison (f x) (g x) c)⟩

abbrev Family (s p n d : ℕ) := Env s → Fin n → Fin p → Translation.Vector (d+1) → F₂

def TableWires {s p n d} (B : Bank s) (F : Family s p n d) : Prop :=
  ∀ j i u, B.Has (fun x => bit (F x j i u))

def CompatibleWires {s p n d} (B : Bank s) (F G : Family s p n d) : Prop :=
  ∀ j i z, B.Has (fun x => truth (compatible (F x j i) (G x j i) z))

def EquationWires {s p n d} (B : Bank s) (F G : Family s p n d) : Prop :=
  ∀ j i ℓ c, B.Has (fun x => truth (validEquation (F x j i) (G x j i) ℓ c))

theorem buildCompatible {s p n d} (B : Bank s) (F G : Family s p n d) (hF : TableWires B F)
    (hG : TableWires B G) :
    B.Grow ((4*(p*n)*2^d)*(1+12*2^d)) (fun E => CompatibleWires E F G) := by
  classical
  let U := Translation.Vector (d+1)
  let I := Fin n × Fin p × U × F₂
  let val := fun (q : I) x => truth (compatible (F x q.1 q.2.1) (G x q.1 q.2.1) q.2.2)
  have step (C : Bank s) (ext : B.Ext C) (q : I) : C.Grow (1+12*2^d) (fun E => E.Has (val q)) := by
    have hb := allWire C (fun u x => G x q.1 q.2.1 (u+q.2.2.1) = F x q.1 q.2.1 u + q.2.2.2) 5
      (fun E e u => compareWire E _ _ _ (e (ext (hG _ _ _))) (e (ext (hF _ _ _))))
    apply hb.weaken ?_ (fun _ h => h)
    simp [Translation.Vector,F₂,pow_succ]; omega
  have h := collectType B val (1+12*2^d) step
  apply h.weaken ?_ (fun E he j i z => he (j,i,z))
  simp [I,U,Translation.Vector,F₂,pow_succ]
  ring_nf
  omega

theorem buildValid {s p n d} (B : Bank s) (F G : Family s p n d) (hc : CompatibleWires B F G) :
    B.Grow ((8*(p*n)*2^d)*(1+8*2^d)) (fun E => EquationWires E F G) := by
  classical
  let U := Translation.Vector (d+1)
  let _ : Finite (Module.Dual F₂ (U × F₂)) :=
    Finite.of_injective (fun f : Module.Dual F₂ (U×F₂) => (f : (U×F₂) → F₂)) DFunLike.coe_injective
  let _ := Fintype.ofFinite (Module.Dual F₂ (U × F₂))
  let I := Fin n × Fin p × Module.Dual F₂ (U × F₂) × F₂
  let val := fun (q : I) x => truth (validEquation (F x q.1 q.2.1) (G x q.1 q.2.1) q.2.2.1 q.2.2.2)
  have step (C : Bank s) (ext : B.Ext C) (q : I) : C.Grow (1+8*2^d) (fun E => E.Has (val q)) := by
    have row (E : Bank s) (e : C.Ext E) (z : U × F₂) : E.Grow 1 (fun A => A.Has (fun x =>
        truth (compatible (F x q.1 q.2.1) (G x q.1 q.2.1) z → q.2.2.1 z = q.2.2.2))) := by
      by_cases hz : q.2.2.1 z = q.2.2.2
      · apply (E.const true).weaken le_rfl
        exact fun _ hh => has_iff hh (fun _ => by simp [truth,hz])
      · apply (Bank.inv (e (ext (hc q.1 q.2.1 z)))).weaken le_rfl
        intro _ hh
        apply has_iff hh
        intro x
        by_cases hv : compatible (F x q.1 q.2.1) (G x q.1 q.2.1) z <;> simp [truth,hv,hz]
    have h := allWire C _ 1 row
    apply h.weaken ?_ (fun _ hh => hh)
    simp [U, Translation.Vector,F₂,pow_succ]; omega
  have h := collectType B val (1+8*2^d) step
  apply h.weaken ?_ (fun E he j i ℓ c => he (j,i,ℓ,c))
  have hcard : Fintype.card (Module.Dual F₂ (U × F₂)) = 4*2^d :=
    Nat.card_eq_fintype_card.symm.trans (local_normals_card d)
  simp [I,Fintype.card_prod,hcard,F₂]
  ring_nf
  omega

private theorem guardWire {s : ℕ} (B : Bank s) (P : Env s → Prop) (v : F₂)
    (hp : B.Has (fun x => truth (P x))) (hz : B.Has (fun _ => false)) :
    B.Has (fun x => bit (if (Classical.propDecidable (P x)).decide then v else 0)) := by
  classical
  have two : ∀ t : F₂, t=0 ∨ t=1 := by decide
  rcases two v with rfl | rfl
  · exact has_iff hz (fun x => by by_cases h : P x <;> simp [bit,h])
  · exact has_iff hp (fun x => by by_cases h : P x <;> simp [bit,truth,h])

def MatrixWires {s p n d} (B : Bank s) (F G : Family s p n d)
    (R : Fin n → Fin p → Translation.Vector (p*n) →ₗ[F₂] Translation.Vector (d+1)) : Prop :=
  (∀ i j, B.Has (fun x => bit (flatRows (F x) (G x) R i j))) ∧
  (∀ i, B.Has (fun x => bit (flatRhs (F x) (G x) i)))

theorem materialize {s p n d} (B : Bank s) (F G : Family s p n d)
    (R : Fin n → Fin p → Translation.Vector (p*n) →ₗ[F₂] Translation.Vector (d+1))
    (heq : EquationWires B F G) : B.Grow 2 (fun E => MatrixWires E F G R) := by
  classical
  obtain ⟨C,e,k,z⟩ := B.const false
  obtain ⟨E,e',k',o⟩ := C.const true
  have ext : B.Ext E := Bank.ext_trans e e'
  have hc (b : Bool) : E.Has (fun _ => b) := by cases b; exact e' z; exact o
  have row (v : Source (Fin p) (Fin n) (Translation.Vector (p*n))) (ix : EqIndex (Fin p) (Fin n) (Translation.Vector (d+1))) :
      E.Has (fun x => bit (shiftMatrix (F x) (G x) R v ix)) := by
    rcases ix with j|⟨j,i,ℓ,c⟩
    · apply has_iff (hc (bit (∑ i, v.2 j i)))
      intro x
      simp [shiftMatrix,matrixRow,coeffLabel,LinearMap.sum_apply]
    · apply has_iff (guardWire E _ (ℓ (R j i v.1,v.2 j i)) (ext (heq j i ℓ c)) (e' z))
      intro x
      by_cases h : validEquation (F x j i) (G x j i) ℓ c <;>
        simp [h,shiftMatrix,matrixRow,coeffLabel,coeffShift]
  have rhs (ix : EqIndex (Fin p) (Fin n) (Translation.Vector (d+1))) :
      E.Has (fun x => bit (matrixRhs (F x) (G x) ix)) := by
    rcases ix with j|⟨j,i,ℓ,c⟩
    · exact hc (bit 0)
    · apply has_iff (guardWire E _ c (ext (heq j i ℓ c)) (e' z))
      intro x
      by_cases h : validEquation (F x j i) (G x j i) ℓ c <;> simp [h,matrixRhs]
  exact ⟨E,ext,by omega,fun i j => row _ _,fun i => rhs _⟩

def matrixCost (k d : ℕ) := 4*k*2^d*(1+12*2^d) + 8*k*2^d*(1+8*2^d) + 2

theorem buildMatrix {s p n d} (B : Bank s) (F G : Family s p n d)
    (R : Fin n → Fin p → Translation.Vector (p*n) →ₗ[F₂] Translation.Vector (d+1))
    (hF : TableWires B F) (hG : TableWires B G) :
    B.Grow (matrixCost (p*n) d) (fun E => MatrixWires E F G R) := by
  obtain ⟨C,e,k,hc⟩ := buildCompatible B F G hF hG
  obtain ⟨D,e',k',hv⟩ := buildValid C F G hc
  obtain ⟨E,e'',k'',hw⟩ := materialize D F G R hv
  exact ⟨E,Bank.ext_trans e (Bank.ext_trans e' e''),by unfold matrixCost; omega,hw⟩

theorem buildShiftMatrix {s p n d} (hp : 0<p) (hn : 0<n) (B : Bank s) (F : Family s p n d)
    (hF : TableWires B F) :
    B.Grow (matrixCost (p*n) d)
      (fun E => MatrixWires E F (fun x i a => F x i (blockNext hp a)) (relativeMap hp hn)) :=
  buildMatrix B F _ _ hF (fun j i u => hF j (blockNext hp i) u)

theorem matrixCost_le (k r d : ℕ) : matrixCost k d ≤ 128*(k+r+2^d+5)^3 := by
  unfold matrixCost
  generalize 2^d = D
  ring_nf
  omega

end PEqualNP.Outside.L_meta_33676_aux.MatrixCircuit

namespace PEqualNP.Outside.L_meta_33676_aux.ShiftCriterion

open Translation PEqualNP.Outside.L_meta_33676_aux.Windows
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit Layout Builder

def tablePos {p n : ℕ} (i : Fin n) (a : Fin p) : Fin (p*n) :=
  ⟨a.val*n+i.val, by
    calc a.val*n+i.val < a.val*n+n := Nat.add_lt_add_left i.isLt _
         _ = (a.val+1)*n := by ring
         _ ≤ p*n := Nat.mul_le_mul_right _ a.isLt⟩

noncomputable def reportTable {p n N : ℕ} (r d : ℕ) (x : Env N) (i : Fin n) (a : Fin p)
    (z : Vector (d+1)) : F₂ :=
  scalar (tableSignal r d (tablePos i a) ((wordEquiv _).symm z) x)

theorem reportTable_wires {p n N r d : ℕ} (B : Bank N)
    (wires : ∀ (i : Fin (p*n)) (a : Fin (2^(d+1))), B.Has (tableSignal r d i a)) :
    ∀ i a z, B.Has (fun x => decide (reportTable (p:=p) (n:=n) r d x i a z = 1)) := by
  intro i a z
  obtain ⟨j,hj,h⟩ := wires (tablePos i a) ((wordEquiv _).symm z)
  refine ⟨j,hj,fun x => (h x).trans ?_⟩
  change tableSignal r d (tablePos i a) ((wordEquiv _).symm z) x = decide (scalar (tableSignal r d (tablePos i a) ((wordEquiv _).symm z) x) = 1)
  cases tableSignal r d (tablePos i a) ((wordEquiv _).symm z) x <;> decide

theorem reportTable_spec {p n N r d : ℕ} (hp : 0<p) (hn : 0<n) (hk : d<p*n) (hr : 4≤r)
    (x : Env N) (hvalid : ∀ i : Fin (p*n), reach r (bankBit r x i) ≤ d) :
    ∀ (w : Word (p*n)) i,
      scalar (rawReport (r:=r) hp hn (rowName (p*n) x) (colName (p*n) x)
        (rowSchedule (p*n) x) (colSchedule (p*n) x) (bankBit r x) w.val i) =
        residueSum hp hn (reportTable r d x) (encode w) i := by
  intro w i
  unfold rawReport
  rw [fold_xor]
  change 0 + _ = _
  rw [zero_add]
  unfold residueSum
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  apply Finset.sum_congr rfl
  intro a _
  apply congrArg scalar
  let pos := tablePos i a
  let v := windowMap (width:=d+1) hp hn i a (encode w)
  let kword := (wordEquiv _).symm v
  let col := bankBit r x pos
  let name := if col then colName (p*n) x else rowName (p*n) x
  let sched := if col then colSchedule (r:=r) (p*n) x else rowSchedule (p*n) x
  have hwin (j : Fin (d+1)) : w.val.testBit ((pos.val+j.val)%(p*n)) = kword.val.testBit j.val := by
    have he : encode kword j = v j := congrFun ((wordEquiv _).apply_symm_apply v) j
    apply scalar_inj
    change scalar (w.val.testBit ((a.val*n+i.val+j.val)%(p*n))) = encode kword j
    rw [show a.val*n+i.val+j.val = i.val+(a.val*n+j.val) by omega]
    exact he.symm
  have hname : name.val = (if col then (colName (p*n) x).val else (rowName (p*n) x).val) := by
    unfold name
    split <;> rfl
  have h := sensor_at_representative hr hk col (hvalid pos) name w sched pos.val kword hwin
  rw [hname] at h
  have hmod : (a.val*n+i.val)%(p*n) = a.val*n+i.val := Nat.mod_eq_of_lt pos.isLt
  unfold rawSensor tableSignal
  dsimp only
  rw [show (⟨(a.val*n+i.val)%(p*n), Nat.mod_lt _ (Nat.mul_pos hp hn)⟩ : Fin (p*n)) = pos from Fin.ext hmod]
  have hind : (if col then (pos.val+(3*r+1))%(p*n) else (pos.val+(2*r-2))%(p*n)) =
      (pos.val+delay r col)%(p*n) := by cases col <;> rfl
  change _ = (sensorState (p*n) r col (representative (p*n) d pos.val kword).val
    (if col then (colName (p*n) x).val else (rowName (p*n) x).val) sched).testBit
    (if col then (pos.val+(3*r+1))%(p*n) else (pos.val+(2*r-2))%(p*n))
  rw [hind]
  exact h

theorem reportTable_encoded {p n r d trailing : ℕ} (hp : 0<p) (hn : 0<n) (hk : d<p*n)
    (hr : 4≤r) (nr nc : Word (p*n)) (cr cc : Fin r → Word (p*n)) (bank : Fin (p*n) → Bool)
    (extra : List Bool) (ht : extra.length=trailing) (hvalid : ∀ i, reach r (bank i) ≤ d) :
    let x := encoded nr nc cr cc bank extra ht
    ∀ (w : Word (p*n)) i, scalar (rawReport hp hn nr nc cr cc bank w.val i) =
      residueSum hp hn (reportTable r d x) (encode w) i := by
  let x := encoded nr nc cr cc bank extra ht
  obtain ⟨hnr,hnc,hcr,hcc,hb⟩ := decode_encoded nr nc cr cc bank extra ht
  change rowName (p*n) x=nr at hnr
  change colName (p*n) x=nc at hnc
  change rowSchedule (p*n) x=cr at hcr
  change colSchedule (p*n) x=cc at hcc
  change bankBit r x=bank at hb
  have v : ∀ i : Fin (p*n), reach r (bankBit r x i) ≤ d := by simpa only [hb] using hvalid
  simpa only [hnr,hnc,hcr,hcc,hb] using reportTable_spec hp hn hk hr x v

end PEqualNP.Outside.L_meta_33676_aux.ShiftCriterion

namespace PEqualNP.Outside.L_meta_33676_aux.EliminationCircuit
open Elimination
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit Builder

theorem count_succ {m n : ℕ} (a : Rows m (n+1)) (b : Bits m) :
    count m (n+1) a b =
      let t := count m n (afterRows a) (afterRhs a b)
      if (pivot? a).isSome then t else 2*t := by
  by_cases h : (candidates a).Nonempty
  · have pv := pivot_min a h
    unfold candidates at h
    simp [count,h,afterRows,afterRhs,pv,candidates]
  · have pv := pivot_none a h
    unfold candidates at h
    simp [count,h,afterRows,afterRhs,pv]

theorem count_le {m n : ℕ} (a : Rows m n) (b : Bits m) : count m n a b ≤ 2^n := by
  rw [count_correct]
  have h := Nat.card_le_card_of_injective (Subtype.val : Satisfying a b → Bits n) Subtype.val_injective
  simpa [Bits,Bit,Nat.card_fun,Satisfying] using h

private theorem change_wire {s} {B : Bank s} {f g : BitFn s} (h : B.Has f) (eq : ∀ x, f x=g x) :
    B.Has g := by
  obtain ⟨i,hi,h⟩ := h
  exact ⟨i,hi,fun x => (h x).trans (eq x)⟩

private theorem all_zero {s : ℕ} {I : Type} (l : List I) (B : Bank s)
    (dat : I → BitFn s) (hd : ∀ i, B.Has (dat i)) (h1 : B.Has (fun _ => true)) :
    B.Grow (l.length*2) (fun E => E.Has (fun x => l.all (fun i => !(dat i x)))) := by
  induction l with
  | nil => exact Bank.Grow.pure B h1
  | cons i l ih =>
    obtain ⟨D,eD,cD,w⟩ := ih
    obtain ⟨E,eE,cE,neg⟩ := Bank.inv (eD (hd i))
    obtain ⟨F,eF,cF,ans⟩ := Bank.meet neg (eE w)
    exact ⟨F,Bank.ext_trans eD (Bank.ext_trans eE eF),by simp [Nat.succ_mul]; omega,
      ans⟩

def countCost (m : ℕ) : ℕ → ℕ
  | 0 => 1+m*2
  | n+1 => columnCost m n + countCost m n + 1 + (n+2)*4

theorem countCost_bound (m n : ℕ) : countCost m n ≤ 16*(m+1)*(n+1)^2 := by
  induction n with
  | zero => simp [countCost]; omega
  | succ n ih =>
    simp only [countCost,columnCost]
    nlinarith [Nat.zero_le m,Nat.zero_le n,Nat.zero_le (m*n)]

theorem countCircuit {s m : ℕ} (n : ℕ) (B : Bank s)
    (a : (Fin s → Bool) → Rows m n) (b : (Fin s → Bool) → Bits m)
    (ha : ∀ i j, B.Has (fun x => bit (a x i j))) (hb : ∀ i, B.Has (fun x => bit (b x i))) :
    B.Grow (countCost m n) (fun E =>
      (∀ j : Fin (n+1), E.Has (fun x => (count m n (a x) (b x)).testBit j.val)) ∧
      E.Has (fun x => decide (0<count m n (a x) (b x)))) := by
  induction n generalizing B b with
  | zero =>
    obtain ⟨C,eC,cC,ho⟩ := B.const true
    obtain ⟨D,eD,cD,w⟩ := all_zero (List.finRange m) C (fun i x => bit (b x i)) (fun i => eC (hb i)) ho
    refine ⟨D,Bank.ext_trans eC eD,?_,?_⟩
    · simp only [List.length_finRange] at cD
      unfold countCost; omega
    · have normalize (x : Fin s → Bool) : (List.finRange m).all (fun i => !(bit (b x i))) = decide (∀ i, b x i=0) := by
        have zero_iff : ∀ z : Bit, (!bit z)=true ↔ z=0 := by decide
        apply Bool.eq_iff_iff.mpr
        simp only [List.all_eq_true,List.mem_finRange,forall_true_left,zero_iff,decide_eq_true_eq]
      constructor
      · intro j
        have h0 : j.val=0 := by omega
        apply change_wire w
        intro x
        rw [normalize,h0]
        by_cases h : ∀ i, b x i=0 <;> simp [count,h]
      · apply change_wire w
        intro x
        rw [normalize]
        by_cases h : ∀ i, b x i=0 <;> simp [count,h]
  | succ n ih =>
    obtain ⟨C,eC,cC,flag,_,hr,hs⟩ := eliminateColumn B a b ha hb
    let rows := fun x => afterRows (a x)
    let rhs := fun x => afterRhs (a x) (b x)
    let t := fun x => count m n (rows x) (rhs x)
    obtain ⟨D,eD,cD,low,feas⟩ := ih C rows rhs hr hs
    obtain ⟨E,eE,cE,hz⟩ := D.const false
    have get (j : ℕ) : E.Has (fun x => (t x).testBit j) := by
      by_cases hj : j<n+1
      · exact eE (low ⟨j,hj⟩)
      · apply change_wire hz
        intro x
        apply Eq.symm
        apply Nat.testBit_lt_two_pow
        have h : 2^n < 2^(n+1) := by simp [pow_succ]
        exact (lt_of_le_of_lt (count_le (rows x) (rhs x)) h).trans_le
          (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
    have shifted (j : ℕ) : E.Has (fun x => (2*(t x)).testBit j) := by
      cases j with
      | zero => exact change_wire hz (fun x => by simpa only [Nat.bit_false] using (Nat.testBit_bit_zero false (t x)).symm)
      | succ j => exact change_wire (get j) (fun x => by simpa only [Nat.bit_false] using (Nat.testBit_bit_succ j false (t x)).symm)
    obtain ⟨F,eF,cF,out⟩ := E.collectFin (n+2)
      (fun j x => (count m (n+1) (a x) (b x)).testBit j.val) 4 (by
        intro G e j
        obtain ⟨H,eH,cH,ans⟩ := Bank.mux (e (eE (eD flag))) (e (get j.val)) (e (shifted j.val))
        refine ⟨H,eH,cH,change_wire ans (fun x => ?_)⟩
        rw [count_succ]
        cases (pivot? (a x)).isSome <;> simp [t,rows,rhs])
    refine ⟨F,Bank.ext_trans eC (Bank.ext_trans eD (Bank.ext_trans eE eF)),by
      simp only [countCost]; omega,out,change_wire (eF (eE feas)) (fun x => ?_)⟩
    rw [count_succ]
    cases (pivot? (a x)).isSome <;> simp [rows,rhs]

theorem solutionCardCircuit {s m : ℕ} (n : ℕ) (B : Bank s)
    (a : (Fin s → Bool) → Rows m n) (b : (Fin s → Bool) → Bits m)
    (ha : ∀ i j, B.Has (fun x => bit (a x i j))) (hb : ∀ i, B.Has (fun x => bit (b x i))) :
    B.Grow (16*(m+1)*(n+1)^2) (fun E =>
      ∀ j : Fin (n+1), E.Has (fun x => (Nat.card (Satisfying (a x) (b x))).testBit j.val)) := by
  apply (countCircuit n B a b ha hb).weaken (countCost_bound m n)
  intro E h j
  simpa only [count_correct] using h.1 j

open Classical in
theorem solvableCircuit {s m : ℕ} (n : ℕ) (B : Bank s)
    (a : (Fin s → Bool) → Rows m n) (b : (Fin s → Bool) → Bits m)
    (ha : ∀ i j, B.Has (fun x => bit (a x i j))) (hb : ∀ i, B.Has (fun x => bit (b x i))) :
    B.Grow (16*(m+1)*(n+1)^2) (fun E =>
      E.Has (fun x => decide (∃ v, solution (a x) (b x) v))) := by
  apply (countCircuit n B a b ha hb).weaken (countCost_bound m n)
  intro E h
  apply change_wire h.2
  intro x
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,count_correct]
  change 0 < Nat.card {v // solution (a x) (b x) v} ↔ _
  rw [Nat.card_pos_iff]
  simp [nonempty_subtype, show Finite {v // solution (a x) (b x) v} from inferInstance]

end PEqualNP.Outside.L_meta_33676_aux.EliminationCircuit

namespace PEqualNP.Outside.L_meta_33676_aux.GoodBank

open Translation ShiftCriterion MatrixCircuit
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit Builder Layout
open PEqualNP.Outside.L_meta_33676_aux.Windows (reach)
open EliminationCircuit (bit countCost)

noncomputable def cfgRows {p n s : ℕ} (hp : 0<p) (hn : 0<n) (r d : ℕ)
    (x : MatrixCircuit.Env s) : Elimination.Rows (n+8*(p*n)*2^d) (2*(p*n)) :=
  flatRows (reportTable r d x) (fun i a => reportTable r d x i (blockNext hp a)) (relativeMap hp hn)

noncomputable def cfgRhs {p n s : ℕ} (hp : 0<p) (r d : ℕ) (x : MatrixCircuit.Env s) :
    Elimination.Bits (n+8*(p*n)*2^d) :=
  flatRhs (reportTable r d x) (fun i a => reportTable r d x i (blockNext hp a))

noncomputable def cfgCount {p n s : ℕ} (hp : 0<p) (hn : 0<n) (r d : ℕ) (x : MatrixCircuit.Env s) :=
  Elimination.count _ _ (cfgRows hp hn r d x) (cfgRhs hp r d x)

def Valid {s : ℕ} (k r d : ℕ) (x : MatrixCircuit.Env s) : Prop := ∀ i : Fin k, reach r (bankBit r x i) ≤ d

def sensorBudget (k r d : ℕ) := 2 + k*2^(d+1)*unitCost k r

def budget (p n r d : ℕ) := sensorBudget (p*n) r d + matrixCost (p*n) d +
  countCost (n+8*(p*n)*2^d) (2*(p*n)) + (2*(p*n)+2)

theorem cfgCount_correct {s p n r d : ℕ} (hp : 0<p) (hn : 0<n) (hk : n<p*n) (hd : d<n)
    (hr : 4≤r) (x : MatrixCircuit.Env s) (hv : Valid (p*n) r d x) :
    cfgCount hp hn r d x = Nat.card {g : Word (p*n) // rawGood
       (rawReport (r:=r) hp hn (rowName (p*n) x) (colName (p*n) x)
         (rowSchedule (p*n) x) (colSchedule (p*n) x) (bankBit r x)) n g} := by
  unfold cfgCount
  rw [Elimination.count_correct]
  exact (Nat.card_congr (solutionEquiv hp hn hk hd _ _ (reportTable_spec hp hn (hd.trans hk) hr x hv))).symm

theorem cfgCount_encoded {p n r d trailing : ℕ} (hp : 0<p) (hn : 0<n) (hk : n<p*n) (hd : d<n)
    (hr : 4≤r) (nr nc : Word (p*n)) (cr cc : Fin r → Word (p*n)) (bank : Fin (p*n) → Bool)
    (extra : List Bool) (ht : extra.length=trailing) (hv : ∀ i, reach r (bank i) ≤ d) :
    cfgCount hp hn r d (encoded nr nc cr cc bank extra ht) =
      Nat.card {g : Word (p*n) // rawGood (rawReport hp hn nr nc cr cc bank) n g} := by
  unfold cfgCount
  rw [Elimination.count_correct]
  exact (Nat.card_congr (solutionEquiv hp hn hk hd _ _
    (reportTable_encoded hp hn (hd.trans hk) hr nr nc cr cc bank extra ht hv))).symm

theorem buildValid {s : ℕ} (k r d : ℕ) (B : Bank s) (base : (Bank.empty s).Ext B) :
    B.Grow (2*k+2) (fun E => E.Has (fun x => truth (Valid k r d x))) := by
  classical
  obtain ⟨C,hC,cC,hz⟩ := B.const false
  have step (D : Bank s) (ext : C.Ext D) (i : Fin k) : D.Grow 1 (fun E =>
      E.Has (fun x => truth (reach r (bankBit r x i) ≤ d))) := by
    have w : D.Has (fun x => bankBit r x i) := ext (empty_raw C (Bank.ext_trans base hC) hz _)
    by_cases h₀ : reach r false ≤ d <;> by_cases h₁ : reach r true ≤ d
    · apply (D.const true).weaken le_rfl
      exact fun E h => has_iff h (fun x => by cases bankBit r x i <;> simp [truth,h₀,h₁])
    · apply (Bank.inv w).weaken le_rfl
      exact fun E h => has_iff h (fun x => by cases bankBit r x i <;> simp [truth,h₀,h₁])
    · apply (Bank.Grow.pure D (p:=fun E => E.Has (fun x => bankBit r x i)) w).weaken (by omega)
      exact fun E h => has_iff h (fun x => by cases bankBit r x i <;> simp [truth,h₀,h₁])
    · apply (D.const false).weaken le_rfl
      exact fun E h => has_iff h (fun x => by cases bankBit r x i <;> simp [truth,h₀,h₁])
  obtain ⟨E,hE,cE,h⟩ := allWire C _ 1 step
  exact ⟨E,Bank.ext_trans hC hE,by simp at cE; omega,h⟩

structure HasBank {p n s : ℕ} (hp : 0<p) (hn : 0<n) (r d : ℕ) (E : Bank s) : Prop where
  tables : ∀ (i : Fin (p*n)) (z : Fin (2^(d+1))), E.Has (tableSignal r d i z)
  rows : ∀ i j, E.Has (fun x => bit (cfgRows hp hn r d x i j))
  rhs : ∀ i, E.Has (fun x => bit (cfgRhs (n:=n) hp r d x i))
  digits : ∀ j : Fin (2*(p*n)+1), E.Has (fun x => (cfgCount hp hn r d x).testBit j.val)
  feasible : E.Has (fun x => decide (0<cfgCount hp hn r d x))
  valid : E.Has (fun x => truth (Valid (p*n) r d x))

theorem sharedBank {p n : ℕ} (hp : 0<p) (hn : 0<n) (r d trailing : ℕ) :
    (Bank.empty (inLen (p*n) r trailing)).Grow (budget p n r d) (HasBank hp hn r d) := by
  let s := inLen (p*n) r trailing
  let F := reportTable (p:=p) (n:=n) (N:=s) r d
  obtain ⟨B,eB,cB,tables⟩ := buildSensorBank (Nat.mul_pos hp hn) r d trailing
  have hT : TableWires B F := reportTable_wires B tables
  obtain ⟨C,eC,cC,hc⟩ := buildShiftMatrix hp hn B F hT
  have rows : ∀ i j, C.Has (fun x => bit (cfgRows hp hn r d x i j)) := hc.1
  have rhs : ∀ i, C.Has (fun x => bit (cfgRhs (n:=n) hp r d x i)) := hc.2
  obtain ⟨D,eD,cD,digits,has⟩ := EliminationCircuit.countCircuit _ C (cfgRows hp hn r d) (cfgRhs hp r d) rows rhs
  have e : (Bank.empty s).Ext D := Bank.ext_trans eB (Bank.ext_trans eC eD)
  obtain ⟨E,eE,cE,hv⟩ := buildValid (p*n) r d D e
  refine ⟨E,Bank.ext_trans e eE,?_,⟨fun i z => eE (eD (eC (tables i z))),
    fun i j => eE (eD (rows i j)),fun i => eE (eD (rhs i)),fun j => eE (digits j),eE has,hv⟩⟩
  unfold budget sensorBudget
  omega

theorem valid_encoded {p n r d trailing : ℕ} (nr nc : Word (p*n))
    (cr cc : Fin r → Word (p*n)) (bank : Fin (p*n) → Bool)
    (extra : List Bool) (ht : extra.length=trailing) :
    Valid (p*n) r d (encoded nr nc cr cc bank extra ht) ↔ ∀ i, reach r (bank i) ≤ d := by
  have e := (decode_encoded nr nc cr cc bank extra ht).2.2.2.2
  change bankBit r (encoded nr nc cr cc bank extra ht) = bank at e
  simp only [Valid,e]

theorem feasible_count_iff {k : ℕ} (P : Word k → Prop) :
    0 < Nat.card {g : Word k // P g} ↔ ∃ g, P g := by
  rw [Nat.card_pos_iff]
  simp [nonempty_subtype,show Finite {g : Word k // P g} from inferInstance]

theorem budget_le {p n : ℕ} (hk : n ≤ p*n) (r d : ℕ) :
    budget p n r d ≤ 2^12*(p*n+r+2^d+5)^4 := by
  have hc := EliminationCircuit.countCost_bound (n+8*(p*n)*2^d) (2*(p*n))
  unfold budget sensorBudget matrixCost unitCost
  rw [pow_succ]
  apply le_trans (Nat.add_le_add_right (Nat.add_le_add_left hc _) _)
  generalize p*n = k at hk ⊢
  generalize 2^d = D
  obtain ⟨q,rfl⟩ := Nat.exists_eq_add_of_le hk
  ring_nf
  omega

end PEqualNP.Outside.L_meta_33676_aux.GoodBank

namespace PEqualNP.Outside.L_meta_33676_aux.Least

open Elimination

def pinRows {m q k : Nat} (A : Rows m q) (key : Fin k → Fin q) (l : Nat) : Rows (m+k) q :=
  Fin.addCases A (fun i j => if l ≤ i.val ∧ key i = j then 1 else 0)

def pinRhs {m k : Nat} (b : Bits m) (l : Nat) (c : Fin k → Bool) : Bits (m+k) :=
  Fin.addCases b (fun i => if l ≤ i.val ∧ c i = true then 1 else 0)

theorem mem_pinned {m q k : Nat} (A : Rows m q) (b : Bits m)
    (key : Fin k → Fin q) (l : Nat) (c : Fin k → Bool) (x : Bits q) :
    solution (pinRows A key l) (pinRhs b l c) x ↔
      solution A b x ∧ ∀ i : Fin k, l ≤ i.val → x (key i) = (if c i then 1 else 0) := by
  have single (i : Fin k) : dot (pinRows A key l (Fin.natAdd m i)) x =
      (if l ≤ i.val then x (key i) else 0) := by
    by_cases h : l ≤ i.val
    · simp [dot,pinRows,h,ite_mul]
    · simp [dot,pinRows,h]
  constructor
  · intro h
    refine ⟨fun j => ?_,fun i hi => ?_⟩
    · simpa [pinRows,pinRhs] using h (Fin.castAdd k j)
    · simpa [single,pinRhs,hi] using h (Fin.natAdd m i)
  · rintro ⟨h,hp⟩ j
    induction j using Fin.addCases with
    | left j => simpa [pinRows,pinRhs] using h j
    | right i =>
      by_cases hi : l ≤ i.val
      · simpa [single,pinRhs,hi] using hp i hi
      · simp [single,pinRhs,hi]

def honestQuery {k : Nat} (P : Fin (2^k) → Prop) (l : Nat) (c : Fin k → Bool) : Prop :=
  ∃ w, P w ∧ ∀ i : Fin k, l ≤ i.val → w.val.testBit i.val = c i

def replace {k : Nat} (c : Fin k → Bool) (j : Nat) (b : Bool) : Fin k → Bool :=
  fun i => if i.val = j then b else c i

def greedy {k : Nat} (ask : Nat → (Fin k → Bool) → Bool) : Nat → (Fin k → Bool) → (Fin k → Bool)
  | 0, c => c
  | j+1, c => greedy ask j (replace c j (!(ask j (replace c j false))))

theorem greedy_correct {k : Nat} (P : Fin (2^k) → Prop)
    (ask : Nat → (Fin k → Bool) → Bool)
    (hs : ∀ j c, ask j c = true ↔ honestQuery P j c)
    (w : Fin (2^k)) (hw : P w) (hm : ∀ v, P v → w ≤ v)
    (l : Nat) (hl : l ≤ k) (c : Fin k → Bool)
    (hc : ∀ i : Fin k, l ≤ i.val → c i = w.val.testBit i.val) :
    greedy ask l c = fun i => w.val.testBit i.val := by
  induction l generalizing c with
  | zero => exact funext (fun i => hc i (Nat.zero_le _))
  | succ j ih =>
    let i : Fin k := ⟨j,by omega⟩
    have eq : ask j (replace c j false) = !(w.val.testBit j) := by
      cases hb : w.val.testBit j with
      | false =>
        apply (hs _ _).mpr
        refine ⟨w,hw,fun a ha => ?_⟩
        by_cases e : a.val=j
        · simp [replace,e,hb]
        · simp [replace,e,hc a (by omega)]
      | true =>
        apply Bool.eq_false_iff.mpr
        intro e
        obtain ⟨v,hv,hvbits⟩ := (hs _ _).mp e
        have hv0 : v.val.testBit j = false := by simpa [replace,i] using hvbits i (Nat.le_refl j)
        have hlt := Nat.lt_of_testBit j hv0 hb (fun t ht => by
          by_cases hk : t<k
          · let u : Fin k := ⟨t,hk⟩
            have h := hvbits u (Nat.le_of_lt ht)
            rw [replace,ite_eq_right (show u.val≠j from Nat.ne_of_gt ht),hc u ht] at h
            exact h
          · have H : 2^k ≤ 2^t := Nat.pow_le_pow_right (by decide) (by omega)
            rw [Nat.testBit_eq_false_of_lt (v.isLt.trans_le H),Nat.testBit_eq_false_of_lt (w.isLt.trans_le H)])
        exact (Nat.not_lt_of_ge (hm v hv)) hlt
    apply ih (by omega)
    intro a ha
    by_cases e : a.val=j
    · simp [replace,e,eq]
    · simp [replace,e,hc a (by omega)]

open Translation ShiftCriterion

theorem pinned_query {p n d : Nat} (hp : 0<p) (hn : 0<n) (hk : n<p*n) (hd : d<n)
    (H : Nat → Fin n → Bool) (T : Fin n → Fin p → Vector (d+1) → F₂)
    (hT : ∀ (w : Word (p*n)) i, scalar (H w.val i) = residueSum hp hn T (encode w) i)
    (l : Nat) (c : Fin (p*n) → Bool) :
    let G := fun i a => T i (blockNext hp a)
    let A := flatRows T G (relativeMap hp hn)
    let b := flatRhs T G
    let key := fun j => varOrder p n (.inl j)
    (∃ x, solution (pinRows A key l) (pinRhs b l c) x) ↔ honestQuery (rawGood H n) l c := by
  dsimp only
  let e := solutionEquiv hp hn hk hd H T hT
  have proj (g : { w : Word (p*n) // rawGood H n w }) (i : Fin (p*n)) :
      (e g).val (varOrder p n (.inl i)) = scalar (g.val.val.testBit i.val) :=
    congrFun (solution_projects hp hn hk hd H T hT g) i
  constructor
  · rintro ⟨x,h⟩
    obtain ⟨ha,hc⟩ := (mem_pinned _ _ _ _ _ _).mp h
    let v : {x // rowSatisfied (flatRows T (fun i a => T i (blockNext hp a)) (relativeMap hp hn))
        (flatRhs T (fun i a => T i (blockNext hp a))) x} := ⟨x,ha⟩
    let g := e.symm v
    refine ⟨g.val,g.property,fun i hi => scalar_inj ?_⟩
    have hbit := proj g i
    rw [show e g = v from e.apply_symm_apply v] at hbit
    exact hbit.symm.trans (hc i hi)
  · rintro ⟨g,hg,hc⟩
    let v : { w : Word (p*n) // rawGood H n w } := ⟨g,hg⟩
    refine ⟨(e v).val,(mem_pinned _ _ _ _ _ _).mpr ⟨(e v).property,fun i hi => ?_⟩⟩
    exact (proj v i).trans (congrArg scalar (hc i hi))

end PEqualNP.Outside.L_meta_33676_aux.Least

namespace PEqualNP.Outside.L_meta_33676_aux.LeastCircuit

open Elimination EliminationCircuit Least
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit.Builder

private theorem wireEq {s} {B : Bank s} {f g : BitFn s} (h : B.Has f)
    (e : ∀ x, f x = g x) : B.Has g := (funext e) ▸ h

open Classical in
noncomputable def ask {m q k : Nat} (A : Rows m q) (b : Bits m) (key : Fin k → Fin q)
    (l : Nat) (c : Fin k → Bool) : Bool :=
  decide (∃ v, solution (pinRows A key l) (pinRhs b l c) v)

theorem pinnedCircuit {s m q k : Nat} (B : Bank s)
    (A : (Fin s → Bool) → Rows m q) (b : (Fin s → Bool) → Bits m) (key : Fin k → Fin q)
    (ha : ∀ i j, B.Has (fun x => bit (A x i j))) (hb : ∀ i, B.Has (fun x => bit (b x i)))
    (zero : B.Has (fun _ => false)) (one : B.Has (fun _ => true))
    (l : Nat) (c : (Fin s → Bool) → Fin k → Bool) (hc : ∀ i, B.Has (fun x => c x i)) :
    B.Grow (16*(m+k+1)*(q+1)^2) (fun E => E.Has (fun x => ask (A x) (b x) key l (c x))) := by
  apply solvableCircuit q B (fun x => pinRows (A x) key l) (fun x => pinRhs (b x) l (c x))
  · intro i j
    induction i using Fin.addCases with
    | left i => simpa [pinRows] using ha i j
    | right i =>
      by_cases h : l ≤ i.val ∧ key i = j
      · simpa [pinRows,h,bit] using one
      · simpa [pinRows,h,bit] using zero
  · intro i
    induction i using Fin.addCases with
    | left i => simpa [pinRhs] using hb i
    | right i =>
      by_cases h : l ≤ i.val
      · apply wireEq (hc i)
        intro x
        cases z : c x i <;> simp [pinRhs,h,z,bit]
      · simpa [pinRhs,h,bit] using zero

theorem greedyCircuit {s m q k : Nat} (key : Fin k → Fin q) (l : Nat)
    (B : Bank s) (A : (Fin s → Bool) → Rows m q) (b : (Fin s → Bool) → Bits m)
    (ha : ∀ i j, B.Has (fun x => bit (A x i j))) (hb : ∀ i, B.Has (fun x => bit (b x i)))
    (zero : B.Has (fun _ => false)) (one : B.Has (fun _ => true))
    (c : (Fin s → Bool) → Fin k → Bool) (hc : ∀ i, B.Has (fun x => c x i)) :
    B.Grow (l*(16*(m+k+1)*(q+1)^2+1))
      (fun E => ∀ i, E.Has (fun x => greedy (ask (A x) (b x) key) l (c x) i)) := by
  induction l generalizing B c with
  | zero => exact ⟨B,Bank.ext_refl _,by simp,hc⟩
  | succ j ih =>
    let c0 := fun x => replace (c x) j false
    have hc0 (i : Fin k) : B.Has (fun x => c0 x i) := by
      by_cases h : i.val=j
      · simpa [c0,replace,h] using zero
      · simpa [c0,replace,h] using hc i
    obtain ⟨C,eC,lenC,w⟩ := pinnedCircuit B A b key ha hb zero one j c0 hc0
    obtain ⟨D,eD,lenD,flip⟩ := Bank.inv w
    have extBD : B.Ext D := Bank.ext_trans eC eD
    let next := fun x => replace (c x) j (!(ask (A x) (b x) key j (c0 x)))
    have hnext (i : Fin k) : D.Has (fun x => next x i) := by
      by_cases h : i.val=j
      · simpa [next,replace,h] using flip
      · simpa [next,replace,h] using extBD (hc i)
    obtain ⟨E,eE,lenE,done⟩ := ih D (fun i t => extBD (ha i t)) (fun i => extBD (hb i))
      (extBD zero) (extBD one) next hnext
    refine ⟨E,Bank.ext_trans extBD eE,?_,done⟩
    rw [Nat.succ_mul]
    omega

open Translation ShiftCriterion

theorem least_key_bits {p n d : Nat} (hp : 0<p) (hn : 0<n) (hk : n<p*n) (hd : d<n)
    (H : Nat → Fin n → Bool) (T : Fin n → Fin p → Translation.Vector (d+1) → F₂)
    (hT : ∀ (w : Word (p*n)) i, scalar (H w.val i) = residueSum hp hn T (encode w) i)
    (w : Word (p*n)) (hgood : rawGood H n w) (hmin : ∀ v, rawGood H n v → w ≤ v) :
    let G := fun i a => T i (blockNext hp a)
    let A := flatRows T G (relativeMap hp hn)
    let b := flatRhs T G
    let key := fun i => varOrder p n (.inl i)
    greedy (ask A b key) (p*n) (fun _ => false) = fun i => w.val.testBit i.val := by
  classical
  dsimp only
  apply greedy_correct (rawGood H n) _ _ w hgood hmin _ (le_refl _)
  · intro i hi
    omega
  · intro j c
    rw [ask,decide_eq_true_eq]
    exact pinned_query hp hn hk hd H T hT j c

theorem least_exists {k : Nat} (P : Word k → Prop) (h : ∃ w, P w) :
    ∃ w, P w ∧ ∀ v, P v → w ≤ v := by
  classical
  let S := Finset.univ.filter P
  have hn : S.Nonempty := by obtain ⟨w,hw⟩ := h; exact ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩⟩
  exact ⟨S.min' hn, (Finset.mem_filter.mp (S.min'_mem hn)).2, fun v hv =>
    S.min'_le v (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩)⟩

end PEqualNP.Outside.L_meta_33676_aux.LeastCircuit

namespace PEqualNP.Outside.L_meta_33676_aux.GoodLeastBank

open Translation ShiftCriterion GoodBank LeastCircuit
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit Builder Layout
open PEqualNP.Outside.L_meta_33676_aux.Windows (reach)

noncomputable def keyBits {p n s : ℕ} (hp : 0<p) (hn : 0<n) (r d : ℕ)
    (x : MatrixCircuit.Env s) : Fin (p*n) → Bool :=
  Least.greedy (ask (cfgRows hp hn r d x) (cfgRhs hp r d x) (fun i => varOrder p n (.inl i)))
     (p*n) (fun _ => false)

noncomputable def cfgLeast {p n s : ℕ} (hp : 0<p) (hn : 0<n) (r d : ℕ)
    (x : MatrixCircuit.Env s) : Word (p*n) :=
  (wordEquiv (p*n)).symm (fun i => scalar (keyBits hp hn r d x i))

theorem cfgLeast_bit {p n s : ℕ} (hp : 0<p) (hn : 0<n) (r d : ℕ) (x : MatrixCircuit.Env s)
    (i : Fin (p*n)) : (cfgLeast hp hn r d x).val.testBit i.val = keyBits hp hn r d x i := by
  apply scalar_inj
  exact congrFun ((wordEquiv (p*n)).apply_symm_apply (fun i => scalar (keyBits hp hn r d x i))) i

def budget (p n r d : ℕ) := GoodBank.budget p n r d + 2 +
  (p*n)*(16*(n+8*(p*n)*2^d+(p*n)+1)*(2*(p*n)+1)^2+1)

structure HasBank {p n s : ℕ} (hp : 0<p) (hn : 0<n) (r d : ℕ) (B : Bank s) : Prop
    extends GoodBank.HasBank hp hn r d B where
  least : ∀ i : Fin (p*n), B.Has (fun x => (cfgLeast hp hn r d x).val.testBit i.val)

theorem grow {p n : ℕ} (hp : 0<p) (hn : 0<n) (r d trailing : ℕ) :
    (Bank.empty (inLen (p*n) r trailing)).Grow (budget p n r d) (HasBank hp hn r d) := by
  obtain ⟨B,eB,cB,hB⟩ := sharedBank hp hn r d trailing
  obtain ⟨C,eC,cC,hz⟩ := B.const false
  obtain ⟨D,eD,cD,ho⟩ := C.const true
  have bd : B.Ext D := Bank.ext_trans eC eD
  obtain ⟨E,eE,cE,hleast⟩ := greedyCircuit (fun i => varOrder p n (.inl i)) (p*n)
    D (cfgRows hp hn r d) (cfgRhs hp r d) (fun i j => bd (hB.rows i j)) (fun i => bd (hB.rhs i))
    (eD hz) ho (fun _ _ => false) (fun _ => eD hz)
  have be : B.Ext E := Bank.ext_trans bd eE
  refine ⟨E,Bank.ext_trans eB be,by unfold budget; omega,
    ⟨⟨fun i t => be (hB.tables i t), fun i j => be (hB.rows i j), fun i => be (hB.rhs i),
      fun j => be (hB.digits j), be hB.feasible,be hB.valid⟩,fun i => ?_⟩⟩
  exact MatrixCircuit.has_iff (hleast i) (fun x => (cfgLeast_bit hp hn r d x i).symm)

theorem least_encoded {p n r d trailing : ℕ} (hp : 0<p) (hn : 0<n) (hk : n<p*n) (hd : d<n)
    (hr : 4≤r) (nr nc : Word (p*n)) (cr cc : Fin r → Word (p*n)) (bank : Fin (p*n) → Bool)
    (extra : List Bool) (ht : extra.length=trailing) (hv : ∀ i, reach r (bank i) ≤ d)
    (g : Word (p*n)) (hg : rawGood (rawReport hp hn nr nc cr cc bank) n g)
    (hm : ∀ h, rawGood (rawReport hp hn nr nc cr cc bank) n h → g ≤ h) :
    cfgLeast hp hn r d (encoded nr nc cr cc bank extra ht) = g := by
  let x := encoded nr nc cr cc bank extra ht
  have he : keyBits hp hn r d x = fun i => g.val.testBit i.val :=
    least_key_bits hp hn hk hd _ _ (reportTable_encoded hp hn (hd.trans hk) hr nr nc cr cc bank extra ht hv) g hg hm
  apply encode_inj
  funext i
  change scalar ((cfgLeast hp hn r d x).val.testBit i.val) = scalar (g.val.testBit i.val)
  rw [cfgLeast_bit,he]

theorem least_encoded_iff {p n r d trailing : ℕ} (hp : 0<p) (hn : 0<n) (hk : n<p*n) (hd : d<n)
    (hr : 4≤r) (nr nc : Word (p*n)) (cr cc : Fin r → Word (p*n)) (bank : Fin (p*n) → Bool)
    (extra : List Bool) (ht : extra.length=trailing) (hv : ∀ i, reach r (bank i) ≤ d) (j : Fin (p*n+1)) :
    let P : Word (p*n) → Prop := rawGood (rawReport hp hn nr nc cr cc bank) n
    let x := encoded nr nc cr cc bank extra ht
    (∃ g, P g ∧ (∀ h, P h → g≤h) ∧ (j.val=0 ∨ g.val.testBit (j.val-1)=true)) ↔
      0 < cfgCount hp hn r d x ∧ (j.val=0 ∨ (cfgLeast hp hn r d x).val.testBit (j.val-1)=true) := by
  dsimp only
  rw [cfgCount_encoded hp hn hk hd hr nr nc cr cc bank extra ht hv,feasible_count_iff]
  constructor
  · rintro ⟨g,hg,hm,hj⟩
    exact ⟨⟨g,hg⟩,by simpa only [least_encoded hp hn hk hd hr nr nc cr cc bank extra ht hv g hg hm] using hj⟩
  · rintro ⟨h,hj⟩
    obtain ⟨g,hg,hm⟩ := least_exists _ h
    exact ⟨g,hg,hm,by simpa only [least_encoded hp hn hk hd hr nr nc cr cc bank extra ht hv g hg hm] using hj⟩

theorem budget_le {p n : ℕ} (hk : n ≤ p*n) (r d : ℕ) :
    budget p n r d ≤ 2^14*(p*n+r+2^d+5)^5 := by
  unfold budget
  apply le_trans (Nat.add_le_add_right (Nat.add_le_add_right (GoodBank.budget_le hk r d) _) _)
  generalize p*n = k at hk ⊢
  generalize 2^d = D
  obtain ⟨q,rfl⟩ := Nat.exists_eq_add_of_le hk
  ring_nf
  omega

end PEqualNP.Outside.L_meta_33676_aux.GoodLeastBank

namespace PEqualNP.Outside.L_meta_33676_aux.WeightedCircuit

open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit.Builder

abbrev Env (n : ℕ) := Fin n → Bool
def HasWord {n : ℕ} (B : Bank n) (w : ℕ) (f : Env n → ℕ) : Prop :=
  ∀ i : Fin w, B.Has (fun x => (f x).testBit i.val)

theorem keep {n w : ℕ} {A B : Bank n} (h : A.Ext B) {f : Env n → ℕ}
    (hf : HasWord A w f) : HasWord B w f := fun i => h (hf i)

private lemma has_congr {n : ℕ} {B : Bank n} {f g : BitFn n}
    (hf : B.Has f) (h : ∀ x, f x=g x) : B.Has g := by
  simpa only [show f=g from funext h] using hf

private theorem majority {n : ℕ} {B : Bank n} {a b c : BitFn n}
    (ha : B.Has a) (hb : B.Has b) (hc : B.Has c) :
    B.Grow 5 (fun E => E.Has (fun x => Bool.atLeastTwo (a x) (b x) (c x))) := by
  obtain ⟨A,eA,kA,hab⟩ := Bank.meet ha hb
  obtain ⟨C,eC,kC,hac⟩ := Bank.meet (eA ha) (eA hc)
  obtain ⟨D,eD,kD,hbc⟩ := Bank.meet (eC (eA hb)) (eC (eA hc))
  obtain ⟨E,eE,kE,h1⟩ := Bank.join (eD (eC hab)) (eD hac)
  obtain ⟨F,eF,kF,h2⟩ := Bank.join h1 (eE hbc)
  exact ⟨F, fun h => eF (eE (eD (eC (eA h)))), by omega, h2⟩

private def carry (w i a b : ℕ) : Bool :=
  BitVec.carry i (BitVec.ofNat w a) (BitVec.ofNat w b) false

private lemma carry_succ {w i : ℕ} (hi : i<w) (a b : ℕ) :
    carry w (i+1) a b = Bool.atLeastTwo (a.testBit i) (b.testBit i) (carry w i a b) := by
  simp only [carry, BitVec.carry_succ, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]

private lemma digit_add {w i : ℕ} (hi : i<w) (a b : ℕ) :
    (a+b).testBit i = xor (a.testBit i) (xor (b.testBit i) (carry w i a b)) := by
  have h := BitVec.getLsbD_add hi (BitVec.ofNat w a) (BitVec.ofNat w b)
  rw [← BitVec.ofNat_add] at h
  simpa only [BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and, carry] using h

private theorem carry_prefix {n w : ℕ} (B : Bank n) (hz : B.Has (fun _ => false))
    (a b : Env n → ℕ) (ha : HasWord B w a) (hb : HasWord B w b) (t : ℕ) (ht : t≤w) :
    B.Grow (t*5) (fun D => ∀ i ≤ t, D.Has (fun x => carry w i (a x) (b x))) := by
  induction t with
  | zero =>
    refine ⟨B, Bank.ext_refl B, by simp, ?_⟩
    intro i hi
    obtain rfl : i=0 := by omega
    simpa [carry] using hz
  | succ t ih =>
    have hlt : t<w := by omega
    obtain ⟨D,eD,kD,hD⟩ := ih (by omega)
    obtain ⟨E,eE,kE,hc⟩ := majority (eD (ha ⟨t,hlt⟩)) (eD (hb ⟨t,hlt⟩)) (hD t (by omega))
    refine ⟨E, Bank.ext_trans eD eE, by rw [Nat.succ_mul]; omega, ?_⟩
    intro i hu
    by_cases hh : i≤t
    · exact eE (hD i hh)
    · obtain rfl : i=t+1 := by omega
      exact has_congr hc (fun x => (carry_succ hlt (a x) (b x)).symm)

theorem addWord {n w : ℕ} (B : Bank n) (hz : B.Has (fun _ => false))
    (a b : Env n → ℕ) (ha : HasWord B w a) (hb : HasWord B w b) :
    B.Grow (w*13) (fun D => HasWord D w (fun x => a x + b x)) := by
  obtain ⟨C,eC,kC,hc⟩ := carry_prefix B hz a b ha hb w (le_refl _)
  obtain ⟨D,eD,kD,hs⟩ := C.collectFin w (fun i x => (a x+b x).testBit i.val) 8 (by
    intro E e i
    obtain ⟨F,eF,kF,h1⟩ := Bank.xor2 (e (eC (hb i))) (e (hc _ i.isLt.le))
    obtain ⟨G,eG,kG,h2⟩ := Bank.xor2 (eF (e (eC (ha i)))) h1
    exact ⟨G, Bank.ext_trans eF eG, by omega,
      has_congr h2 (fun x => (digit_add i.isLt (a x) (b x)).symm)⟩)
  exact ⟨D, Bank.ext_trans eC eD, by omega, hs⟩

theorem muxWord {n w : ℕ} (B : Bank n) (f : BitFn n) (a b : Env n → ℕ)
    (hf : B.Has f) (ha : HasWord B w a) (hb : HasWord B w b) :
    B.Grow (w*4) (fun D => HasWord D w (fun x => if f x then a x else b x)) := by
  apply B.collectFin w _ 4
  intro C e i
  apply (Bank.mux (e hf) (e (ha i)) (e (hb i))).weaken (le_refl _)
  intro D hD
  exact has_congr hD (fun x => by cases h : f x <;> simp [h])

theorem constWord {n w : ℕ} (B : Bank n) (hz : B.Has (fun _ => false))
    (ho : B.Has (fun _ => true)) (c : ℕ) : HasWord B w (fun _ => c) := by
  intro i
  cases h : c.testBit i.val
  · simpa only [h] using hz
  · simpa only [h] using ho

theorem sumWords {n w : ℕ} {α : Type*} [DecidableEq α] (B : Bank n)
    (hz : B.Has (fun _ => false)) (ho : B.Has (fun _ => true))
    (U : Finset α) (val : α → Env n → ℕ) (cost : ℕ)
    (emit : ∀ j ∈ U, ∀ D, B.Ext D → D.Grow cost (fun E => HasWord E w (val j))) :
    B.Grow (U.card*(cost+w*13)) (fun E => HasWord E w (fun x => ∑ j ∈ U, val j x)) := by
  induction U using Finset.induction_on with
  | empty =>
    simpa using Bank.Grow.pure B (constWord (w:=w) B hz ho 0)
  | @insert j U hj ih =>
    obtain ⟨D,eD,kD,hU⟩ := ih (fun a ha => emit a (Finset.mem_insert_of_mem ha))
    obtain ⟨E,eE,kE,hj'⟩ := emit j (Finset.mem_insert_self _ _) D eD
    obtain ⟨F,eF,kF,hF⟩ := addWord E (eE (eD hz)) (val j) _ hj' (keep eE hU)
    refine ⟨F, Bank.ext_trans eD (Bank.ext_trans eE eF), ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hj, Nat.succ_mul]
      omega
    · simpa [Finset.sum_insert hj] using hF

private theorem gather {n w : ℕ} {α : Type*} [DecidableEq α] (B : Bank n)
    (U : Finset α) (f : α → Env n → ℕ) (cost : ℕ)
    (emit : ∀ j ∈ U, ∀ D, B.Ext D → D.Grow cost (fun E => HasWord E w (f j))) :
    B.Grow (U.card*cost) (fun E => ∀ j ∈ U, HasWord E w (f j)) := by
  induction U using Finset.induction_on with
  | empty => exact ⟨B, Bank.ext_refl B, by simp, by simp⟩
  | @insert j U hj ih =>
    obtain ⟨D,eD,kD,hD⟩ := ih (fun i hi => emit i (Finset.mem_insert_of_mem hi))
    obtain ⟨E,eE,kE,he⟩ := emit j (Finset.mem_insert_self _ _) D eD
    refine ⟨E, Bank.ext_trans eD eE, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hj, Nat.succ_mul]
      omega
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl|hu
      · exact he
      · exact keep eE (hD a hu)

theorem shiftWord {n w : ℕ} (B : Bank n) (hz : B.Has (fun _ => false))
    (m : ℕ) (a : Env n → ℕ) (ha : HasWord B w a) :
    HasWord B w (fun x => 2^m * a x) := by
  intro i
  by_cases h : m ≤ i.val
  · exact has_congr (ha ⟨i.val-m,by omega⟩) (fun x => by simp [Nat.testBit_two_pow_mul,h])
  · exact has_congr hz (fun x => by simp [Nat.testBit_two_pow_mul,h])

theorem scaleWord {n w : Nat} (B : Bank n) (z : B.Has (fun _ => false)) (o : B.Has (fun _ => true))
    (a : Env n → Nat) (ha : HasWord B w a) (l c : Nat) (hc : c < 2^l) :
    B.Grow (l*(w*13)) (fun E => HasWord E w (fun x => c*a x)) := by
  induction l generalizing c with
  | zero =>
    have eq : c=0 := by simpa using hc
    subst c
    exact ⟨B,Bank.ext_refl _,by simp,by simpa using constWord (w:=w) B z o 0⟩
  | succ l ih =>
    have hdiv : c/2 < 2^l := by rw [pow_succ] at hc; omega
    obtain ⟨D,eD,lenD,half⟩ := ih _ hdiv
    have twice : HasWord D w (fun x => 2 * (c/2*a x)) := by
      simpa only [pow_one] using shiftWord D (eD z) 1 _ half
    by_cases even : c % 2 = 0
    · have e : c = 2*(c/2) := by omega
      refine ⟨D,eD,by rw [Nat.succ_mul]; omega,?_⟩
      intro i
      exact has_congr (twice i) (fun x => by dsimp only; rw [← Nat.mul_assoc,← e])
    · obtain ⟨E,eE,lenE,res⟩ := addWord D (eD z) _ _ twice (keep eD ha)
      have e : c = 2*(c/2)+1 := by omega
      refine ⟨E,Bank.ext_trans eD eE,by rw [Nat.succ_mul]; omega,?_⟩
      intro i
      apply has_congr (res i)
      intro x
      have eq : 2*(c/2*a x)+a x = c*a x := calc
        _ = (2*(c/2)+1)*a x := by ring
        _ = _ := congrArg (fun t => t*a x) e.symm
      dsimp only
      rw [eq]

def layer {s : Nat} {State Origin : Type} [Fintype Origin]
    (prev : State → Env s → Nat) (src : State → Origin → State)
    (wt : State → Origin → Nat) (on : State → Origin → Env s → Bool)
    (v : State) (x : Env s) : Nat :=
  ∑ t, if on v t x then wt v t * prev (src v t) x else 0

theorem sparseLayer {s w L : Nat} {State Origin : Type} [Fintype State] [Fintype Origin]
    (B : Bank s) (z : B.Has (fun _ => false)) (o : B.Has (fun _ => true))
    (prev : State → Env s → Nat) (hp : ∀ u, HasWord B w (prev u))
    (src : State → Origin → State) (wt : State → Origin → Nat) (hw : ∀ v t, wt v t < 2^L)
    (on : State → Origin → Env s → Bool) (ho : ∀ v t, B.Has (on v t)) :
    B.Grow (Fintype.card State * (Fintype.card Origin * (L*(w*13)+w*4+w*13)))
      (fun E => ∀ v, HasWord E w (layer prev src wt on v)) := by
  classical
  suffices H : B.Grow (Fintype.card State * (Fintype.card Origin * (L*(w*13)+w*4+w*13)))
      (fun E => ∀ v ∈ (Finset.univ : Finset State), HasWord E w (layer prev src wt on v)) by
    simpa using H
  apply gather B Finset.univ (fun v => layer prev src wt on v) _
  intro v _ D eD
  apply sumWords D (eD z) (eD o) Finset.univ
    (fun t x => if on v t x then wt v t * prev (src v t) x else 0) (L*(w*13)+w*4)
  intro t _ E eE
  have keepBE : B.Ext E := Bank.ext_trans eD eE
  obtain ⟨F,eF,lenF,scaled⟩ := scaleWord E (keepBE z) (keepBE o) _ (keep keepBE (hp _)) L _ (hw _ _)
  obtain ⟨G,eG,lenG,out⟩ := muxWord F (on v t) _ _ (eF (keepBE (ho v t))) scaled
    (constWord F (eF (keepBE z)) (eF (keepBE o)) 0)
  exact ⟨G,Bank.ext_trans eF eG,by omega,out⟩

def layers {s : Nat} {State Origin : Type} [Fintype Origin] (init : State → Env s → Nat)
    (src : Nat → State → Origin → State) (wt : Nat → State → Origin → Nat)
    (on : Nat → State → Origin → Env s → Bool) : Nat → State → Env s → Nat
  | 0 => init
  | t+1 => layer (layers init src wt on t) (src t) (wt t) (on t)

theorem compileLayers {s w L Q : Nat} {State Origin : Type} [Fintype State] [Fintype Origin]
    (B : Bank s) (zero : B.Has (fun _ => false)) (one : B.Has (fun _ => true))
    (init : State → Env s → Nat) (hinit : ∀ u, HasWord B w (init u))
    (src : Nat → State → Origin → State) (wt : Nat → State → Origin → Nat)
    (on : Nat → State → Origin → Env s → Bool) (t : Nat)
    (bound : ∀ j<t, ∀ v a, wt j v a < 2^L)
    (emit : ∀ j<t, ∀ E : Bank s, B.Ext E → ∀ v a, E.Grow Q (fun F => F.Has (on j v a))) :
    B.Grow (t*(Fintype.card State*Fintype.card Origin*(Q+L*(w*13)+w*4+w*13)))
      (fun E => ∀ v, HasWord E w (layers init src wt on t v)) := by
  induction t with
  | zero => exact ⟨B,Bank.ext_refl _,by simp,hinit⟩
  | succ t ih =>
    obtain ⟨C,eC,lenC,prev⟩ := ih (fun j hj => bound j (by omega)) (fun j hj => emit j (by omega))
    obtain ⟨D,eD,lenD,gates⟩ := PEqualNP.Outside.L_meta_33676_aux.SensorCircuit.SensorBuilder.collectType C
      (fun va : State × Origin => on t va.1 va.2) Q
      (fun E eE va => emit t (by omega) E (Bank.ext_trans eC eE) va.1 va.2)
    have extBD : B.Ext D := Bank.ext_trans eC eD
    obtain ⟨E,eE,lenE,out⟩ := sparseLayer D (extBD zero) (extBD one)
      (layers init src wt on t) (fun u => keep eD (prev u)) (src t) (wt t) (bound t (by omega)) (on t)
      (fun v a => gates (v,a))
    refine ⟨E,Bank.ext_trans extBD eE,?_,out⟩
    rw [Fintype.card_prod] at lenD
    calc
      E.gates.length ≤ B.gates.length +
          t*(Fintype.card State*Fintype.card Origin*(Q+L*(w*13)+w*4+w*13)) +
          (Fintype.card State*Fintype.card Origin)*Q +
          Fintype.card State*(Fintype.card Origin*(L*(w*13)+w*4+w*13)) := by omega
      _ = _ := by ring

end PEqualNP.Outside.L_meta_33676_aux.WeightedCircuit

namespace PEqualNP.Outside.L_meta_33676_aux.Ranking

abbrev Word (k : ℕ) := Fin (2^k)

def translate {k : ℕ} (g w : Word k) : Word k :=
  ⟨w.val ^^^ g.val, Nat.xor_lt_two_pow w.isLt g.isLt⟩

@[simp] theorem translate_translate {k : ℕ} (g w : Word k) :
    translate g (translate g w) = w := by
  apply Fin.ext
  simp [translate]

noncomputable def slice {k : ℕ} (P : Word k → Prop) (l h : ℕ) : Finset (Word k) := by
  classical
  exact Finset.univ.filter fun w => P w ∧ w.val >>> l = h

@[simp] theorem mem_slice {k : ℕ} {P : Word k → Prop} {w : Word k} {l h : ℕ} :
    w ∈ slice P l h ↔ P w ∧ w.val >>> l = h := by classical simp [slice]

theorem slice_split {k : ℕ} (P : Word k → Prop) (l h : ℕ) :
    slice P (l+1) h = slice P l (2*h) ∪ slice P l (2*h+1) := by
  classical
  ext w
  simp only [Finset.mem_union,mem_slice,Nat.shiftRight_eq_div_pow,Nat.pow_succ,
    ← Nat.div_div_eq_div_mul]
  by_cases hw : P w <;> simp only [hw, true_and, false_and, false_or, iff_self]
  omega

theorem slice_disjoint {k : ℕ} (P : Word k → Prop) (l h : ℕ) :
    Disjoint (slice P l (2*h)) (slice P l (2*h+1)) := by
  apply Finset.disjoint_left.mpr
  intro w h₀ h₁
  have a := (mem_slice.mp h₀).2
  have b := (mem_slice.mp h₁).2
  omega

theorem left_lt_right {k : ℕ} {P : Word k → Prop} {l h : ℕ} {a b : Word k}
    (ha : a ∈ slice P l (2*h)) (hb : b ∈ slice P l (2*h+1)) : a < b := by
  have A := (mem_slice.mp ha).2
  have B := (mem_slice.mp hb).2
  rw [Nat.shiftRight_eq_div_pow] at A B
  by_contra! hle
  have H := Nat.div_le_div_right (c := 2^l) (show b.val ≤ a.val from hle)
  omega

theorem count_translated {k : ℕ} (P : Word k → Prop) (g : Word k) (l h : ℕ) :
    (slice (fun w => P (translate g w)) l h).card =
    (slice P l (h ^^^ (g.val >>> l))).card := by
  classical
  let A := slice (fun w => P (translate g w)) l h
  have image : A.image (translate g) = slice P l (h ^^^ (g.val >>> l)) := by
    ext w
    simp only [Finset.mem_image,mem_slice]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨hp,hv⟩ := mem_slice.mp hu
      refine ⟨hp, ?_⟩
      change (u.val ^^^ g.val) >>> l = _
      rw [Nat.shiftRight_xor_distrib, hv]
    · rintro ⟨hp, hv⟩
      refine ⟨translate g w, mem_slice.mpr ⟨by simpa using hp, ?_⟩, translate_translate g w⟩
      change (w.val ^^^ g.val) >>> l = h
      simp [Nat.shiftRight_xor_distrib, hv]
  rw [← image,Finset.card_image_of_injective]
  exact fun a b h => by simpa using congrArg (translate g) h

def rank {k : ℕ} (S : Finset (Word k)) (w : Word k) : ℕ :=
  (S.filter (· < w)).card

theorem rank_left {k : ℕ} {A B : Finset (Word k)} (ord : ∀ a ∈ A, ∀ b ∈ B, a < b)
    {w : Word k} (hw : w ∈ A) : rank (A ∪ B) w = rank A w := by
  have empty : B.filter (· < w) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hB,hlt⟩ := Finset.mem_filter.mp hx
    exact lt_asymm hlt (ord w hw x hB)
  simp [rank,Finset.filter_union,empty]

theorem rank_right {k : ℕ} {A B : Finset (Word k)} (ord : ∀ a ∈ A, ∀ b ∈ B, a < b)
    {w : Word k} (hw : w ∈ B) : rank (A ∪ B) w = A.card + rank B w := by
  have full : A.filter (· < w) = A := Finset.filter_eq_self.mpr (fun a ha => ord a ha w hw)
  have dis : Disjoint A (B.filter (· < w)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (lt_irrefl x) (ord x hx x (Finset.mem_filter.mp hy).1)
  simp [rank,Finset.filter_union,full,Finset.card_union_of_disjoint dis]

def selectPrefix (C : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, h, _ => h
  | l+1, h, t => if t < C l (2*h) then selectPrefix C l (2*h) t
    else selectPrefix C l (2*h+1) (t-C l (2*h))

theorem selectPrefix_spec {k : ℕ} (P : Word k → Prop) (C : ℕ → ℕ → ℕ)
    (hc : ∀ l h, C l h = (slice P l h).card) (l h t : ℕ) (ht : t < C l h) :
    ∃ w ∈ slice P l h, selectPrefix C l h t = w.val ∧ rank (slice P l h) w = t := by
  induction l generalizing h t with
  | zero =>
    have ht' : 0 < (slice P 0 h).card := by rw [← hc]; omega
    obtain ⟨w,hw⟩ := Finset.card_pos.mp ht'
    have single : slice P 0 h = {w} := by
      ext x
      simp only [Finset.mem_singleton]
      constructor
      · intro hx
        apply Fin.ext
        simpa using (mem_slice.mp hx).2.trans (mem_slice.mp hw).2.symm
      · rintro rfl
        exact hw
    have wv : w.val = h := by simpa using (mem_slice.mp hw).2
    have tz : t = 0 := by rw [hc,single,Finset.card_singleton] at ht; omega
    exact ⟨w,hw,by simpa [selectPrefix] using wv.symm,by simp [rank,single,tz]⟩
  | succ l ih =>
    have ord : ∀ a ∈ slice P l (2*h), ∀ b ∈ slice P l (2*h+1), a < b :=
      fun _ ha _ hb => left_lt_right ha hb
    rw [slice_split]
    by_cases hleft : t < C l (2*h)
    · obtain ⟨w,hw,he,hr⟩ := ih (2*h) t hleft
      exact ⟨w,Finset.mem_union_left _ hw,by simpa [selectPrefix,hleft] using he,
        (rank_left ord hw).trans hr⟩
    · have total := hc (l+1) h
      rw [slice_split,Finset.card_union_of_disjoint (slice_disjoint P l h),← hc,← hc] at total
      have ht' : t-C l (2*h) < C l (2*h+1) := by omega
      obtain ⟨w,hw,he,hr⟩ := ih (2*h+1) _ ht'
      refine ⟨w,Finset.mem_union_right _ hw,by simpa [selectPrefix,hleft] using he,?_⟩
      rw [rank_right ord hw,hr,← hc]
      omega

theorem translated_branch_bit (h l g : ℕ) (b : Bool) :
    (((2*h + b.toNat) ^^^ (g >>> l)).testBit 0) = xor b (g.testBit l) := by
  rw [Nat.testBit_xor,Nat.testBit_shiftRight,Nat.add_zero]
  have e : (2*h+b.toNat).testBit 0 = b := by
    cases b <;> simp [Nat.testBit_zero, Nat.add_mod]
  rw [e]

private theorem full_slice {k : ℕ} (P : Word k → Prop) [DecidablePred P] :
    slice P k 0 = Finset.univ.filter P := by
  ext w
  simp [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt w.isLt]

private theorem rankNat {k : ℕ} (P : Word k → Prop) (w : Word k) :
    rank (slice P k 0) w = Nat.card {z : Word k // z < w ∧ P z} := by
  classical
  rw [full_slice,Nat.card_eq_fintype_card,Fintype.card_subtype]
  simp [rank,Finset.filter_filter,and_comm]

private theorem rank_lt_card {k : ℕ} (S : Finset (Word k)) {w : Word k} (hw : w ∈ S) : rank S w < S.card := by
  apply Finset.card_lt_card
  refine lt_of_le_of_ne (Finset.filter_subset _ _) ?_
  intro h
  have hn : w ∈ S.filter (· < w) := h.symm ▸ hw
  exact (lt_irrefl w) (Finset.mem_filter.mp hn).2

private theorem rank_strict {k : ℕ} (S : Finset (Word k)) {a b : Word k} (ha : a ∈ S) (hab : a<b) :
    rank S a < rank S b := by
  apply Finset.card_lt_card
  refine lt_of_le_of_ne ?_ ?_
  · intro x hx
    obtain ⟨hx,hl⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hx,hl.trans hab⟩
  · intro h
    have h₁ : a ∈ S.filter (· < b) := Finset.mem_filter.mpr ⟨ha,hab⟩
    have h₂ : a ∈ S.filter (· < a) := h.symm ▸ h₁
    exact (lt_irrefl a) (Finset.mem_filter.mp h₂).2

theorem original_rank_interface {k : ℕ} (P : Word k → Prop) (g : Word k) (Q : ℕ → ℕ → ℕ)
    (hQ : ∀ l h, Q l h = (slice (fun w => P (translate g w)) l h).card)
    (t j : ℕ) :
    let C := fun l h => Q l (h ^^^ (g.val >>> l))
    C k 0 = Nat.card {w : Word k // P w} ∧
    ((∃ w : Word k, P w ∧ Nat.card {z : Word k // z < w ∧ P z} = t ∧
        (j = 0 ∨ w.val.testBit (j-1) = true)) ↔
      t < C k 0 ∧ (j = 0 ∨ (selectPrefix C k 0 t).testBit (j-1) = true)) := by
  classical
  intro C
  have hc (l h : ℕ) : C l h = (slice P l h).card := by
    change Q l (h ^^^ (g.val >>> l)) = _
    rw [hQ,count_translated]
    simp
  have allmem (w : Word k) : w ∈ slice P k 0 ↔ P w := by simp [full_slice]
  refine ⟨?_,?_⟩
  · rw [hc,full_slice,Nat.card_eq_fintype_card,Fintype.card_subtype]
  constructor
  · rintro ⟨w,hw,hr,hbit⟩
    have hw' := (allmem w).mpr hw
    have hr' : rank (slice P k 0) w = t := (rankNat P w).trans hr
    have ht : t<C k 0 := by rw [hc, ← hr']; exact rank_lt_card _ hw'
    obtain ⟨u, hu, he, hur⟩ := selectPrefix_spec P C hc k 0 t ht
    have heq : u=w := by
      rcases lt_trichotomy u w with h|h|h
      · have := rank_strict _ hu h; omega
      · exact h
      · have := rank_strict _ hw' h; omega
    exact ⟨ht, by simpa [he,heq] using hbit⟩
  · rintro ⟨ht,hbit⟩
    obtain ⟨w,hw,he,hr⟩ := selectPrefix_spec P C hc k 0 t ht
    exact ⟨w,(allmem w).mp hw,(rankNat P w).symm.trans hr,by simpa [he] using hbit⟩

def rowPinned (n l a j : ℕ) : Prop := l/n < a ∨ (a=l/n ∧ l % n ≤ j)

theorem rowPinned_iff {n : ℕ} (hn : 0<n) (l a : ℕ) (j : Fin n) :
    rowPinned n l a j.val ↔ l ≤ a*n+j.val := by
  have eq₀ := Nat.div_add_mod l n
  rw [Nat.mul_comm n (l/n)] at eq₀
  have bound (x y : ℕ) (hxy : x<y) (u : Fin n) : x*n + u.val < y*n := by
    calc
      _ < (x+1)*n := by rw [Nat.add_mul,Nat.one_mul]; exact Nat.add_lt_add_left u.isLt _
      _ ≤ _ := Nat.mul_le_mul_right n hxy
  have m : l % n<n := Nat.mod_lt _ hn
  rcases lt_trichotomy (l/n) a with ha|ha|ha
  · have lt := bound (l/n) a ha ⟨l % n,m⟩
    unfold rowPinned
    dsimp at lt
    omega
  · subst a
    simp [rowPinned]
    omega
  · have lt := bound a (l/n) ha j
    unfold rowPinned
    omega

theorem prefix_rows {p n : ℕ} (hn : 0<n) (w : Word (p*n)) (l h : ℕ) :
    w.val >>> l = h ↔ h < 2^(p*n-l) ∧
      ∀ (a : Fin p) (j : Fin n), rowPinned n l a.val j.val →
        w.val.testBit (a.val*n+j.val) = h.testBit (a.val*n+j.val-l) := by
  have bound : w.val >>> l < 2^(p*n-l) := by
    rw [Nat.shiftRight_eq_div_pow,Nat.div_lt_iff_lt_mul (by positivity),←pow_add]
    exact w.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  constructor
  · rintro rfl
    refine ⟨bound,?_⟩
    intro a j hp
    have le := (rowPinned_iff hn l a.val j).mp hp
    rw [Nat.testBit_shiftRight]
    congr 1
    omega
  · rintro ⟨hh,hrow⟩
    apply Nat.eq_of_testBit_eq
    intro t
    by_cases ht : t < p*n-l
    · let idx : Fin (p*n) := ⟨l+t,by omega⟩
      obtain ⟨⟨a,j⟩,eq⟩ := finProdFinEquiv.surjective idx
      have pos : a.val*n + j.val = l+t := by
        have v := congrArg Fin.val eq
        change j.val + n*a.val = l+t at v
        rw [Nat.mul_comm a.val n,Nat.add_comm]
        exact v
      have e := hrow a j ((rowPinned_iff hn l a.val j).mpr (by omega))
      rwa [pos,Nat.add_sub_cancel_left,← Nat.testBit_shiftRight] at e
    · have le : 2^(p*n-l) ≤ 2^t := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow (bound.trans_le le),Nat.testBit_lt_two_pow (hh.trans_le le)]

def distinguished (p n l : ℕ) : ℕ := min (l/n) (p-1)
def cutoff (p n l : ℕ) : ℕ := l - distinguished p n l*n

theorem distinguished_lt {p : ℕ} (hp : 0<p) (n l : ℕ) : distinguished p n l < p :=
  (min_le_right _ _).trans_lt (by omega)

theorem pinned_around_cut {p n : ℕ} (hp : 0<p) (hn : 0<n) (l : ℕ) (a : Fin p) (j : Fin n) :
    rowPinned n l a.val j.val ↔ distinguished p n l < a.val ∨
      (a.val = distinguished p n l ∧ cutoff p n l ≤ j.val) := by
  have eq := Nat.div_add_mod l n
  rw [Nat.mul_comm n (l/n)] at eq
  by_cases lo : l/n ≤ p-1
  · have cut : cutoff p n l = l % n := by unfold cutoff distinguished; rw [min_eq_left lo]; omega
    simp [rowPinned,distinguished,min_eq_left lo,cut]
  · have ge : p ≤ l/n := by omega
    have high : p*n ≤ l := (Nat.mul_le_mul_right n ge).trans (by omega)
    have e : p*n = (p-1)*n+n := by
      rw [← Nat.succ_mul,show (p-1).succ=p by omega]
    have cut : n ≤ cutoff p n l := by unfold cutoff distinguished; rw [min_eq_right (by omega)]; omega
    have qa : a.val ≤ p-1 := by omega
    unfold rowPinned
    simp [distinguished,min_eq_right (by omega : p-1≤l/n)]
    omega

abbrev rowData (p n l : ℕ) :=
  (Fin (distinguished p n l) → Fin n → Bool) × (Fin (min n (cutoff p n l)) → Bool)

def fixedValue (n l h a j : ℕ) : Bool := h.testBit (a*n+j-l)

def assembleRows {p n l : ℕ} (h : ℕ) (X : rowData p n l) (a : Fin p) (j : Fin n) : Bool :=
  if lo : a.val < distinguished p n l then X.1 ⟨a.val,lo⟩ j
  else if mid : a.val = distinguished p n l ∧ j.val < cutoff p n l then
    X.2 ⟨j.val,lt_min j.isLt mid.2⟩
  else fixedValue n l h a.val j.val

theorem assemblePinned {p n l : ℕ} (hp : 0<p) (hn : 0<n) (h : ℕ) (X : rowData p n l)
    (a : Fin p) (j : Fin n) (pin : rowPinned n l a.val j.val) :
    assembleRows h X a j = fixedValue n l h a.val j.val := by
  rw [pinned_around_cut hp hn] at pin
  unfold assembleRows
  split_ifs <;> first | rfl | omega

abbrev pinnedPanel (p n l h : ℕ) := {R : Fin p → Fin n → Bool //
  ∀ a j, rowPinned n l a.val j.val → R a j = fixedValue n l h a.val j.val}

def prefixPanelEquiv {p n : ℕ} (hp : 0<p) (hn : 0<n) (l h : ℕ) :
    pinnedPanel p n l h ≃ rowData p n l :=
  { toFun := fun R => (fun a j => R.val ⟨a.val,a.isLt.trans (distinguished_lt hp n l)⟩ j,
        fun j => R.val ⟨distinguished p n l,distinguished_lt hp n l⟩ ⟨j.val,j.isLt.trans_le (min_le_left _ _)⟩)
    invFun := fun X => ⟨assembleRows h X,assemblePinned hp hn h X⟩
    left_inv := by
      intro R
      apply Subtype.ext
      funext a j
      simp only [assembleRows]
      split_ifs with lo mid
      · rfl
      · exact congrArg (fun row : Fin p => R.val row j) (Fin.ext mid.1.symm)
      · apply (R.property a j _).symm
        rw [pinned_around_cut hp hn]
        omega
    right_inv := by
      intro X
      apply Prod.ext
      · funext a j
        simp [assembleRows,a.isLt]
      · funext j
        have hj := j.isLt.trans_le (min_le_right n (cutoff p n l))
        simp [assembleRows,hj] }

theorem countedRows {p n : ℕ} (hp : 0<p) (hn : 0<n) (l h : ℕ)
    (P : (Fin p → Fin n → Bool) → Prop) :
    Nat.card {R : Fin p → Fin n → Bool // h < 2^(p*n-l) ∧
      (∀ a j, rowPinned n l a.val j.val → R a j = fixedValue n l h a.val j.val) ∧ P R} =
      if h < 2^(p*n-l) then Nat.card {X : rowData p n l // P (assembleRows h X)} else 0 := by
  classical
  by_cases ok : h < 2^(p*n-l)
  · rw [ite_eq_left ok]
    let E : {R : Fin p → Fin n → Bool // h < 2^(p*n-l) ∧
        (∀ a j, rowPinned n l a.val j.val → R a j = fixedValue n l h a.val j.val) ∧ P R} ≃
        {R : pinnedPanel p n l h // P R.val} :=
      ⟨fun R => ⟨⟨R.val,R.property.2.1⟩,R.property.2.2⟩,
       fun R => ⟨R.val.val,ok,R.val.property,R.property⟩,fun _ => rfl,fun _ => rfl⟩
    let e := (prefixPanelEquiv hp hn l h).symm
    exact Nat.card_congr (E.trans (e.subtypeEquiv (fun _ => Iff.rfl)).symm)
  · rw [ite_eq_right ok]
    let : IsEmpty {R : Fin p → Fin n → Bool // h < 2^(p*n-l) ∧
        (∀ a j, rowPinned n l a.val j.val → R a j = fixedValue n l h a.val j.val) ∧ P R} :=
      ⟨fun R => ok R.property.1⟩
    exact Nat.card_of_isEmpty

end PEqualNP.Outside.L_meta_33676_aux.Ranking

namespace PEqualNP.Outside.L_meta_33676_aux.RankCircuit
open Ranking WeightedCircuit
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit.Builder

private theorem mapWire {s} {B : Bank s} {f g : BitFn s} (h : B.Has f) (eq : ∀ x, f x=g x) :
    B.Has g := by
  obtain ⟨i,hi,h⟩ := h
  exact ⟨i,hi,fun x => (h x).trans (eq x)⟩

private theorem complement_bit {w b : Nat} (hb : b<2^w) (i : Fin w) :
    (2^w-1-b).testBit i.val = !b.testBit i.val := by
  have e := BitVec.getLsbD_not (x:=BitVec.ofNat w b) (i:=i.val)
  rw [← BitVec.testBit_toNat] at e
  rw [BitVec.getLsbD_ofNat] at e
  simpa [BitVec.toNat_not,Nat.mod_eq_of_lt hb,i.isLt] using e

private def probe (w a b : Nat) := a+(2^w-1-b)+1

private theorem probe_high {w a b : Nat} (ha : a<2^w) (hb : b<2^w) :
    (probe w a b).testBit w = decide (b≤a) := by
  by_cases h : b≤a
  · have e : probe w a b = (a-b)+2^w := by unfold probe; omega
    have hd : a-b<2^w := by omega
    rw [e,Nat.testBit_eq_decide_div_mod_eq,Nat.add_div_right _ (Nat.two_pow_pos w),Nat.div_eq_of_lt hd]
    simp [h]
  · have e : probe w a b < 2^w := by unfold probe; omega
    simp [Nat.testBit_lt_two_pow e,h]

private theorem probe_low {w a b : Nat} (ha : a<2^w) (hb : b<2^w) (hle : b≤a) (i : Fin w) :
    (probe w a b).testBit i.val = (a-b).testBit i.val := by
  have e : probe w a b = (a-b)+2^w := by unfold probe; omega
  have h : (probe w a b) % 2^w = a-b := by rw [e,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  have eq := congrArg (fun z : Nat => z.testBit i.val) h
  simpa [Nat.testBit_mod_two_pow,i.isLt] using eq

private theorem widen {s w v : ℕ} (B : Bank s) (z : B.Has (fun _ => false))
    (a : Env s → ℕ) (h : ∀ x, a x<2^w) (ha : HasWord B w a) : HasWord B v a := by
  intro i
  by_cases hi : i.val<w
  · exact ha ⟨i.val,hi⟩
  · exact mapWire z (fun x => (Nat.testBit_lt_two_pow
      ((h x).trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))).symm)

theorem subtractBranch {s w : ℕ} (B : Bank s) (z : B.Has (fun _ => false)) (o : B.Has (fun _ => true))
    (a b : Env s → ℕ) (ba : ∀ x, a x<2^w) (bb : ∀ x, b x<2^w)
    (ha : HasWord B w a) (hb : HasWord B w b) :
    B.Grow (32*(w+1)) (fun E => E.Has (fun x => decide (b x ≤ a x)) ∧
      HasWord E w (fun x => if a x<b x then a x else a x-b x)) := by
  let comp := fun x => 2^w-1-b x
  obtain ⟨C,eC,cC,hC⟩ := B.collectFin w (fun i x => (comp x).testBit i.val) 1 (by
    intro D e i
    obtain ⟨E,e',c',v⟩ := Bank.inv (e (hb i))
    exact ⟨E,e',c',mapWire v (fun x => (complement_bit (bb x) i).symm)⟩)
  have bc (x : Env s) : comp x < 2^w := by
    have h := Nat.two_pow_pos w; dsimp [comp]; omega
  obtain ⟨D,eD,cD,hD⟩ := addWord (w:=w+1) C (eC z) a comp
    (widen C (eC z) a ba (keep eC ha)) (widen C (eC z) comp bc hC)
  obtain ⟨T,eT,cT,hT⟩ := addWord (w:=w+1) D (eD (eC z)) _ (fun _ => 1) hD
    (constWord D (eD (eC z)) (eD (eC o)) 1)
  have eBT : B.Ext T := Bank.ext_trans eC (Bank.ext_trans eD eT)
  have hflag : T.Has (fun x => decide (b x ≤ a x)) :=
    mapWire (hT ⟨w, by omega⟩) (fun x => probe_high (ba x) (bb x))
  have hlow : HasWord T w (fun x => probe w (a x) (b x)) := fun i => hT ⟨i.val,by omega⟩
  obtain ⟨E,e,c,v⟩ := muxWord T _ _ a hflag hlow (keep eBT ha)
  refine ⟨E,Bank.ext_trans eBT e,by omega,e hflag,?_⟩
  intro i
  apply mapWire (v i)
  intro x
  by_cases h : b x ≤ a x
  · simp only [h,decide_true,↓reduceIte,not_lt_of_ge h]
    exact probe_low (ba x) (bb x) h i
  · simp [h,lt_of_not_ge h]

private theorem appendBit {s w : ℕ} (B : Bank s) (h : Env s → ℕ) (f : BitFn s)
    (hh : HasWord B w h) (hf : B.Has f) : HasWord B w (fun x => Nat.bit (f x) (h x)) := by
  intro i
  cases hi : i.val with
  | zero =>
    exact mapWire hf (fun x => by simp)
  | succ j =>
    exact mapWire (hh ⟨j,by omega⟩) (fun x => by simp [Nat.testBit_bit_succ])

def nextPrefix (h rank left : ℕ) := if rank<left then 2*h else 2*h+1

private theorem nextPrefix_eq (h rank left : ℕ) :
    nextPrefix h rank left = Nat.bit (decide (left≤rank)) h := by
  by_cases e : rank<left <;> simp [nextPrefix,e,Nat.bit,show (left≤rank) ↔ ¬rank<left by omega]

def PinnedCounter {s : ℕ} (base : Bank s) (k queryCost : ℕ) (C : Env s → ℕ → ℕ → ℕ) : Prop :=
  ∀ D : Bank s, base.Ext D → ∀ l, l≤k → ∀ h : Env s → ℕ,
    (∀ x, h x<2^(k-l)) → HasWord D k h →
    D.Grow queryCost (fun E => HasWord E (k+1) (fun x => C x l (h x)))

private theorem rankLoop {s k q : ℕ} (base : Bank s) (C : Env s → ℕ → ℕ → ℕ)
    (emit : PinnedCounter base k q C)
    (bounded : ∀ x l h, C x l h < 2^(k+1))
    (l : ℕ) (hl : l≤k) (D : Bank s) (ext : base.Ext D)
    (z : D.Has (fun _ => false)) (o : D.Has (fun _ => true))
    (h t : Env s → ℕ) (bh : ∀ x, h x<2^(k-l)) (bt : ∀ x, t x<2^(k+1))
    (hh : HasWord D k h) (ht : HasWord D (k+1) t) :
    D.Grow (l*(q+32*(k+2))) (fun E => HasWord E k (fun x => selectPrefix (C x) l (h x) (t x))) := by
  induction l generalizing D h t with
  | zero => exact ⟨D,Bank.ext_refl D,by simp,hh⟩
  | succ l ih =>
    have exp : 2^(k-l) = 2^(k-(l+1))*2 := by
      rw [show k-l = k-(l+1)+1 by omega,pow_succ]
    let even := fun x => 2*h x
    have be (x : Env s) : even x < 2^(k-l) := by have H := bh x; unfold even; rw [exp]; omega
    have we : HasWord D k even := by
      simpa only [Nat.bit_false] using appendBit D h (fun _ => false) hh z
    let left := fun x => C x l (even x)
    obtain ⟨A,eA,cA,cnt⟩ := emit D ext l (by omega) even be we
    obtain ⟨B,eB,cB,flag,rnk⟩ := subtractBranch A (eA z) (eA o) t left bt
      (fun x => bounded x l (even x)) (keep eA ht) cnt
    have edb : D.Ext B := Bank.ext_trans eA eB
    let nh := fun x => nextPrefix (h x) (t x) (left x)
    let nt := fun x => if t x<left x then t x else t x-left x
    have wh : HasWord B k nh := by
      simpa only [nh,nextPrefix_eq] using appendBit B h _ (keep edb hh) flag
    have bnh (x : Env s) : nh x<2^(k-l) := by
      have H := bh x
      unfold nh nextPrefix; rw [exp]; split <;> omega
    have bnt (x : Env s) : nt x<2^(k+1) := by
      have H := bt x
      unfold nt; split <;> omega
    obtain ⟨E,eE,cE,ans⟩ := ih (by omega) B (Bank.ext_trans ext edb)
      (edb z) (edb o) nh nt bnh bnt wh rnk
    refine ⟨E,Bank.ext_trans edb eE,?_,?_⟩
    · rw [Nat.succ_mul]; omega
    · intro i
      apply mapWire (ans i)
      intro x
      simp only [nh,nt,nextPrefix,selectPrefix,left,even]
      split <;> rfl

theorem compileRank {s k q : ℕ} (base : Bank s) (C : Env s → ℕ → ℕ → ℕ)
    (emit : PinnedCounter base k q C) (bounded : ∀ x l h, C x l h<2^(k+1))
    (t : Env s → ℕ) (bt : ∀ x, t x<2^(k+1)) (ht : HasWord base (k+1) t) :
    base.Grow (3+(k+1)*(q+32*(k+2))) (fun E =>
      HasWord E (k+1) (fun x => C x k 0) ∧ E.Has (fun x => decide (t x<C x k 0)) ∧
      HasWord E k (fun x => selectPrefix (C x) k 0 (t x))) := by
  obtain ⟨A,eA,cA,z⟩ := base.const false
  obtain ⟨B,eB,cB,o⟩ := A.const true
  have e0 : base.Ext B := Bank.ext_trans eA eB
  have zeroH : HasWord B k (fun _ => 0) := constWord B (eB z) o 0
  have bz (x : Env s) : (0:ℕ)<2^(k-k) := Nat.two_pow_pos _
  obtain ⟨D,eD,cD,cnt⟩ := emit B e0 k (le_refl _) (fun _ => 0) bz zeroH
  obtain ⟨T,eT,cT,right,_⟩ := subtractBranch D (eD (eB z)) (eD o) t _ bt
    (fun x => bounded x k 0) (keep (Bank.ext_trans e0 eD) ht) cnt
  obtain ⟨U,eU,cU,flag⟩ := Bank.inv right
  have eBU : B.Ext U := Bank.ext_trans eD (Bank.ext_trans eT eU)
  have e0U : base.Ext U := Bank.ext_trans e0 eBU
  obtain ⟨F,eF,cF,rank⟩ := rankLoop base C emit bounded k (le_refl _) U e0U
    (eBU (eB z)) (eBU o) (fun _ => 0) t bz bt (keep eBU zeroH) (keep e0U ht)
  refine ⟨F,Bank.ext_trans e0U eF,?_,keep (Bank.ext_trans eT (Bank.ext_trans eU eF)) cnt,
    eF (mapWire flag (fun x => by by_cases h : t x<C x k 0 <;> simp [h,Nat.not_le_of_gt,Nat.le_of_not_gt])),rank⟩
  rw [Nat.add_mul]; omega

def unshifted {s k : ℕ} (Q : Env s → ℕ → ℕ → ℕ) (g : Env s → Word k)
    (x : Env s) (l h : ℕ) := Q x l (h ^^^ ((g x).val >>> l))

theorem translateCounter {s k q : ℕ} (base : Bank s) (Q : Env s → ℕ → ℕ → ℕ)
    (g : Env s → Word k) (hg : HasWord base k (fun x => (g x).val))
    (emit : PinnedCounter base k q Q) :
    PinnedCounter base k (1+k*4+q) (unshifted Q g) := by
  intro D ext l hl h bh wh
  let shifted := fun x => (g x).val >>> l
  have bound (x : Env s) : shifted x < 2^(k-l) := by
    unfold shifted
    rw [Nat.shiftRight_eq_div_pow,Nat.div_lt_iff_lt_mul (Nat.two_pow_pos l),←pow_add,
      Nat.sub_add_cancel hl]
    exact (g x).isLt
  obtain ⟨F,eF,cF,z⟩ := D.const false
  have ge := keep (Bank.ext_trans ext eF) hg
  have gs : HasWord F k shifted := by
    intro i
    by_cases hi : l+i.val<k
    · exact mapWire (ge ⟨l+i.val,hi⟩) (fun x => by simp [shifted,Nat.testBit_shiftRight])
    · exact mapWire z (fun x => by
        change false = ((g x).val >>> l).testBit i.val
        rw [Nat.testBit_shiftRight, Nat.testBit_lt_two_pow
          ((g x).isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))])
  let key := fun x => h x ^^^ shifted x
  obtain ⟨E,eE,cE,pins⟩ := F.collectFin k (fun i x => (key x).testBit i.val) 4 (by
    intro S e i
    simpa only [key,Nat.testBit_xor] using Bank.xor2 (e (eF (wh i))) (e (gs i)))
  have e0E : base.Ext E := Bank.ext_trans ext (Bank.ext_trans eF eE)
  obtain ⟨U,eU,cU,out⟩ := emit E e0E l hl key (fun x => Nat.xor_lt_two_pow (bh x) (bound x)) pins
  exact ⟨U,Bank.ext_trans eF (Bank.ext_trans eE eU),by omega,out⟩

open Classical in
theorem compileOriginalRank {s k q : ℕ} (base : Bank s) (P : Env s → Word k → Prop)
    (Q : Env s → ℕ → ℕ → ℕ) (g : Env s → Word k) (hg : HasWord base k (fun x => (g x).val))
    (emit : PinnedCounter base k q Q)
    (hQ : ∀ x l h, Q x l h = (slice (fun w => P x (translate (g x) w)) l h).card)
    (t : Env s → ℕ) (bt : ∀ x, t x<2^(k+1)) (ht : HasWord base (k+1) t) :
    let N := fun x => Nat.card {w : Word k // P x w}
    let picked := fun x => selectPrefix (unshifted Q g x) k 0 (t x)
    base.Grow (3+(k+1)*((1+k*4+q)+32*(k+2))) (fun E =>
      HasWord E (k+1) N ∧ E.Has (fun x => decide (t x<N x)) ∧ HasWord E k picked ∧
      ∀ x j, (∃ w : Word k, P x w ∧ Nat.card {z : Word k // z<w ∧ P x z} = t x ∧
        (j=0 ∨ w.val.testBit (j-1)=true)) ↔ t x<N x ∧ (j=0 ∨ (picked x).testBit (j-1)=true)) := by
  let C := unshifted Q g
  have bound (x : Env s) (l h : ℕ) : C x l h<2^(k+1) := by
    unfold C unshifted
    rw [hQ]
    apply lt_of_le_of_lt (Finset.card_le_univ _)
    simp [Word,pow_succ]
  have correct (x : Env s) (j : ℕ) := original_rank_interface (P x) (g x) (Q x) (hQ x) (t x) j
  have cnt (x : Env s) : C x k 0 = Nat.card {w : Word k // P x w} := (correct x 0).1
  obtain ⟨E,e,c,w,flag,out⟩ := compileRank base C (translateCounter base Q g hg emit) bound t bt ht
  refine ⟨E,e,c,?_,mapWire flag (fun x => by rw [cnt]),out,?_⟩
  · intro i
    exact mapWire (w i) (fun x => congrArg (fun v : Nat => v.testBit i.val) (cnt x))
  · intro x j
    have eq := (correct x j).2
    change _ ↔ t x<C x k 0 ∧ _ at eq
    rwa [cnt] at eq

theorem counter_mod {s k q : ℕ} {base : Bank s} {Q : Env s → ℕ → ℕ → ℕ}
    (emit : PinnedCounter base k q Q) :
    PinnedCounter base k q (fun x l h => Q x l h % 2^(k+1)) := by
  intro D ed l hl h bh wh
  obtain ⟨E,e,c,w⟩ := emit D ed l hl h bh wh
  exact ⟨E,e,c,fun j => mapWire (w j) (fun x => by simp [Nat.testBit_mod_two_pow,j.isLt])⟩

open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit.Layout

theorem readPostedField {k r v trailing : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (bank : Fin k → Bool) (before after : List Bool) (word : Fin (2^v))
    (ht : (before ++ bits v word.val ++ after).length=trailing) :
    let x := encoded nr nc cr cc bank (before ++ bits v word.val ++ after) ht
    readWord v (3*k+2*r*k+before.length) x = word := by
  let x := encoded nr nc cr cc bank (before ++ bits v word.val ++ after) ht
  let pre := cfg nr nc cr cc bank ++ before
  have hl : pre.length=3*k+2*r*k+before.length := by simp [pre]
  have hx : List.ofFn x=pre++bits v word.val++after := by
    rw [show List.ofFn x = _ from ofFn_encoded nr nc cr cc bank _ _]
    simp [pre,List.append_assoc]
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i<v
  · change (readWord v _ x).val.testBit i = _
    rw [readWord_bit v _ x ⟨i,hi⟩]
    unfold raw
    rw [hx,←hl,List.getD_append _ _ _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by omega),Nat.add_sub_cancel_left]
    simp [bits,List.getD_eq_getElem?_getD,hi]
  · have p := Nat.pow_le_pow_right Nat.zero_lt_two (show v ≤ i by omega)
    rw [Nat.testBit_lt_two_pow ((readWord v _ x).isLt.trans_le p),Nat.testBit_lt_two_pow (word.isLt.trans_le p)]

end PEqualNP.Outside.L_meta_33676_aux.RankCircuit

namespace PEqualNP.Outside.L_meta_33676_aux.QueryCircuit

open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit Builder Layout
open PEqualNP.Outside.L_meta_33676_aux.Windows (reach)

private theorem mapWire {s} {B : Bank s} {f g : BitFn s} (h : B.Has f) (eq : ∀ x, f x=g x) :
    B.Has g := by
  obtain ⟨i,hi,h⟩ := h
  exact ⟨i,hi,fun x => (h x).trans (eq x)⟩

private theorem allWire {s : ℕ} {I : Type} (l : List I) (B : Bank s)
    (f : I → BitFn s) (hf : ∀ i, B.Has (f i)) (ho : B.Has (fun _ => true)) :
    B.Grow l.length (fun E => E.Has (fun x => l.all (fun i => f i x))) := by
  induction l with
  | nil => exact Bank.Grow.pure B ho
  | cons i l ih =>
    obtain ⟨D,e,c,w⟩ := ih
    obtain ⟨E,e',c',out⟩ := Bank.meet (e (hf i)) w
    exact ⟨E,Bank.ext_trans e e',by simp; omega,out⟩

def valid {N : ℕ} (k r d : ℕ) (x : Env N) : Bool :=
  decide (∀ i : Fin k, reach r (bankBit r x i) ≤ d)

theorem validCircuit {N : ℕ} (k r d : ℕ) (B : Bank N) (ext : (Bank.empty N).Ext B) :
    B.Grow (2+5*k) (fun E => E.Has (valid k r d)) := by
  obtain ⟨C,eC,cC,z⟩ := B.const false
  obtain ⟨D,eD,cD,o⟩ := C.const true
  have hcons (b : Bool) : D.Has (fun _ => b) := by cases b; exact eD z; exact o
  have e0 : (Bank.empty N).Ext D := Bank.ext_trans ext (Bank.ext_trans eC eD)
  let good := fun (i : Fin k) (x : Env N) => decide (reach r (bankBit r x i) ≤ d)
  obtain ⟨T,eT,cT,hT⟩ := D.collectFin k good 4 (by
    intro F e i
    obtain ⟨G,h,c,w⟩ := Bank.mux (e (empty_raw D e0 (eD z) (2*k+2*r*k+i.val)))
      (e (hcons (decide (reach r true ≤ d)))) (e (hcons (decide (reach r false ≤ d))))
    exact ⟨G,h,c,mapWire w (fun x => by
      change (if bankBit r x i then _ else _) = decide (reach r (bankBit r x i) ≤ d)
      cases bankBit r x i <;> rfl)⟩)
  obtain ⟨E,e,c,w⟩ := allWire (List.finRange k) T good hT (eT o)
  refine ⟨E,Bank.ext_trans (Bank.ext_trans eC eD) (Bank.ext_trans eT e),?_,mapWire w (fun x => ?_)⟩
  · simp at c; omega
  · apply Bool.eq_iff_iff.mpr; simp [good,valid]

private theorem wordEq {s w : ℕ} (B : Bank s) (q : Env s → Fin (2^w)) (idx : Fin (2^w))
    (hq : ∀ i : Fin w, B.Has (fun x => (q x).val.testBit i.val)) (ho : B.Has (fun _ => true)) :
    B.Grow (w*2) (fun E => E.Has (fun x => decide ((q x).val=idx.val))) := by
  let f := fun (i : Fin w) (x : Env s) => (q x).val.testBit i.val == idx.val.testBit i.val
  obtain ⟨D,e,c,wires⟩ := B.collectFin w f 1 (by
    intro E e i
    cases h : idx.val.testBit i.val with
    | false =>
      obtain ⟨F,ef,cf,wire⟩ := Bank.inv (e (hq i))
      exact ⟨F,ef,cf,mapWire wire (fun x => by simp [f,h])⟩
    | true =>
      exact ⟨E,Bank.ext_refl E,by omega,mapWire (e (hq i)) (fun x => by simp [f,h])⟩)
  obtain ⟨E,ef,cf,out⟩ := allWire (List.finRange w) D f wires (e ho)
  refine ⟨E,Bank.ext_trans e ef,?_,mapWire out (fun x => ?_)⟩
  · simp at c cf; omega
  · apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true,List.mem_finRange,forall_true_left,f,beq_iff_eq,decide_eq_true_eq]
    constructor
    · intro eq
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i<w
      · exact eq ⟨i,hi⟩
      · have hpow := Nat.pow_le_pow_right Nat.zero_lt_two (show w ≤ i by omega)
        rw [Nat.testBit_lt_two_pow ((q x).isLt.trans_le hpow),Nat.testBit_lt_two_pow (idx.isLt.trans_le hpow)]
    · intro eq i; rw [eq]

def queryIndex {s w : ℕ} (k : ℕ) (q : Env s → Fin (2^w)) (x : Env s) : Option (Fin (k+1)) :=
  (List.ofFn (id : Fin (k+1) → Fin (k+1))).find? (fun i => decide ((q x).val=i.val))

theorem queryIndex_eq {s w k : ℕ} (q : Env s → Fin (2^w)) (x : Env s) (j : Fin (k+1))
    (h : (q x).val=j.val) : queryIndex k q x = some j := by
  unfold queryIndex
  apply (List.find?_ofFn_eq_some_of_injective (f:=id) (i:=j) Function.injective_id).mpr
  refine ⟨by simp [h],?_⟩
  intro i hi
  simp only [id_eq,decide_eq_true_eq,h]
  exact ne_of_gt hi

def sentinel {s k : ℕ} (least : Fin k → BitFn s) : Fin (k+1) → BitFn s := Fin.cons (fun _ => true) least

def packed {s w : ℕ} (k : ℕ) (q : Env s → Fin (2^w)) (mode validFlag existsFlag : BitFn s)
    (bits : Fin (k+1) → BitFn s) (least : Fin k → BitFn s) (x : Env s) : Bool :=
  let j := queryIndex k q x
  validFlag x && (if mode x then (j.map (fun i => bits i x)).getD false
    else existsFlag x && (j.map (fun i => sentinel least i x)).getD false)

def queryCost (k w : ℕ) := 2+(k+1)*(w*2)+2*((k+1)*4)+6

theorem queryCircuit {s w : ℕ} (k : ℕ) (hw : k+1 ≤ 2^w) (B : Bank s)
    (q : Env s → Fin (2^w)) (mode validFlag existsFlag : BitFn s)
    (bits : Fin (k+1) → BitFn s) (least : Fin k → BitFn s)
    (hq : ∀ i : Fin w, B.Has (fun x => (q x).val.testBit i.val))
    (hm : B.Has mode) (hv : B.Has validFlag) (he : B.Has existsFlag)
    (hc : ∀ j, B.Has (bits j)) (hl : ∀ j, B.Has (least j)) :
    B.Grow (queryCost k w) (fun E => E.Has (packed k q mode validFlag existsFlag bits least)) := by
  obtain ⟨C,eC,cC,z⟩ := B.const false
  obtain ⟨D,eD,cD,o⟩ := C.const true
  have eb : B.Ext D := Bank.ext_trans eC eD
  let test := fun (i : Fin (k+1)) (x : Env s) => decide ((q x).val=i.val)
  obtain ⟨T,eT,cT,hT⟩ := D.collectFin (k+1) test (w*2) (by
    intro E e i
    exact wordEq E q ⟨i.val,i.isLt.trans_le hw⟩ (fun j => e (eb (hq j))) (e o))
  let l := List.ofFn (id : Fin (k+1) → Fin (k+1))
  obtain ⟨A,eA,cA,value⟩ := EliminationCircuit.firstWire l T test bits hT
    (fun i => eT (eb (hc i))) (eT (eD z))
  have sel (i : Fin (k+1)) : A.Has (sentinel least i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact eA (eT o)
    · exact eA (eT (eb (hl j)))
  obtain ⟨U,eU,cU,ls⟩ := EliminationCircuit.firstWire l A test (sentinel least)
    (fun i => eA (hT i)) sel (eA (eT (eD z)))
  have eu : B.Ext U := Bank.ext_trans eb (Bank.ext_trans eT (Bank.ext_trans eA eU))
  obtain ⟨P,eP,cP,enable⟩ := Bank.meet (eu he) ls
  obtain ⟨H,eH,cH,out⟩ := Bank.mux (eP (eu hm)) (eP (eU value)) enable
  obtain ⟨F,eF,cF,done⟩ := Bank.meet (eH (eP (eu hv))) out
  refine ⟨F,Bank.ext_trans eu (Bank.ext_trans eP (Bank.ext_trans eH eF)),?_,done⟩
  simp [l] at cA cU
  unfold queryCost
  omega

def indexWord {N : ℕ} (k r before : ℕ) (x : Env N) := readWord (k+1) (3*k+2*r*k+before) x
def countMode {N : ℕ} (k r before : ℕ) (x : Env N) := raw x (3*k+2*r*k+before+(k+1))
def queryTail {k : ℕ} (before : List Bool) (j : Fin (k+1)) (mode : Bool) :=
  before ++ bits (k+1) j.val ++ [mode]

@[simp] theorem queryTail_length {k : ℕ} (before : List Bool) (j : Fin (k+1)) (mode : Bool) :
    (queryTail before j mode).length = before.length+(k+1)+1 := by simp [queryTail,Nat.add_assoc]

theorem decodeQuery {k r : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (bank : Fin k → Bool) (before : List Bool) (j : Fin (k+1)) (mode : Bool) :
    let x := encoded nr nc cr cc bank (queryTail before j mode) (queryTail_length before j mode)
    (indexWord k r before.length x).val = j.val ∧ countMode k r before.length x = mode := by
  let x := encoded nr nc cr cc bank (queryTail before j mode) (queryTail_length before j mode)
  let pre := cfg nr nc cr cc bank ++ before
  have hlen : pre.length = 3*k+2*r*k+before.length := by simp [pre]
  have hx : List.ofFn x = pre ++ bits (k+1) j.val ++ [mode] := by
    rw [show List.ofFn x = _ from ofFn_encoded nr nc cr cc bank _ _]
    simp [pre,queryTail,List.append_assoc]
  constructor
  · apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < k+1
    · change (readWord (k+1) _ x).val.testBit i = _
      rw [readWord_bit (k+1) _ x ⟨i,hi⟩]
      unfold raw
      rw [hx,←hlen,List.getD_append _ _ _ _ (by simp; omega),
        List.getD_append_right _ _ _ _ (by omega),Nat.add_sub_cancel_left]
      simp [bits,List.getD_eq_getElem?_getD,hi]
    · have hpow := Nat.pow_le_pow_right Nat.zero_lt_two (show k+1 ≤ i by omega)
      rw [Nat.testBit_lt_two_pow ((indexWord k r before.length x).isLt.trans_le hpow),
        Nat.testBit_lt_two_pow ((j.isLt.trans (Nat.lt_two_pow_self)).trans_le hpow)]
  · change raw x (3*k+2*r*k+before.length+(k+1)) = mode
    unfold raw
    rw [hx,←hlen,← show (pre++bits (k+1) j.val).length = pre.length+(k+1) by simp]
    simp [List.getD_eq_getElem?_getD]

def layoutCost (k : ℕ) := 1+(2+5*k)+queryCost k (k+1)

theorem postedQueryCircuit {N : ℕ} (k r d before : ℕ) (B : Bank N) (ext : (Bank.empty N).Ext B)
    (existsFlag : BitFn N) (countBits : Fin (k+1) → BitFn N) (least : Fin k → BitFn N)
    (he : B.Has existsFlag) (hc : ∀ j, B.Has (countBits j)) (hl : ∀ j, B.Has (least j)) :
    B.Grow (layoutCost k) (fun E => E.Has (packed k (indexWord k r before) (countMode k r before)
      (valid k r d) existsFlag countBits least)) := by
  obtain ⟨C,eC,cC,z⟩ := B.const false
  obtain ⟨D,eD,cD,v⟩ := validCircuit k r d C (Bank.ext_trans ext eC)
  have eb : B.Ext D := Bank.ext_trans eC eD
  have e0 : (Bank.empty N).Ext D := Bank.ext_trans ext eb
  obtain ⟨E,eE,cE,ans⟩ := queryCircuit k (Nat.le_of_lt Nat.lt_two_pow_self) D
    (indexWord k r before) (countMode k r before) (valid k r d) existsFlag countBits least
    (readWord_wires D e0 (eD z) (k+1) (3*k+2*r*k+before))
    (empty_raw D e0 (eD z) (3*k+2*r*k+before+(k+1))) v (eb he)
    (fun i => eb (hc i)) (fun i => eb (hl i))
  exact ⟨E,Bank.ext_trans eb eE,by unfold layoutCost; omega,ans⟩

theorem sentinel_word {s k : ℕ} (least : Env s → ℕ) (j : Fin (k+1)) (x : Env s) :
    sentinel (fun i x => (least x).testBit i.val) j x =
      decide (j.val=0 ∨ (least x).testBit (j.val-1)=true) := by
  refine Fin.cases ?_ (fun a => ?_) j
  · simp [sentinel]
  · simp [sentinel]

theorem postedQuery_eval {k r d : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (bank : Fin k → Bool) (before : List Bool) (j : Fin (k+1)) (mode : Bool)
    (existsFlag : BitFn (inLen k r (before.length+(k+1)+1)))
    (cnt least : Env (inLen k r (before.length+(k+1)+1)) → ℕ) :
    let x := encoded nr nc cr cc bank (queryTail before j mode) (queryTail_length before j mode)
    packed k (indexWord k r before.length) (countMode k r before.length) (valid k r d)
      existsFlag (fun i u => (cnt u).testBit i.val) (fun i u => (least u).testBit i.val) x =
      (decide (∀ i, reach r (bank i) ≤ d) &&
        (if mode then (cnt x).testBit j.val else existsFlag x &&
          decide (j.val=0 ∨ (least x).testBit (j.val-1)=true))) := by
  let x := encoded nr nc cr cc bank (queryTail before j mode) (queryTail_length before j mode)
  obtain ⟨hi,hm⟩ := decodeQuery nr nc cr cc bank before j mode
  have hi : (indexWord k r before.length x).val=j.val := hi
  have hm : countMode k r before.length x=mode := hm
  have hb : bankBit r x=bank := (decode_encoded nr nc cr cc bank _ _).2.2.2.2
  have hv : valid k r d x = decide (∀ i, reach r (bank i) ≤ d) := by unfold valid; rw [hb]
  change packed k _ _ _ _ _ _ x = _
  unfold packed
  rw [queryIndex_eq _ _ j hi,hm,hv]
  simp [sentinel_word]
  rfl

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem finish {N budget : ℕ} {f : BitFn N}
    (h : (Bank.empty N).Grow budget (fun E => E.Has f)) :
    ∃ A : Circuit, FanInTwo A ∧ ReadsBack N A ∧ A.size ≤ budget ∧
      ∀ x, A.eval (List.ofFn x) = f x := by
  obtain ⟨E,_,cost,i,_,ev⟩ := h
  exact ⟨⟨E.gates,i⟩,E.fan,E.back,by simpa [Circuit.size,Bank.empty] using cost,ev⟩

theorem layoutCost_bound (k : ℕ) : layoutCost k ≤ 32*(k+1)^2 := by
  unfold layoutCost queryCost
  nlinarith [Nat.zero_le k,Nat.zero_le (k*k)]

abbrev aLen (k r : ℕ) := inLen k r (0+(k+1)+1)

theorem finishA {k r d budget : ℕ} (existsFlag : BitFn (aLen k r)) (cnt least : Env (aLen k r) → ℕ)
    (h : (Bank.empty (aLen k r)).Grow budget (fun E => E.Has (packed k (indexWord k r 0)
      (countMode k r 0) (valid k r d) existsFlag (fun i x => (cnt x).testBit i.val)
      (fun i x => (least x).testBit i.val)))) :
    ∃ A : Circuit, FanInTwo A ∧ ReadsBack (3*k+2*r*k+(k+1)+1) A ∧ A.size ≤ budget ∧
      ∀ (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k)) (bank : Fin k → Bool)
        (j : Fin (k+1)) (mode : Bool),
        let x := encoded nr nc cr cc bank (queryTail [] j mode) (queryTail_length [] j mode)
        A.eval (cfg nr nc cr cc bank ++ bits (k+1) j.val ++ [mode]) =
          (decide (∀ i, reach r (bank i) ≤ d) &&
          (if mode then (cnt x).testBit j.val else existsFlag x &&
            decide (j.val=0 ∨ (least x).testBit (j.val-1)=true))) := by
  obtain ⟨A,fan,back,size,correct⟩ := finish h
  refine ⟨A,fan,?_,size,?_⟩
  · convert back using 1
    simp [aLen,inLen,Nat.add_assoc]
  · intro nr nc cr cc bank j mode
    let x := encoded nr nc cr cc bank (queryTail [] j mode) (queryTail_length [] j mode)
    have hlist : List.ofFn x = cfg nr nc cr cc bank ++ bits (k+1) j.val ++ [mode] := by
      rw [show List.ofFn x = _ from ofFn_encoded nr nc cr cc bank _ _]
      simp [queryTail,List.append_assoc]
    rw [← hlist,correct]
    exact postedQuery_eval nr nc cr cc bank [] j mode existsFlag cnt least

end PEqualNP.Outside.L_meta_33676_aux.QueryCircuit

namespace PEqualNP.Outside.L_meta_33676_aux.RankedC

open Translation ShiftCriterion
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit Builder Layout
open PEqualNP.Outside.L_meta_33676_aux.Windows (reach)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open RankCircuit (PinnedCounter)
open GoodLeastBank (cfgLeast)
open GoodBank (cfgCount)
open QueryCircuit (indexWord countMode packed queryIndex_eq)

def trailing (k n : ℕ) := n+2*(k+1)+1
def numInputs (p n r : ℕ) := inLen (p*n) r (trailing (p*n) n)
def target {s : ℕ} (k n r : ℕ) (x : Env s) := readWord n (3*k+2*r*k) x
def rankField {s : ℕ} (k n r : ℕ) (x : Env s) := readWord (k+1) (3*k+2*r*k+n) x

def report {s p n : ℕ} (hp : 0<p) (hn : 0<n) (r : ℕ) (x : Env s) :=
  rawReport (r:=r) hp hn (rowName (p*n) x) (colName (p*n) x)
    (rowSchedule (p*n) x) (colSchedule (p*n) x) (bankBit r x)

def hit {s p n : ℕ} (hp : 0<p) (hn : 0<n) (r : ℕ) (x : Env s) (w : Word (p*n)) : Prop :=
  ∀ i : Fin n, report hp hn r x w.val i = (target (p*n) n r x).val.testBit i.val

def OracleSpec {p n : ℕ} (hp : 0<p) (hn : 0<n) (r d : ℕ)
    (Q : Env (numInputs p n r) → ℕ → ℕ → ℕ) : Prop :=
  ∀ x, GoodBank.Valid (p*n) r d x → 0<cfgCount hp hn r d x →
    ∀ l, l≤p*n → ∀ h, h<2^(p*n-l) →
      Q x l h = (Ranking.slice (fun w => hit hp hn r x (Ranking.translate (cfgLeast hp hn r d x) w)) l h).card

def budget (k prep q : ℕ) := prep+1+(3+(k+1)*((1+k*4+q)+32*(k+2)))+QueryCircuit.layoutCost k+1

private theorem prefix_congr {k : ℕ} (A B : ℕ → ℕ → ℕ)
    (eq : ∀ l, l≤k → ∀ h, h<2^(k-l) → A l h=B l h) (l : ℕ) (hl : l≤k) (h t : ℕ)
    (bh : h<2^(k-l)) : Ranking.selectPrefix A l h t = Ranking.selectPrefix B l h t := by
  induction l generalizing h t with
  | zero => rfl
  | succ l ih =>
    have exp : 2^(k-l) = 2^(k-(l+1))*2 := by rw [show k-l=k-(l+1)+1 by omega,pow_succ]
    have left : 2*h<2^(k-l) := by rw [exp]; omega
    have right : 2*h+1<2^(k-l) := by rw [exp]; omega
    simp only [Ranking.selectPrefix,eq l (by omega) (2*h) left]
    split <;> exact ih (by omega) _ _ (by first | exact left | exact right)

noncomputable def effective {s k : ℕ} (Q : Env s → ℕ → ℕ → ℕ) (g : Env s → Word k) :=
  RankCircuit.unshifted (fun x l h => Q x l h % 2^(k+1)) g

private theorem actualRank {k : ℕ} (P : Word k → Prop) (g : Word k) (Q : ℕ → ℕ → ℕ)
    (eq : ∀ l, l≤k → ∀ h, h<2^(k-l) → Q l h=(Ranking.slice (fun w => P (Ranking.translate g w)) l h).card)
    (t j : ℕ) :
    let C := fun l h => Q l (h ^^^ (g.val >>> l)) % 2^(k+1)
    C k 0 = Nat.card {w : Word k // P w} ∧
    ((∃ w : Word k, P w ∧ Nat.card {z : Word k // z<w ∧ P z}=t ∧
      (j=0 ∨ w.val.testBit (j-1)=true)) ↔ t<C k 0 ∧ (j=0 ∨ (Ranking.selectPrefix C k 0 t).testBit (j-1)=true)) := by
  intro C
  let Q' := fun l h => (Ranking.slice (fun w => P (Ranking.translate g w)) l h).card
  let C' := fun l h => Q' l (h ^^^ (g.val >>> l))
  have same (l : ℕ) (hl : l≤k) (h : ℕ) (bh : h<2^(k-l)) : C l h=C' l h := by
    have gs : g.val >>> l<2^(k-l) := by
      rw [Nat.shiftRight_eq_div_pow,Nat.div_lt_iff_lt_mul (Nat.two_pow_pos l),←pow_add,Nat.sub_add_cancel hl]
      exact g.isLt
    change Q _ _ % _ = _
    rw [eq l hl _ (Nat.xor_lt_two_pow bh gs)]
    apply Nat.mod_eq_of_lt
    apply lt_of_le_of_lt (Finset.card_le_univ _)
    simp [pow_succ]
  have init := same k (le_refl _) 0 (Nat.two_pow_pos _)
  rw [init,prefix_congr C C' same k (le_refl _) 0 t (Nat.two_pow_pos _)]
  exact Ranking.original_rank_interface P g Q' (fun _ _ => rfl) t j

def querySuffix {k n : ℕ} (y : Word n) (t : Word (k+1)) (j : Fin (k+1)) (mode : Bool) :=
  bits n y.val ++ bits (k+1) t.val ++ bits (k+1) j.val ++ [mode]

@[simp] theorem queryLength {k n : ℕ} (y : Word n) (t : Word (k+1)) (j : Fin (k+1)) (mode : Bool) :
    (querySuffix y t j mode).length = trailing k n := by simp [querySuffix,trailing]; omega

def cfgEnv {p n r : ℕ} (nr nc : Word (p*n)) (cr cc : Fin r → Word (p*n)) (bank : Fin (p*n) → Bool)
    (y : Word n) (t : Word (p*n+1)) (j : Fin (p*n+1)) (mode : Bool) : Env (numInputs p n r) :=
  encoded nr nc cr cc bank (querySuffix y t j mode) (queryLength y t j mode)

private theorem read_field {s v : ℕ} (x : Env s) (before after : List Bool) (w : Fin (2^v))
    (hx : List.ofFn x = before++bits v w.val++after) : readWord v before.length x = w := by
  apply Fin.ext; apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i<v
  · rw [readWord_bit v _ x ⟨i,hi⟩]
    unfold raw
    rw [hx,List.getD_append _ _ _ _ (by simp; omega),List.getD_append_right _ _ _ _ (by omega),
      Nat.add_sub_cancel_left]
    simp [bits,List.getD_eq_getElem?_getD,hi]
  · have pw := Nat.pow_le_pow_right Nat.zero_lt_two (show v ≤ i by omega)
    rw [Nat.testBit_lt_two_pow ((readWord v _ x).isLt.trans_le pw),Nat.testBit_lt_two_pow (w.isLt.trans_le pw)]

private theorem decode {p n r : ℕ} (nr nc : Word (p*n)) (cr cc : Fin r → Word (p*n)) (bank : Fin (p*n) → Bool)
    (y : Word n) (t : Word (p*n+1)) (j : Fin (p*n+1)) (mode : Bool) :
    let k := p*n
    let x := cfgEnv nr nc cr cc bank y t j mode
    target k n r x=y ∧ rankField k n r x=t ∧ (indexWord k r (n+(k+1)) x).val=j.val ∧
      countMode k r (n+(k+1)) x=mode := by
  let k := p*n
  let x := cfgEnv nr nc cr cc bank y t j mode
  let head := cfg nr nc cr cc bank
  have h : List.ofFn x = head++bits n y.val++bits (k+1) t.val++bits (k+1) j.val++[mode] := by
    rw [show List.ofFn x = _ from ofFn_encoded nr nc cr cc bank _ _]
    simp [querySuffix,head,k,List.append_assoc]
  have hh : head.length=3*k+2*r*k := cfg_length _ _ _ _ _
  let jw : Fin (2^(k+1)) := ⟨j.val,j.isLt.trans Nat.lt_two_pow_self⟩
  change target k n r x=y ∧ rankField k n r x=t ∧ (indexWord k r (n+(k+1)) x).val=j.val ∧ _
  refine ⟨?_,?_,?_,?_⟩
  · unfold target; rw [←hh]
    exact read_field x head (bits (k+1) t.val++bits (k+1) j.val++[mode]) y (by rw [h]; simp [List.append_assoc])
  · unfold rankField; rw [←hh,← show (head++bits n y.val).length=head.length+n by simp]
    exact read_field x (head++bits n y.val) (bits (k+1) j.val++[mode]) t (by rw [h]; simp [List.append_assoc,k])
  · have he : (head++bits n y.val++bits (k+1) t.val).length=3*k+2*r*k+(n+(k+1)) := by simp [hh,Nat.add_assoc]
    exact congrArg Fin.val (show indexWord k r (n+(k+1)) x=jw by
      unfold indexWord; rw [←he]; exact read_field x _ [mode] jw h)
  · change raw x (3*k+2*r*k+(n+(k+1))+(k+1))=mode
    have he : (head++bits n y.val++bits (k+1) t.val++bits (k+1) j.val).length=3*k+2*r*k+(n+(k+1))+(k+1) := by
      simp [hh,Nat.add_assoc]
    unfold raw
    rw [h,←he]
    simp [List.getD_eq_getElem?_getD]

noncomputable def output {p n : ℕ} (hp : 0<p) (hn : 0<n) (r d : ℕ)
    (Q : Env (numInputs p n r) → ℕ → ℕ → ℕ) (x : Env (numInputs p n r)) : Bool :=
  let k := p*n
  let C := effective Q (cfgLeast hp hn r d)
  let t := fun z => (rankField k n r z).val
  let cnt := fun z => C z k 0
  let picked := fun z => Ranking.selectPrefix (C z) k 0 (t z)
  decide (0<cfgCount hp hn r d x) &&
    packed k (indexWord k r (n+(k+1))) (countMode k r (n+(k+1))) (QueryCircuit.valid k r d)
      (fun z => decide (t z<cnt z)) (fun i z => (cnt z).testBit i.val)
      (fun i z => (picked z).testBit i.val) x

theorem grow {p n : ℕ} (hp : 0<p) (hn : 0<n) (r d q prep : ℕ)
    (Q : Env (numInputs p n r) → ℕ → ℕ → ℕ)
    (setup : (Bank.empty (numInputs p n r)).Grow prep (fun B =>
      GoodLeastBank.HasBank hp hn r d B ∧ PinnedCounter B (p*n) q Q)) :
    (Bank.empty (numInputs p n r)).Grow (budget (p*n) prep q) (fun E => E.Has (output hp hn r d Q)) := by
  let k := p*n
  let N := numInputs p n r
  let g : Env N → Word k := cfgLeast hp hn r d
  let t := fun z : Env N => (rankField k n r z).val
  let C := effective Q g
  obtain ⟨B,eB,cB,hb,emit⟩ := setup
  obtain ⟨Z,eZ,cZ,z⟩ := B.const false
  have e0Z : (Bank.empty N).Ext Z := Bank.ext_trans eB eZ
  have emZ : PinnedCounter Z k q Q :=
    fun F e l hl h bh wh => emit F (Bank.ext_trans eZ e) l hl h bh wh
  have gWire : WeightedCircuit.HasWord Z k (fun x => (g x).val) := fun i => eZ (hb.least i)
  have cs : PinnedCounter Z k (1+k*4+q) C := RankCircuit.translateCounter Z _ g gWire (RankCircuit.counter_mod emZ)
  have ht : WeightedCircuit.HasWord Z (k+1) t := readWord_wires Z e0Z z (k+1) _
  obtain ⟨D,eD,cD,digits,flag,picked⟩ := RankCircuit.compileRank Z C cs
    (fun _ _ _ => Nat.mod_lt _ (Nat.two_pow_pos _)) t (fun x => (rankField k n r x).isLt) ht
  have e0D : (Bank.empty N).Ext D := Bank.ext_trans e0Z eD
  obtain ⟨T,eT,cT,ans⟩ := QueryCircuit.postedQueryCircuit k r d (n+(k+1)) D e0D
    _ _ _ flag digits picked
  obtain ⟨U,eU,cU,done⟩ := Bank.meet (eT (eD (eZ hb.feasible))) ans
  exact ⟨U,Bank.ext_trans e0D (Bank.ext_trans eT eU),by unfold budget; dsimp [k] at cD cT; omega,done⟩

open Classical in
theorem value {p n r d : ℕ} (hp : 0<p) (hn : 0<n) (hk : n<p*n) (hd : d<n) (hr : 4≤r)
    (Q : Env (numInputs p n r) → ℕ → ℕ → ℕ) (spec : OracleSpec hp hn r d Q)
    (x : Env (numInputs p n r)) (j : Fin (p*n+1)) (mode : Bool)
    (hi : (indexWord (p*n) r (n+(p*n+1)) x).val=j.val)
    (hm : countMode (p*n) r (n+(p*n+1)) x=mode) :
    output hp hn r d Q x = decide (GoodBank.Valid (p*n) r d x ∧
      (∃ g : Word (p*n), rawGood (report hp hn r x) n g) ∧
      (if mode then (Nat.card {w : Word (p*n) // hit hp hn r x w}).testBit j.val=true
       else ∃ w : Word (p*n), hit hp hn r x w ∧
         Nat.card {z : Word (p*n) // z<w ∧ hit hp hn r x z}=(rankField (p*n) n r x).val ∧
         (j.val=0 ∨ w.val.testBit (j.val-1)=true))) := by
  unfold output packed
  dsimp only
  rw [queryIndex_eq _ _ j hi,hm]
  simp only [Option.map_some, Option.getD_some, QueryCircuit.sentinel_word]
  have validFlag : QueryCircuit.valid (p*n) r d x = decide (GoodBank.Valid (p*n) r d x) := by
    unfold QueryCircuit.valid GoodBank.Valid
    apply congrArg (fun D : Decidable (∀ i : Fin (p*n), reach r (bankBit r x i) ≤ d) => @decide _ D)
    exact Subsingleton.elim _ _
  rw [validFlag]
  by_cases hv : GoodBank.Valid (p*n) r d x
  · have gh : 0<cfgCount hp hn r d x ↔ ∃ g : Word (p*n), rawGood (report hp hn r x) n g := by
      rw [GoodBank.cfgCount_correct hp hn hk hd hr x hv]
      exact GoodBank.feasible_count_iff _
    by_cases hg : 0<cfgCount hp hn r d x
    · have eq := actualRank (hit hp hn r x) (cfgLeast hp hn r d x) (Q x) (spec x hv hg)
        (rankField (p*n) n r x).val j.val
      let C := effective Q (cfgLeast hp hn r d)
      change C x (p*n) 0 = _ ∧ (_ ↔ (rankField (p*n) n r x).val<C x (p*n) 0 ∧ _) at eq
      have ex := gh.mp hg
      cases mode
      · simp only [hv,hg,ex,decide_true,Bool.true_and,true_and,Bool.false_eq_true,↓reduceIte]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true,decide_eq_true_eq]
        exact eq.2.symm
      · simp only [hv,hg,ex,decide_true,Bool.true_and,true_and,↓reduceIte]
        rw [←eq.1]
        simp [C]
    · have ex := mt gh.mpr hg
      simp [hg,ex]
  · simp [hv]

open Classical in
theorem physical {p n r d : ℕ} (hp : 0<p) (hn : 0<n) (hk : n<p*n) (hd : d<n) (hr : 4≤r)
    (Q : Env (numInputs p n r) → ℕ → ℕ → ℕ) (q prep : ℕ)
    (setup : (Bank.empty (numInputs p n r)).Grow prep (fun B =>
      GoodLeastBank.HasBank hp hn r d B ∧ PinnedCounter B (p*n) q Q))
    (spec : OracleSpec hp hn r d Q)
    (size : budget (p*n) prep q ≤ 2^60*(p*n+r+2^d+5)^28*((p+(2^d)^3).choose p)) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack (3*(p*n)+2*r*(p*n)+n+2*(p*n+1)+1) C ∧
      C.size ≤ 2^60*(p*n+r+2^d+5)^28*((p+(2^d)^3).choose p) ∧
      ∀ (nr nc : Word (p*n)) (cr cc : Fin r → Word (p*n)) (bank : Fin (p*n) → Bool)
        (y : Word n) (t : Word (p*n+1)) (j : Fin (p*n+1)) (mode : Bool),
        let H := rawReport hp hn nr nc cr cc bank
        let P := fun w : Word (p*n) => ∀ i : Fin n, H w.val i = y.val.testBit i.val
        C.eval (cfg nr nc cr cc bank ++ bits n y.val ++ bits (p*n+1) t.val ++ bits (p*n+1) j.val ++ [mode]) =
          decide ((∀ i, reach r (bank i) ≤ d) ∧ (∃ g : Word (p*n), rawGood H n g) ∧
            (if mode then (Nat.card {w : Word (p*n) // P w}).testBit j.val=true else
              ∃ w : Word (p*n), P w ∧ Nat.card {z : Word (p*n) // z<w ∧ P z}=t.val ∧
                (j.val=0 ∨ w.val.testBit (j.val-1)=true))) := by
  obtain ⟨C,fan,back,cost,correct⟩ := QueryCircuit.finish (grow hp hn r d q prep Q setup)
  refine ⟨C,fan,?_,cost.trans size,?_⟩
  · convert back using 1
    simp [numInputs,inLen,trailing,Nat.add_assoc]
  · intro nr nc cr cc bank y t j mode
    let x := cfgEnv nr nc cr cc bank y t j mode
    have input : List.ofFn x = cfg nr nc cr cc bank ++ bits n y.val ++ bits (p*n+1) t.val ++
        bits (p*n+1) j.val ++ [mode] := by
      rw [show List.ofFn x = _ from ofFn_encoded nr nc cr cc bank _ _]; simp [querySuffix,List.append_assoc]
    have ⟨hy,ht,hi,hm⟩ := decode nr nc cr cc bank y t j mode
    have actual := value hp hn hk hd hr Q spec x j mode hi hm
    have pars := decode_encoded nr nc cr cc bank (querySuffix y t j mode) (queryLength y t j mode)
    have rep : report hp hn r x = rawReport hp hn nr nc cr cc bank := by
      unfold report
      obtain ⟨u,v,a,b,c⟩ := pars
      change rowName (p*n) x=nr at u
      change colName (p*n) x=nc at v
      change rowSchedule (p*n) x=cr at a
      change colSchedule (p*n) x=cc at b
      change bankBit r x=bank at c
      rw [u,v,a,b,c]
    have hy : target (p*n) n r x=y := hy
    have ht : rankField (p*n) n r x=t := ht
    have valEq := GoodBank.valid_encoded nr nc cr cc bank (querySuffix y t j mode) (queryLength y t j mode) (d:=d)
    change GoodBank.Valid (p*n) r d x ↔ _ at valEq
    rw [←input,correct]
    simpa only [rep,hit,hy,ht,valEq] using actual

end PEqualNP.Outside.L_meta_33676_aux.RankedC

namespace PEqualNP.Outside.L_meta_33676_aux.Recognition

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit Builder Layout
open PEqualNP.Outside.L_meta_33676_aux.Windows (reach)
open Translation ShiftCriterion GoodBank QueryCircuit

theorem finalCost {p n : Nat} (hk : n ≤ p*n) (r d : Nat) :
    GoodLeastBank.budget p n r d + layoutCost (p*n) ≤ 2^40*(p*n+r+2^d+5)^13 := by
  let K := p*n+r+2^d+5
  have h1 := GoodLeastBank.budget_le hk r d
  have h2 := layoutCost_bound (p*n)
  have hz : 1 ≤ K := by dsimp only [K]; generalize 2^d = D; omega
  have hk' : p*n+1 ≤ K := by dsimp only [K]; generalize 2^d = D; omega
  have h2' := (Nat.pow_le_pow_left hk' 2).trans (Nat.pow_le_pow_right hz (show 2≤13 by decide))
  have h1' := Nat.pow_le_pow_right hz (show 5≤13 by decide)
  calc
    _ ≤ 2^14*K^5 + 32*(p*n+1)^2 := Nat.add_le_add h1 h2
    _ ≤ 2^14*K^13+32*K^13 := Nat.add_le_add (Nat.mul_le_mul_left _ h1') (Nat.mul_le_mul_left _ h2')
    _ ≤ 2^40*K^13 := by rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by decide)

open Classical in
theorem recognition (p n r d : Nat) (hp : 0<p) (hn : 0<n) (hk : n<p*n) (hd : d<n) (hr : 4≤r) :
    let k := p*n
    ∃ A : Circuit, FanInTwo A ∧ ReadsBack (3*k+2*r*k+(k+1)+1) A ∧
      A.size ≤ 2^40*(k+r+2^d+5)^13 ∧
      ∀ (nr nc : Word k) (cr cc : Fin r → Word k) (bank : Fin k → Bool)
        (j : Fin (k+1)) (mode : Bool),
        let P := rawGood (rawReport hp hn nr nc cr cc bank) n
        A.eval (cfg nr nc cr cc bank ++ bits (k+1) j.val ++ [mode]) =
        decide ((∀ i, reach r (bank i) ≤ d) ∧ (if mode then (Nat.card {g : Word k // P g}).testBit j.val = true
          else ∃ g, P g ∧ (∀ v, P v → g ≤ v) ∧ (j.val=0 ∨ g.val.testBit (j.val-1)=true))) := by
  let k := p*n
  let count := cfgCount (s:=aLen k r) hp hn r d
  let least := fun x => (GoodLeastBank.cfgLeast (s:=aLen k r) hp hn r d x).val
  let ok := fun x => decide (0<count x)
  obtain ⟨B,eB,cB,w⟩ := GoodLeastBank.grow hp hn r d (0+(k+1)+1)
  have wc (j : Fin (k+1)) : B.Has (fun x => (count x).testBit j.val) :=
    w.digits ⟨j.val,by dsimp [k] at *; omega⟩
  obtain ⟨C,eC,cC,ans⟩ := postedQueryCircuit k r d 0 B eB ok (fun i x => (count x).testBit i.val)
    (fun i x => (least x).testBit i.val) w.feasible wc w.least
  obtain ⟨A,fan,back,sz,out⟩ := finishA (d:=d) ok count least (budget:=GoodLeastBank.budget p n r d+layoutCost k)
    ⟨C,Bank.ext_trans eB eC,by simp [Bank.empty] at cB ⊢; omega,ans⟩
  refine ⟨A,fan,back,sz.trans (finalCost hk.le r d),?_⟩
  intro nr nc cr cc bank j mode
  dsimp only
  rw [out nr nc cr cc bank j mode]
  by_cases hv : ∀ i, reach r (bank i) ≤ d
  · have cnt := cfgCount_encoded hp hn hk hd hr nr nc cr cc bank (queryTail [] j mode)
      (queryTail_length [] j mode) hv
    have minEq := GoodLeastBank.least_encoded_iff hp hn hk hd hr nr nc cr cc bank (queryTail [] j mode)
      (queryTail_length [] j mode) hv j
    cases mode
    · apply Bool.eq_iff_iff.mpr
      simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq, Bool.and_eq_true,ok,count,least]
      exact and_congr Iff.rfl minEq.symm
    · apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Bool.and_eq_true, ↓reduceIte,count,cnt]
      rfl
  · apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    constructor <;> intro h <;> exact False.elim (hv h.1)

end PEqualNP.Outside.L_meta_33676_aux.Recognition

namespace PEqualNP.Outside.L_meta_33676_aux.RankedC

open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit Builder Layout

def CounterPackage {p n : ℕ} (hp : 0<p) (hn : 0<n) (r d : ℕ) : Prop :=
  ∃ (Q : Env (numInputs p n r) → ℕ → ℕ → ℕ) (q prep : ℕ),
    (Bank.empty (numInputs p n r)).Grow prep (fun B => GoodLeastBank.HasBank hp hn r d B ∧
      RankCircuit.PinnedCounter B (p*n) q Q) ∧
    OracleSpec hp hn r d Q ∧ budget (p*n) prep q ≤ 2^60*(p*n+r+2^d+5)^28*((p+(2^d)^3).choose p)

private theorem size_room {k M H prep q : ℕ} (hm : k+2≤M) (hH : 1≤H)
    (hp : prep ≤ 2^56*M^27*H) (hq : q ≤ 2^56*M^27*H) :
    budget k prep q ≤ 2^60*M^28*H := by
  let a := 2^56*M^27*H
  have ma : 32*M^2 ≤ a := by
    calc 32*M^2 ≤ 2^56*M^27 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_right (by omega) (by decide))
         _ ≤ a := Nat.le_mul_of_pos_right _ (by omega)
  have mm : M ≤ M^2 := by nlinarith [show M*(M-1)≥0 by omega, show 1≤M by omega]
  have m32 : 32*M ≤ a := le_trans (Nat.mul_le_mul_left _ mm) ma
  have oneA : 1+k*4≤a := by omega
  have ga : 1+k*4+q+32*(k+2) ≤ a+a+a := by change q≤a at hq; omega
  have tail : QueryCircuit.layoutCost k ≤ a := (QueryCircuit.layoutCost_bound k).trans <| by
    calc 32*(k+1)^2 ≤ 32*M^2 := by gcongr; omega
         _ ≤ a := ma
  have ba : a≤M*a := Nat.le_mul_of_pos_left a (by omega)
  have apos : 0<a := by omega
  have hp : prep≤a := hp
  calc budget k prep q ≤ a+1+(3+M*(a+a+a))+a+1 := by
         unfold budget; gcongr; omega
       _ ≤ 16*M*a := by nlinarith
       _ = _ := by unfold a; ring

theorem budget_room {k M H prep q : ℕ} (hm : k+2≤M) (hH : 1≤H)
    (hp : prep ≤ 2^56*M^27*H) (hq : q ≤ 2^56*M^27*H) :
    budget k prep q ≤ 2^60*M^28*H := size_room hm hH hp hq

private theorem normBool {α : Sort*} (b : Bool) (h : Decidable (b=true)) (u v : α) :
    @ite α (b=true) h u v = cond b u v := by cases b <;> simp

set_option maxHeartbeats 1500000 in
theorem posted_of_counter (realize : ∀ (p n r d : Nat) (hp : 2≤p) (hd : 0<d) (hn : d<n), 4≤r →
    CounterPackage (p:=p) (n:=n) (by omega) (by omega) r d) : (∀ (p n r d : Nat) (hp : 2 ≤ p) (hd : 0 < d) (hn : d < n), 4 ≤ r →
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  let k := p*n
  let D := 2^d
  let W := Fin (2^k)
  let Y := Fin (2^n)
  let rot := fun (h w : Nat) =>
    ((w <<< (h % k)) ||| (w >>> (k - h % k))) % 2^k
  let step := fun (w : Nat) =>
    (List.range k).foldl (fun acc i => acc ||| ((xor (w.testBit i)
      (!(w.testBit ((i+1)%k)) && w.testBit ((i+2)%k))).toNat <<< i)) 0
  let state := fun (col : Bool) (w name : Nat) (c : Fin r → W) =>
    let b := if col then 2 else 1
    (List.finRange r).foldl (fun x j =>
      step (x ^^^ rot b x ^^^ rot (k-b) x) ^^^
        rot (if col then 3*(j.val+1)+1 else 2*j.val) w ^^^ (c j).val)
      (rot (if col then 3 else 1) w ^^^ name)
  let reach := fun col : Bool => if col then 7*r-2 else 5*r-3
  let delay := fun col : Bool => if col then 3*r+1 else 2*r-2
  let bits := fun (a x : Nat) => (List.range a).map (fun i => x.testBit i)
  let sched := fun (c : Fin r → W) => (List.finRange r).flatMap (fun j => bits k (c j).val)
  ∃ A C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo A ∧ PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (3*k+2*r*k+(k+1)+1) A ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (3*k+2*r*k+n+2*(k+1)+1) C ∧
    A.size ≤ 2^40*(k+r+D+5)^13 ∧
    C.size ≤ 2^60*(k+r+D+5)^28*((p+D^3).choose p) ∧
    ∀ (nr nc : W) (cr cc : Fin r → W) (bank : Fin k → Bool) (y : Y)
      (t : Fin (2^(k+1))) (j : Fin (k+1)) (countMode : Bool),
      let valid := ∀ i, reach (bank i) ≤ d
      let report := fun (w : Nat) (i : Fin n) => (List.finRange p).foldl (fun bit a =>
        let pos := a.val*n+i.val
        let col := bank ⟨pos % k, Nat.mod_lt _ (Nat.mul_pos (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hp) (Nat.lt_trans hd hn))⟩
        xor bit ((state col w (if col then nc.val else nr.val)
          (if col then cc else cr)).testBit ((pos+delay col)%k))) false
      let good := fun g : W => ∀ w : W,
        report ((rot n w.val) ^^^ g.val) = report (w.val ^^^ g.val)
      let hit := fun w : W => ∀ i : Fin n, report w.val i = y.val.testBit i.val
      let cfg := bits k nr.val ++ bits k nc.val ++ sched cr ++ sched cc ++ List.ofFn bank
      (A.eval (cfg ++ bits (k+1) j.val ++ [countMode]) =
        decide (valid ∧ (if countMode then (Nat.card {g : W // good g}).testBit j.val = true
          else ∃ g : W, good g ∧ (∀ h : W, good h → g ≤ h) ∧
            (j.val = 0 ∨ g.val.testBit (j.val-1) = true)))) ∧
      (C.eval (cfg ++ bits n y.val ++ bits (k+1) t.val ++ bits (k+1) j.val ++ [countMode]) =
        decide (valid ∧ (∃ g : W, good g) ∧
          (if countMode then (Nat.card {w : W // hit w}).testBit j.val = true else
           ∃ w : W, hit w ∧ Nat.card {z : W // z < w ∧ hit z} = t.val ∧
             (j.val = 0 ∨ w.val.testBit (j.val-1) = true))))) := by
  intro p n r d hp hd hn hr
  have hp' : 0<p := by omega
  have hn' : 0<n := by omega
  have hk : n<p*n := by have h := Nat.mul_le_mul_right n hp; omega
  obtain ⟨A,fa,ba,sa,runA⟩ := Recognition.recognition p n r d hp' hn' hk hn hr
  obtain ⟨Q,q,prep,setup,spec,budget⟩ := realize p n r d hp hd hn hr
  obtain ⟨C,fc,bc,sc,runC⟩ := physical hp' hn' hk hn hr Q q prep setup spec budget
  refine ⟨A,C,fa,fc,ba,bc,sa,sc,?_⟩
  intro nr nc cr cc bank y t j mode
  constructor
  · apply (runA nr nc cr cc bank j mode).trans
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    simp +unfoldPartialApp only [Translation.rawGood,Translation.rawRot,
      ShiftCriterion.rawReport,ShiftCriterion.rawSensor,L_meta_33676_aux.Windows.reach,
      L_meta_33676_aux.Windows.delay,L_meta_33676_aux.Windows.sensorState,L_meta_33676_aux.Windows.chiK,
      L_meta_33676_aux.Windows.rotK,normBool]
  · apply (runC nr nc cr cc bank y t j mode).trans
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    simp +unfoldPartialApp only [Translation.rawGood,Translation.rawRot,
      ShiftCriterion.rawReport,ShiftCriterion.rawSensor,L_meta_33676_aux.Windows.reach,
      L_meta_33676_aux.Windows.delay,L_meta_33676_aux.Windows.sensorState,L_meta_33676_aux.Windows.chiK,
      L_meta_33676_aux.Windows.rotK,normBool]

end PEqualNP.Outside.L_meta_33676_aux.RankedC

namespace PEqualNP.Outside.L_meta_33676_aux.Transfer

theorem histogram_count (p D : ℕ) :
    Nat.card (Sym (Option (Fin D × Fin D × Fin D)) p) = (p+D^3).choose p := by
  rw [Sym.natCard_sym_eq_choose]
  simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_prod, Fintype.card_fin]
  congr 1
  simp [pow_succ,Nat.mul_assoc]
  omega

noncomputable def selected {I A : Type*} [Fintype I] (typ : I → A) (z : I → Bool) (a : A) :
    Finset {i : I // typ i = a} := by
  classical
  exact Finset.univ.filter fun i => z i.val = true

noncomputable def labeled (I A : Type*) [Fintype I] (typ : I → A) (q : A → ℕ) :=
  {z : I → Bool // ∀ a, (selected typ z a).card = q a}

noncomputable def choices {I A : Type*} [Fintype I] (typ : I → A) (q : A → ℕ) (a : A) :
    Finset (Finset {i : I // typ i = a}) := by
  classical
  exact Finset.univ.powersetCard (q a)

noncomputable def bits {I A : Type*} [Fintype I] (typ : I → A) (q : A → ℕ)
    (S : (a:A) → ↥(choices typ q a)) (i : I) : Bool := by
  classical
  exact decide ((⟨i,rfl⟩ : {j : I // typ j = typ i}) ∈ (S (typ i)).val)

theorem select_bits {I A : Type*} [Fintype I] (typ : I → A) (q : A → ℕ)
    (S : (a:A) → ↥(choices typ q a)) (a : A) : selected typ (bits typ q S) a = (S a).val := by
  classical
  ext ⟨i, rfl⟩
  simp [selected,bits]

noncomputable def choicesEquiv {I A : Type*} [Fintype I] (typ : I → A) (q : A → ℕ) :
    labeled I A typ q ≃ ((a:A) → ↥(choices typ q a)) := by
  classical
  let toChoices (z : labeled I A typ q) (a : A) : ↥(choices typ q a) :=
    ⟨selected typ z.val a, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,z.property a⟩⟩
  refine ⟨toChoices,fun S => ⟨bits typ q S, fun a => ?_⟩,?_,?_⟩
  · rw [select_bits]
    exact (Finset.mem_powersetCard.mp (S a).property).2
  · intro z
    apply Subtype.ext
    funext i
    simp [toChoices,bits,selected]
  · intro S
    funext a
    apply Subtype.ext
    exact select_bits typ q S a

theorem labeled_transition_count {I A : Type*} [Fintype I] [Fintype A] (typ : I → A) (q : A → ℕ) :
    Nat.card (labeled I A typ q) = ∏ a : A, (Nat.card {i : I // typ i = a}).choose (q a) := by
  classical
  rw [Nat.card_congr (choicesEquiv typ q)]
  simp [Nat.card_eq_fintype_card, Fintype.card_pi, choices]

private theorem sum_bits {X : Type*} [Fintype X] (z : X → Bool) (f : Bool → Bool) :
    (∑ i, (f (z i)).toNat) =
      (Finset.univ.filter (fun i => z i = true)).card * (f true).toNat +
      (Fintype.card X - (Finset.univ.filter (fun i => z i = true)).card) * (f false).toNat := by
  classical
  let T := Finset.univ.filter (fun i => z i = true)
  let F := Finset.univ.filter (fun i => ¬z i = true)
  have n : F.card = Fintype.card X - T.card := by
    have card := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset X)) (p := fun i => z i = true)
    change T.card + F.card = _ at card
    rw [Finset.card_univ] at card
    omega
  have one : (∑ i ∈ T, (f (z i)).toNat) = T.card * (f true).toNat := by
    calc
      _ = ∑ _i ∈ T, (f true).toNat := Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])
      _ = _ := by simp
  have zero : (∑ i ∈ F, (f (z i)).toNat) = F.card * (f false).toNat := by
    calc
      _ = ∑ _i ∈ F, (f false).toNat := Finset.sum_congr rfl (fun i hi => by
        rw [Bool.eq_false_iff.mpr (Finset.mem_filter.mp hi).2])
      _ = _ := by simp
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => z i = true) (fun i => (f (z i)).toNat)]
  exact congrArg₂ (·+·) one (zero.trans (by rw [n]))

noncomputable def population {I A : Type*} (typ : I → A) (a : A) : ℕ := Nat.card {i : I // typ i = a}

def onesIn (f : Bool → Bool) (n q : ℕ) : ℕ := q*(f true).toNat + (n-q)*(f false).toNat

theorem output_sum {I A : Type*} [Fintype I] [Fintype A] (typ : I → A) (q : A → ℕ)
    (f : A → Bool → Bool) (z : labeled I A typ q) :
    (∑ i, (f (typ i) (z.val i)).toNat) = ∑ a, onesIn (f a) (population typ a) (q a) := by
  classical
  let e := Equiv.sigmaFiberEquiv typ
  calc
    _ = ∑ v : Σ a, {i : I // typ i = a}, (f (typ (e v)) (z.val (e v))).toNat :=
      (e.sum_comp (fun i => (f (typ i) (z.val i)).toNat)).symm
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro a _
      change (∑ u : {i : I // typ i = a}, (f (typ u.val) (z.val u.val)).toNat) = _
      have same := Finset.sum_congr (s₁ := (Finset.univ : Finset {i : I // typ i=a})) rfl
        (g := fun u : {i : I // typ i = a} => (f a (z.val u.val)).toNat)
        (f := fun u : {i : I // typ i = a} => (f (typ u.val) (z.val u.val)).toNat)
        (fun u _ => by rw [u.property])
      rw [same, sum_bits]
      have cnt : (Finset.univ.filter (fun u : {i : I // typ i=a} => z.val u.val = true)).card = q a := z.property a
      simp [onesIn,population,Nat.card_eq_fintype_card,cnt]

abbrev Result := ℕ × ℕ × Bool

noncomputable def measured {I : Type*} [Fintype I] (typ z : I → Bool)
    (f : Bool → Bool → Bool) (flag : Bool) : Result :=
  (∑ i, (!(z i)).toNat, ∑ i, (z i).toNat,
    xor flag ((∑ i, (f (typ i) (z i)).toNat).testBit 0))

noncomputable def predicted {I : Type*} (typ : I → Bool) (q : Bool → ℕ)
    (f : Bool → Bool → Bool) (flag : Bool) : Result :=
  ((population typ false - q false) + (population typ true - q true), q false+q true,
   xor flag ((onesIn (f false) (population typ false) (q false) +
     onesIn (f true) (population typ true) (q true)).testBit 0))

theorem measured_eq_predicted {I : Type*} [Fintype I] (typ : I → Bool) (q : Bool → ℕ)
    (f : Bool → Bool → Bool) (flag : Bool) (z : labeled I Bool typ q) :
    measured typ z.val f flag = predicted typ q f flag := by
  have zero := output_sum typ q (fun _ b => !b) z
  have one := output_sum typ q (fun _ b => b) z
  have parity := output_sum typ q f z
  simp only [Fintype.sum_bool, onesIn, Bool.not_true, Bool.not_false, Bool.toNat_false,
    Bool.toNat_true, Nat.mul_zero,Nat.mul_one,Nat.zero_add,Nat.add_zero] at zero one
  rw [Fintype.sum_bool] at parity
  simp [measured,predicted,zero,one,parity,Nat.add_comm]

theorem grouped_transition {I : Type*} [Fintype I] (typ : I → Bool) (q : Bool → ℕ)
    (f : Bool → Bool → Bool) (flag : Bool) (result : Result) :
    Nat.card {z : labeled I Bool typ q // measured typ z.val f flag = result} =
      if predicted typ q f flag = result then
        (population typ false).choose (q false) * (population typ true).choose (q true) else 0 := by
  classical
  by_cases h : predicted typ q f flag = result
  · rw [ite_eq_left h, Nat.card_congr (Equiv.subtypeUnivEquiv (fun z => (measured_eq_predicted typ q f flag z).trans h))]
    simpa [Fintype.prod_bool,population,Nat.mul_comm] using labeled_transition_count typ q
  · rw [ite_eq_right h]
    let : IsEmpty {z : labeled I Bool typ q // measured typ z.val f flag = result} :=
      ⟨fun z => h ((measured_eq_predicted typ q f flag z.val).symm.trans z.property)⟩
    exact Nat.card_of_isEmpty

theorem pair_transfer {I : Type*} [Fintype I] (typ : I → Bool)
    (f : Bool → Bool → Bool) (flag : Bool) (result : Result) :
    Nat.card {z : I → Bool // measured typ z f flag = result} =
      ∑ u : Bool → Fin (Fintype.card I + 1),
        if predicted typ (fun a => (u a).val) f flag = result then
          (population typ false).choose (u false).val * (population typ true).choose (u true).val
        else 0 := by
  classical
  let X := {z : I → Bool // measured typ z f flag = result}
  let U := Bool → Fin (Fintype.card I+1)
  let N (x:X) (a:Bool) := (selected typ x.val a).card
  have hN (x:X) (a:Bool) : N x a ≤ Fintype.card I :=
    (Finset.card_le_univ _).trans (Fintype.card_le_of_injective
      (Subtype.val : {i : I // typ i=a} → I) Subtype.val_injective)
  let index (x:X) : U := fun a => ⟨N x a, Nat.lt_succ_of_le (hN x a)⟩
  have eqv (u:U) : {x : X // index x=u} ≃
      {z : labeled I Bool typ (fun a => (u a).val) // measured typ z.val f flag = result} := by
    refine ⟨fun x => ⟨⟨x.val.val,fun a => ?_⟩,x.val.property⟩,
      fun z => ⟨⟨z.val.val,z.property⟩,?_⟩,fun _ => rfl,fun _ => rfl⟩
    · exact congrArg Fin.val (congrFun x.property a)
    · funext a
      apply Fin.ext
      exact z.val.property a
  calc
    _ = Nat.card (Σ u : U, {x : X // index x = u}) :=
      Nat.card_congr (Equiv.sigmaFiberEquiv index).symm
    _ = _ := by
      rw [Nat.card_sigma]
      apply Finset.sum_congr rfl
      intro u _
      exact (Nat.card_congr (eqv u)).trans (grouped_transition typ _ f flag result)

private theorem lowBit_add (m n : ℕ) : (m+n).testBit 0 = xor (m.testBit 0) (n.testBit 0) := by
  calc
    _ = (m ^^^ n).testBit 0 := by simp [Nat.testBit_zero,Nat.xor_mod_two_eq]
    _ = _ := Nat.testBit_xor m n 0

theorem list_parity {I : Type*} (xs : List I) (f : I → Bool) (flag : Bool) :
    xs.foldl (fun b i => xor b (f i)) flag =
      xor flag ((xs.map fun i => (f i).toNat).sum.testBit 0) := by
  induction xs generalizing flag with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,lowBit_add]
    cases flag <;> cases f x <;> simp

theorem indexed_parity (p : ℕ) (f : Fin p → Bool) (flag : Bool) :
    (List.finRange p).foldl (fun b i => xor b (f i)) flag =
      xor flag ((∑ i, (f i).toNat).testBit 0) := by
  rw [list_parity]
  simp [List.finRange,List.sum_ofFn,Function.comp_def]

def trail {S : Type*} (start : S) : List S → Multiset (S × S)
  | [] => 0
  | next :: rest => (start,next) ::ₘ trail next rest

noncomputable def paths {S : Type*} [Fintype S] [DecidableEq S] (n : ℕ) (a b : S) (H : Multiset (S × S)) : ℕ := by
  exact ∑ x : Fin n → S, if trail a (List.ofFn x ++ [b]) = H then 1 else 0

noncomputable def cycles {S : Type*} [Fintype S] [DecidableEq S] (n : ℕ) (H : Multiset (S × S)) : ℕ := by
  exact ∑ x : Fin (n+1) → S, if trail (x 0) (List.ofFn (Fin.tail x) ++ [x 0]) = H then 1 else 0

private theorem peel {S : Type*} [DecidableEq S] (a : S) (s H : Multiset S) :
    (if a ::ₘ s = H then 1 else 0 : ℕ) =
    if a ∈ H then (if s = H.erase a then 1 else 0) else 0 := by
  by_cases ha : a∈H
  · have iff₀ : a ::ₘ s = H ↔ s = H.erase a := by
      constructor
      · rintro rfl
        simp
      · rintro rfl
        exact Multiset.cons_erase ha
    simp [ha,iff₀]
  · have hn : a ::ₘ s ≠ H := fun eq => ha (eq ▸ Multiset.mem_cons_self a s)
    simp [ha,hn]

theorem paths_zero {S : Type*} [Fintype S] [DecidableEq S] (a b : S) (H : Multiset (S×S)) :
    paths 0 a b H = if {(a,b)} = H then 1 else 0 := by simp [paths, trail]

theorem paths_succ {S : Type*} [Fintype S] [DecidableEq S] (n : ℕ) (a b : S) (H : Multiset (S×S)) :
    paths (n+1) a b H = ∑ c : S, if (a,c) ∈ H then paths n c b (H.erase (a,c)) else 0 := by
  let e := Fin.consEquiv (n:=n) (fun _ => S)
  unfold paths
  rw [← e.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  simp only [e,Fin.consEquiv_apply,List.ofFn_cons,List.cons_append,trail]
  by_cases hc : (a,c)∈H
  · simp only [peel,ite_eq_left hc]
  · simp [peel,hc]

theorem indexed_seam {S : Type*} [Fintype S] [DecidableEq S] (n : ℕ) (H : Multiset (S × S)) :
    cycles n H = ∑ a : S, paths n a a H := by
  let e := Fin.consEquiv (n:=n) (fun _ => S)
  unfold cycles paths
  rw [← e.sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro x _
  simp [e]

abbrev pairOrigins (p r₀ r₁ : ℕ) :=
  {x : Fin (p+1) × Fin (p+1) × Fin (p+1) × Fin (p+1) × Bool //
    x.2.2.1.val ≤ x.1.val ∧ x.2.2.2.1.val ≤ x.2.1.val ∧
    x.1.val - x.2.2.1.val + (x.2.1.val - x.2.2.2.1.val) = r₀ ∧
    x.2.2.1.val + x.2.2.2.1.val = r₁}

def originKey {p r₀ r₁ : ℕ} (x : pairOrigins p r₀ r₁) : Fin (p+1) × Fin (p+1) × Bool :=
  (x.val.1,x.val.2.2.1,x.val.2.2.2.2)

theorem originKey_injective (p r₀ r₁ : ℕ) : Function.Injective (@originKey p r₀ r₁) := by
  rintro ⟨⟨a,b,i,j,f⟩,hai,hbj,hz,ho⟩ ⟨⟨a',b',i',j',f'⟩,hai',hbj',hz',ho'⟩ e
  simp only [originKey,Prod.mk.injEq] at e
  rcases e with ⟨rfl,rfl,rfl⟩
  change i.val + j.val = r₁ at ho
  change i.val + j'.val = r₁ at ho'
  change a.val - i.val + (b.val - j.val) = r₀ at hz
  change a.val - i.val + (b'.val - j'.val) = r₀ at hz'
  change j.val ≤ b.val at hbj
  change j'.val ≤ b'.val at hbj'
  have ee : j = j' := Fin.ext (by omega)
  have bb : b = b' := Fin.ext (by omega)
  cases ee
  cases bb
  rfl

theorem origin_count (p r₀ r₁ : ℕ) : Nat.card (pairOrigins p r₀ r₁) ≤ 2*(p+1)^2 := by
  classical
  calc
    _ ≤ Nat.card (Fin (p+1) × Fin (p+1) × Bool) :=
      Nat.card_le_card_of_injective _ (originKey_injective p r₀ r₁)
    _ = _ := by simp [Nat.card_eq_fintype_card]; ring

theorem population_total {I : Type*} [Fintype I] (typ : I → Bool) :
    Fintype.card I = population typ false + population typ true := by
  classical
  calc
    _ = Fintype.card (Σ a, {i : I // typ i=a}) :=
      Fintype.card_congr (Equiv.sigmaFiberEquiv typ).symm
    _ = _ := by simp [population,Nat.card_eq_fintype_card,Fintype.card_sigma,Nat.add_comm]

def cellResult (n q : Bool → ℕ) (f : Bool → Bool → Bool) (flag : Bool) : Result :=
  ((n false - q false) + (n true - q true), q false + q true,
   xor flag ((onesIn (f false) (n false) (q false) + onesIn (f true) (n true) (q true)).testBit 0))

def pairWeight (n : Bool → ℕ) (f : Bool → Bool → Bool) (flag : Bool) (result : Result) : ℕ :=
  ∑ u : Bool → Fin (n false + n true + 1),
    if cellResult n (fun a => (u a).val) f flag = result then
      (n false).choose (u false).val * (n true).choose (u true).val
    else 0

theorem pairWeight_spec {I : Type*} [Fintype I] (typ : I → Bool)
    (f : Bool → Bool → Bool) (flag : Bool) (result : Result) :
    Nat.card {z : I → Bool // measured typ z f flag = result} =
      pairWeight (population typ) f flag result := by
  rw [pair_transfer,population_total typ]
  rfl

theorem histogram_step {X U V : Type*} (A : X → Type*) [Fintype X] [Fintype U]
    [∀ x, Fintype (A x)] (hist : X → U) (step : (x : X) → A x → V)
    (weight : U → V → ℕ) (v : V)
    (uniform : ∀ x, Nat.card {a : A x // step x a = v} = weight (hist x) v) :
    Nat.card {xa : Σ x, A x // step xa.1 xa.2 = v} =
      ∑ u, Nat.card {x : X // hist x = u} * weight u v := by
  classical
  let E : {xa : Σ x, A x // step xa.1 xa.2 = v} ≃ Σ x, {a : A x // step x a = v} :=
    ⟨fun q => ⟨q.val.1,q.val.2,q.property⟩,fun ⟨x,a⟩ => ⟨⟨x,a.val⟩,a.property⟩,
     fun _ => rfl,fun _ => rfl⟩
  rw [Nat.card_congr E,Nat.card_sigma]
  simp_rw [uniform]
  let e := Equiv.sigmaFiberEquiv hist
  rw [← e.sum_comp,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro u _
  change (∑ s : {x : X // hist x=u}, weight (hist s.val) v) = _
  calc
    _ = ∑ _s : {x : X // hist x=u}, weight u v :=
      Finset.sum_congr rfl fun s _ => by rw [s.property]
    _ = _ := by simp [Nat.card_eq_fintype_card]

theorem population_indicator {I : Type*} [Fintype I] (z : I → Bool) (b : Bool) :
    population z b = ∑ i, if z i = b then 1 else 0 := by
  classical
  simp [population,Nat.card_eq_fintype_card,Fintype.card_subtype]

theorem population_false {I : Type*} [Fintype I] (z : I → Bool) :
    population z false = ∑ i, (!(z i)).toNat := by
  rw [population_indicator]
  apply Finset.sum_congr rfl
  intro i _
  cases z i <;> rfl

theorem population_true {I : Type*} [Fintype I] (z : I → Bool) :
    population z true = ∑ i, (z i).toNat := by
  rw [population_indicator]
  apply Finset.sum_congr rfl
  intro i _
  cases z i <;> rfl

section Cell

variable {A : Type*} [DecidableEq A] {I : A → Type*} [∀ a, Fintype (I a)]

abbrev cellBank (I : A → Type*) := (a : A) → I a → Bool
abbrev histogramState (A : Type*) := (A → Bool → ℕ) × Bool

noncomputable def profile (old : cellBank I) (flag : Bool) : histogramState A :=
  (fun a => population (old a),flag)

noncomputable def writeCell (c : A) (old : cellBank I) (flag : Bool)
    (f : Bool → Bool → Bool) (z : I c → Bool) : cellBank I × Bool :=
  (Function.update old c z, (measured (old c) z f flag).2.2)

noncomputable def cellWeight (c : A) (old dest : histogramState A)
    (f : Bool → Bool → Bool) : ℕ := by
  classical
  exact if ∀ a, a≠c → old.1 a = dest.1 a then
    pairWeight (old.1 c) f old.2 (dest.1 c false,dest.1 c true,dest.2) else 0

theorem cellWeight_spec (c : A) (old : cellBank I) (flag : Bool)
    (f : Bool → Bool → Bool) (dest : histogramState A) :
    Nat.card {z : I c → Bool //
      profile (writeCell c old flag f z).1 (writeCell c old flag f z).2 = dest} =
      cellWeight c (profile old flag) dest f := by
  classical
  by_cases agree : ∀ a, a≠c → (profile old flag).1 a = dest.1 a
  · simp only [cellWeight,ite_eq_left agree]
    change _ = pairWeight (population (old c)) f flag _
    rw [← pairWeight_spec (old c)]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro z
    let w := writeCell c old flag f z
    have same : (profile w.1 w.2).1 c = population z := by
      simp [w,writeCell,profile]
    have other (a : A) (ha : a≠c) : (profile w.1 w.2).1 a = dest.1 a := by
      simpa [w,writeCell,profile,Function.update_of_ne ha] using agree a ha
    change profile w.1 w.2 = dest ↔ _
    constructor
    · intro e
      have h := congrFun (congrArg Prod.fst e) c
      rw [same] at h
      have hf : (measured (old c) z f flag).2.2 = dest.2 := congrArg (fun u : histogramState A => u.2) e
      refine Prod.ext ?_ (Prod.ext ?_ hf)
      · exact (population_false z).symm.trans (congrFun h false)
      · exact (population_true z).symm.trans (congrFun h true)
    · intro e
      have hf : (profile w.1 w.2).2 = dest.2 := congrArg (fun v : Result => v.2.2) e
      refine Prod.ext ?_ hf
      funext a
      by_cases h : a=c
      · subst a
        rw [same]
        funext b
        cases b
        · exact (population_false z).trans (congrArg Prod.fst e)
        · exact (population_true z).trans (congrArg (fun v : Result => v.2.1) e)
      · exact other a h
  · simp only [cellWeight,ite_eq_right agree]
    have neq (z : I c → Bool) : profile (writeCell c old flag f z).1 (writeCell c old flag f z).2 ≠ dest := by
      intro ez
      apply agree
      intro a ha
      have e := congrFun (congrArg Prod.fst ez) a
      simpa [profile,writeCell,Function.update_of_ne ha] using e
    let : IsEmpty {z : I c → Bool // profile (writeCell c old flag f z).1 (writeCell c old flag f z).2 = dest} :=
      ⟨fun z => neq z.val z.property⟩
    exact Nat.card_of_isEmpty

end Cell

end PEqualNP.Outside.L_meta_33676_aux.Transfer

namespace PEqualNP.Outside.L_meta_33676_aux.ShiftedReport

open Translation ShiftCriterion PEqualNP.Outside.L_meta_33676_aux.Windows

theorem cyclic_const {p : ℕ} {S : Type*} (hp : 0<p) (f : Fin p → S)
    (edge : ∀ a, f (blockNext hp a)=f a) (a : Fin p) :
    f a = f ⟨0,hp⟩ := by
  rcases a with ⟨t,ht⟩
  induction t with
  | zero => rfl
  | succ t ih =>
    let j : Fin p := ⟨t,by omega⟩
    have hj : blockNext hp j = ⟨t+1,ht⟩ := by
      apply Fin.ext
      change (if t+1<p then t+1 else 0)=t+1
      simp [ht]
    exact (hj ▸ edge j).trans (ih (by omega))

def normalized {p : ℕ} {S : Type*} [AddGroup S] (T : Fin p → S → F₂)
    (L : Fin p → S) (a : Fin p) (z : S) := T a (z+L a) - T a (L a)

theorem normalize_rows {p : ℕ} {S : Type*} [AddCommGroup S] [Module F₂ S]
    (hp : 0<p) (T : Fin p → S → F₂) (L : Fin p → S)
    (hc : ∀ x : Fin p → S,
      ∑ a, T (blockNext hp a) (x a+(L (blockNext hp a)-L a)) = ∑ a, T a (x a)) :
    ∀ a z, normalized T L a z = normalized T L ⟨0,hp⟩ z := by
  obtain ⟨b,_,hb⟩ := (parity_iff_compatible T (fun a => T (blockNext hp a))
    (fun a => L (blockNext hp a)-L a)).mp hc
  have adj (a : Fin p) (z : S) : T (blockNext hp a) (z+L (blockNext hp a)) =
      T a (z+L a) + b a := by
    have h := hb a (z+L a)
    change T (blockNext hp a) ((z+L a)+(L (blockNext hp a)-L a)) = _ at h
    rwa [show (z+L a)+(L (blockNext hp a)-L a) = z+L (blockNext hp a) by abel] at h
  intro a z
  apply cyclic_const hp (fun a => normalized T L a z) _ a
  intro j
  have bz := adj j z
  have b0 := adj j 0
  simp only [zero_add] at b0
  unfold normalized
  rw [bz,b0]
  abel

def commonTable {p n d : ℕ} (hp : 0<p) (hn : 0<n)
    (T : Fin n → Fin p → Vector (d+1) → F₂) (g : Word (p*n)) (i : Fin n) :
    Vector (d+1) → F₂ :=
  normalized (T i) (fun a => windowMap hp hn i a (encode g)) ⟨0,hp⟩

theorem commonTable_spec {p n d : ℕ} (hp : 0<p) (hn : 0<n) (hkn : n<p*n) (hd : d<n)
    (H : ℕ → Fin n → Bool) (T : Fin n → Fin p → Vector (d+1) → F₂)
    (hT : ∀ (w : Word (p*n)) i, scalar (H w.val i) = residueSum hp hn T (encode w) i)
    (g : Word (p*n)) (hg : rawGood H n g) :
    ∀ (w : Word (p*n)) i,
      scalar (H (w.val ^^^ g.val) i) =
        (∑ a, commonTable hp hn T g i (windowMap hp hn i a (encode w))) + scalar (H g.val i) := by
  let L (i : Fin n) (a : Fin p) := windowMap (width:=d+1) hp hn i a (encode g)
  have hc := (good_with_tables hp hn hkn hd H T hT g).mp hg
  have norm (i : Fin n) := normalize_rows hp (T i) (L i) (hc i)
  unfold commonTable
  intro w i
  change scalar (H (plusWord w g).val i) = _
  rw [hT,encode_plusWord,hT]
  unfold residueSum
  simp only [map_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← norm i a]
  simp [normalized,L]

theorem shifted_report {p n d : ℕ} (hp : 0<p) (hn : 0<n) (hkn : n<p*n) (hd : d<n)
    (H : ℕ → Fin n → Bool) (T : Fin n → Fin p → Vector (d+1) → F₂)
    (hT : ∀ (w : Word (p*n)) i, scalar (H w.val i) = residueSum hp hn T (encode w) i)
    (g : Word (p*n)) (hg : rawGood H n g) :
    ∃ F : Fin n → Vector (d+1) → F₂, (∀ i, F i 0 = 0) ∧ ∀ (w : Word (p*n)) i,
      scalar (H (w.val ^^^ g.val) i) =
        (∑ a, F i (windowMap hp hn i a (encode w))) + scalar (H g.val i) := by
  exact ⟨commonTable hp hn T g,fun i => by simp [commonTable,normalized],
    commonTable_spec hp hn hkn hd H T hT g hg⟩

theorem actual_shifted_report {p n r d : ℕ} (hp : 0<p) (hn : 0<n) (hkn : n<p*n) (hd : d<n)
    (hr : 4≤r) (nr nc : Word (p*n)) (cr cc : Fin r → Word (p*n))
    (bank : Fin (p*n) → Bool) (valid : ∀ j, reach r (bank j) ≤ d) (g : Word (p*n))
    (hg : rawGood (rawReport hp hn nr nc cr cc bank) n g) :
    ∃ F : Fin n → Vector (d+1) → F₂, (∀ i, F i 0 = 0) ∧ ∀ (w : Word (p*n)) i,
      scalar (rawReport hp hn nr nc cr cc bank (w.val ^^^ g.val) i) =
        (∑ a, F i (windowMap hp hn i a (encode w))) +
          scalar (rawReport hp hn nr nc cr cc bank g.val i) := by
  obtain ⟨T,hT⟩ := existsReportTables hp hn (hd.trans hkn) hr nr nc cr cc bank valid
  exact shifted_report hp hn hkn hd _ T hT g hg

def panel {p n : ℕ} (w : Word (p*n)) (a : Fin p) (j : Fin n) : Bool :=
  w.val.testBit (a.val*n+j.val)

theorem panel_bijective (p n : ℕ) : Function.Bijective (@panel p n) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_,by simp [← pow_mul,Nat.mul_comm]⟩
  intro x y e
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t<p*n
  · obtain ⟨⟨a,j⟩,h⟩ := finProdFinEquiv.surjective (⟨t,ht⟩ : Fin (p*n))
    have h' := congrArg Fin.val h
    change j.val+n*a.val = t at h'
    rw [← h',Nat.add_comm j.val,Nat.mul_comm n]
    exact congrFun (congrFun e a) j
  · have bnd : 2^(p*n) ≤ 2^t := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (x.isLt.trans_le bnd), Nat.testBit_lt_two_pow (y.isLt.trans_le bnd)]

def panelWindow {p n d : ℕ} (hp : 0<p) (hd : d<n)
    (R : Fin p → Fin n → Bool) (i : Fin n) (a : Fin p) : Vector (d+1) :=
  fun j => if h : i.val+j.val<n then scalar (R a ⟨i.val+j.val,h⟩)
    else scalar (R (blockNext hp a) ⟨i.val+j.val-n,by omega⟩)

theorem panel_window_eq {p n d : ℕ} (hp : 0<p) (hn : 0<n) (hd : d<n)
    (w : Word (p*n)) (i : Fin n) (a : Fin p) :
    panelWindow hp hd (panel w) i a = windowMap hp hn i a (encode w) := by
  funext j
  have bounded (a : Fin p) (s : ℕ) (hs : s<n) : a.val*n+s < p*n := by
    calc
      _ < (a.val+1)*n := by rw [Nat.add_mul,Nat.one_mul]; exact Nat.add_lt_add_left hs _
      _ ≤ _ := Nat.mul_le_mul_right _ a.isLt
  change (if h : i.val+j.val<n then scalar (w.val.testBit (a.val*n + (i.val+j.val)))
    else scalar (w.val.testBit ((blockNext hp a).val*n + (i.val+j.val-n)))) =
    scalar (w.val.testBit ((i.val+(a.val*n+j.val))%(p*n)))
  rw [show i.val+(a.val*n+j.val) = a.val*n+(i.val+j.val) by omega]
  by_cases hij : i.val+j.val < n
  · simp [hij,Nat.mod_eq_of_lt (bounded a _ hij)]
  · simp only [hij,↓reduceDIte]
    let s := i.val+j.val-n
    have hs : s<n := by dsimp [s]; omega
    have e : a.val*n+(i.val+j.val) = (a.val+1)*n+s := by
      dsimp [s]; rw [Nat.add_mul,Nat.one_mul]; omega
    rw [e]
    by_cases ha : a.val+1<p
    · have hnext : (blockNext hp a).val = a.val+1 := by simp [blockNext,ha]
      rw [hnext,Nat.mod_eq_of_lt (bounded ⟨a.val+1,ha⟩ s hs)]
    · have hnext : (blockNext hp a).val = 0 := by simp [blockNext,ha]
      have hlast : a.val+1=p := by omega
      have hpn : n ≤ p*n := calc
        n = 1*n := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ hp
      rw [hnext,hlast,Nat.zero_mul,Nat.zero_add,Nat.add_mod_left,Nat.mod_eq_of_lt (hs.trans_le hpn)]

theorem shifted_slice_panel {p n d : ℕ} (hp : 0<p) (hn : 0<n) (hd : d<n)
    (H : ℕ → Fin n → Bool) (g : Word (p*n)) (F : Fin n → Vector (d+1) → F₂)
    (hf : ∀ (w : Word (p*n)) i, scalar (H (w.val ^^^ g.val) i) =
      (∑ a, F i (windowMap hp hn i a (encode w))) + scalar (H g.val i))
    (y : Fin n → Bool) (l h : ℕ) :
    (Ranking.slice (fun w : Word (p*n) => ∀ i, H (w.val ^^^ g.val) i = y i) l h).card =
      Nat.card {R : Fin p → Fin n → Bool // h < 2^(p*n-l) ∧
        (∀ a j, Ranking.rowPinned n l a.val j.val →
          R a j = h.testBit (a.val*n+j.val-l)) ∧
        ∀ i, (∑ a, F i (panelWindow hp hd R i a)) + scalar (H g.val i) = scalar (y i)} := by
  classical
  let e := Equiv.ofBijective _ (panel_bijective p n)
  have cond (w : Word (p*n)) : w ∈ Ranking.slice (fun w : Word (p*n) => ∀ i, H (w.val ^^^ g.val) i = y i) l h ↔
      h < 2^(p*n-l) ∧
        (∀ (a:Fin p) (j:Fin n), Ranking.rowPinned n l a.val j.val →
          e w a j = h.testBit (a.val*n+j.val-l)) ∧
        ∀ i, (∑ a, F i (panelWindow hp hd (e w) i a)) + scalar (H g.val i) = scalar (y i) := by
    rw [Ranking.mem_slice,Ranking.prefix_rows hn]
    change ((_ ∧ _) ↔ _ ∧ _ ∧ ∀ i, (∑ a, F i (panelWindow hp hd (panel w) i a)) + scalar (H g.val i) = scalar (y i))
    simp_rw [panel_window_eq hp hn hd,← hf]
    constructor
    · rintro ⟨report,bound,pin⟩
      exact ⟨bound,pin,fun i => congrArg scalar (report i)⟩
    · rintro ⟨bound,pin,report⟩
      exact ⟨fun i => scalar_inj (report i),bound,pin⟩
  exact (Nat.card_eq_finsetCard _).symm.trans (Nat.card_congr (e.subtypeEquiv cond))

theorem shifted_slice_freeRows {p n d : ℕ} (hp : 0<p) (hn : 0<n) (hd : d<n)
    (H : ℕ → Fin n → Bool) (g : Word (p*n)) (F : Fin n → Vector (d+1) → F₂)
    (hf : ∀ (w : Word (p*n)) i, scalar (H (w.val ^^^ g.val) i) =
      (∑ a, F i (windowMap hp hn i a (encode w))) + scalar (H g.val i))
    (y : Fin n → Bool) (l h : ℕ) :
    (Ranking.slice (fun w : Word (p*n) => ∀ i, H (w.val ^^^ g.val) i = y i) l h).card =
      if h < 2^(p*n-l) then Nat.card {X : Ranking.rowData p n l //
        ∀ i, (∑ a, F i (panelWindow hp hd (Ranking.assembleRows h X) i a)) +
          scalar (H g.val i) = scalar (y i)} else 0 := by
  rw [shifted_slice_panel hp hn hd H g F hf y l h]
  apply Ranking.countedRows hp hn

end PEqualNP.Outside.L_meta_33676_aux.ShiftedReport

namespace PEqualNP.Outside.L_meta_33676_aux.StreamRows

open Translation ShiftCriterion ShiftedReport

abbrev Trace (n d : ℕ) := Fin (n+d) → Bool
abbrev State (d : ℕ) := Fin d → Bool
abbrev Stream (n d : ℕ) := State d × (Fin n → Bool)
abbrev Panel (p n : ℕ) := Fin p → Fin n → Bool

def stateAt {n d : ℕ} (v : Trace n d) (t : Fin (n+1)) : State d :=
  fun j => v ⟨t.val+j.val,by omega⟩

def branch {n d : ℕ} (v : Trace n d) (t : Fin n) : Bool :=
  v ⟨t.val+d,by omega⟩

def windowAt {n d : ℕ} (v : Trace n d) (t : Fin n) : Fin (d+1) → Bool :=
  fun j => v ⟨t.val+j.val,by omega⟩

def nextState {d : ℕ} (s : State d) (b : Bool) : State d :=
  fun j => if h : j.val+1<d then s ⟨j.val+1,h⟩ else b

theorem state_step {n d : ℕ} (v : Trace n d) (t : Fin n) :
    stateAt v t.succ = nextState (stateAt v t.castSucc) (branch v t) := by
  funext j
  by_cases hj : j.val+1<d
  · simp only [stateAt,nextState,hj,Fin.val_succ,Fin.val_castSucc]
    congr 2; omega
  · simp only [stateAt,nextState,hj,branch,Fin.val_succ]
    congr 2; omega

theorem unique_states {n d : ℕ} (v : Trace n d) (states : Fin (n+1) → State d)
    (h₀ : states 0 = stateAt v 0)
    (hn : ∀ t : Fin n, states t.succ = nextState (states t.castSucc) (branch v t)) :
    ∀ t, states t = stateAt v t := by
  intro t
  induction t using Fin.induction with
  | zero => exact h₀
  | succ i ih => rw [hn i,ih,state_step]

theorem window_last {n d : ℕ} (v : Trace n d) (t : Fin n) :
    windowAt v t (Fin.last d) = branch v t := rfl

theorem window_front {n d : ℕ} (v : Trace n d) (t : Fin n) (j : Fin d) :
    windowAt v t j.castSucc = stateAt v t.castSucc j := rfl

def streamToTrace {n d : ℕ} (s : Stream n d) : Trace n d :=
  fun i => if h : i.val<d then s.1 ⟨i.val,h⟩ else s.2 ⟨i.val-d,by omega⟩

def traceToStream {n d : ℕ} (v : Trace n d) : Stream n d := (stateAt v 0,branch v)

@[simp] theorem traceToStream_toTrace {n d : ℕ} (s : Stream n d) :
    traceToStream (streamToTrace s) = s := by
  refine Prod.ext ?_ ?_
  · funext i
    change (if h : 0+i.val<d then s.1 ⟨0+i.val,h⟩ else s.2 ⟨0+i.val-d,by omega⟩) = s.1 i
    simp [i.isLt]
  · funext i
    unfold traceToStream branch streamToTrace
    simp [show ¬i.val+d<d by omega]

@[simp] theorem streamToTrace_toStream {n d : ℕ} (v : Trace n d) :
    streamToTrace (traceToStream v) = v := by
  funext i
  by_cases hi : i.val<d
  · simp [streamToTrace,hi,traceToStream,stateAt]
  · simp [streamToTrace,hi,traceToStream,branch,Nat.sub_add_cancel (Nat.le_of_not_gt hi)]

def traceEquivStream (n d : ℕ) : Trace n d ≃ Stream n d where
  toFun := traceToStream
  invFun := streamToTrace
  left_inv := streamToTrace_toStream
  right_inv := traceToStream_toTrace

def panelTraces {p n d : ℕ} (hp : 0<p) (hd : d≤n) (rows : Panel p n) (a : Fin p) : Trace n d :=
  fun t => if h : t.val<n then rows a ⟨t.val,h⟩ else rows (blockNext hp a) ⟨t.val-n,by omega⟩

def tracePanel {p n d : ℕ} (v : Fin p → Trace n d) : Panel p n :=
  fun a t => v a ⟨t.val,by omega⟩

def seam {p n d : ℕ} (hp : 0<p) (v : Fin p → Trace n d) : Prop :=
  ∀ a, stateAt (v a) (Fin.last n) = stateAt (v (blockNext hp a)) 0

theorem panel_seam {p n d : ℕ} (hp : 0<p) (hd : d≤n) (rows : Panel p n) :
    seam hp (panelTraces hp hd rows) := by
  intro a
  funext j
  have hj : j.val < n := j.isLt.trans_le hd
  simp [stateAt,panelTraces,hj,show ¬n+j.val<n by omega]

@[simp] theorem tracePanel_of_panel {p n d : ℕ} (hp : 0<p) (hd : d≤n) (rows : Panel p n) :
    tracePanel (panelTraces hp hd rows) = rows := by
  funext a j
  simp [tracePanel,panelTraces,j.isLt]

theorem panel_of_tracePanel {p n d : ℕ} (hp : 0<p) (hd : d≤n) (v : Fin p → Trace n d)
    (h : seam hp v) : panelTraces hp hd (tracePanel v) = v := by
  funext a i
  by_cases hi : i.val<n
  · simp [tracePanel,panelTraces,hi]
  · let j : Fin d := ⟨i.val-n,by omega⟩
    have e := congrFun (h a) j
    simp only [stateAt,Fin.val_last,Fin.val_zero,Nat.zero_add] at e
    have idx : (⟨n+j.val,by omega⟩ : Fin (n+d)) = i := by
      apply Fin.ext
      change n+(i.val-n)=i.val
      omega
    rw [idx] at e
    simpa [tracePanel,panelTraces,hi,j] using e.symm

def panelEquivTraces {p n d : ℕ} (hp : 0<p) (hd : d≤n) :
    Panel p n ≃ {v : Fin p → Trace n d // seam hp v} where
  toFun rows := ⟨panelTraces hp hd rows,panel_seam hp hd rows⟩
  invFun v := tracePanel v.val
  left_inv := tracePanel_of_panel hp hd
  right_inv v := Subtype.ext (panel_of_tracePanel hp hd v.val v.property)

def streamSeam {p n d : ℕ} (hp : 0<p) (s : Fin p → Stream n d) : Prop :=
  ∀ a, stateAt (streamToTrace (s a)) (Fin.last n) = (s (blockNext hp a)).1

def panelEquivStreams {p n d : ℕ} (hp : 0<p) (hd : d≤n) :
    Panel p n ≃ {s : Fin p → Stream n d // streamSeam hp s} :=
  (panelEquivTraces hp hd).trans <| (Equiv.piCongrRight (fun _ => traceEquivStream n d)).subtypeEquiv
    (p:=seam hp) (q:=streamSeam hp) (by
      intro v
      change (∀ a, stateAt (v a) (Fin.last n) = stateAt (v (blockNext hp a)) 0) ↔
        ∀ a, stateAt (streamToTrace (traceToStream (v a))) (Fin.last n) = (traceToStream (v (blockNext hp a))).1
      simp only [streamToTrace_toStream]
      rfl)

theorem panelWindow_trace {p n d : ℕ} (hp : 0<p) (hd : d<n) (rows : Panel p n) (a : Fin p)
    (i : Fin n) : panelWindow hp hd rows i a =
      fun j => scalar (windowAt (panelTraces hp hd.le rows a) i j) := by
  funext j
  by_cases hj : i.val+j.val<n <;> simp [panelWindow,panelTraces,windowAt,hj]

end PEqualNP.Outside.L_meta_33676_aux.StreamRows

namespace PEqualNP.Outside.L_meta_33676_aux.ColumnTransfer

open Transfer

private theorem bitAdd (a b : ℕ) : (a+b).testBit 0 = xor (a.testBit 0) (b.testBit 0) := by
  simp only [Nat.testBit_zero]
  by_cases ha : a % 2=1 <;> by_cases hb : b % 2=1 <;> simp [ha,hb] <;> omega

abbrev Cell := Bool → ℕ
abbrev Tables (N : ℕ) := Fin N → Bool → Bool → Bool
abbrev Counts (N : ℕ) := Fin N → Cell

def countNew {I : Type} [Fintype I] (z : I→Bool) (b : Bool) : ℕ :=
  if b then ∑ i, (z i).toNat else ∑ i, (!(z i)).toNat

noncomputable def Matches {N : ℕ} (I : Fin N→Type) [∀ j, Fintype (I j)]
    (old : ∀ j, I j→Bool) (f : Tables N) (R : Counts N)
    (first last : Bool) (z : ∀ j, I j→Bool) : Prop :=
  (∀ j, countNew (z j) false = R j false ∧ countNew (z j) true = R j true) ∧
  xor first ((∑ j, ∑ v : I j, (f j (old j v) (z j v)).toNat).testBit 0) = last

noncomputable def kernel : (N : ℕ) → Counts N → Tables N → Counts N → Bool → Bool → ℕ
  | 0, _, _, _, first, last => if first=last then 1 else 0
  | N+1, P, f, R, first, last =>
    ∑ flag : Bool, pairWeight (P 0) (f 0) first (R 0 false,R 0 true,flag) *
      kernel N (fun j => P j.succ) (fun j => f j.succ) (fun j => R j.succ) flag last

theorem splitMatches {N : ℕ} (I : Fin (N+1)→Type) [∀ j, Fintype (I j)]
    (old : ∀ j, I j→Bool) (f : Tables (N+1)) (R : Counts (N+1))
    (a b : Bool) (z : ∀ j, I j→Bool) :
    Matches I old f R a b z ↔
      (measured (old 0) (z 0) (f 0) a).1 = R 0 false ∧
      (measured (old 0) (z 0) (f 0) a).2.1 = R 0 true ∧
      Matches (fun j => I j.succ) (fun j => old j.succ) (fun j => f j.succ)
        (fun j => R j.succ) (measured (old 0) (z 0) (f 0) a).2.2 b (fun j => z j.succ) := by
  simp only [Matches,Fin.forall_fin_succ,Fin.sum_univ_succ,measured,countNew,ite_true,ite_false,
    Bool.false_eq_true,bitAdd,Bool.xor_assoc]
  tauto

noncomputable def splitEquiv {N : ℕ} (I : Fin (N+1)→Type) [∀ j, Fintype (I j)]
    (old : ∀ j, I j→Bool) (f : Tables (N+1)) (R : Counts (N+1)) (a b : Bool) :
    {z // Matches I old f R a b z} ≃
      Σ flag : Bool, {z : I 0 → Bool // measured (old 0) z (f 0) a = (R 0 false,R 0 true,flag)} ×
        {zs // Matches (fun j => I j.succ) (fun j => old j.succ) (fun j => f j.succ)
          (fun j => R j.succ) flag b zs} := by
  let left (z : {z // Matches I old f R a b z}) :
      Σ flag : Bool, {w : I 0 → Bool // measured (old 0) w (f 0) a = (R 0 false,R 0 true,flag)} ×
        {zs // Matches (fun j => I j.succ) (fun j => old j.succ) (fun j => f j.succ)
          (fun j => R j.succ) flag b zs} := by
    have h := (splitMatches I old f R a b z.val).1 z.property
    exact ⟨_,⟨z.val 0,Prod.ext h.1 (Prod.ext h.2.1 rfl)⟩,⟨fun j => z.val j.succ,h.2.2⟩⟩
  refine ⟨left,?_,?_,?_⟩
  · rintro ⟨flag,⟨z,hz⟩,⟨zs,hzs⟩⟩
    let zz : ∀ j, I j→Bool := Fin.cons z zs
    refine ⟨zz,(splitMatches I old f R a b zz).2 ?_⟩
    simpa only [zz,Fin.cons_zero,Fin.cons_succ,hz] using
      (show R 0 false = R 0 false ∧ R 0 true = R 0 true ∧ _ from ⟨rfl,rfl,hzs⟩)
  · intro z
    apply Subtype.ext
    exact Fin.cons_self_tail z.val
  · rintro ⟨flag,⟨z,hz⟩,⟨zs,hzs⟩⟩
    have hc := congrArg (fun t : Result => t.2.2) hz
    change (measured (old 0) z (f 0) a).2.2 = flag at hc
    subst flag
    rfl

theorem kernel_correct (N : ℕ) (I : Fin N→Type) [inst : ∀ j, Fintype (I j)]
    (old : ∀ j, I j→Bool) (f : Tables N) (R : Counts N) (a b : Bool) :
    Nat.card {z // Matches I old f R a b z} =
      kernel N (fun j => population (old j)) f R a b := by
  induction N generalizing a b with
  | zero =>
    classical
    by_cases h : a=b
    · subst b
      have eq : ∀ z, Matches I old f R a a z := by simp [Matches]
      rw [Nat.card_congr (Equiv.subtypeUnivEquiv eq)]
      simp [kernel,Nat.card_eq_fintype_card]
    · have _ : IsEmpty {z // Matches I old f R a b z} := ⟨fun z => by simpa [Matches,h] using z.property⟩
      simp [kernel,h]
  | succ n ih =>
    classical
    rw [Nat.card_congr (splitEquiv I old f R a b),Nat.card_sigma]
    change _ = ∑ flag : Bool, _
    apply Finset.sum_congr rfl
    intro flag _
    rw [Nat.card_prod,pairWeight_spec,ih (fun j => I j.succ) (fun j => old j.succ)]

noncomputable def groupedBits {X : Type} {N : ℕ} (group : X → Fin N) :
    (X→Bool) ≃ ((j : Fin N) → {x // group x=j} → Bool) where
  toFun z _ v := z v.val
  invFun z v := z (group v) ⟨v,rfl⟩
  left_inv _ := rfl
  right_inv z := by
    funext j v
    rcases v with ⟨v,h⟩
    cases h
    rfl

theorem countNew_card {I : Type} [Fintype I] (z : I→Bool) (b : Bool) :
    countNew z b = Nat.card {v // z v=b} := by
  classical
  have f (v : I) : (if b then (z v).toNat else (!(z v)).toNat) =
      if z v=b then 1 else 0 := by cases b <;> cases z v <;> decide
  cases b <;> simp only [countNew, Bool.false_eq_true,ite_false,ite_true] at f ⊢ <;>
    simp only [f,Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.card_filter]

theorem group_cell {X : Type} [Fintype X] {N : ℕ} (group : X → Fin N) (z : X→Bool)
    (j : Fin N) (b : Bool) :
    countNew (groupedBits group z j) b = Nat.card {v // (group v,z v)=(j,b)} := by
  classical
  rw [countNew_card]
  exact Nat.card_congr
    { toFun := fun v => ⟨v.val.val,Prod.ext v.val.property v.property⟩
      invFun := fun v => ⟨⟨v.val,congrArg Prod.fst v.property⟩,congrArg Prod.snd v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem group_sum {X : Type} [Fintype X] {N : ℕ} (group : X → Fin N) (value : X→ℕ) :
    (∑ j, ∑ w : {x // group x=j}, value w.val) = ∑ w, value w := by
  classical
  calc
    _ = ∑ t : Σ j, {x // group x=j}, value ((Equiv.sigmaFiberEquiv group) t) := by
      rw [Fintype.sum_sigma]; rfl
    _ = _ := (Equiv.sigmaFiberEquiv group).sum_comp value

def physical {X C : Type} [Fintype X] {N : ℕ} (group : X→Fin N) (old : X→Bool) (f : Tables N)
    (rename : Fin N × Bool ≃ C) (result : C→ℕ) (a b : Bool) (z : X→Bool) : Prop :=
  (∀ c, Nat.card {x // rename (group x,z x)=c} = result c) ∧
    xor a ((∑ x, (f (group x) (old x) (z x)).toNat).testBit 0) = b

theorem physical_iff {X C : Type} [Fintype X] {N : ℕ} (group : X→Fin N) (old : X→Bool)
    (f : Tables N) (rename : Fin N × Bool ≃ C) (result : C→ℕ) (a b : Bool) (z : X→Bool) :
    physical group old f rename result a b z ↔ Matches (fun j => {x // group x=j})
      (fun _ x => old x.val) f (fun j t => result (rename (j,t))) a b (groupedBits group z) := by
  classical
  have he j t : countNew (groupedBits group z j) t = Nat.card {x // rename (group x,z x)=rename (j,t)} := by
    rw [group_cell]
    simp only [EmbeddingLike.apply_eq_iff_eq]
  have hsum : (∑ j, ∑ v : {x // group x=j}, (f j (old v.val) (groupedBits group z j v)).toNat) =
      ∑ x, (f (group x) (old x) (z x)).toNat := by
    rw [← group_sum group (fun x => (f (group x) (old x) (z x)).toNat)]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    rintro ⟨v,hv⟩ _
    simp only [groupedBits,Equiv.coe_fn_mk,hv]
  unfold physical Matches
  rw [hsum]
  apply and_congr_left
  intro _
  constructor
  · exact fun h j => ⟨(he j false).trans (h _),(he j true).trans (h _)⟩
  · intro h c
    obtain ⟨⟨j,t⟩,rfl⟩ := rename.surjective c
    rw [← he]
    cases t with
    | false => exact (h j).1
    | true => exact (h j).2

theorem column_count {X C : Type} [Fintype X] {N : ℕ} (group : X→Fin N) (old : X→Bool)
    (f : Tables N) (rename : Fin N × Bool ≃ C) (result : C→ℕ) (a b : Bool) :
    Nat.card {z // physical group old f rename result a b z} =
      kernel N (fun j => population (fun v : {x // group x=j} => old v.val))
        f (fun j t => result (rename (j,t))) a b := by
  let e := (groupedBits group).subtypeEquiv (physical_iff group old f rename result a b)
  exact (Nat.card_congr e).trans (kernel_correct N _ _ f _ a b)

open StreamRows

abbrev Slot (d : ℕ) := State d × State d × State d
abbrev Cluster (h : ℕ) := State (h+1) × State h × State (h+1)

def clusterOf {h : ℕ} (v : Slot (h+1)) : Cluster h := (v.1,Fin.tail v.2.1,v.2.2)
def leftover {h : ℕ} (v : Slot (h+1)) : Bool := v.2.1 0

def renameCells (h : ℕ) : Cluster h × Bool ≃ Slot (h+1) where
  toFun z := (z.1.1,Fin.snoc z.1.2.1 z.2,z.1.2.2)
  invFun z := ((z.1,fun i => z.2.1 i.castSucc,z.2.2),z.2.1 (Fin.last h))
  left_inv := by
    rintro ⟨⟨a,t,c⟩,b⟩
    simp
  right_inv := by
    rintro ⟨a,t,c⟩
    have he := Fin.snoc_init_self t
    change (a, Fin.snoc (Fin.init t) (t (Fin.last h)),c) = _
    rw [he]

theorem rename_step {h : ℕ} (v : Slot (h+1)) (b : Bool) :
    renameCells h (clusterOf v,b) = (v.1,nextState v.2.1 b,v.2.2) := by
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext i
  induction i using Fin.lastCases with
  | last => simp [renameCells,clusterOf,nextState,Fin.snoc_last]
  | cast i =>
    have hi : i.val+1<h+1 := by omega
    simp [renameCells,clusterOf,nextState,hi,Fin.snoc_castSucc,Fin.tail,Fin.succ]

noncomputable def cellOrder (h : ℕ) := Fintype.equivFin (Cluster h)

theorem deBruijn_column {X : Type} [Fintype X] (h : ℕ) (source : X→Slot (h+1))
    (f : Cluster h→Bool→Bool→Bool) (desired : Slot (h+1)→ℕ) (start finish : Bool) :
    Nat.card {z : X→Bool //
      (∀ c, Nat.card {x // ((source x).1,nextState (source x).2.1 (z x),(source x).2.2) = c} = desired c) ∧
      xor start ((∑ x, (f (clusterOf (source x)) (leftover (source x)) (z x)).toNat).testBit 0) = finish} =
    kernel (Fintype.card (Cluster h))
      (fun j => population (fun v : {x // cellOrder h (clusterOf (source x))=j} => leftover (source v.val)))
      (fun j => f ((cellOrder h).symm j))
      (fun j t => desired (renameCells h ((cellOrder h).symm j,t))) start finish := by
  let E := ((Equiv.prodCongr (cellOrder h).symm (Equiv.refl Bool)).trans (renameCells h))
  have hc := column_count (fun x => cellOrder h (clusterOf (source x))) (fun x => leftover (source x))
    (fun j => f ((cellOrder h).symm j)) E desired start finish
  simpa only [physical,E,Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply,
    Equiv.symm_apply_apply,rename_step] using hc

end PEqualNP.Outside.L_meta_33676_aux.ColumnTransfer

namespace PEqualNP.Outside.L_meta_33676_aux.PinnedBoundary

open Ranking (rowPinned distinguished cutoff fixedValue)
open Translation ShiftCriterion ShiftedReport StreamRows

def starts {p n d : ℕ} (hd : d≤n) (R : Panel p n) (a : Fin p) : State d :=
  fun j => R a ⟨j.val,j.isLt.trans_le hd⟩

def nextStart {p n d : ℕ} (l h : ℕ) (U : State d) : State d :=
  fun j => if distinguished p n l + 1 < p then fixedValue n l h (distinguished p n l+1) j.val else U j

theorem nextStart_spec {p n d : ℕ} (hp : 0<p) (hn : 0<n) (hd : d≤n) (l h : ℕ)
    (R : Ranking.pinnedPanel p n l h) :
    starts hd R.val (blockNext hp ⟨distinguished p n l,Ranking.distinguished_lt hp n l⟩) =
      nextStart (p:=p) (n:=n) l h (starts hd R.val ⟨0,hp⟩) := by
  funext j
  let q := distinguished p n l
  by_cases inner : q+1<p
  · have idx : blockNext hp (⟨q,Ranking.distinguished_lt hp n l⟩ : Fin p) = ⟨q+1,inner⟩ := by
      apply Fin.ext
      simp [blockNext,inner]
    simp only [starts,nextStart,show distinguished p n l+1<p from inner,ite_true]
    rw [idx]
    apply R.property
    apply (Ranking.pinned_around_cut hp hn ..).mpr
    exact Or.inl (Nat.lt_succ_self _)
  · have idx : blockNext hp (⟨q,Ranking.distinguished_lt hp n l⟩ : Fin p) = ⟨0,hp⟩ := by
      apply Fin.ext
      simp [blockNext,inner]
    dsimp [q] at idx
    simp [starts,nextStart,show ¬distinguished p n l+1<p from inner,idx]

def fixedWindow {p n d : ℕ} (l h : ℕ) (U : State d) (a : Fin p) (i : Fin n) : Vector (d+1) :=
  fun j => scalar (if inside : i.val+j.val<n then fixedValue n l h a.val (i.val+j.val)
    else if a.val+1<p then fixedValue n l h (a.val+1) (i.val+j.val-n)
    else U ⟨i.val+j.val-n,by omega⟩)

theorem fixedWindow_spec {p n d : ℕ} (hp : 0<p) (hn : 0<n) (hd : d<n) (l h : ℕ)
    (R : Ranking.pinnedPanel p n l h) (a : Fin p) (ha : distinguished p n l<a.val) (i : Fin n) :
    panelWindow hp hd R.val i a = fixedWindow l h (starts hd.le R.val ⟨0,hp⟩) a i := by
  funext j
  have fixed (b : Fin p) (hb : distinguished p n l<b.val) (t : Fin n) :
      R.val b t = fixedValue n l h b.val t.val :=
    R.property b t ((Ranking.pinned_around_cut hp hn l b t).mpr (Or.inl hb))
  by_cases inside : i.val+j.val<n
  · simp [panelWindow,fixedWindow,inside,fixed a ha]
  · by_cases next : a.val+1<p
    · have idx : blockNext hp a = ⟨a.val+1,next⟩ := by apply Fin.ext; simp [blockNext,next]
      have hi : distinguished p n l < (⟨a.val+1,next⟩ : Fin p).val := ha.trans (Nat.lt_succ_self _)
      simp [panelWindow,fixedWindow,inside,next,idx,fixed _ hi]
    · have idx : blockNext hp a = ⟨0,hp⟩ := by apply Fin.ext; simp [blockNext,next]
      simp [panelWindow,fixedWindow,inside,next,idx,starts]

theorem split_row_pins {n d : ℕ} (hd : d≤n) (t : ℕ) (R : Fin n → Bool)
    (fixed : ℕ → Bool) :
    (∀ j : Fin n, t≤j.val → R j=fixed j.val) ↔
      (∀ j : Fin d, t≤j.val → R ⟨j.val,j.isLt.trans_le hd⟩ = fixed j.val) ∧
      (∀ i : Fin n, ∀ (h : i.val+d < n), t ≤ i.val+d → R ⟨i.val+d,h⟩ = fixed (i.val+d)) := by
  constructor
  · intro all
    exact ⟨fun j h => all _ h,fun i h le => all _ le⟩
  · rintro ⟨beginning,rest⟩ j hj
    by_cases early : j.val<d
    · exact beginning ⟨j.val,early⟩ hj
    · let i : Fin n := ⟨j.val-d,by omega⟩
      have e : i.val+d=j.val := Nat.sub_add_cancel (Nat.le_of_not_gt early)
      have h := rest i (by omega) (by omega)
      simpa [e] using h

private theorem sum_free {p q : ℕ} {M : Type*} [AddCommMonoid M] (hq : q ≤ p)
    (f : Fin p → M) : (∑ a, if a.val<q then f a else 0) =
    ∑ b : Fin q, f ⟨b.val,b.isLt.trans_le hq⟩ := by
  classical
  rw [← Finset.sum_filter]
  let e : Fin q ≃ {a : Fin p // a.val<q} :=
    ⟨fun b => ⟨⟨b.val,b.isLt.trans_le hq⟩,b.isLt⟩,fun a => ⟨a.val.val,a.property⟩,fun _ => rfl,fun _ => rfl⟩
  calc
    _ = ∑ a : {a : Fin p // a.val<q}, f a.val := Finset.sum_subtype _ (by simp) _
    _ = _ := (e.sum_comp (fun a => f a.val)).symm

theorem column_parity {p n d : ℕ} (hp : 0<p) (hn : 0<n) (hd : d<n) (l h : ℕ)
    (R : Ranking.pinnedPanel p n l h) (i : Fin n) (F : Vector (d+1) → F₂) :
    let q := distinguished p n l
    let aq : Fin p := ⟨q,Ranking.distinguished_lt hp n l⟩
    let U := starts hd.le R.val ⟨0,hp⟩
    (∑ a, F (panelWindow hp hd R.val i a)) =
      (∑ a : Fin q, F (panelWindow hp hd R.val i ⟨a.val,a.isLt.trans (Ranking.distinguished_lt hp n l)⟩)) +
      F (panelWindow hp hd R.val i aq) +
      ∑ a : Fin p, if q<a.val then F (fixedWindow l h U a i) else 0 := by
  classical
  intro q aq U
  let f (a : Fin p) := F (panelWindow hp hd R.val i a)
  let fix (a : Fin p) := F (fixedWindow l h U a i)
  have identity (a : Fin p) : f a = (if a.val<q then f a else 0) +
      (if a=aq then f aq else 0) + (if q<a.val then fix a else 0) := by
    rcases lt_trichotomy a.val q with lo|eq|hi
    · have ha : a≠aq := fun h => Nat.ne_of_lt lo (congrArg Fin.val h)
      simp [lo,ha,Nat.not_lt_of_ge lo.le]
    · have ea : a=aq := Fin.ext eq
      subst a
      simp [aq]
    · have ha : a≠aq := fun h => Nat.ne_of_gt hi (congrArg Fin.val h)
      have hf : f a = fix a := congrArg F (fixedWindow_spec hp hn hd l h R a hi i)
      simp [hi,ha,Nat.not_lt_of_ge hi.le,hf]
  calc
    _ = ∑ a, ((if a.val<q then f a else 0) + (if a=aq then f aq else 0) +
        (if q<a.val then fix a else 0)) := Finset.sum_congr rfl (fun a _ => identity a)
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib,sum_free (Ranking.distinguished_lt hp n l).le]
      simp [f,fix,U]
      rfl

end PEqualNP.Outside.L_meta_33676_aux.PinnedBoundary

namespace PEqualNP.Outside.L_meta_33676_aux.InitialDP

open StreamRows ColumnTransfer Ranking WeightedCircuit
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit Builder

abbrev Macro (q d : ℕ) := State d × State d × Sym (Slot d) q
abbrev Starts (q d : ℕ) := Fin (q+1) → State d

def histogram {q d : ℕ} (f : Fin q → Slot d) : Sym (Slot d) q :=
  Sym.mk (List.ofFn f : Multiset (Slot d)) (by simp)

theorem histogram_count {q d : ℕ} (f : Fin q → Slot d) (c : Slot d) :
    (histogram f).toMultiset.count c = Nat.card {a : Fin q // f a=c} := by
  classical
  change (↑(List.ofFn f) : Multiset (Slot d)).count c = _
  rw [Multiset.coe_count,List.count_ofFn,Nat.card_eq_fintype_card,Fintype.card_subtype]

def initialSlots {q d : ℕ} (u : Starts q d) (i : Fin q) : Slot d :=
  (u i.castSucc,u i.castSucc,u i.succ)

def signature {q d : ℕ} (u : Starts q d) : Macro q d :=
  (u 0,u (Fin.last q),histogram (initialSlots u))

noncomputable def initWeight {q d : ℕ} (s : Macro q d) : ℕ :=
  Nat.card {u : Starts q d // signature u=s}

def pinValid {d : ℕ} (n l q cutoff h : ℕ) (v : State d) : Prop :=
  ∀ j : Fin d, cutoff ≤ j.val → v j = fixedValue n l h q j.val

open Classical in
noncomputable def initValue (p n d l h : ℕ) (s : Macro (distinguished p n l) d) : ℕ :=
  if pinValid n l (distinguished p n l) (cutoff p n l) h s.2.1 then initWeight s else 0

theorem initValue_spec (p n d l h : ℕ) (s : Macro (distinguished p n l) d) :
    initValue p n d l h s = Nat.card {u : Starts (distinguished p n l) d //
      signature u=s ∧ pinValid n l (distinguished p n l) (cutoff p n l) h (u (Fin.last _))} := by
  classical
  let P (u : Starts (distinguished p n l) d) := pinValid n l (distinguished p n l) (cutoff p n l) h (u (Fin.last _))
  have common (u : Starts (distinguished p n l) d) (hu : signature u=s) :
      u (Fin.last _) = s.2.1 := congrArg (fun v => v.2.1) hu
  unfold initValue
  split
  next good =>
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun u => ⟨fun hu => ⟨hu,common u hu ▸ good⟩,And.left⟩)
  next nogood =>
    let : IsEmpty {u : Starts (distinguished p n l) d // signature u=s ∧ P u} :=
      ⟨fun u => nogood (common u.val u.property.1 ▸ u.property.2)⟩
    change 0 = Nat.card {u : Starts (distinguished p n l) d // signature u=s ∧ P u}
    simp

theorem histogram_card {q d p : ℕ} (hq : q≤p) :
    Fintype.card (Macro q d) ≤ (2^d)^2 * (p+(2^d)^3).choose p := by
  let D := 2^d
  let A := D^3
  have pos : 0<A := by unfold A D; positivity
  have hist : Fintype.card (Sym (Slot d) q) = (A+q-1).choose q := by
    rw [Sym.card_sym_eq_choose]; congr 2
    simp [Slot,State,A,D,pow_succ,Nat.mul_assoc]
  have mono (n : ℕ) : (A+n-1).choose n ≤ (A+(n+1)-1).choose (n+1) := by
    rw [show A+(n+1)-1=(A+n-1)+1 by omega,Nat.choose_succ_succ]; omega
  have all : (A+q-1).choose q ≤ (A+p-1).choose p := (monotone_nat_of_le_succ mono) hq
  have total := all.trans (Nat.choose_le_choose p (show A+p-1≤p+A by omega))
  change Fintype.card (State d × State d × Sym (Slot d) q) ≤ D^2 * (p+A).choose p
  simp only [Fintype.card_prod,State,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,hist]
  rw [←Nat.mul_assoc,pow_two]
  exact Nat.mul_le_mul_left _ total

theorem weight_bound {q d : ℕ} (s : Macro q d) : initWeight s ≤ 2^(d*(q+1)) := by
  have h := Nat.card_le_card_of_injective (Subtype.val : {u : Starts q d // signature u=s} → Starts q d)
    Subtype.val_injective
  simpa only [initWeight,Starts,State,Nat.card_fun,Nat.card_fin,show Nat.card Bool=2 by simp,←pow_mul] using h

theorem mapWire {s} {B : Bank s} {f g : BitFn s} (h : B.Has f) (eq : ∀ x, f x=g x) :
    B.Has g := by
  obtain ⟨i,hi,h⟩ := h
  exact ⟨i,hi,fun x => (h x).trans (eq x)⟩

theorem allWires {s : ℕ} {I : Type} (l : List I) (B : Bank s)
    (f : I → BitFn s) (hf : ∀ i, B.Has (f i)) (ho : B.Has (fun _ => true)) :
    B.Grow l.length (fun E => E.Has (fun x => l.all (fun i => f i x))) := by
  induction l with
  | nil => exact Bank.Grow.pure B ho
  | cons i l ih =>
    obtain ⟨D,e,c,w⟩ := ih
    obtain ⟨E,e',c',out⟩ := Bank.meet (e (hf i)) w
    exact ⟨E,Bank.ext_trans e e',by simp; omega,out⟩

open Classical in
private theorem pinCircuit {s p n d l : ℕ} (hp : 0<p) (hd : d≤n) (v : State d)
    (B : Bank s) (o : B.Has (fun _ => true)) (h : Env s → ℕ) (wh : HasWord B (p*n) h) :
    B.Grow (2*d) (fun E => E.Has (fun x => decide
      (pinValid n l (distinguished p n l) (cutoff p n l) (h x) v))) := by
  let q := distinguished p n l
  let cut := cutoff p n l
  let f := fun (i : Fin d) (x : Env s) => decide (cut ≤ i.val → v i = fixedValue n l (h x) q i.val)
  obtain ⟨D,e,c,hf⟩ := B.collectFin d f 1 (by
    intro E e i
    have bound : q*n+i.val-l < p*n := by
      have qn := Nat.mul_le_mul_right n (Ranking.distinguished_lt hp n l)
      change (q+1)*n ≤ p*n at qn
      rw [Nat.add_mul,Nat.one_mul] at qn
      omega
    by_cases le : cut ≤ i.val
    · have w := e (wh ⟨q*n+i.val-l,bound⟩)
      cases hv : v i with
      | false =>
        obtain ⟨F,ef,cf,b⟩ := Bank.inv w
        exact ⟨F,ef,cf,mapWire b (fun x => by simp [f,le,hv,fixedValue])⟩
      | true =>
        exact ⟨E,Bank.ext_refl E,by omega,mapWire w (fun x => by simp [f,le,hv,fixedValue])⟩
    · exact ⟨E,Bank.ext_refl E,by omega,mapWire (e o) (fun x => by simp [f,le])⟩)
  obtain ⟨E,eE,cE,out⟩ := allWires (List.finRange d) D f hf (e o)
  refine ⟨E,Bank.ext_trans e eE,?_,mapWire out (fun x => ?_)⟩
  · simp at c cE; omega
  · apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true,List.mem_finRange,forall_true_left,f,decide_eq_true_eq]
    rfl

theorem compileInitial {s p n d l : ℕ} (hp : 0<p) (hd : d≤n) (B : Bank s)
    (h : Env s → ℕ) (wh : HasWord B (p*n) h) (width : ℕ) :
    B.Grow (2+2^d*(2*d)) (fun E =>
      ∀ st : Macro (distinguished p n l) d, HasWord E width (fun x => initValue p n d l (h x) st)) := by
  classical
  obtain ⟨C,eC,cC,z⟩ := B.const false
  obtain ⟨D,eD,cD,o⟩ := C.const true
  have eb : B.Ext D := Bank.ext_trans eC eD
  obtain ⟨E,e,c,w⟩ := SensorBuilder.collectType D
    (fun v : State d => fun x => decide (pinValid n l (distinguished p n l) (cutoff p n l) (h x) v))
    (2*d) (fun F ef v => pinCircuit hp hd v F (ef o) h (keep (Bank.ext_trans eb ef) wh))
  refine ⟨E,Bank.ext_trans eb e,?_,?_⟩
  · simp [State] at c; omega
  · intro st i
    cases digit : (initWeight st).testBit i.val with
    | false =>
      exact mapWire (e (eD z)) (fun x => by
        dsimp only; unfold initValue; split <;> simp [digit])
    | true =>
      exact mapWire (w st.2.1) (fun x => by
        dsimp only; unfold initValue; split <;> rename_i hv <;> simp [digit,hv])

end PEqualNP.Outside.L_meta_33676_aux.InitialDP

namespace PEqualNP.Outside.L_meta_33676_aux.CommonCircuit

open Translation ShiftCriterion ShiftedReport MatrixCircuit
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit Builder SensorBuilder
open EliminationCircuit (bit)

private theorem scalar_bit (z : F₂) : scalar (bit z) = z := by revert z; decide

private theorem bit_sub (a b : F₂) : xor (bit a) (bit b) = bit (a-b) := by revert a b; decide
private theorem bit_add (a b : F₂) : xor (bit a) (bit b) = bit (a+b) := by revert a b; decide

theorem complementControl {s : Nat} (B : Bank s) (f : Env s → F₂) (hf : B.Has (fun x => bit (f x)))
    (z : F₂) : B.Grow 1 (fun E => E.Has (fun x => bit (z+f x))) := by
  have hs : ∀ a : F₂, a = 0 ∨ a = 1 := by decide
  rcases hs z with rfl | rfl
  · exact ⟨B,Bank.ext_refl _,by omega,by simpa using hf⟩
  · apply (Bank.inv hf).weaken le_rfl
    intro E h
    apply has_iff h
    have eq : ∀ a : F₂, (!(bit a)) = bit (1+a) := by decide
    exact fun x => eq _

def lookupCost (w : Nat) := 1+2^w*(4+2*w)

theorem lookup {s w : Nat} (B : Bank s) (T : Env s → Translation.Vector w → F₂)
    (key : Env s → Translation.Vector w)
    (ht : ∀ v, B.Has (fun x => bit (T x v))) (hk : ∀ j, B.Has (fun x => bit (key x j))) :
    B.Grow (lookupCost w) (fun E => E.Has (fun x => bit (T x (key x)))) := by
  classical
  let pred := fun v x => key x = v → T x v = 1
  have each (D : Bank s) (ext : B.Ext D) (v : Translation.Vector w) :
    D.Grow (1+w*2+2) (fun E => E.Has (fun x => truth (pred v x))) := by
    have eqbit (C : Bank s) (extC : D.Ext C) (j : Fin w) :
      C.Grow 1 (fun E => E.Has (fun x => truth (key x j = v j))) := by
      have hw := extC (ext (hk j))
      have two : ∀ a : F₂, a=0 ∨ a=1 := by decide
      rcases two (v j) with hv | hv
      · apply (Bank.inv hw).weaken le_rfl
        intro E h
        apply has_iff h
        intro x
        rw [hv]
        apply Bool.eq_iff_iff.mpr
        have eq : ∀ a : F₂, (!(bit a))=true ↔ a=0 := by decide
        simpa only [truth_true] using eq (key x j)
      · refine ⟨C,Bank.ext_refl _,by omega,has_iff hw (fun x => ?_)⟩
        rw [hv]
        apply Bool.eq_iff_iff.mpr
        simp [bit]
    obtain ⟨C,eC,lenC,eq⟩ := allWire D (fun j x => key x j=v j) 1 eqbit
    obtain ⟨E,eE,lenE,neg⟩ := Bank.inv eq
    obtain ⟨F,eF,lenF,h⟩ := Bank.join neg (eE (eC (ext (ht v))))
    refine ⟨F,Bank.ext_trans eC (Bank.ext_trans eE eF),?_,has_iff h (fun x => ?_)⟩
    · simp at lenC; omega
    · apply Bool.eq_iff_iff.mpr
      simp [pred,bit,truth,funext_iff,imp_iff_not_or]
  obtain ⟨D,eD,lenD,h⟩ := allWire B pred (1+w*2+2) each
  refine ⟨D,eD,?_,has_iff h (fun x => ?_)⟩
  · simp [F₂] at lenD
    unfold lookupCost
    ring_nf at lenD ⊢
    exact lenD
  · apply Bool.eq_iff_iff.mpr
    simp [truth,pred,bit]

theorem offsetLookup {s w : Nat} (B : Bank s) (T : Env s → Translation.Vector w → F₂)
    (key : Env s → Translation.Vector w) (z : Translation.Vector w)
    (ht : ∀ v, B.Has (fun x => bit (T x v))) (hk : ∀ j, B.Has (fun x => bit (key x j))) :
    B.Grow (w+lookupCost w) (fun E => E.Has (fun x => bit (T x (z+key x)))) := by
  obtain ⟨C,eC,lenC,addr⟩ := B.collectFin w (fun j x => bit (z j + key x j)) 1
    (fun D eD j => complementControl D _ (eD (hk j)) (z j))
  obtain ⟨D,eD,lenD,val⟩ := lookup C T (fun x => z+key x) (fun v => eC (ht v)) addr
  exact ⟨D,Bank.ext_trans eC eD,by simp at lenC; omega,val⟩

theorem sumField {s : Nat} {I : Type} [DecidableEq I] (B : Bank s)
    (S : Finset I) (f : I → Env s → F₂) (hb : ∀ i, B.Has (fun x => bit (f i x))) :
    B.Grow (1+S.card*4) (fun E => E.Has (fun x => bit (∑ i ∈ S, f i x))) := by
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨E,ext,len,hz⟩ := B.const false
    exact ⟨E,ext,by simpa using len,by simpa [bit] using hz⟩
  | insert i t hi ih =>
    obtain ⟨D,extD,lenD,hD⟩ := ih
    obtain ⟨E,extE,lenE,hE⟩ := Bank.xor2 (extD (hb i)) hD
    refine ⟨E,Bank.ext_trans extD extE,?_,has_iff hE (fun x => ?_)⟩
    · rw [Finset.card_insert_of_notMem hi,Nat.succ_mul]; omega
    · simp only [Finset.sum_insert hi]
      exact bit_add _ _

def signalCost (p n d : Nat) :=
  p*n*(d+1+lookupCost (d+1)) + n*(2^(d+1))*(d+1+lookupCost (d+1)+4) + n*(1+p*4)

theorem commonAndOffset {s p n d : Nat} (hp : 0<p) (hn : 0<n) (B : Bank s)
    (T : Family s p n d) (g : Env s → Word (p*n))
    (ht : TableWires B T) (hg : ∀ i : Fin (p*n), B.Has (fun x => (g x).val.testBit i.val)) :
    B.Grow (signalCost p n d) (fun E =>
      (∀ (i : Fin n) (z : Translation.Vector (d+1)), E.Has (fun x => bit (commonTable hp hn (T x) (g x) i z))) ∧
      ∀ i, E.Has (fun x => bit (residueSum hp hn (T x) (encode (g x)) i))) := by
  classical
  let key := fun (i : Fin n) (a : Fin p) x => windowMap (width:=d+1) hp hn i a (encode (g x))
  have hk (i : Fin n) (a : Fin p) (j : Fin (d+1)) :
      B.Has (fun x => bit (key i a x j)) := by
    apply has_iff (hg (cyclicWindow hp hn i.val (a,j)))
    intro x
    change _ = bit (scalar _)
    cases (g x).val.testBit (cyclicWindow hp hn i.val (a,j)).val <;> decide
  let base := fun (u : Fin n × Fin p) x => bit (T x u.1 u.2 (key u.1 u.2 x))
  obtain ⟨C,eC,lenC,atBase⟩ := collectType B base (d+1+lookupCost (d+1)) (by
    intro D eD u
    apply (offsetLookup D (fun x => T x u.1 u.2) (key u.1 u.2) 0
      (fun v => eD (ht u.1 u.2 v)) (fun j => eD (hk u.1 u.2 j))).weaken le_rfl
    intro E h
    simpa [base] using h)
  let common := fun (v : Fin n × Translation.Vector (d+1)) x => bit (commonTable hp hn (T x) (g x) v.1 v.2)
  obtain ⟨D,eD,lenD,htab⟩ := collectType C common (d+1+lookupCost (d+1)+4) (by
    intro V eV u
    let a0 : Fin p := ⟨0,hp⟩
    obtain ⟨E,eE,leE,res⟩ := offsetLookup V (fun x => T x u.1 a0) (key u.1 a0) u.2
      (fun z => eV (eC (ht _ _ z))) (fun j => eV (eC (hk _ _ j)))
    obtain ⟨F,eF,leF,hF⟩ := Bank.xor2 res (eE (eV (atBase (u.1,a0))))
    exact ⟨F,Bank.ext_trans eE eF,by omega,has_iff hF (fun x => bit_sub _ _)⟩)
  obtain ⟨F,eF,lenF,bias⟩ := collectType D (fun i x => bit (residueSum hp hn (T x) (encode (g x)) i))
    (1+p*4) (by
      intro E eE i
      simpa [residueSum,base,key] using sumField E (Finset.univ : Finset (Fin p))
        (fun a x => T x i a (key i a x)) (fun a => eE (eD (atBase (i,a)))))
  refine ⟨F,Bank.ext_trans eC (Bank.ext_trans eD eF),?_,fun i z => eF (htab (i,z)),bias⟩
  simp [Translation.Vector,F₂] at lenC lenD lenF
  unfold signalCost
  rw [Nat.mul_comm p n]
  omega

end PEqualNP.Outside.L_meta_33676_aux.CommonCircuit

namespace PEqualNP.Outside.L_meta_33676_aux.BoundaryCircuit

open Translation ShiftCriterion StreamRows PinnedBoundary CommonCircuit MatrixCircuit
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit Builder SensorBuilder
open EliminationCircuit (bit)

theorem fixedBitWire {s k : Nat} (B : Bank s) (h : Env s → Nat)
    (hh : ∀ i : Fin k, B.Has (fun x => (h x).testBit i.val)) (bound : ∀ x, h x < 2^k)
    (z : B.Has (fun _ => false)) (j : Nat) : B.Has (fun x => (h x).testBit j) := by
  by_cases hj : j<k
  · exact hh ⟨j,hj⟩
  · apply has_iff z
    intro x
    exact (Nat.testBit_eq_false_of_lt ((bound x).trans_le (Nat.pow_le_pow_right (by decide) (by omega)))).symm

theorem fixedAddress {s p n d : Nat} (B : Bank s) (l : Nat) (h : Env s → Nat)
    (hh : ∀ i : Fin (p*n), B.Has (fun x => (h x).testBit i.val)) (bound : ∀ x, h x < 2^(p*n))
    (z : B.Has (fun _ => false)) (o : B.Has (fun _ => true))
    (U : State d) (a : Fin p) (i : Fin n) (j : Fin (d+1)) :
    B.Has (fun x => bit (fixedWindow l (h x) U a i j)) := by
  have sc (f : Env s → Bool) (w : B.Has f) : B.Has (fun x => bit (scalar (f x))) :=
    has_iff w (fun x => by cases f x <;> decide)
  unfold fixedWindow
  by_cases ij : i.val+j.val<n
  · simp only [ij, ↓reduceDIte]
    exact sc _ (fixedBitWire B h hh bound z _)
  · simp only [ij, ↓reduceDIte]
    by_cases ab : a.val+1<p
    · simp only [ab, ↓reduceIte]
      exact sc _ (fixedBitWire B h hh bound z _)
    · simp only [ab, ↓reduceIte]
      apply sc
      cases U ⟨i.val+j.val-n,by omega⟩
      · exact z
      · exact o

def fixedParity {s p n d : Nat} (F : Env s → Fin n → Translation.Vector (d+1) → F₂)
    (l : Nat) (h : Env s → Nat) (U : State d) (i : Fin n) (x : Env s) : F₂ :=
  ∑ a : Fin p, if Ranking.distinguished p n l < a.val then F x i (fixedWindow l (h x) U a i) else 0

def boundaryCost (p n d : Nat) := 2^d*n*(p*lookupCost (d+1) + (1+p*4))

theorem buildFixedParity {s p n d : Nat} (B : Bank s)
    (F : Env s → Fin n → Translation.Vector (d+1) → F₂)
    (hw : ∀ i v, B.Has (fun x => bit (F x i v)))
    (l : Nat) (h : Env s → Nat) (hh : ∀ i : Fin (p*n), B.Has (fun x => (h x).testBit i.val))
    (bound : ∀ x, h x < 2^(p*n)) (z : B.Has (fun _ => false)) (o : B.Has (fun _ => true)) :
    B.Grow (boundaryCost p n d) (fun E => ∀ U i, E.Has (fun x => bit (fixedParity (p:=p) F l h U i x))) := by
  classical
  let f (v : State d × Fin n) (a : Fin p) (x : Env s) : F₂ :=
    if Ranking.distinguished p n l<a.val then F x v.2 (fixedWindow l (h x) v.1 a v.2) else 0
  obtain ⟨D,eD,lenD,all⟩ := collectType B
    (fun v : State d × Fin n => fun x => bit (fixedParity (p:=p) F l h v.1 v.2 x))
    (p*lookupCost (d+1)+(1+p*4)) (by
      intro C eC v
      obtain ⟨E,eE,lenE,bank⟩ := collectType C (fun a x => bit (f v a x)) (lookupCost (d+1)) (by
        intro J eJ a
        have ext : B.Ext J := Bank.ext_trans eC eJ
        by_cases ha : Ranking.distinguished p n l < a.val
        · simpa [f,ha] using lookup J (fun x => F x v.2) (fun x => fixedWindow l (h x) v.1 a v.2)
            (fun t => ext (hw _ t)) (fun j => ext (fixedAddress B l h hh bound z o v.1 a v.2 j))
        · refine ⟨J,Bank.ext_refl _,by omega,?_⟩
          simpa [f,ha,bit] using ext z)
      obtain ⟨K,eK,lenK,out⟩ := sumField E Finset.univ (f v) bank
      refine ⟨K,Bank.ext_trans eE eK,?_,out⟩
      simp only [Fintype.card_fin,Finset.card_univ] at lenE lenK
      omega)
  exact ⟨D,eD,by simpa [boundaryCost,State] using lenD, fun U i => all (U,i)⟩

end PEqualNP.Outside.L_meta_33676_aux.BoundaryCircuit

namespace PEqualNP.Outside.L_meta_33676_aux.BranchDP

open InitialDP StreamRows Ranking WeightedCircuit
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit Builder

def branchAllowed (p n d l h : ℕ) (i : Fin n) (z : Bool) : Prop :=
  i.val+d<n → cutoff p n l ≤ i.val+d → z = fixedValue n l h (distinguished p n l) (i.val+d)

def preceding {e : ℕ} (new : State (e+1)) (b : Bool) : State (e+1) :=
  Fin.cons b (Fin.init new)

def appended {e : ℕ} (new : State (e+1)) := new (Fin.last e)

theorem next_eq {e : ℕ} (v : State (e+1)) (z : Bool) :
    nextState v z = Fin.snoc (Fin.tail v) z := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [nextState]
  | cast j => simp [nextState,show j.val+1<e+1 by omega,Fin.snoc_castSucc,Fin.tail,Fin.succ]

theorem recover_next {e : ℕ} (new : State (e+1)) (b : Bool) :
    nextState (preceding new b) (appended new) = new := by
  rw [next_eq]
  simp [preceding,appended,Fin.snoc_init_self]

def preimages {e : ℕ} (new : State (e+1)) :
    Bool ≃ {p : State (e+1) × Bool // nextState p.1 p.2 = new} where
  toFun b := ⟨(preceding new b,appended new),recover_next new b⟩
  invFun p := p.val.1 0
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨v,z⟩,hv⟩
    apply Subtype.ext
    change (preceding new (v 0),appended new) = (v,z)
    rw [←hv,next_eq]
    apply Prod.ext
    · simp [preceding,Fin.cons_self_tail]
    · simp [appended]

def control {s : ℕ} (pin : Bool → BitFn s) (residual : BitFn s)
    (table : Bool → BitFn s) (z parity : Bool) (x : Env s) : Bool :=
  pin z x && (xor parity (table z x) == residual x)

def advance {s q e : ℕ} (pin : Bool → BitFn s) (residual : State (e+1) → BitFn s)
    (table : State (e+1) → Bool → BitFn s) (prev : Macro q (e+1) → Bool → Env s → ℕ)
    (v : Macro q (e+1)) (x : Env s) : ℕ :=
  ∑ b : Bool × Bool,
    if control pin (residual v.1) (table (preceding v.2.1 b.1)) (appended v.2.1) b.2 x then
      prev (v.1,preceding v.2.1 b.1,v.2.2) b.2 x
    else 0

theorem advance_spec {s q e : ℕ} (pin : Bool → BitFn s) (residual : State (e+1) → BitFn s)
    (table : State (e+1) → Bool → BitFn s) (prev : Macro q (e+1) → Bool → Env s → ℕ)
    (v : Macro q (e+1)) (x : Env s) :
    advance pin residual table prev v x =
      ∑ t : {p : State (e+1) × Bool // nextState p.1 p.2=v.2.1}, ∑ parity : Bool,
        if control pin (residual v.1) (table t.val.1) t.val.2 parity x then
          prev (v.1,t.val.1,v.2.2) parity x else 0 := by
  rw [← (preimages v.2.1).sum_comp,advance,Fintype.sum_prod_type]
  rfl

open Classical in
theorem branchWires {s p n d : ℕ} (B : Bank s) (zero : B.Has (fun _ => false)) (one : B.Has (fun _ => true))
    (l : ℕ) (h : Env s → ℕ) (bh : ∀ x,h x<2^(p*n)) (wh : HasWord B (p*n) h) (i : Fin n) (z : Bool) :
    B.Grow 1 (fun E => E.Has (fun x => decide (branchAllowed p n d l (h x) i z))) := by
  have bit := BoundaryCircuit.fixedBitWire B h wh bh zero (distinguished p n l*n+(i.val+d)-l)
  by_cases inside : i.val+d<n
  · by_cases fixed : cutoff p n l ≤ i.val+d
    · cases z with
      | false =>
        obtain ⟨D,e,c,w⟩ := Bank.inv bit
        exact ⟨D,e,c,mapWire w (fun x => by simp [branchAllowed,inside,fixed,fixedValue])⟩
      | true =>
        exact ⟨B,Bank.ext_refl _,by omega,mapWire bit (fun x => by simp [branchAllowed,inside,fixed,fixedValue])⟩
    · exact ⟨B,Bank.ext_refl _,by omega,mapWire one (fun x => by simp [branchAllowed,fixed])⟩
  · exact ⟨B,Bank.ext_refl _,by omega,mapWire one (fun x => by simp [branchAllowed,inside])⟩

private theorem controlWire {s : ℕ} (B : Bank s) (pin : Bool → BitFn s) (residual : BitFn s)
    (table : Bool → BitFn s) (z parity : Bool) (hp : B.Has (pin z)) (hr : B.Has residual)
    (ht : B.Has (table z)) :
    B.Grow 7 (fun E => E.Has (control pin residual table z parity)) := by
  have spec (x : Env s) : (xor parity (table z x) == residual x) =
      (if parity then xor (table z x) (residual x) else !(xor (table z x) (residual x))) := by
    cases parity <;> cases table z x <;> cases residual x <;> decide
  obtain ⟨F,eF,cF,neq⟩ := Bank.xor2 ht hr
  have wires : F.Grow 1 (fun G => G.Has (fun x => if parity then xor (table z x) (residual x)
      else !(xor (table z x) (residual x)))) := by
    cases parity with
    | true => exact ⟨F,Bank.ext_refl _,by omega,neq⟩
    | false => exact Bank.inv neq
  obtain ⟨G,eG,cG,v⟩ := wires
  obtain ⟨E,eE,cE,ans⟩ := Bank.meet (eG (eF hp)) v
  exact ⟨E,Bank.ext_trans eF (Bank.ext_trans eG eE),by omega,mapWire ans (fun x => by simp [control,spec])⟩

theorem gatherWords {n w : ℕ} {α : Type*} [DecidableEq α] (B : Bank n)
    (U : Finset α) (f : α → Env n → ℕ) (cost : ℕ)
    (emit : ∀ j ∈ U, ∀ D, B.Ext D → D.Grow cost (fun E => HasWord E w (f j))) :
    B.Grow (U.card*cost) (fun E => ∀ j ∈ U, HasWord E w (f j)) := by
  induction U using Finset.induction_on with
  | empty => exact ⟨B, Bank.ext_refl B, by simp, by simp⟩
  | @insert j U hj ih =>
    obtain ⟨D,eD,kD,hD⟩ := ih (fun i hi => emit i (Finset.mem_insert_of_mem hi))
    obtain ⟨E,eE,kE,he⟩ := emit j (Finset.mem_insert_self _ _) D eD
    refine ⟨E, Bank.ext_trans eD eE, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hj, Nat.succ_mul]
      omega
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl|hu
      · exact he
      · exact keep eE (hD a hu)

open Classical in

theorem compileAdvance {s p n e q w : ℕ} (B : Bank s)
    (zero : B.Has (fun _ => false)) (one : B.Has (fun _ => true))
    (l : ℕ) (h : Env s → ℕ) (bh : ∀ x,h x<2^(p*n)) (wh : HasWord B (p*n) h) (i : Fin n)
    (residual : State (e+1) → BitFn s) (table : State (e+1) → Bool → BitFn s)
    (prev : Macro q (e+1) → Bool → Env s → ℕ)
    (hr : ∀ U,B.Has (residual U)) (ht : ∀ c z,B.Has (table c z)) (hv : ∀ u b,HasWord B w (prev u b)) :
    let pin := fun z x => decide (branchAllowed p n (e+1) l (h x) i z)
    B.Grow (2+(2^(e+1))^2*4*7+Fintype.card (Macro q (e+1))*(4*(w*17)))
      (fun E => ∀ v,HasWord E w (advance pin residual table prev v)) := by
  let pin := fun z x => decide (branchAllowed p n (e+1) l (h x) i z)
  obtain ⟨D,eD,cD,ws⟩ := SensorBuilder.collectType B pin 1 (fun E e z =>
    branchWires E (e zero) (e one) l h bh (keep e wh) i z)
  let key := State (e+1) × State (e+1) × Bool × Bool
  let ctl := fun t : key => control pin (residual t.1) (table (preceding t.2.1 t.2.2.1))
    (appended t.2.1) t.2.2.2
  obtain ⟨T,eT,cT,cs⟩ := SensorBuilder.collectType D ctl 7 (by
    intro S es t
    exact controlWire S pin _ _ _ _ (es (ws _)) (es (eD (hr _))) (es (eD (ht _ _))))
  have eBT := @Bank.ext_trans s B D T eD eT
  let val := advance pin residual table prev
  let V := Macro q (e+1)
  classical
  have all : T.Grow (Fintype.card V*(4*(w*17))) (fun E => ∀ v,HasWord E w (val v)) := by
    classical
    let S := (Finset.univ : Finset V)
    suffices T.Grow (S.card*(4*(w*17))) (fun E => ∀ v∈S,HasWord E w (val v)) by simpa only [S,Finset.mem_univ,forall_true_left,Finset.card_univ] using this
    apply gatherWords T S val (4*(w*17))
    intro v _ D e
    let src := fun t : Bool×Bool => (v.1,preceding v.2.1 t.1,v.2.2)
    let vctl := fun t : Bool×Bool => ctl (v.1,v.2.1,t.1,t.2)
    let term := fun t : Bool×Bool => fun x => if vctl t x then prev (src t) t.2 x else 0
    obtain ⟨F,ef,cf,wires⟩ := sumWords (w:=w) D (e (eBT zero)) (e (eBT one)) Finset.univ term (w*4) (by
      intro t _ G eg
      exact muxWord G (vctl t) _ _ (eg (e (cs _))) (keep (Bank.ext_trans eBT (Bank.ext_trans e eg)) (hv _ _))
        (constWord G (eg (e (eBT zero))) (eg (e (eBT one))) 0))
    exact ⟨F,ef,by simp at cf; omega,wires⟩
  obtain ⟨K,ek,ck,kval⟩ := all
  refine ⟨K,Bank.ext_trans eBT ek,?_,kval⟩
  have keycard : Fintype.card key=(2^(e+1))^2*4 := by simp [key,State]; ring
  rw [keycard] at cT
  simp at cD
  dsimp only [V] at ck
  omega

end PEqualNP.Outside.L_meta_33676_aux.BranchDP

namespace PEqualNP.Outside.L_meta_33676_aux.ActiveRows

open Ranking (rowPinned distinguished cutoff fixedValue pinnedPanel distinguished_lt)
open Translation ShiftCriterion ShiftedReport StreamRows PinnedBoundary

abbrev Dynamic (p n d l : ℕ) := Fin (distinguished p n l + 1) → Trace n d

def index {p n l : ℕ} (hp : 0<p) (a : Fin (distinguished p n l+1)) : Fin p :=
  ⟨a.val,a.isLt.trans_le (distinguished_lt hp n l)⟩

def extract {p n d l : ℕ} (hp : 0<p) (hd : d≤n) (R : Panel p n) : Dynamic p n d l :=
  fun a => panelTraces hp hd R (index hp a)

def recover {p n d l : ℕ} (h : ℕ) (v : Dynamic p n d l) : Panel p n :=
  fun a j => if act : a.val<distinguished p n l+1 then
    v ⟨a.val,act⟩ ⟨j.val,by omega⟩ else fixedValue n l h a.val j.val

def localPins {p n d l : ℕ} (h : ℕ) (v : Dynamic p n d l) : Prop :=
  ∀ j : Fin n, cutoff p n l ≤ j.val →
    v (Fin.last _) ⟨j.val,by omega⟩ = fixedValue n l h (distinguished p n l) j.val

def lastSeam {p n d l : ℕ} (h : ℕ) (v : Dynamic p n d l) : Prop :=
  stateAt (v (Fin.last _)) (Fin.last n) = nextStart (p:=p) (n:=n) l h (stateAt (v 0) 0)

def freeSeam {p n d l : ℕ} (v : Dynamic p n d l) : Prop :=
  ∀ a : Fin (distinguished p n l), stateAt (v a.castSucc) (Fin.last n) = stateAt (v a.succ) 0

theorem recovered_pins {p n d l : ℕ} (hp : 0<p) (hn : 0<n) (h : ℕ) (v : Dynamic p n d l) :
    (∀ a j, rowPinned n l a.val j.val → recover h v a j = fixedValue n l h a.val j.val) ↔ localPins h v := by
  constructor
  · intro pin j hj
    let a : Fin p := ⟨distinguished p n l,distinguished_lt hp n l⟩
    have eq := pin a j ((Ranking.pinned_around_cut hp hn l a j).mpr (Or.inr ⟨rfl,hj⟩))
    simpa [a,recover,Fin.last] using eq
  · intro pin a j hj
    rw [Ranking.pinned_around_cut hp hn] at hj
    rcases hj with above|⟨ea,hj⟩
    · simp [recover,show ¬a.val<distinguished p n l+1 by omega]
    · have ha : a.val < distinguished p n l+1 := by omega
      simp only [recover,ha,↓reduceDIte]
      have idx : (⟨a.val,ha⟩ : Fin (distinguished p n l+1))=Fin.last _ := Fin.ext ea
      rw [idx,ea]
      exact pin j hj

theorem recover_extract {p n d l h : ℕ} (hp : 0<p) (hn : 0<n) (hd : d≤n)
    (R : pinnedPanel p n l h) : recover h (extract (l:=l) hp hd R.val) = R.val := by
  funext a j
  by_cases act : a.val < distinguished p n l+1
  · simp [recover,extract,act,index,panelTraces,j.isLt]
  · simp only [recover,act,↓reduceDIte]
    exact (R.property a j ((Ranking.pinned_around_cut hp hn l a j).mpr (Or.inl (by omega)))).symm

theorem directStart {p n d l : ℕ} (hp : 0<p) (hd : d≤n) (R : Panel p n)
    (a : Fin (distinguished p n l+1)) :
    stateAt (extract hp hd R a) 0 = starts hd R (index hp a) := by
  funext j
  simp [stateAt,extract,panelTraces,starts,j.isLt.trans_le hd]

theorem directEnd {p n d l : ℕ} (hp : 0<p) (hd : d≤n) (R : Panel p n)
    (a : Fin (distinguished p n l+1)) :
    stateAt (extract hp hd R a) (Fin.last n) = starts hd R (blockNext hp (index hp a)) := by
  funext j
  simp [stateAt,extract,panelTraces,starts,show ¬n+j.val<n by omega]

theorem nextFree {p n l : ℕ} (hp : 0<p) (a : Fin (distinguished p n l)) :
    blockNext hp (index hp a.castSucc) = index hp a.succ := by
  apply Fin.ext
  have bnd : a.val+1 < p := lt_of_le_of_lt a.isLt (distinguished_lt hp n l)
  simp [index,blockNext,bnd]

theorem extract_conditions {p n d l h : ℕ} (hp : 0<p) (hn : 0<n) (hd : d≤n)
    (R : pinnedPanel p n l h) :
    let v := extract (l:=l) hp hd R.val
    localPins h v ∧ freeSeam v ∧ lastSeam h v := by
  intro v
  have basis :=  recover_extract hp hn hd R
  refine ⟨(recovered_pins hp hn h v).mp ?_,?_,?_⟩
  · change ∀ a j, rowPinned n l a.val j.val → recover h (extract hp hd R.val) a j = _
    rw [basis]
    exact R.property
  · intro a
    rw [show v = extract hp hd R.val by rfl,directEnd,directStart,nextFree]
  · change stateAt (extract hp hd R.val (Fin.last _)) (Fin.last n) = nextStart _ _ (stateAt (extract hp hd R.val 0) 0)
    rw [directEnd,directStart]
    exact nextStart_spec hp hn hd l h R

theorem extract_recover {p n d l h : ℕ} (hp : 0<p) (hn : 0<n) (hd : d≤n)
    (v : Dynamic p n d l) (pin : localPins h v) (free : freeSeam v) (last : lastSeam h v) :
    extract hp hd (recover h v) = v := by
  funext a t
  have active (a : Fin (distinguished p n l+1)) (j : Fin n) :
      recover h v (index hp a) j = v a ⟨j.val,by omega⟩ := by simp [recover,index,a.isLt]
  by_cases original : t.val<n
  · simp [extract,panelTraces,original,active]
  · let j : Fin d := ⟨t.val-n,by omega⟩
    have end_at : stateAt (v a) (Fin.last n) j = v a t := by
      dsimp [stateAt,j]
      congr 1
      apply Fin.ext
      dsimp
      omega
    have successor : starts hd (recover h v) (blockNext hp (index hp a)) = stateAt (v a) (Fin.last n) := by
      refine Fin.lastCases ?_ (fun b => ?_) a
      · let R : pinnedPanel p n l h := ⟨recover h v,(recovered_pins hp hn h v).mpr pin⟩
        have ns := nextStart_spec hp hn hd l h R
        change starts hd R.val (blockNext hp ⟨distinguished p n l,distinguished_lt hp n l⟩) = _
        rw [ns]
        apply Eq.trans _ last.symm
        congr 1
        funext j
        simpa [starts,stateAt,R,index] using active 0 ⟨j.val,j.isLt.trans_le hd⟩
      · rw [nextFree,free b]
        funext j
        simpa [starts,stateAt] using active b.succ ⟨j.val,j.isLt.trans_le hd⟩
    exact (show panelTraces hp hd (recover h v) (index hp a) t = starts hd (recover h v) (blockNext hp (index hp a)) j by
      simp [panelTraces,original,starts,j]).trans ((congrFun successor j).trans end_at)

def pinnedEquivActive {p n d : ℕ} (hp : 0<p) (hn : 0<n) (hd : d≤n) (l h : ℕ) :
    pinnedPanel p n l h ≃ {v : Dynamic p n d l // localPins h v ∧ freeSeam v ∧ lastSeam h v} where
  toFun R := ⟨extract hp hd R.val,extract_conditions hp hn hd R⟩
  invFun v := ⟨recover h v.val,(recovered_pins hp hn h v.val).mpr v.property.1⟩
  left_inv R := Subtype.ext (recover_extract hp hn hd R)
  right_inv v := Subtype.ext (extract_recover hp hn hd v.val v.property.1 v.property.2.1 v.property.2.2)

end PEqualNP.Outside.L_meta_33676_aux.ActiveRows

namespace PEqualNP.Outside.L_meta_33676_aux.HistoryFold

open scoped Classical
open Transfer

def Hist (I B : Type) : ℕ → Type
  | 0 => I
  | t+1 => Hist I B t × B

instance histFintype {I B : Type} [Fintype I] [Fintype B] : (t : ℕ) → Fintype (Hist I B t)
  | 0 => inferInstanceAs (Fintype I)
  | t+1 =>
    letI := histFintype (I:=I) (B:=B) t
    inferInstanceAs (Fintype (Hist I B t × B))

variable {I B M H : Type}

def state (init : I → M) (step : ℕ → M → B → M) : (t : ℕ) → Hist I B t → M
  | 0, a => init a
  | t+1, z => step t (state init step t z.1) z.2

def allowed (init : I → M) (step : ℕ → M → B → M)
    (seed : I → Prop) (enable : ℕ → M → B → Prop) : (t : ℕ) → Hist I B t → Prop
  | 0, a => seed a
  | t+1, z => allowed init step seed enable t z.1 ∧ enable t (state init step t z.1) z.2

def count [Fintype H] (seed : H→ℕ) (transfer : ℕ → H → H → ℕ) : ℕ → H → ℕ
  | 0, u => seed u
  | t+1, v => ∑ u, count seed transfer t u * transfer t u v

theorem count_histories [Fintype I] [Fintype B] [Fintype H]
    (init : I → M) (step : ℕ → M → B → M) (seed : I → Prop)
    (enable : ℕ → M → B → Prop) (summary : M → H) (transfer : ℕ → H → H → ℕ)
    (uniform : ∀ t m v, Nat.card {b : B // enable t m b ∧ summary (step t m b)=v} =
      transfer t (summary m) v) (n : ℕ) (v : H) :
    count (fun u => Nat.card {a : I // seed a ∧ summary (init a)=u}) transfer n v =
      Nat.card {z : Hist I B n // allowed init step seed enable n z ∧ summary (state init step n z)=v} := by
  classical
  induction n generalizing v with
  | zero => rfl
  | succ t ih =>
    let X := {z : Hist I B t // allowed init step seed enable t z}
    let m (x : X) := state init step t x.val
    let T (x : X) := {b : B // enable t (m x) b}
    let E : {z : Hist I B (t+1) // allowed init step seed enable (t+1) z ∧ summary (state init step (t+1) z)=v} ≃
        {e : Σ x : X, T x // summary (step t (m e.1) e.2.val)=v} :=
      ⟨fun z => ⟨⟨⟨z.val.1,z.property.1.1⟩,⟨z.val.2,z.property.1.2⟩⟩,z.property.2⟩,
       fun e => ⟨(e.val.1.val,e.val.2.val),⟨e.val.1.property,e.val.2.property⟩,e.property⟩,
       fun _ => rfl, fun _ => rfl⟩
    rw [Nat.card_congr E]
    have localW (x : X) : Nat.card {b : T x // summary (step t (m x) b.val)=v} =
        transfer t (summary (m x)) v :=
      (Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter _ _)).trans (uniform t (m x) v)
    have st := histogram_step T (fun x => summary (m x)) (fun x b => summary (step t (m x) b.val))
      (transfer t) v localW
    rw [st]
    unfold count
    apply Finset.sum_congr rfl
    intro u _
    rw [ih]
    congr 1
    exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm

theorem finish [Fintype I] [Fintype B] [Fintype H] (init : I → M) (step : ℕ → M → B → M)
    (seed : I → Prop) (enable : ℕ → M → B → Prop) (summary : M → H)
    (transfer : ℕ → H → H → ℕ) (uniform : ∀ t m v,
      Nat.card {b : B // enable t m b ∧ summary (step t m b)=v} = transfer t (summary m) v)
    (n : ℕ) (done : H → Prop) :
    Nat.card {z : Hist I B n // allowed init step seed enable n z ∧ done (summary (state init step n z))} =
      ∑ u, if done u then count (fun u => Nat.card {a : I // seed a ∧ summary (init a)=u}) transfer n u else 0 := by
  classical
  let Z := {z : Hist I B n // allowed init step seed enable n z}
  let key (z : Z) := summary (state init step n z.val)
  let T := {z : Z // done (key z)}
  let split (z : T) := key z.val
  calc
    _ = Nat.card T := Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
    _ = Nat.card (Σ u : H, {z : T // split z=u}) := Nat.card_congr (Equiv.sigmaFiberEquiv split).symm
    _ = _ := by
      rw [Nat.card_sigma]
      apply Finset.sum_congr rfl
      intro u _
      by_cases ok : done u
      · rw [ite_eq_left ok,count_histories init step seed enable summary transfer uniform]
        let F : {z : T // split z=u} ≃
            {z : Hist I B n // allowed init step seed enable n z ∧ summary (state init step n z)=u} :=
          ⟨fun z => ⟨z.val.val.val,z.val.val.property,z.property⟩,
           fun z => ⟨⟨⟨z.val,z.property.1⟩,by change done (summary (state init step n z.val)); rw [z.property.2]; exact ok⟩,z.property.2⟩,
           fun _ => rfl,fun _ => rfl⟩
        exact Nat.card_congr F
      · rw [ite_eq_right ok]
        let : IsEmpty {z : T // split z=u} := ⟨fun z => ok (z.property ▸ z.val.property)⟩
        exact Nat.card_of_isEmpty

def pack : (n : ℕ) → I → (Fin n→B) → Hist I B n
  | 0, a, _ => a
  | n+1, a, col => (pack n a (Fin.init col),col (Fin.last n))

def unpack : (n : ℕ) → Hist I B n → I × (Fin n→B)
  | 0, a => (a,Fin.elim0)
  | n+1, z => ((unpack n z.1).1,Fin.snoc (unpack n z.1).2 z.2)

theorem pack_unpack (n : ℕ) (z : Hist I B n) :
    pack n (unpack n z).1 (unpack n z).2 = z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases z with ⟨z,b⟩
    simp [pack,unpack,ih]
    rfl

theorem unpack_pack (n : ℕ) (a : I) (col : Fin n→B) : unpack n (pack n a col) = (a,col) := by
  induction n with
  | zero => exact Prod.ext rfl (Subsingleton.elim _ _)
  | succ n ih => simp [pack,unpack,ih,Fin.snoc_init_self]

def columnEquiv (n : ℕ) : Hist I B n ≃ I×(Fin n→B) :=
  ⟨unpack n,fun z => pack n z.1 z.2,pack_unpack n,fun z => unpack_pack n z.1 z.2⟩

theorem trajectory (init : I→M) (step : ℕ→M→B→M) (seed : I→Prop)
    (enable : ℕ→M→B→Prop) (n : ℕ) (a : I) (cols : Fin n→B) (path : Fin (n+1)→M)
    (zero : init a = path 0)
    (succ : ∀ t : Fin n, step t.val (path t.castSucc) (cols t) = path t.succ) :
    state init step n (pack n a cols) = path (Fin.last n) ∧
      (allowed init step seed enable n (pack n a cols) ↔
        seed a ∧ ∀ t : Fin n, enable t.val (path t.castSucc) (cols t)) := by
  induction n with
  | zero => exact ⟨zero,by simp [pack,allowed]⟩
  | succ n ih =>
    let short := fun t : Fin (n+1) => path t.castSucc
    have prior := ih (Fin.init cols) short zero (fun t => succ t.castSucc)
    have endPath : state init step n (pack n a (Fin.init cols)) = path (Fin.last n).castSucc := prior.1
    refine ⟨?_,?_⟩
    · change step n (state init step n (pack n a (Fin.init cols))) (cols (Fin.last n)) = _
      rw [endPath]
      exact succ (Fin.last n)
    · change (allowed init step seed enable n (pack n a (Fin.init cols)) ∧
        enable n (state init step n (pack n a (Fin.init cols))) (cols (Fin.last n))) ↔ _
      rw [prior.2,endPath]
      constructor
      · rintro ⟨⟨hs,steps⟩,last⟩
        refine ⟨hs,fun t => ?_⟩
        exact Fin.lastCases last (fun t => steps t) t
      · rintro ⟨hs,all⟩
        exact ⟨⟨hs,fun t => all t.castSucc⟩,all (Fin.last n)⟩

end PEqualNP.Outside.L_meta_33676_aux.HistoryFold

namespace PEqualNP.Outside.L_meta_33676_aux.PanelCount

open Ranking (rowPinned distinguished cutoff fixedValue pinnedPanel distinguished_lt)
open Translation ShiftCriterion ShiftedReport StreamRows PinnedBoundary ActiveRows InitialDP
open scoped Classical

abbrev Live (q d : ℕ) := Starts q d × Starts q d
abbrev Bits (q : ℕ) := Fin (q+1) → Bool

def seed {q d : ℕ} (u : Starts q d) : Live q d := (u,u)
def step {q d : ℕ} (_ : ℕ) (m : Live q d) (z : Bits q) : Live q d :=
  (m.1,fun a => nextState (m.2 a) (z a))
def slots {q d : ℕ} (m : Live q d) (a : Fin q) : ColumnTransfer.Slot d :=
  (m.1 a.castSucc,m.2 a.castSucc,m.1 a.succ)
def project {q d : ℕ} (m : Live q d) : Macro q d :=
  (m.1 0,m.2 (Fin.last q),histogram (slots m))

@[simp] theorem project_seed {q d : ℕ} (u : Starts q d) : project (seed u) = signature u := rfl

def seeds {p n d l : ℕ} (v : Dynamic p n d l) : Starts (distinguished p n l) d := fun a => stateAt (v a) 0
def cols {p n d l : ℕ} (v : Dynamic p n d l) (i : Fin n) : Bits (distinguished p n l) :=
  fun a => branch (v a) i
def path {p n d l : ℕ} (v : Dynamic p n d l) (t : Fin (n+1)) : Live (distinguished p n l) d :=
  (seeds v,fun a => stateAt (v a) t)

def historiesEquiv {p n d l : ℕ} :
    Dynamic p n d l ≃ HistoryFold.Hist (Starts (distinguished p n l) d) (Bits (distinguished p n l)) n :=
  let stream := Equiv.piCongrRight (fun _ : Fin (distinguished p n l+1) => traceEquivStream n d)
  let fields : (Fin (distinguished p n l+1) → Stream n d) ≃ Starts (distinguished p n l) d × (Fin n → Bits (distinguished p n l)) :=
    ⟨fun x => (fun a => (x a).1,fun t a => (x a).2 t),fun z a => (z.1 a,fun t => z.2 t a),
     fun _ => rfl,fun _ => rfl⟩
  (stream.trans fields).trans (HistoryFold.columnEquiv n).symm

theorem historiesEquiv_apply {p n d l : ℕ} (v : Dynamic p n d l) :
    historiesEquiv v = HistoryFold.pack n (seeds v) (cols v) := rfl

def seedPins {d : ℕ} (p n l h : ℕ) (u : Starts (distinguished p n l) d) : Prop :=
  pinValid n l (distinguished p n l) (cutoff p n l) h (u (Fin.last _))

def colPin (p n d l h : ℕ) (i : Fin n) (z : Bool) : Prop :=
  i.val+d<n → cutoff p n l ≤ i.val+d → z=fixedValue n l h (distinguished p n l) (i.val+d)

abbrev Pass (q n d : ℕ) := Fin n → State d → Starts q d → Bits q → Prop

def enabled {p n d l : ℕ} (h : ℕ) (pass : Pass (distinguished p n l) n d)
    (t : ℕ) (m : Live (distinguished p n l) d) (z : Bits (distinguished p n l)) : Prop :=
  if lt : t<n then colPin p n d l h ⟨t,lt⟩ (z (Fin.last _)) ∧ pass ⟨t,lt⟩ (m.1 0) m.2 z else False

def panelPass {p n d l : ℕ} (pass : Pass (distinguished p n l) n d) (v : Dynamic p n d l) : Prop :=
  ∀ i : Fin n, pass i (seeds v 0) (fun a => stateAt (v a) i.castSucc) (cols v i)

theorem traces_allowed {p n d l : ℕ} (hd : d≤n) (h : ℕ) (pass : Pass (distinguished p n l) n d)
    (v : Dynamic p n d l) :
    HistoryFold.state seed step n (historiesEquiv v) = path v (Fin.last n) ∧
    (HistoryFold.allowed seed step (seedPins p n l h) (enabled h pass) n (historiesEquiv v) ↔
      localPins h v ∧ panelPass pass v) := by
  rw [historiesEquiv_apply]
  have st (i : Fin n) : step i.val (path v i.castSucc) (cols v i) = path v i.succ :=
    Prod.ext rfl (funext fun a => (state_step (v a) i).symm)
  have tr := HistoryFold.trajectory seed step (seedPins p n l h) (enabled h pass) n (seeds v) (cols v) (path v) rfl st
  refine ⟨tr.1,tr.2.trans ?_⟩
  let q := distinguished p n l
  let t := cutoff p n l
  let R (j : Fin n) := v (Fin.last q) ⟨j.val,by omega⟩
  let fixed := fixedValue n l h q
  have pinned := split_row_pins hd t R fixed
  change (seedPins p n l h (seeds v) ∧ ∀ i : Fin n, enabled h pass i.val (path v i.castSucc) (cols v i)) ↔
    (∀ j, t ≤ Fin.val j → R j=fixed j.val) ∧ _
  rw [pinned]
  have begin : seedPins p n l h (seeds v) ↔ ∀ j : Fin d, t ≤ j.val → R ⟨j.val,j.isLt.trans_le hd⟩=fixed j.val := by
    simp [seedPins,pinValid,seeds,stateAt,R,fixed,t,q]
  simp only [enabled,dite_eq_left (Fin.isLt _)]
  rw [begin]
  change (_ ∧ ∀ i : Fin n, (i.val+d<n → t ≤ i.val+d → _ = _) ∧ _) ↔ (_ ∧ _) ∧ _
  constructor
  · rintro ⟨hs,all⟩
    exact ⟨⟨hs,fun i hi he => (all i).1 hi he⟩,fun i => (all i).2⟩
  · rintro ⟨⟨hs,pin⟩,all⟩
    exact ⟨hs,fun i => ⟨fun hi he => pin i hi he,all i⟩⟩

def terminal (p n d l h : ℕ) (s : Macro (distinguished p n l) d) : Prop :=
  nextStart (p:=p) (n:=n) l h s.1 = s.2.1 ∧ ∀ c ∈ s.2.2.toMultiset, c.2.1=c.2.2

theorem path_terminal {p n d l : ℕ} (h : ℕ) (v : Dynamic p n d l) :
    terminal p n d l h (project (path v (Fin.last n))) ↔ freeSeam v ∧ lastSeam h v := by
  let m := path v (Fin.last n)
  have mem (c : ColumnTransfer.Slot d) : c ∈ (histogram (slots m)).toMultiset ↔ ∃ a, slots m a=c := by
    simp [histogram,List.mem_ofFn]
  constructor
  · rintro ⟨hc,hs⟩
    exact ⟨fun a => hs (slots m a) ((mem _).mpr ⟨a,rfl⟩),hc.symm⟩
  · rintro ⟨hs,hc⟩
    exact ⟨hc.symm,fun c h => by rcases (mem _).mp h with ⟨a,rfl⟩; exact hs a⟩

theorem pinned_count {p n d l : ℕ} (hp : 0<p) (hn : 0<n) (hd : d≤n) (h : ℕ)
    (pass : Pass (distinguished p n l) n d)
    (K : ℕ → Macro (distinguished p n l) d → Macro (distinguished p n l) d → ℕ)
    (localK : ∀ t m v, Nat.card {z : Bits (distinguished p n l) //
      enabled h pass t m z ∧ project (step t m z)=v} = K t (project m) v) :
    Nat.card {R : pinnedPanel p n l h // panelPass pass (extract hp hd R.val)} =
      ∑ v, if terminal p n d l h v then HistoryFold.count (initValue p n d l h) K n v else 0 := by
  classical
  let A (v : Dynamic p n d l) := localPins h v ∧ freeSeam v ∧ lastSeam h v
  let e := pinnedEquivActive hp hn hd l h
  let E : {R : pinnedPanel p n l h // panelPass pass (extract hp hd R.val)} ≃
      {v : Dynamic p n d l // A v ∧ panelPass pass v} :=
    (e.subtypeEquiv (p:=fun R => panelPass pass (extract hp hd R.val)) (q:=fun v => panelPass pass v.val)
      (fun _ => Iff.rfl)).trans (Equiv.subtypeSubtypeEquivSubtypeInter _ _)
  let C := HistoryFold.Hist (Starts (distinguished p n l) d) (Bits (distinguished p n l)) n
  let enable := enabled h pass
  let ok (z : C) := HistoryFold.allowed seed step (seedPins p n l h) enable n z ∧
    terminal p n d l h (project (HistoryFold.state seed step n z))
  have test (v : Dynamic p n d l) : (A v ∧ panelPass pass v) ↔ ok (historiesEquiv v) := by
    obtain ⟨hs,hc⟩ := traces_allowed hd h pass v
    change _ ↔ HistoryFold.allowed seed step (seedPins p n l h) (enabled h pass) n (historiesEquiv v) ∧ _
    rw [hc]
    rw [hs,path_terminal]
    unfold A
    tauto
  rw [Nat.card_congr (E.trans (historiesEquiv.subtypeEquiv test))]
  have final := HistoryFold.finish seed step (seedPins p n l h) enable project K localK n (terminal p n d l h)
  have ini : (fun u => Nat.card {a : Starts (distinguished p n l) d // seedPins p n l h a ∧ project (seed a)=u}) =
      initValue p n d l h := by
    funext u
    rw [initValue_spec]
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun _ => and_comm
  rw [ini] at final
  exact final

def reading {d : ℕ} (curr : State d) (z : Bool) : Vector (d+1) :=
  fun j => scalar (@Fin.snoc d (fun _ => Bool) curr z j)

theorem read_panel {p n d l : ℕ} (hp : 0<p) (hd : d<n) (R : Panel p n)
    (a : Fin (distinguished p n l+1)) (i : Fin n) :
    reading (stateAt (extract hp hd.le R a) i.castSucc) (branch (extract hp hd.le R a) i) =
      panelWindow hp hd R i (index hp a) := by
  rw [panelWindow_trace]
  funext j
  refine Fin.lastCases ?_ (fun b => ?_) j
  · simp [reading,extract,window_last]
  · simp [reading,extract,window_front]

def reportPass (p n d l h : ℕ) (F : Fin n → Vector (d+1) → F₂)
    (offset : Fin n → F₂) (y : Fin n → Bool) : Pass (distinguished p n l) n d :=
  fun i U cur z =>
    (∑ a : Fin (distinguished p n l), F i (reading (cur a.castSucc) (z a.castSucc))) +
      F i (reading (cur (Fin.last _)) (z (Fin.last _))) +
      (∑ a : Fin p, if distinguished p n l<a.val then F i (fixedWindow l h U a i) else 0) +
      offset i = scalar (y i)

theorem reportPass_spec {p n d l h : ℕ} (hp : 0<p) (hn : 0<n) (hd : d<n)
    (F : Fin n → Vector (d+1) → F₂) (offset : Fin n → F₂) (y : Fin n → Bool)
    (R : pinnedPanel p n l h) :
    panelPass (reportPass p n d l h F offset y) (extract hp hd.le R.val) ↔
      ∀ i, (∑ a, F i (panelWindow hp hd R.val i a)) + offset i = scalar (y i) := by
  unfold panelPass
  apply forall_congr'
  intro i
  dsimp only [reportPass,cols]
  simp only [read_panel (l:=l) hp hd R.val]
  rw [column_parity hp hn hd l h R i (F i)]
  have first : seeds (extract (l:=l) hp hd.le R.val) 0 = starts hd.le R.val ⟨0,hp⟩ :=
    directStart (l:=l) hp hd.le R.val 0
  rw [first]
  rfl

theorem ranked_slice {p n d l h : ℕ} (hp : 0<p) (hn : 0<n) (hd : d<n)
    (H : ℕ → Fin n → Bool) (g : Word (p*n)) (F : Fin n → Vector (d+1) → F₂)
    (spec : ∀ (w : Word (p*n)) i, scalar (H (w.val ^^^ g.val) i) =
      (∑ a, F i (windowMap hp hn i a (encode w))) + scalar (H g.val i))
    (y : Fin n → Bool) (hpref : h<2^(p*n-l))
    (K : ℕ → Macro (distinguished p n l) d → Macro (distinguished p n l) d → ℕ)
    (localK : ∀ t m v, Nat.card {z : Bits (distinguished p n l) //
      enabled h (reportPass p n d l h F (fun i=>scalar (H g.val i)) y) t m z ∧ project (step t m z)=v}
      = K t (project m) v) :
    (Ranking.slice (fun w : Word (p*n) => ∀ i, H (w.val ^^^ g.val) i = y i) l h).card =
      ∑ v, if terminal p n d l h v then HistoryFold.count (initValue p n d l h) K n v else 0 := by
  classical
  let off := fun i => scalar (H g.val i)
  let pass := reportPass p n d l h F off y
  rw [← pinned_count hp hn hd.le h pass K localK,shifted_slice_panel hp hn hd H g F spec y l h]
  let P (R : Panel p n) := ∀ i, (∑ a, F i (panelWindow hp hd R i a)) + off i = scalar (y i)
  let E : {R : Panel p n // h<2^(p*n-l) ∧
      (∀ a j, rowPinned n l a.val j.val → R a j = fixedValue n l h a.val j.val) ∧ P R} ≃
      {R : pinnedPanel p n l h // P R.val} :=
    ⟨fun R => ⟨⟨R.val,R.property.2.1⟩,R.property.2.2⟩,
     fun R => ⟨R.val.val,hpref,R.val.property,R.property⟩,fun _ => rfl,fun _ => rfl⟩
  exact Nat.card_congr (E.trans (Equiv.subtypeEquivRight (fun R => (reportPass_spec hp hn hd F off y R).symm)))

end PEqualNP.Outside.L_meta_33676_aux.PanelCount

namespace PEqualNP.Outside.L_meta_33676_aux.DistinguishedCount

open StreamRows InitialDP BranchDP WeightedCircuit
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit Builder
open scoped Classical

theorem advance_labeled {s q d : ℕ} {X : Type} [Fintype X] (x : Env s)
    (pin : Bool → BitFn s) (residual : State (d+1) → BitFn s) (table : State (d+1) → Bool → BitFn s)
    (prev : Macro q (d+1) → Bool → Env s → ℕ) (old : X → Macro q (d+1)) (par : X → Bool)
    (weights : ∀ v b, prev v b x = Nat.card {e : X // old e=v ∧ par e=b})
    (v : Macro q (d+1)) :
    advance pin residual table prev v x =
      Nat.card {w : X × Bool //
        ((old w.1).1,nextState (old w.1).2.1 w.2,(old w.1).2.2)=v ∧
          control pin (residual (old w.1).1) (table (old w.1).2.1) w.2 (par w.1) x = true} := by
  classical
  let W := {w : X × Bool //
      ((old w.1).1,nextState (old w.1).2.1 w.2,(old w.1).2.2)=v ∧
        control pin (residual (old w.1).1) (table (old w.1).2.1) w.2 (par w.1) x = true}
  let B := {b : State (d+1) × Bool // nextState b.1 b.2=v.2.1}
  let key (w : W) : B × Bool :=
    (⟨((old w.val.1).2.1,w.val.2),congrArg (fun z : Macro q (d+1) => z.2.1) w.property.1⟩,par w.val.1)
  have fiber (t : B) (b : Bool) :
      Nat.card {w : W // key w=(t,b)} =
        if control pin (residual v.1) (table t.val.1) t.val.2 b x then prev (v.1,t.val.1,v.2.2) b x else 0 := by
    by_cases enabled : control pin (residual v.1) (table t.val.1) t.val.2 b x = true
    · rw [ite_eq_left enabled,weights]
      let E : {w : W // key w=(t,b)} ≃ {e : X // old e=(v.1,t.val.1,v.2.2) ∧ par e=b} :=
        { toFun := fun w => ⟨w.val.val.1,by
            have hu := congrArg (fun r : Macro q (d+1) => r.1) w.val.property.1
            have hh := congrArg (fun r : Macro q (d+1) => r.2.2) w.val.property.1
            have ho := congrArg (fun r : B×Bool => r.1.val.1) w.property
            exact ⟨Prod.ext hu (Prod.ext ho hh),congrArg Prod.snd w.property⟩⟩
          invFun := fun e => ⟨⟨(e.val,t.val.2),by
              rw [e.property.1,e.property.2]
              exact ⟨Prod.ext rfl (Prod.ext t.property rfl),enabled⟩⟩,by
                apply Prod.ext _ e.property.2
                apply Subtype.ext
                exact Prod.ext (congrArg (fun r : Macro q (d+1) => r.2.1) e.property.1) rfl⟩
          left_inv := fun w => Subtype.ext (Subtype.ext (Prod.ext rfl
            (congrArg (fun r : B×Bool => r.1.val.2) w.property).symm))
          right_inv := fun _ => rfl }
      exact Nat.card_congr E
    · rw [ite_eq_right enabled]
      let : IsEmpty {w : W // key w=(t,b)} := ⟨fun w => by
        have hu := congrArg (fun r : Macro q (d+1) => r.1) w.val.property.1
        change (old w.val.val.1).1 = v.1 at hu
        have ho : (old w.val.val.1).2.1 = t.val.1 := congrArg (fun r : B×Bool => r.1.val.1) w.property
        have hz : w.val.val.2 = t.val.2 := congrArg (fun r : B×Bool => r.1.val.2) w.property
        have hp : par w.val.val.1=b := congrArg Prod.snd w.property
        exact enabled (by simpa only [←hu,←ho,←hz,←hp] using w.val.property.2)⟩
      exact Nat.card_of_isEmpty
  rw [advance_spec]
  have h := Nat.card_congr (Equiv.sigmaFiberEquiv key).symm
  rw [Nat.card_sigma,Fintype.sum_prod_type] at h
  simp_rw [fiber] at h
  exact h.symm

theorem advance_sum {s q d : ℕ} {S : Type} [Fintype S] (x : Env s)
    (pin : Bool → BitFn s) (residual : State (d+1) → BitFn s) (table : State (d+1) → Bool → BitFn s)
    (prev : Macro q (d+1) → Bool → Env s → ℕ) (wt : S→ℕ)
    (parts : S → Macro q (d+1) → Bool → Env s → ℕ)
    (lin : ∀ v b, prev v b x = ∑ u, wt u * parts u v b x) (v : Macro q (d+1)) :
    advance pin residual table prev v x = ∑ u, wt u * advance pin residual table (parts u) v x := by
  classical
  unfold advance
  simp_rw [lin,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp_all

def joined (q : ℕ) : (Fin q → Bool) × Bool ≃ PanelCount.Bits q :=
  (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => Bool))

@[simp] theorem joined_cast {q : ℕ} (v : (Fin q → Bool) × Bool) (a : Fin q) :
    joined q v a.castSucc = v.1 a := by simp [joined]

@[simp] theorem joined_last {q : ℕ} (v : (Fin q → Bool) × Bool) :
    joined q v (Fin.last q) = v.2 := by simp [joined]

def mid {q d : ℕ} (m : PanelCount.Live q d) (z : Fin q→Bool) : Macro q d :=
  (m.1 0,m.2 (Fin.last q),histogram (fun j => (m.1 j.castSucc,nextState (m.2 j.castSucc) (z j),m.1 j.succ)))

def freePar {q d s : ℕ} (table : State d → Bool → BitFn s) (m : PanelCount.Live q d) (z : Fin q→Bool) (x : Env s) : Bool :=
  ((∑ j,(table (m.2 j.castSucc) (z j) x).toNat).testBit 0)

theorem joined_step {q d : ℕ} (t : ℕ) (m : PanelCount.Live q d) (w : (Fin q→Bool)×Bool) :
    PanelCount.project (PanelCount.step t m (joined q w)) =
      ((mid m w.1).1,nextState (mid m w.1).2.1 w.2,(mid m w.1).2.2) := by
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · change nextState (m.2 (Fin.last q)) (joined q w (Fin.last q)) = _
    rw [joined_last]
    rfl
  · apply congrArg histogram
    funext a
    change (m.1 a.castSucc,nextState (m.2 a.castSucc) (joined q w a.castSucc),m.1 a.succ)=_
    rw [joined_cast]

theorem join_afterFree {s q d : ℕ} (x : Env s) (t : ℕ) (m : PanelCount.Live q (d+1))
    (pin : Bool → BitFn s) (residual : State (d+1) → BitFn s) (table : State (d+1) → Bool → BitFn s)
    (prev : Macro q (d+1) → Bool → Env s → ℕ)
    (weights : ∀ v b, prev v b x = Nat.card {z : Fin q→Bool // mid m z=v ∧ freePar table m z x=b})
    (allowed : PanelCount.Bits q → Prop)
    (works : ∀ w : (Fin q→Bool)×Bool, allowed (joined q w) ↔
      control pin (residual (m.1 0)) (table (m.2 (Fin.last q))) w.2 (freePar table m w.1 x) x = true)
    (v : Macro q (d+1)) :
    advance pin residual table prev v x =
      Nat.card {z : PanelCount.Bits q // allowed z ∧ PanelCount.project (PanelCount.step t m z)=v} := by
  rw [advance_labeled x pin residual table prev (mid m) (fun z => freePar table m z x) weights]
  apply Nat.card_congr
  apply (joined q).subtypeEquiv
  intro w
  rw [works,joined_step]
  exact and_comm

end PEqualNP.Outside.L_meta_33676_aux.DistinguishedCount

namespace PEqualNP.Outside.L_meta_33676_aux.SparseCell

open Transfer
open scoped Classical

variable {A S K : Type*}

def countsMatch (n q : Bool → ℕ) (r₀ r₁ : ℕ) : Prop :=
  q false ≤ n false ∧ q true ≤ n true ∧
  (n false - q false) + (n true - q true) = r₀ ∧ q false + q true = r₁

def flipFlag (n q : Bool → ℕ) (f : Bool → Bool → Bool) (flag : Bool) : Bool :=
  xor flag ((onesIn (f false) (n false) (q false) + onesIn (f true) (n true) (q true)).testBit 0)

abbrev Choices (n : Bool → ℕ) := Bool → Fin (n false + n true + 1)

def coefficient (n q : Bool → ℕ) : ℕ := (n false).choose (q false) * (n true).choose (q true)

theorem pairWeight_expand (n : Bool → ℕ) (f : Bool → Bool → Bool) (flag next : Bool) (u v : ℕ) :
    pairWeight n f flag (u,v,next) = ∑ q : Choices n,
      if countsMatch n (fun i => (q i).val) u v ∧ flipFlag n (fun i => (q i).val) f flag = next
      then coefficient n (fun i => (q i).val) else 0 := by
  classical
  unfold pairWeight
  apply Finset.sum_congr rfl
  intro q _
  by_cases h₀ : (q false).val ≤ n false
  · by_cases h₁ : (q true).val ≤ n true
    · simp [cellResult,countsMatch,flipFlag,coefficient,h₀,h₁,and_assoc]
    · have z := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h₁)
      simp [countsMatch,h₁,z]
  · have z := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h₀)
    simp [countsMatch,h₀,z]

def feasible (key : S → K) (view : S → histogramState A) (c : A) (v s : S)
    (q : Choices ((view s).1 c)) : Prop :=
  key s = key v ∧ (∀ a, a≠c → (view s).1 a = (view v).1 a) ∧
    countsMatch ((view s).1 c) (fun b => (q b).val) ((view v).1 c false) ((view v).1 c true)

abbrev edge (key : S → K) (view : S → histogramState A) (c : A) (v : S) :=
  {e : Σ s, Choices ((view s).1 c) // feasible key view c v e.1 e.2}

def edgeKey (key : S → K) (view : S → histogramState A) (c : A) (v : S) (p : ℕ)
    (bound : ∀ s, (view s).1 c false + (view s).1 c true ≤ p) (e : edge key view c v) :
    Fin (p+1) × Fin (p+1) × Bool :=
  (⟨(view e.val.1).1 c false,by have := bound e.val.1; omega⟩,
   ⟨(e.val.2 false).val,by have := (e.val.2 false).isLt; have := bound e.val.1; omega⟩,
   (view e.val.1).2)

theorem edgeKey_injective (key : S → K) (view : S → histogramState A)
    (inj : Function.Injective (fun s => (key s,view s))) (c : A) (v : S) (p : ℕ)
    (bound : ∀ s, (view s).1 c false + (view s).1 c true ≤ p) :
    Function.Injective (edgeKey key view c v p bound) := by
  rintro ⟨⟨s,q⟩,h⟩ ⟨⟨t,r⟩,g⟩ eq
  obtain ⟨hk,hs,h₀,h₁,hz,ho⟩ := h
  obtain ⟨gk,gs,g₀,g₁,gz,go⟩ := g
  have n₀ : (view s).1 c false = (view t).1 c false :=
    congrArg (fun x : Fin (p+1) × Fin (p+1) × Bool => x.1.val) eq
  have q₀ : (q false).val = (r false).val :=
    congrArg (fun x : Fin (p+1) × Fin (p+1) × Bool => x.2.1.val) eq
  have fl : (view s).2 = (view t).2 := congrArg (fun x : Fin (p+1) × Fin (p+1) × Bool => x.2.2) eq
  change (q false).val + (q true).val = _ at ho
  change (r false).val + (r true).val = _ at go
  change ((view s).1 c false - (q false).val) + ((view s).1 c true - (q true).val) = _ at hz
  change ((view t).1 c false - (r false).val) + ((view t).1 c true - (r true).val) = _ at gz
  change (q true).val ≤ (view s).1 c true at h₁
  change (r true).val ≤ (view t).1 c true at g₁
  have q₁ : (q true).val = (r true).val := by omega
  have n₁ : (view s).1 c true = (view t).1 c true := by omega
  have st : s = t := by
    apply inj
    refine Prod.ext (hk.trans gk.symm) (Prod.ext ?_ fl)
    funext a b
    by_cases ha : a=c
    · subst a
      cases b <;> assumption
    · exact congrFun ((hs a ha).trans (gs a ha).symm) b
  subst t
  have qr : q=r := by funext b; apply Fin.ext; cases b <;> assumption
  cases qr
  rfl

theorem sparse_bound [Finite S] (key : S → K) (view : S → histogramState A)
    (inj : Function.Injective (fun s => (key s,view s))) (c : A) (v : S) (p : ℕ)
    (bound : ∀ s, (view s).1 c false + (view s).1 c true ≤ p) :
    Nat.card (edge key view c v) ≤ 2*(p+1)^2 := by
  calc
    _ ≤ Nat.card (Fin (p+1) × Fin (p+1) × Bool) := Nat.card_le_card_of_injective _
      (edgeKey_injective key view inj c v p bound)
    _ = _ := by simp [Nat.card_eq_fintype_card]; ring

theorem sub_sum {E : Type*} [Fintype E] (ok : E → Prop) (F : E → ℕ) :
    (∑ e, if ok e then F e else 0) = ∑ e : Subtype ok, F e.val := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_subtype
  simp

def edgeWeight (key : S → K) (view : S → histogramState A) (c : A) (v : S)
    (e : edge key view c v) : ℕ :=
  coefficient ((view e.val.1).1 c) (fun b => (e.val.2 b).val)

def edgeActive (key : S → K) (view : S → histogramState A) (c : A) (v : S)
    (e : edge key view c v) (f : Bool → Bool → Bool) : Prop :=
  flipFlag ((view e.val.1).1 c) (fun b => (e.val.2 b).val) f (view e.val.1).2 = (view v).2

set_option maxHeartbeats 1100000 in

theorem sparse_sum [Fintype S] (key : S → K) (view : S → histogramState A) (c : A) (v : S)
    (f : Bool → Bool → Bool) (prev : S → ℕ) :
    (∑ s : S, if key s = key v then cellWeight c (view s) (view v) f * prev s else 0) =
      ∑ e : edge key view c v, if edgeActive key view c v e f then
        edgeWeight key view c v e * prev e.val.1 else 0 := by
  classical
  let X := Σ s, Choices ((view s).1 c)
  let ok (e : X) := feasible key view c v e.1 e.2
  let F (e : X) := if flipFlag ((view e.1).1 c) (fun b => (e.2 b).val) f (view e.1).2 = (view v).2 then
    coefficient ((view e.1).1 c) (fun b => (e.2 b).val) * prev e.1 else 0
  have per (s : S) :
      (if key s = key v then cellWeight c (view s) (view v) f * prev s else 0) =
        ∑ q : Choices ((view s).1 c), if ok ⟨s,q⟩ then F ⟨s,q⟩ else 0 := by
    by_cases hk : key s = key v
    · by_cases ha : ∀ a, a≠c → (view s).1 a = (view v).1 a
      · simp only [hk,ite_true,cellWeight,ite_eq_left ha]
        rw [pairWeight_expand,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro q _
        have hOk : ok ⟨s,q⟩ ↔ countsMatch ((view s).1 c) (fun b => (q b).val) ((view v).1 c false) ((view v).1 c true) :=
          ⟨fun h => h.2.2,fun h => ⟨hk,ha,h⟩⟩
        by_cases hq : countsMatch ((view s).1 c) (fun b => (q b).val) ((view v).1 c false) ((view v).1 c true)
        <;> by_cases hf : flipFlag ((view s).1 c) (fun b => (q b).val) f (view s).2 = (view v).2
        <;> simp [hOk,hq,hf,F]
      · simp [hk,ha,cellWeight,ok,feasible]
    · simp [hk,ok,feasible]
  calc
    _ = ∑ s, ∑ q : Choices ((view s).1 c), if ok ⟨s,q⟩ then F ⟨s,q⟩ else 0 :=
      Finset.sum_congr rfl (fun s _ => per s)
    _ = ∑ e : X, if ok e then F e else 0 := (Fintype.sum_sigma (fun e : X => if ok e then F e else 0)).symm
    _ = ∑ e : Subtype ok, F e.val := sub_sum ok F
    _ = _ := by
      apply Finset.sum_congr (by ext; simp)
      intro e _
      by_cases hf : edgeActive key view c v e f <;>
        simp [edgeActive] at hf <;> simp [F,edgeActive,edgeWeight,hf]

theorem edgeWeight_bound (key : S → K) (view : S → histogramState A) (c : A) (v : S) (p : ℕ)
    (bound : ∀ s, (view s).1 c false + (view s).1 c true ≤ p) (e : edge key view c v) :
    edgeWeight key view c v e < 2^(p+1) := by
  let n := (view e.val.1).1 c
  calc
    _ ≤ 2^(n false) * 2^(n true) :=
      Nat.mul_le_mul (Nat.choose_le_two_pow _ _) (Nat.choose_le_two_pow _ _)
    _ = 2^(n false+n true) := (pow_add _ _ _).symm
    _ ≤ 2^p := Nat.pow_le_pow_right (by decide) (bound e.val.1)
    _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)

noncomputable def lookup {E O : Type*} (embed : E → O) : O → Option E :=
  Function.extend embed some (fun _ => none)

theorem sum_lookup {E O : Type*} [Fintype E] [Fintype O] (embed : E → O)
    (inj : Function.Injective embed) (F : E → ℕ) :
    (∑ t : O, (lookup embed t).elim 0 F) = ∑ e, F e := by
  classical
  have entry (t : O) : (lookup embed t).elim 0 F = Function.extend embed F 0 t := by
    by_cases h : ∃ x, embed x=t
    · obtain ⟨a,rfl⟩ := h
      simp [lookup,inj.extend_apply]
    · simp [lookup,Function.extend,h]
  simp_rw [entry]
  exact Finset.sum_extend_zero_of_injective F inj (fun _ => Finset.mem_univ _)

abbrev origin (p : ℕ) := Fin (p+1) × Fin (p+1) × Bool

def fetch (v : S) {E : Type*} (source : E → S) (slot : Option E) := slot.elim v source

theorem uniform_sparse_sum [Fintype S] (key : S → K) (view : S → histogramState A)
    (inj : Function.Injective (fun s => (key s,view s))) (c : A) (v : S) (p : ℕ)
    (bound : ∀ s, (view s).1 c false + (view s).1 c true ≤ p)
    (f : Bool → Bool → Bool) (prev : S → ℕ) :
    let slot := lookup (edgeKey key view c v p bound)
    (∑ s, if key s = key v then cellWeight c (view s) (view v) f * prev s else 0) =
      ∑ t : origin p, if (slot t).elim False (fun e => edgeActive key view c v e f) then
        (slot t).elim 0 (edgeWeight key view c v) * prev (fetch v (fun e => e.val.1) (slot t))
        else 0 := by
  classical
  dsimp only
  rw [sparse_sum]
  let E := edge key view c v
  let code := edgeKey key view c v p bound
  let term (e : E) := if edgeActive key view c v e f then edgeWeight key view c v e * prev e.val.1 else 0
  rw [← sum_lookup code (edgeKey_injective key view inj c v p bound) term]
  apply Finset.sum_congr rfl
  intro t _
  change (lookup code t).elim 0 term = if (lookup code t).elim False _ then _ else _
  cases he : lookup code t with
  | none => simp
  | some e =>
    by_cases ha : edgeActive key view c v e f <;> simp [fetch,term,ha]

end PEqualNP.Outside.L_meta_33676_aux.SparseCell

namespace PEqualNP.Outside.L_meta_33676_aux.ColumnCircuit

open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit.Builder
open WeightedCircuit Transfer SparseCell
open scoped Classical

private def lutCost : Nat → Nat
  | 0 => 0
  | n+1 => lutCost n + lutCost n + 4

private theorem lut {s : Nat} (n : Nat) (B : Bank s)
    (cz : B.Has (fun _ => false)) (co : B.Has (fun _ => true))
    (sig : Fin n → BitFn s) (hs : ∀ i,B.Has (sig i))
    (F : (Fin n → Bool) → Bool) :
    B.Grow (lutCost n) (fun E => E.Has (fun x => F (fun i => sig i x))) := by
  induction n generalizing B with
  | zero =>
    have h : ∀ x : Env s, (fun i => sig i x) = Fin.elim0 := fun _ => funext (fun i => i.elim0)
    cases e : F Fin.elim0
    · exact Bank.Grow.pure B (by simpa only [h,e] using cz)
    · exact Bank.Grow.pure B (by simpa only [h,e] using co)
  | succ n ih =>
    obtain ⟨C,eC,lC,ht⟩ := ih B cz co (fun i => sig i.succ) (fun i => hs i.succ)
      (fun v => F (Fin.cons true v))
    obtain ⟨D,eD,lD,hf⟩ := ih C (eC cz) (eC co) (fun i => sig i.succ) (fun i => eC (hs i.succ))
      (fun v => F (Fin.cons false v))
    obtain ⟨E,eE,lE,out⟩ := Bank.mux (eD (eC (hs 0))) (eD ht) hf
    refine ⟨E,Bank.ext_trans eC (Bank.ext_trans eD eE),by simp only [lutCost]; omega,?_⟩
    convert out using 1
    funext x
    have eq : (fun i => sig i x) = Fin.cons (sig 0 x) (fun i => sig i.succ x) := by
      funext i
      refine Fin.cases rfl (fun j => rfl) i
    rw [eq]
    cases (sig 0 x) <;> rfl

theorem tableTest {s : Nat} (B : Bank s)
    (cz : B.Has (fun _ => false)) (co : B.Has (fun _ => true))
    (f : Env s → Bool → Bool → Bool) (wires : ∀ b z, B.Has (fun x => f x b z))
    (F : (Bool → Bool → Bool) → Bool) :
    B.Grow 60 (fun E => E.Has (fun x => F (f x))) := by
  let e : (Bool × Bool) ≃ Fin 4 := Fintype.equivFinOfCardEq (by decide)
  let sig (i : Fin 4) (x : Env s) := f x (e.symm i).1 (e.symm i).2
  have H := lut 4 B cz co sig (fun i => wires _ _) (fun bits => F (fun b z => bits (e (b,z))))
  simpa [sig, lutCost] using H

variable {S K A : Type} [Fintype S] [DecidableEq A]

noncomputable def dense {s : Nat} (key : S → K) (view : S → histogramState A)
    (cells : Nat → A) (tbl : Nat → S → Env s → Bool → Bool → Bool)
    (init : S → Env s → Nat) : Nat → S → Env s → Nat
  | 0 => init
  | t+1 => fun v x => ∑ u, if key u = key v then
      cellWeight (cells t) (view u) (view v) (tbl t v x) * dense key view cells tbl init t u x else 0

theorem compileCells {s w : Nat} (p : Nat) (key : S → K) (view : S → histogramState A)
    (inj : Function.Injective (fun u => (key u,view u))) (cells : Nat → A)
    (bounded : ∀ t u, (view u).1 (cells t) false + (view u).1 (cells t) true ≤ p)
    (tbl : Nat → S → Env s → Bool → Bool → Bool) (T : Nat) (B : Bank s)
    (zero : B.Has (fun _ => false)) (one : B.Has (fun _ => true))
    (wires : ∀ t<T, ∀ v b z,B.Has (fun x => tbl t v x b z))
    (init : S → Env s → Nat) (initial : ∀ v, HasWord B w (init v)) :
    B.Grow (T*(Fintype.card S*(2*(p+1)^2)*(60+(p+1)*(w*13)+w*4+w*13)))
      (fun E => ∀ v, HasWord E w (dense key view cells tbl init T v)) := by
  classical
  let slot t v := lookup (edgeKey key view (cells t) v p (bounded t))
  let src t v a := fetch v (fun e => e.val.1) (slot t v a)
  let wt t v a := (slot t v a).elim 0 (edgeWeight key view (cells t) v)
  let on t v a (x : Env s) := decide ((slot t v a).elim False
    (fun e => edgeActive key view (cells t) v e (tbl t v x)))
  have eq (t : Nat) : dense key view cells tbl init t = layers init src wt on t := by
    induction t with
    | zero => rfl
    | succ t ih =>
      funext v x
      simp only [dense, layers, layer]
      rw [ih]
      simpa only [on, decide_eq_true_eq] using uniform_sparse_sum key view inj (cells t) v p
        (bounded t) (tbl t v x) (fun u => layers init src wt on t u x)
  have hw (t : Nat) (v : S) (a : origin p) : wt t v a < 2^(p+1) := by
    unfold wt
    cases slot t v a with
    | none => exact Nat.two_pow_pos _
    | some e => exact edgeWeight_bound key view (cells t) v p (bounded t) e
  have he (t : Nat) (ht : t<T) (E : Bank s) (eE : B.Ext E) (v : S) (a : origin p) :
      E.Grow 60 (fun F => F.Has (on t v a)) :=
    tableTest E (eE zero) (eE one) (tbl t v) (fun b z => eE (wires t ht v b z))
      (fun f => decide ((slot t v a).elim False (fun e => edgeActive key view (cells t) v e f)))
  rw [eq]
  have hcard : Fintype.card (origin p) = 2*(p+1)^2 := by
    simp [origin,pow_two]; ring
  simpa only [hcard] using compileLayers B zero one init initial src wt on T (fun j _ => hw j) he

end PEqualNP.Outside.L_meta_33676_aux.ColumnCircuit

namespace PEqualNP.Outside.L_meta_33676_aux.ColumnHistory

open Transfer ColumnCircuit WeightedCircuit
open scoped Classical

variable {N : Nat} {H : Type} (I : H → Fin N → Type) [∀ h j,Fintype (I h j)]
  (old : ∀ h,cellBank (I h))

abbrev Partial (t : Nat) (h : H) := { z : cellBank (I h) // ∀ j,t≤j.val → z j=old h j }
abbrev Hist (t : Nat) := Σ h,Partial I old t h

noncomputable def add {t : Nat} (ht : t<N) (h : H) (z : Partial I old t h)
    (b : I h ⟨t,ht⟩ → Bool) : Partial I old (t+1) h :=
  ⟨Function.update z.val ⟨t,ht⟩ b,fun j hj => by
    rw [Function.update_of_ne (show j ≠ ⟨t,ht⟩ from fun e => by simp [e] at hj)]
    exact z.property j (by omega)⟩

noncomputable def rollback {t : Nat} (ht : t<N) (h : H) (z : Partial I old (t+1) h) :
    Partial I old t h := ⟨Function.update z.val ⟨t,ht⟩ (old h ⟨t,ht⟩),fun j hj => by
  by_cases e : j=⟨t,ht⟩
  · subst j; simp
  · rw [Function.update_of_ne e]
    exact z.property j (by have : j.val ≠ t := fun eq => e (Fin.ext eq); omega)⟩

noncomputable def extendEquiv {t : Nat} (ht : t<N) :
    (Σ u : Hist I old t,I u.1 ⟨t,ht⟩ → Bool) ≃ Hist I old (t+1) where
  toFun := fun u => ⟨u.1.1,add I old ht u.1.1 u.1.2 u.2⟩
  invFun := fun u => ⟨⟨u.1,rollback I old ht u.1 u.2⟩,u.2.val ⟨t,ht⟩⟩
  left_inv := by
    rintro ⟨⟨h,z⟩,b⟩
    have eq : rollback I old ht h (add I old ht h z b) = z := by
      apply Subtype.ext
      change Function.update (Function.update z.val ⟨t,ht⟩ b) ⟨t,ht⟩ (old h ⟨t,ht⟩) = z.val
      rw [Function.update_idem,← z.property ⟨t,ht⟩ (by simp),Function.update_eq_self]
    have eb : (add I old ht h z b).val ⟨t,ht⟩ = b := Function.update_self ..
    change Sigma.mk (β:=fun u : Hist I old t => I u.1 ⟨t,ht⟩→Bool) (Sigma.mk h (rollback I old ht h (add I old ht h z b))) ((add I old ht h z b).val ⟨t,ht⟩) = _
    rw [eb]
    exact congrArg (fun r : Partial I old t h => Sigma.mk (β:=fun u : Hist I old t => I u.1 ⟨t,ht⟩→Bool) ⟨h,r⟩ b) eq
  right_inv := by
    rintro ⟨h,z⟩
    apply congrArg (fun r : Partial I old (t+1) h => Sigma.mk h r)
    apply Subtype.ext
    change Function.update (Function.update z.val ⟨t,ht⟩ _) ⟨t,ht⟩ (z.val ⟨t,ht⟩) = _
    rw [Function.update_idem,Function.update_eq_self]

variable (order : Nat→Fin N) (ordered : ∀ t (ht : t<N),(order t).val=t)
variable (f : ∀ h : H, Fin N → Bool → Bool → Bool) (start : H→Bool)

noncomputable def flag (t : Nat) (h : H) (z : cellBank (I h)) : Bool :=
  xor (start h) ((∑ i ∈ Finset.range t,
    ∑ a : I h (order i), (f h (order i) (old h (order i) a) (z (order i) a)).toNat).testBit 0)

private theorem bitAdd (a b : ℕ) : (a+b).testBit 0 = xor (a.testBit 0) (b.testBit 0) := by
  simp only [Nat.testBit_zero]
  by_cases ha : a % 2=1 <;> by_cases hb : b % 2=1 <;> simp [ha,hb] <;> omega

include ordered in
theorem flag_succ {t : Nat} (ht : t<N) (h : H) (z : Partial I old t h) (b : I h ⟨t,ht⟩→Bool) :
    flag I old order f start (t+1) h (add I old ht h z b).val =
      (measured (z.val ⟨t,ht⟩) b (f h ⟨t,ht⟩) (flag I old order f start t h z.val)).2.2 := by
  have idx : order t = ⟨t,ht⟩ := Fin.ext (ordered t ht)
  let Z := (add I old ht h z b).val
  have keep (i : Nat) (hi : i<t) : Z (order i)=z.val (order i) := by
    have ne : order i ≠ ⟨t,ht⟩ := fun e => by have v : (order i).val=t := congrArg Fin.val e; have v' := ordered i (hi.trans ht); omega
    exact Function.update_of_ne ne ..
  have sw : Z ⟨t,ht⟩=b := Function.update_self ..
  have same : (∑ i ∈ Finset.range t, ∑ a : I h (order i),
        (f h (order i) (old h (order i) a) (Z (order i) a)).toNat) =
      ∑ i ∈ Finset.range t, ∑ a : I h (order i),
        (f h (order i) (old h (order i) a) (z.val (order i) a)).toNat := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [keep i (Finset.mem_range.mp hi)]
  change xor _ ((∑ i ∈ Finset.range (t+1), ∑ a : I h (order i),
    (f h (order i) (old h (order i) a) (Z (order i) a)).toNat).testBit 0) = _
  rw [Finset.sum_range_succ,bitAdd,same,idx,sw]
  simp only [measured, flag,z.property ⟨t,ht⟩ (by simp), Bool.xor_assoc]

variable {K S : Type} [Fintype H] [Fintype S] (key : S→K) (view : S→histogramState (Fin N))
  (inj : Function.Injective (fun v => (key v,view v))) (key0 : H→K)
  (pack : (h:H) → cellBank (I h) → Bool → S)
  (hkey : ∀ h z flag0,key (pack h z flag0)=key0 h)
  (hview : ∀ h z flag0,view (pack h z flag0)=profile z flag0)

noncomputable def state (t : Nat) (u : Hist I old t) : S :=
  pack u.1 u.2.val (flag I old order f start t u.1 u.2.val)

noncomputable def tally (t : Nat) (v : S) : Nat :=
  Nat.card {u : Hist I old t // state I old order f start pack t u=v}

include inj hkey hview ordered in
theorem tally_step (g : K → Fin N → Bool → Bool → Bool)
    (tables : ∀ h, f h = g (key0 h)) {t : Nat} (ht : t<N) (v : S) :
    tally I old order f start pack (t+1) v =
    ∑ u, if key u=key v then cellWeight (order t) (view u) (view v) (g (key v) (order t)) *
      tally I old order f start pack t u else 0 := by
  classical
  let c : Fin N := ⟨t,ht⟩
  have idx : order t = c := Fin.ext (ordered t ht)
  let st := state I old order f start pack
  let e := extendEquiv I old ht
  let step (u : Hist I old t) (b : I u.1 c→Bool) := st (t+1) (e ⟨u,b⟩)
  let coeff (u v : S) := if key u=key v then cellWeight c (view u) (view v) (g (key v) c) else 0
  have per (u : Hist I old t) : Nat.card {b : I u.1 c→Bool // step u b=v} = coeff (st t u) v := by
    rcases u with ⟨h,z⟩
    let a := flag I old order f start t h z.val
    have k0 : key (st t ⟨h,z⟩)=key0 h := hkey _ _ _
    have outKey (b) : key (step ⟨h,z⟩ b)=key0 h := hkey _ _ _
    by_cases k : key0 h=key v
    · have act : f h c = g (key v) c := by rw [tables,k]
      have outView (b) : view (step ⟨h,z⟩ b) =
          profile (writeCell c z.val a (g (key v) c) b).1 (writeCell c z.val a (g (key v) c) b).2 := by
        dsimp [step,st,state,e,extendEquiv]
        rw [hview,flag_succ I old order ordered f start ht h z b,act]
        rfl
      have fibre (b) : step ⟨h,z⟩ b=v ↔ profile (writeCell c z.val a (g (key v) c) b).1
          (writeCell c z.val a (g (key v) c) b).2 = view v := by
        rw [←outView]
        exact ⟨congrArg view,fun hv => inj (Prod.ext ((outKey b).trans k) hv)⟩
      rw [Nat.card_congr (Equiv.subtypeEquivRight fibre),cellWeight_spec]
      simp only [coeff,k0,k,ite_true]
      rw [show view (st t ⟨h,z⟩) = profile z.val a from hview ..]
    · let : IsEmpty {b : I h c→Bool // step ⟨h,z⟩ b=v} :=
        ⟨fun b => k ((outKey b.val).symm.trans (congrArg key b.property))⟩
      simp [coeff,k0,k]
  let reorder := e.subtypeEquiv (p:=fun z => step z.1 z.2=v)
    (q:=fun u => st (t+1) u=v) (fun _ => Iff.rfl)
  change Nat.card {u : Hist I old (t+1) // st (t+1) u=v} = _
  rw [←Nat.card_congr reorder,histogram_step _ (st t) step coeff v per,idx]
  apply Finset.sum_congr rfl
  intro u _
  by_cases eq : key u=key v <;> simp [tally,st,coeff,eq,mul_comm]

noncomputable def emptyHist : H ≃ Hist I old 0 where
  toFun h := ⟨h,⟨old h,fun _ _ => rfl⟩⟩
  invFun := Sigma.fst
  left_inv _ := rfl
  right_inv := by
    rintro ⟨h,z⟩
    apply congrArg (fun r : Partial I old 0 h => Sigma.mk h r)
    exact Subtype.ext (funext fun j => (z.property j (Nat.zero_le _)).symm)

noncomputable def fullHist : (Σ h,cellBank (I h)) ≃ Hist I old N where
  toFun := fun ⟨h,z⟩ => ⟨h,⟨z,fun j hj => (Nat.not_le_of_gt j.isLt hj).elim⟩⟩
  invFun := fun u => ⟨u.1,u.2.val⟩
  left_inv _ := rfl
  right_inv _ := rfl

include ordered in
theorem flag_all (h : H) (z : cellBank (I h)) :
    flag I old order f start N h z =
      xor (start h) ((∑ j, ∑ a : I h j, (f h j (old h j a) (z j a)).toNat).testBit 0) := by
  unfold flag
  rw [← Fin.sum_univ_eq_sum_range]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [show order j.val = j from Fin.ext (ordered j.val j.isLt)]

include inj hkey hview ordered in
theorem dense_labeled {s : Nat} (x : Env s) (g : K → Fin N → Bool → Bool → Bool)
    (tables : ∀ h, f h = g (key0 h)) (tbl : Nat → S → Env s → Bool → Bool → Bool)
    (stable : ∀ t (ht : t<N) v,tbl t v x = g (key v) (order t))
    (init : S → Env s → Nat)
    (initial : ∀ v,init v x = Nat.card {h : H // pack h (old h) (start h)=v}) (v : S) :
    dense key view order tbl init N v x =
      Nat.card {u : Σ h,cellBank (I h) // pack u.1 u.2
        (xor (start u.1) ((∑ j,∑ a : I u.1 j, (f u.1 j (old u.1 j a) (u.2 j a)).toNat).testBit 0))=v} := by
  classical
  have all (t : Nat) (ht : t≤N) (u : S) : dense key view order tbl init t u x =
      tally I old order f start pack t u := by
    induction t generalizing u with
    | zero =>
      change init u x = _
      rw [initial]
      apply Nat.card_congr
      apply (emptyHist I old).subtypeEquiv
      intro h
      simp [emptyHist,state,flag]
    | succ t ih =>
      simp only [dense,stable t (by omega),tally_step I old order ordered f start key view inj key0 pack hkey hview g tables (by omega : t<N)]
      apply Finset.sum_congr rfl
      intro a _
      rw [ih (by omega)]
  rw [all N le_rfl v]
  symm
  apply Nat.card_congr
  apply (fullHist I old).subtypeEquiv
  rintro ⟨h,z⟩
  simp [fullHist,state,flag_all I old order ordered]

end PEqualNP.Outside.L_meta_33676_aux.ColumnHistory

namespace PEqualNP.Outside.L_meta_33676_aux.FreeColumn

open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit.Builder
open ColumnCircuit WeightedCircuit Transfer ColumnTransfer StreamRows
open scoped Classical

abbrev Reg (K P : Type) (q : Nat) := K × Sym P q × Bool
abbrev CellReg (K : Type) (q N : Nat) := Reg K (Fin N × Bool) q

def hist {P : Type} {q : Nat} (tags : Fin q→P) : Sym P q :=
  Sym.mk (List.ofFn tags : Multiset P) (by simp)

theorem countHist {P : Type} [DecidableEq P] {q : Nat} (f : Fin q→P) (c : P) :
    (hist f).toMultiset.count c = Nat.card {a : Fin q // f a=c} := by
  change (↑(List.ofFn f) : Multiset P).count c = _
  rw [Multiset.coe_count,List.count_ofFn,Nat.card_eq_fintype_card,Fintype.card_subtype]

theorem mapHist {P Q : Type} {q : Nat} (e : P≃Q) (f : Fin q→P) :
    Sym.equivCongr e (hist f) = hist (fun a => e (f a)) := by
  apply Sym.ext
  change Multiset.map e (↑(List.ofFn f) : Multiset P) = ↑(List.ofFn (fun a => e (f a)))
  simp [List.map_ofFn,Function.comp_def]

def view {K : Type} {q N : Nat} (s : CellReg K q N) : histogramState (Fin N) :=
  (fun j b => s.2.1.toMultiset.count (j,b),s.2.2)

theorem view_inj (K : Type) (q N : Nat) :
    Function.Injective (fun s : CellReg K q N => (s.1,view s)) := by
  rintro ⟨u,m,b⟩ ⟨v,n,c⟩ eq
  have hk : u=v := congrArg Prod.fst eq
  have hb : b=c := congrArg (fun e => e.2.2) eq
  have hm : m=n := by
    apply Sym.ext
    apply Multiset.ext.mpr
    rintro ⟨j,z⟩
    exact congrArg (fun e : K × histogramState (Fin N) => e.2.1 j z) eq
  simp [hk,hb,hm]

theorem countsBound {N : Nat} (s : Multiset (Fin N×Bool)) (j : Fin N) :
    s.count (j,false) + s.count (j,true) ≤ s.card := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rcases a with ⟨i,b⟩
    by_cases h : i=j <;> cases b <;> simp [Multiset.count_cons,h] at * <;> (try split_ifs) <;> omega

theorem view_bound {K : Type} {q N : Nat} (s : CellReg K q N) (j : Fin N) :
    (view s).1 j false + (view s).1 j true ≤ q :=
  (countsBound s.2.1.toMultiset j).trans (le_of_eq s.2.1.property)

def order (N : Nat) (h : 0<N) (t : Nat) : Fin N := ⟨t % N,Nat.mod_lt _ h⟩

noncomputable def regEquiv {K P Q : Type} (q : Nat) (e : P≃Q) : Reg K P q ≃ Reg K Q q :=
  Equiv.prodCongr (Equiv.refl K) (Equiv.prodCongr (Sym.equivCongr e) (Equiv.refl Bool))

variable {K P : Type} [Fintype K] [Fintype P] {q N s : Nat}

noncomputable def column (hN : 0<N) (before after : P ≃ Fin N×Bool)
    (table : K → Env s → Fin N → Bool → Bool → Bool)
    (init : Reg K P q → Env s → Nat) (v : Reg K P q) (x : Env s) : Nat :=
  let idx := order N hN
  dense Prod.fst view idx (fun t u y => table u.1 y (idx t))
    (fun u => init ((regEquiv q before).symm u)) N (regEquiv q after v) x

theorem compileColumn {w : Nat} (hN : 0<N) (before after : P ≃ Fin N×Bool)
    (table : K → Env s → Fin N → Bool → Bool → Bool) (init : Reg K P q → Env s → Nat)
    (B : Bank s) (zero : B.Has (fun _ => false)) (one : B.Has (fun _ => true))
    (wires : ∀ k j b z,B.Has (fun x => table k x j b z))
    (initial : ∀ u,HasWord B w (init u)) :
    B.Grow (N*(Fintype.card (Reg K P q)*(2*(q+1)^2)*(60+(q+1)*(w*13)+w*4+w*13)))
      (fun E => ∀ v,HasWord E w (column hN before after table init v)) := by
  let idx := order N hN
  have eq := Fintype.card_congr (regEquiv (K:=K) q before)
  rw [eq]
  apply (compileCells q Prod.fst view (view_inj K q N) idx (fun t u => view_bound u (idx t))
    (fun t u x => table u.1 x (idx t)) N B zero one (fun t _ u b z => wires _ _ _ _)
    (fun u => init ((regEquiv q before).symm u)) (fun u => initial _)).weaken (le_refl _)
  exact fun E out v => out (regEquiv q after v)

def rawOld (d : Nat) : Slot (d+1) ≃ Cluster d × Bool where
  toFun v := (clusterOf v,leftover v)
  invFun v := (v.1.1,Fin.cons v.2 v.1.2.1,v.1.2.2)
  left_inv v := by
    rcases v with ⟨a,w,b⟩
    change (a, Fin.cons (w 0) (Fin.tail w), b) = _
    rw [Fin.cons_self_tail]
  right_inv := by rintro ⟨⟨a,t,c⟩,b⟩; simp [clusterOf,leftover]

noncomputable def before (d : Nat) := (rawOld d).trans
  (Equiv.prodCongr (cellOrder d) (Equiv.refl Bool))

noncomputable def after (d : Nat) := (renameCells d).symm.trans
  (Equiv.prodCongr (cellOrder d) (Equiv.refl Bool))

theorem after_next (d : Nat) (v : Slot (d+1)) (b : Bool) :
    after d (v.1,nextState v.2.1 b,v.2.2) = ((before d v).1,b) := by
  rw [←rename_step]
  simp [after,before,rawOld]

theorem profilePacked {H : Type} (key0 : H→K) (group : H→Fin q→Fin N)
    (h : H) (z : (j : Fin N) → {a // group h a=j}→Bool) (b : Bool) :
    view (key0 h, hist (fun a => (group h a, (groupedBits (group h)).symm z a)),b) =
      profile z b := by
  refine Prod.ext ?_ rfl
  funext j k
  rw [show (view (key0 h,hist (fun a => (group h a, (groupedBits (group h)).symm z a)),b)).1 j k =
    Nat.card {a // (group h a, (groupedBits (group h)).symm z a)=(j,k)} from countHist ..]
  rw [←group_cell,Equiv.apply_symm_apply,countNew_card]
  rfl

theorem column_labeled {H : Type} [Fintype H] (hN : 0<N) (bef aft : P≃ Fin N×Bool)
    (table : K → Env s → Fin N → Bool → Bool → Bool) (init : Reg K P q → Env s → Nat)
    (x : Env s) (raw : H→Fin q→P) (key0 : H→K) (start : H→Bool)
    (initial : ∀ v,init v x = Nat.card {h : H // (key0 h,hist (raw h),start h)=v})
    (v : Reg K P q) :
    column hN bef aft table init v x =
      Nat.card {u : H × (Fin q→Bool) //
        (key0 u.1, hist (fun a => aft.symm ((bef (raw u.1 a)).1,u.2 a)),
          xor (start u.1) ((∑ a, (table (key0 u.1) x (bef (raw u.1 a)).1 (bef (raw u.1 a)).2 (u.2 a)).toNat).testBit 0)) = v} := by
  classical
  let group (h : H) (a : Fin q) := (bef (raw h a)).1
  let bit (h : H) (a : Fin q) := (bef (raw h a)).2
  let I (h : H) (j : Fin N) := {a // group h a=j}
  let old (h : H) := groupedBits (group h) (bit h)
  let pack (h : H) (z : cellBank (I h)) (b : Bool) : CellReg K q N :=
    (key0 h, hist (fun a => (group h a, (groupedBits (group h)).symm z a)),b)
  let f (h : H) := table (key0 h) x
  let idx := order N hN
  let tbl (t : Nat) (u : CellReg K q N) (y : Env s) := table u.1 y (idx t)
  let seed (u : CellReg K q N) := init ((regEquiv q bef).symm u)
  have hinit (u : CellReg K q N) : seed u x = Nat.card {h : H // pack h (old h) (start h)=u} := by
    rw [show seed u x = init ((regEquiv q bef).symm u) x from rfl,initial]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro h
    rw [←(regEquiv q bef).apply_eq_iff_eq]
    simp only [Equiv.apply_symm_apply]
    have same : (regEquiv q bef) (key0 h,hist (raw h),start h) = pack h (old h) (start h) := by
      change (key0 h,Sym.equivCongr bef (hist (raw h)),start h) = _
      rw [mapHist]
      simp only [pack,old,Equiv.symm_apply_apply]
      rfl
    rw [same]
  change dense Prod.fst view idx tbl seed N (regEquiv q aft v) x = _
  rw [ColumnHistory.dense_labeled I old idx (fun t ht => Nat.mod_eq_of_lt ht) f start Prod.fst view
    (view_inj K q N) key0 pack (fun _ _ _ => rfl) (profilePacked key0 group)
    x (fun k => table k x) (fun _ => rfl) tbl (fun _ _ _ => rfl) seed hinit]
  symm
  let e : H × (Fin q→Bool) ≃ Σ h,cellBank (I h) :=
    (Equiv.sigmaEquivProd H (Fin q→Bool)).symm.trans (Equiv.sigmaCongrRight (fun h => groupedBits (group h)))
  apply Nat.card_congr
  apply e.subtypeEquiv
  rintro ⟨h,z⟩
  dsimp only [e,Equiv.trans_apply,Equiv.sigmaEquivProd,Equiv.sigmaCongrRight,Equiv.coe_fn_mk,Equiv.coe_fn_symm_mk]
  have sum : (∑ j,∑ a : I h j,(f h j (old h j a) (groupedBits (group h) z j a)).toNat) =
      ∑ a,(table (key0 h) x (group h a) (bit h a) (z a)).toNat := by
    rw [←group_sum (group h) (fun a => (table (key0 h) x (group h a) (bit h a) (z a)).toNat)]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    rintro ⟨a,ha⟩ _
    dsimp [I,f,old,groupedBits]
    rw [ha]
  let flag := xor (start h) ((∑ a, (table (key0 h) x (group h a) (bit h a) (z a)).toNat).testBit 0)
  change ((key0 h,hist (fun a => aft.symm (group h a,z a)),flag) = v) ↔
    ((pack h (groupedBits (group h) z) (xor (start h)
      ((∑ j,∑ a : I h j,(f h j (old h j a) (groupedBits (group h) z j a)).toNat).testBit 0))) = regEquiv q aft v)
  rw [sum]
  have same : regEquiv q aft (key0 h,hist (fun a => aft.symm (group h a,z a)),flag) =
      pack h (groupedBits (group h) z) flag := by
    change (_,Sym.equivCongr aft (hist _),_) = _
    rw [mapHist]
    simp only [pack,Equiv.symm_apply_apply,Equiv.apply_symm_apply]
    rfl
  exact ((regEquiv q aft).apply_eq_iff_eq).symm.trans (by rw [same])

end PEqualNP.Outside.L_meta_33676_aux.FreeColumn

namespace PEqualNP.Outside.L_meta_33676_aux.FreeColumn

open ColumnCircuit WeightedCircuit Transfer ColumnTransfer StreamRows
open scoped Classical

theorem dense_sum {S K A U : Type} [Fintype S] [Fintype U] {s : Nat}
    (key : S→K) (vw : S→histogramState A) (cells : Nat→A)
    (tbl : Nat→S→Env s→Bool→Bool→Bool)
    (a : U→Env s→Nat) (f : U→S→Env s→Nat) (t : Nat) (v : S) (x : Env s) :
    dense key vw cells tbl (fun v x => ∑ u,a u x*f u v x) t v x =
      ∑ u,a u x*dense key vw cells tbl (f u) t v x := by
  induction t generalizing v with
  | zero => rfl
  | succ t ih =>
    simp only [dense,ih]
    calc
      _ = ∑ w : S, ∑ u : U,a u x *
          (if key w=key v then cellWeight (cells t) (vw w) (vw v) (tbl t v x) *
            dense key vw cells tbl (f u) t w x else 0) := by
        apply Finset.sum_congr rfl
        intro w _
        by_cases h : key w=key v <;> simp [h,Finset.mul_sum,mul_left_comm]
      _ = _ := by rw [Finset.sum_comm]; simp [Finset.mul_sum]

noncomputable def singletonSeed {V : Type} {s : Nat} (u v : V) (_ : Env s) : Nat :=
  if u=v then 1 else 0

theorem column_sum {K P : Type} [Fintype K] [Fintype P] {q N s : Nat}
    (hN : 0<N) (bef aft : P≃Fin N×Bool) (table : K→Env s→Fin N→Bool→Bool→Bool)
    (init : Reg K P q→Env s→Nat) (v : Reg K P q) (x : Env s) :
    column hN bef aft table init v x = ∑ u,init u x*column hN bef aft table (singletonSeed u) v x := by
  classical
  unfold column
  let E := regEquiv (K:=K) q bef
  have e : (fun u => init (E.symm u)) = (fun u x => ∑ v : Reg K P q,init v x*singletonSeed v (E.symm u) x) := by
    funext u x
    simp [singletonSeed]
  rw [show (fun u => init ((regEquiv q bef).symm u)) = _ from e,dense_sum]

theorem singleton_column {K P : Type} [Fintype K] [Fintype P] {q N s : Nat}
    (hN : 0<N) (bef aft : P≃Fin N×Bool) (table : K→Env s→Fin N→Bool→Bool→Bool)
    (key0 : K) (raw : Fin q→P) (start : Bool) (v : Reg K P q) (x : Env s) :
    column hN bef aft table (singletonSeed (key0,hist raw,start)) v x =
      Nat.card {z : Fin q→Bool //
        (key0,hist (fun a => aft.symm ((bef (raw a)).1,z a)),xor start
          ((∑ a,(table key0 x (bef (raw a)).1 (bef (raw a)).2 (z a)).toNat).testBit 0))=v} := by
  classical
  have init (u : Reg K P q) : singletonSeed (key0,hist raw,start) u x =
      Nat.card {h : Unit // (key0,hist raw,start)=u} := by
    by_cases eq : (key0,hist raw,start)=u
    · simp [singletonSeed,eq,Nat.card_eq_fintype_card]
    · simp [singletonSeed,eq]
  rw [column_labeled hN bef aft table _ x (fun _ : Unit => raw) (fun _ => key0) (fun _ => start) init]
  apply Nat.card_congr
  exact (Equiv.punitProd (Fin q→Bool)).subtypeEquiv (fun _ => Iff.rfl)

theorem deBruijn_singleton {K : Type} [Fintype K] {q d s : Nat}
    (table : K→Env s→Fin (Fintype.card (Cluster d))→Bool→Bool→Bool)
    (k : K) (raw : Fin q→Slot (d+1)) (a : Bool) (v : Reg K (Slot (d+1)) q) (x : Env s) :
    column Fintype.card_pos (before d) (after d) table (singletonSeed (k,hist raw,a)) v x =
      Nat.card {z : Fin q→Bool //
        (k,hist (fun j => ((raw j).1,nextState (raw j).2.1 (z j),(raw j).2.2)),xor a
          ((∑ j,(table k x (cellOrder d (clusterOf (raw j))) (leftover (raw j)) (z j)).toNat).testBit 0))=v} := by
  rw [singleton_column]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro z
  have next (j : Fin q) : (after d).symm ((before d (raw j)).1,z j) =
      ((raw j).1,nextState (raw j).2.1 (z j),(raw j).2.2) := by
    rw [←after_next,Equiv.symm_apply_apply]
  simp only [next]
  rfl

end PEqualNP.Outside.L_meta_33676_aux.FreeColumn

namespace PEqualNP.Outside.L_meta_33676_aux.FreeColumn

open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit.Builder
open ColumnCircuit WeightedCircuit Transfer ColumnTransfer StreamRows
open scoped Classical

theorem growVia {K P D : Type} [Fintype K] [Fintype P] [Fintype D] {q N s w : Nat}
    (reg : Reg K P q ≃ D) (hN : 0<N) (bef aft : P≃Fin N×Bool)
    (tbl : K→Env s→Fin N→Bool→Bool→Bool) (init : Reg K P q→Env s→Nat)
    (B : Bank s) (zero : B.Has (fun _ => false)) (one : B.Has (fun _ => true))
    (wire : ∀ k j b z,B.Has (fun x => tbl k x j b z)) (initw : ∀ u,HasWord B w (init u)) :
    B.Grow (N*(Fintype.card D*(2*(q+1)^2)*(60+(q+1)*(w*13)+w*4+w*13)))
      (fun E=>∀v,HasWord E w (column hN bef aft tbl init v)) := by
  have C := compileColumn hN bef aft tbl init B zero one wire initw
  exact C.weaken (le_of_eq (congrArg (fun n => N*(n*(2*(q+1)^2)*(60+(q+1)*(w*13)+w*4+w*13)))
    (Fintype.card_congr reg))) (fun _ h => h)

end PEqualNP.Outside.L_meta_33676_aux.FreeColumn

namespace PEqualNP.Outside.L_meta_33676_aux.FreePass

open ColumnTransfer StreamRows WeightedCircuit FreeColumn InitialDP PanelCount
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit.Builder
open scoped Classical

abbrev Table (s d : Nat) := State d→Bool→BitFn s
abbrev Register (q d : Nat) := Reg (State d × State d) (Slot d) q

def register (q d : Nat) : Macro q d × Bool ≃ Register q d where
  toFun v := ((v.1.1,v.1.2.1),v.1.2.2,v.2)
  invFun v := ((v.1.1,v.1.2,v.2.1),v.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def tableCells {e s : Nat} (F : Table s (e+1)) (_ : State (e+1)×State (e+1))
    (x : Env s) (j : Fin (Fintype.card (Cluster e))) (b z : Bool) : Bool :=
  F (Fin.cons b ((cellOrder e).symm j).2.1) z x

theorem tableCells_at {e s : Nat} (F : Table s (e+1)) (k : State (e+1)×State (e+1))
    (x : Env s) (v : Slot (e+1)) (z : Bool) :
    tableCells F k x (cellOrder e (clusterOf v)) (leftover v) z = F v.2.1 z x := by
  simp [tableCells,leftover,clusterOf,Fin.cons_self_tail]

def seed {q d s : Nat} (prev : Macro q d → Env s→Nat) (u : Register q d) (x : Env s) : Nat :=
  if u.2.2 then 0 else prev (u.1.1,u.1.2,u.2.1) x

noncomputable def run {q e s : Nat} (F : Table s (e+1)) (prev : Macro q (e+1)→Env s→Nat)
    (v : Macro q (e+1)) (b : Bool) (x : Env s) : Nat :=
  column (Fintype.card_pos (α:=Cluster e)) (before e) (after e) (tableCells F) (seed prev)
    (register q (e+1) (v,b)) x

def cost (q e w : Nat) := Fintype.card (Cluster e) *
  ((Fintype.card (Macro q (e+1)) * 2) * (2*(q+1)^2) * (60+(q+1)*(w*13)+w*4+w*13))

set_option maxHeartbeats 200000 in
theorem grow {q e w s : Nat} (B : Bank s) (zero : B.Has (fun _ => false)) (one : B.Has (fun _ => true))
    (F : Table s (e+1)) (wires : ∀ t b,B.Has (F t b))
    (prev : Macro q (e+1)→Env s→Nat) (initial : ∀ u,HasWord B w (prev u)) :
    B.Grow (cost q e w) (fun E => ∀ v b, HasWord E w (run F prev v b)) := by
  have hseed (u : Register q (e+1)) : HasWord B w (seed prev u) := by
    cases h : u.2.2 with
    | false =>
      rw [show seed prev u = prev (u.1.1,u.1.2,u.2.1) from funext (fun x => by simp [seed,h])]
      exact initial _
    | true =>
      rw [show seed prev u = fun _ => 0 from funext (fun x => by simp [seed,h])]
      exact constWord B zero one 0
  have hw (k : State (e+1) × State (e+1)) (j : Fin (Fintype.card (Cluster e))) (b z : Bool) :
      B.Has (fun x => tableCells F k x j b z) := wires _ _
  have C := growVia (N:=Fintype.card (Cluster e)) (q:=q) (w:=w) (s:=s) (K:=State (e+1) × State (e+1)) (P:=Slot (e+1))
    (register q (e+1)).symm (Fintype.card_pos (α:=Cluster e)) (before e) (after e) (tableCells F) (seed prev) B zero one hw hseed
  refine C.weaken (le_of_eq ?_) (fun E out v b => out (register q (e+1) (v,b)))
  exact congrArg (fun n => Fintype.card (Cluster e)*(n*(2*(q+1)^2)*(60+(q+1)*(w*13)+w*4+w*13)))
    ((Fintype.card_prod _ _).trans (congrArg (fun t => Fintype.card (Macro q (e+1))*t) Fintype.card_bool))

theorem seed_one {q d s : Nat} (u : Macro q d) :
    seed (s:=s) (singletonSeed u) = singletonSeed (register q d (u,false)) := by
  classical
  funext v x
  obtain ⟨⟨i,j⟩,m,b⟩ := v
  rcases u with ⟨i',j',m'⟩
  cases b <;> simp [seed,singletonSeed,register,and_assoc]

theorem seed_expansion {q d s : Nat} (prev : Macro q d→Env s→Nat) (u : Register q d) (x : Env s) :
    seed prev u x = ∑ v,prev v x*seed (singletonSeed v) u x := by
  obtain ⟨⟨i,j⟩,m,b⟩ := u
  cases b <;> simp [seed,singletonSeed]
  rw [Finset.sum_eq_single (i,j,m)]
  · simp
  · intro a _ ne; simp [ne]
  · simp

theorem run_sum {q e s : Nat} (F : Table s (e+1)) (prev : Macro q (e+1)→Env s→Nat)
    (v : Macro q (e+1)) (b : Bool) (x : Env s) :
    run F prev v b x = ∑ u,prev u x*run F (singletonSeed u) v b x := by
  unfold run column
  let idx := order (Fintype.card (Cluster e)) (Fintype.card_pos (α:=Cluster e))
  let cv := regEquiv (K:=State (e+1)×State (e+1)) q (before e)
  have flat : (fun r => seed prev (cv.symm r)) =
      (fun r x => ∑ u,prev u x * seed (singletonSeed u) (cv.symm r) x) :=
    funext (fun r => funext (fun y => seed_expansion prev (cv.symm r) y))
  rw [show (fun r => seed prev ((regEquiv q (before e)).symm r)) = _ from flat]
  exact dense_sum _ _ _ _ _ _ _ _ _

theorem run_single {q e s : Nat} (F : Table s (e+1)) (m : Live q (e+1))
    (v : Macro q (e+1)) (b : Bool) (x : Env s) :
    run F (singletonSeed (project m)) v b x =
      Nat.card {z : Fin q→Bool //
        (m.1 0,m.2 (Fin.last q),histogram (fun j =>
          (m.1 j.castSucc,nextState (m.2 j.castSucc) (z j),m.1 j.succ)))=v ∧
        ((∑ j,(F (m.2 j.castSucc) (z j) x).toNat).testBit 0)=b} := by
  rw [run,seed_one]
  change column (Fintype.card_pos (α:=Cluster e)) (before e) (after e) (tableCells F)
      (singletonSeed ((m.1 0,m.2 (Fin.last q)),hist (slots m),false)) (register q (e+1) (v,b)) x = _
  rw [deBruijn_singleton]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro z
  rcases v with ⟨U,V,M⟩
  simp only [tableCells_at,Bool.false_xor,register,Equiv.coe_fn_mk,Prod.mk.injEq,
    slots,hist,histogram]
  tauto

end PEqualNP.Outside.L_meta_33676_aux.FreePass

namespace PEqualNP.Outside.L_meta_33676_aux.FullColumn

open InitialDP StreamRows WeightedCircuit
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit Builder
open scoped Classical

noncomputable def fullStep {s n e q : ℕ} (p l : ℕ) (h : Env s → ℕ) (i : Fin n)
    (row : FreePass.Table s (e+1)) (residual : State (e+1) → BitFn s)
    (prev : Macro q (e+1) → Env s → ℕ) : Macro q (e+1) → Env s → ℕ :=
  BranchDP.advance (fun z x => decide (BranchDP.branchAllowed p n (e+1) l (h x) i z))
    residual row (FreePass.run row prev)

def cost (q e w : ℕ) :=
  FreePass.cost q e w + (2+(2^(e+1))^2*4*7+Fintype.card (Macro q (e+1))*(4*(w*17)))

theorem grow {s n e q w : ℕ} (p l : ℕ) (h : Env s → ℕ) (i : Fin n)
    (row : FreePass.Table s (e+1)) (residual : State (e+1) → BitFn s)
    (prev : Macro q (e+1) → Env s → ℕ) (B : Bank s)
    (zero : B.Has (fun _ => false)) (one : B.Has (fun _ => true)) (bh : ∀ x,h x<2^(p*n))
    (wh : HasWord B (p*n) h) (hr : ∀ c z,B.Has (row c z)) (hs : ∀ u,B.Has (residual u))
    (hv : ∀ v,HasWord B w (prev v)) :
    B.Grow (cost q e w) (fun E => ∀ v,HasWord E w (fullStep p l h i row residual prev v)) := by
  obtain ⟨D,eD,cD,free⟩ := FreePass.grow B zero one row hr prev hv
  obtain ⟨E,eE,cE,step⟩ := BranchDP.compileAdvance D (eD zero) (eD one) l h bh (keep eD wh) i
    residual row (FreePass.run row prev) (fun U => eD (hs U)) (fun c z => eD (hr c z)) free
  exact ⟨E,Bank.ext_trans eD eE,by unfold cost; omega,step⟩

end PEqualNP.Outside.L_meta_33676_aux.FullColumn

namespace PEqualNP.Outside.L_meta_33676_aux.PanelSetup

open Translation ShiftCriterion ShiftedReport StreamRows CommonCircuit BoundaryCircuit MatrixCircuit
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit Builder
open EliminationCircuit (bit)

noncomputable def normalizedTable {p n s : Nat} (hp : 0<p) (hn : 0<n) (r d : Nat)
    (x : Env s) (i : Fin n) (u : Translation.Vector (d+1)) :=
  commonTable hp hn (reportTable r d x) (GoodLeastBank.cfgLeast hp hn r d x) i u

noncomputable def bias {p n s : Nat} (hp : 0<p) (hn : 0<n) (r d : Nat)
    (x : Env s) (i : Fin n) :=
  residueSum hp hn (reportTable r d x) (encode (GoodLeastBank.cfgLeast hp hn r d x)) i

noncomputable def adjustedTarget {p n s : Nat} (hp : 0<p) (hn : 0<n) (r d : Nat)
    (x : Env s) (i : Fin n) :=
  bias hp hn r d x i + scalar ((RankedC.target (p*n) n r x).val.testBit i.val)

structure Prepared {s p n : Nat} (hp : 0<p) (hn : 0<n) (r d : Nat) (B : Bank s) : Prop where
  base : GoodLeastBank.HasBank hp hn r d B
  common : ∀ i u, B.Has (fun x => bit (normalizedTable hp hn r d x i u))
  target : ∀ i, B.Has (fun x => bit (adjustedTarget hp hn r d x i))
  zero : B.Has (fun _ => false)
  one : B.Has (fun _ => true)

def prepCost (p n r d : Nat) := GoodLeastBank.budget p n r d + signalCost p n d + 2 + n*4

theorem prepare {p n : Nat} (hp : 0<p) (hn : 0<n) (r d : Nat) :
    (Bank.empty (RankedC.numInputs p n r)).Grow (prepCost p n r d) (Prepared hp hn r d) := by
  obtain ⟨B,eB,lenB,b⟩ := GoodLeastBank.grow hp hn r d (RankedC.trailing (p*n) n)
  obtain ⟨C,eC,lenC,common,off⟩ := commonAndOffset hp hn B (reportTable r d) (GoodLeastBank.cfgLeast hp hn r d)
    (reportTable_wires B b.tables) b.least
  obtain ⟨D,eD,lenD,hz⟩ := C.const false
  obtain ⟨E,eE,lenE,ho⟩ := D.const true
  have ext : (Bank.empty _).Ext E := Bank.ext_trans eB (Bank.ext_trans eC (Bank.ext_trans eD eE))
  have hy := Layout.readWord_wires E ext (eE hz) n (3*(p*n)+2*r*(p*n))
  obtain ⟨F,eF,lenF,adj⟩ := E.collectFin n (fun i x => bit (adjustedTarget hp hn r d x i)) 4 (by
    intro J eJ i
    obtain ⟨K,eK,lenK,res⟩ := Bank.xor2 (eJ (eE (eD (off i)))) (eJ (hy i))
    refine ⟨K,eK,lenK,has_iff res (fun x => ?_)⟩
    have xorScalar : ∀ (a : F₂) (v : Bool), xor (bit a) v = bit (a+scalar v) := by decide
    exact xorScalar _ _)
  have extBF : B.Ext F := Bank.ext_trans eC (Bank.ext_trans eD (Bank.ext_trans eE eF))
  refine ⟨F,Bank.ext_trans eB extBF,?_,⟨⟨⟨fun i j => extBF (b.tables i j),fun i j => extBF (b.rows i j),
    fun i => extBF (b.rhs i),fun i => extBF (b.digits i),extBF b.feasible,extBF b.valid⟩,
    fun i => extBF (b.least i)⟩,fun i u => eF (eE (eD (common i u))),adj,eF (eE hz),eF ho⟩⟩
  unfold prepCost
  simp [Bank.empty] at lenB ⊢
  omega

noncomputable def residual {p n s : Nat} (hp : 0<p) (hn : 0<n) (r d l : Nat)
    (h : Env s → Nat) (U : State d) (i : Fin n) (x : Env s) :=
  fixedParity (p:=p) (normalizedTable hp hn r d) l h U i x + adjustedTarget hp hn r d x i

theorem residualWires {p n s d : Nat} (hp : 0<p) (hn : 0<n) (r l : Nat) (B : Bank s)
    (prep : Prepared hp hn r d B) (h : Env s → Nat)
    (hh : ∀ i : Fin (p*n), B.Has (fun x => (h x).testBit i.val)) (bound : ∀ x, h x < 2^(p*n)) :
    B.Grow (boundaryCost p n d + 2^d*n*4)
      (fun E => ∀ U i, E.Has (fun x => bit (residual hp hn r d l h U i x))) := by
  obtain ⟨C,eC,lenC,par⟩ := buildFixedParity B (normalizedTable hp hn r d) prep.common l h hh bound prep.zero prep.one
  obtain ⟨D,eD,lenD,out⟩ := SensorBuilder.collectType C
    (fun v : State d × Fin n => fun x => bit (residual hp hn r d l h v.1 v.2 x)) 4 (by
      intro K eK v
      obtain ⟨E,eE,lenE,w⟩ := Bank.xor2 (eK (par v.1 v.2)) (eK (eC (prep.target v.2)))
      have eq : ∀ a b : F₂, xor (bit a) (bit b) = bit (a+b) := by decide
      exact ⟨E,eE,lenE,has_iff w (fun x => eq _ _)⟩)
  simp [State] at lenD
  exact ⟨D,Bank.ext_trans eC eD,by omega,fun U i => out (U,i)⟩

private theorem core_bounds (k r D : Nat) : k ≤ k+r+D+5 ∧ D ≤ k+r+D+5 ∧ 1 ≤ k+r+D+5 := by omega

theorem prepCost_bound {p n : Nat} (hp : 0<p) (hn : 0<n) (r d : Nat) :
    prepCost p n r d ≤ 2^17*(p*n+r+2^d+5)^5 := by
  have nk : n ≤ p*n := by simpa using Nat.mul_le_mul_right n hp
  have pk : p ≤ p*n := by simpa using Nat.mul_le_mul_left p hn
  have dk := Nat.lt_two_pow_self (n:=d)
  have h := GoodLeastBank.budget_le nk r d
  unfold prepCost signalCost lookupCost
  rw [pow_succ]
  generalize p*n = k at nk pk h ⊢
  generalize 2^d = D at dk h ⊢
  let M := k+r+D+5
  obtain ⟨km,dm,hm⟩ := core_bounds k r D
  change k≤M at km; change D≤M at dm
  have nm : n≤M := nk.trans km
  have pm : p≤M := pk.trans km
  have mm : d≤M := dk.le.trans dm
  calc
    _ ≤ 2^14*M^5 + (M*(M+1+(1+M*2*(4+2*(M+1)))) +
        M*(M*2)*(M+1+(1+M*2*(4+2*(M+1)))+4)+M*(1+M*4)) + 2 + M*4 := by
      gcongr
      all_goals first | exact h | exact km | exact dm | exact mm | exact pm | exact nm
    _ ≤ 2^17*M^5 := by
      obtain ⟨z,hz⟩ := Nat.exists_eq_add_of_le (show 1≤M from hm)
      rw [hz]
      ring_nf
      omega

theorem boundaryCost_bound (p n r d : Nat) (hp : 0<p) (hn : 0<n) :
    boundaryCost p n d + 2^d*n*4 ≤ 2^8*(p*n+r+2^d+5)^5 := by
  have nk : n ≤ p*n := by simpa using Nat.mul_le_mul_right n hp
  have pk : p ≤ p*n := by simpa using Nat.mul_le_mul_left p hn
  have dk := Nat.lt_two_pow_self (n:=d)
  unfold boundaryCost lookupCost
  rw [pow_succ]
  generalize p*n = k at nk pk ⊢
  generalize 2^d = D at dk ⊢
  let M := k+r+D+5
  obtain ⟨km,dm,hm⟩ := core_bounds k r D
  change k≤M at km; change D≤M at dm
  have nm : n≤M := nk.trans km
  have pm : p≤M := pk.trans km
  have mm : d≤M := dk.le.trans dm
  calc
    _ ≤ M*M*(M*(1+M*2*(4+2*(M+1)))+(1+M*4))+M*M*4 := by
      gcongr
    _ ≤ 2^8*M^5 := by
      obtain ⟨z,hz⟩ := Nat.exists_eq_add_of_le (show 1≤M from hm)
      rw [hz]
      ring_nf
      omega

end PEqualNP.Outside.L_meta_33676_aux.PanelSetup

namespace PEqualNP.Outside.L_meta_33676_aux.BranchReport

open StreamRows InitialDP Translation ShiftCriterion PanelCount WeightedCircuit
open EliminationCircuit (bit)
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit Builder
open scoped Classical

theorem parity_sum {A : Type*} [Fintype A] (f : A → Translation.F₂) :
    (∑ a,(bit (f a)).toNat).testBit 0 = bit (∑ a,f a) := by
  classical
  have add (a b : ℕ) : (a+b).testBit 0=xor (a.testBit 0) (b.testBit 0) := by
    simp only [Nat.testBit_zero]
    by_cases ha : a % 2=1 <;> by_cases hb : b % 2=1 <;> simp [ha,hb] <;> omega
  have sum (S : Finset A) : (∑ a∈S,(bit (f a)).toNat).testBit 0=bit (∑ a∈S,f a) := by
    induction S using Finset.induction_on with
    | empty => simp [bit]
    | @insert a S ha ih =>
      rw [Finset.sum_insert ha,Finset.sum_insert ha,add,ih]
      have one (b : Bool) : b.toNat.testBit 0=b := by cases b <;> decide
      have two : ∀ v w : Translation.F₂, xor (bit v) (bit w)=bit (v+w) := by decide
      rw [one,two]
  exact sum Finset.univ

noncomputable def rowBit {s p n d : ℕ} (hp : 0<p) (hn : 0<n) (r : ℕ)
    (i : Fin n) (c : StreamRows.State d) (z : Bool) (x : Env s) :=
  bit (PanelSetup.normalizedTable hp hn r d x i (PanelCount.reading c z))

noncomputable def freeFlag {s p n d : ℕ} (hp : 0<p) (hn : 0<n) (r l : ℕ) (i : Fin n)
    (m : PanelCount.Live (Ranking.distinguished p n l) d)
    (z : PanelCount.Bits (Ranking.distinguished p n l)) (x : Env s) : Bool :=
  (∑ a : Fin (Ranking.distinguished p n l),(rowBit hp hn r i (m.2 a.castSucc) (z a.castSucc) x).toNat).testBit 0

theorem rowWires {s p n d : ℕ} (hp : 0<p) (hn : 0<n) (r : ℕ) (B : Bank s)
    (hw : PanelSetup.Prepared hp hn r d B) (i : Fin n) (c : StreamRows.State d) (z : Bool) :
    B.Has (rowBit hp hn r i c z) := hw.common i (PanelCount.reading c z)

theorem enabled_iff {s p n d : ℕ} (hp : 0<p) (hn : 0<n) (r l : ℕ) (h : Env s → ℕ)
    (i : Fin n) (m : PanelCount.Live (Ranking.distinguished p n l) d)
    (z : PanelCount.Bits (Ranking.distinguished p n l)) (x : Env s) :
    PanelCount.enabled (h x) (PanelCount.reportPass p n d l (h x) (PanelSetup.normalizedTable hp hn r d x)
      (PanelSetup.bias hp hn r d x) (fun j => (RankedC.target (p*n) n r x).val.testBit j.val)) i.val m z ↔
    BranchDP.control (fun v y => decide (BranchDP.branchAllowed p n d l (h y) i v))
      (fun y => bit (PanelSetup.residual hp hn r d l h (m.1 0) i y))
      (rowBit hp hn r i (m.2 (Fin.last _))) (z (Fin.last _)) (freeFlag hp hn r l i m z x) x = true := by
  simp only [PanelCount.enabled,dite_eq_left i.isLt,BranchDP.control,Bool.and_eq_true,
    beq_iff_eq]
  apply and_congr
  · exact ⟨fun hp => @decide_eq_true _ (Classical.propDecidable _) hp,
      fun hp => @of_decide_eq_true _ (Classical.propDecidable _) hp⟩
  simp only [PanelCount.reportPass,freeFlag,rowBit,parity_sum,PanelSetup.residual,
    BoundaryCircuit.fixedParity,PanelSetup.adjustedTarget]
  have eq : ∀ (a b c d : Translation.F₂) (y : Bool),
    a+b+c+d=ShiftCriterion.scalar y ↔ xor (bit a) (bit b)=bit (c+(d+ShiftCriterion.scalar y)) := by decide
  exact eq _ _ _ _ _

end PEqualNP.Outside.L_meta_33676_aux.BranchReport

namespace PEqualNP.Outside.L_meta_33676_aux.FullColumn

open InitialDP StreamRows WeightedCircuit PanelCount PanelSetup BranchReport
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit Builder
open scoped Classical

theorem fullStep_sum {s n e q : ℕ} (p l : ℕ) (h : Env s → ℕ) (i : Fin n)
    (row : FreePass.Table s (e+1)) (residual : State (e+1) → BitFn s)
    (prev : Macro q (e+1) → Env s → ℕ) (v : Macro q (e+1)) (x : Env s) :
    fullStep p l h i row residual prev v x =
      ∑ u, prev u x * fullStep p l h i row residual (FreeColumn.singletonSeed u) v x := by
  unfold fullStep
  exact DistinguishedCount.advance_sum x _ residual row (FreePass.run row prev) (fun u => prev u x)
    (fun u => FreePass.run row (FreeColumn.singletonSeed u)) (fun v b => FreePass.run_sum row prev v b x) v

theorem fullStep_single {s p n e : ℕ} (hp : 0<p) (hn : 0<n) (r l : ℕ) (h : Env s → ℕ)
    (i : Fin n) (m : Live (Ranking.distinguished p n l) (e+1))
    (v : Macro (Ranking.distinguished p n l) (e+1)) (x : Env s) :
    fullStep p l h i (rowBit hp hn r i)
      (fun u x => EliminationCircuit.bit (PanelSetup.residual hp hn r (e+1) l h u i x))
      (FreeColumn.singletonSeed (project m)) v x =
    Nat.card {z : Bits (Ranking.distinguished p n l) //
      enabled (h x) (reportPass p n (e+1) l (h x) (normalizedTable hp hn r (e+1) x)
        (bias hp hn r (e+1) x) (fun j => (RankedC.target (p*n) n r x).val.testBit j.val)) i.val m z ∧
        project (step i.val m z)=v} := by
  unfold fullStep
  refine DistinguishedCount.join_afterFree x i.val m _ _ _ _ (fun v b => FreePass.run_single (rowBit hp hn r i) m v b x) _ ?_ v
  intro w
  have cond := enabled_iff hp hn r l h i m (DistinguishedCount.joined _ w) x
  simpa only [freeFlag,DistinguishedCount.joined_last,DistinguishedCount.joined_cast,DistinguishedCount.freePar] using cond

end PEqualNP.Outside.L_meta_33676_aux.FullColumn

namespace PEqualNP.Outside.L_meta_33676_aux.FullColumn

open StreamRows InitialDP WeightedCircuit
open EliminationCircuit (bit)
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit Builder

private theorem choice_eq {A : Type} {P Q : Prop} {d : Decidable P} {e : Decidable Q}
    (u v : A) (prop : P=Q) : @ite A P d u v = @ite A Q e u v := by
  subst Q
  cases Subsingleton.elim d e
  rfl

private theorem advance_env {s q e : ℕ} (pin1 pin2 : Bool → BitFn s)
    (r1 r2 : State (e+1) → BitFn s) (tbl : FreePass.Table s (e+1))
    (prev : Macro q (e+1) → Bool → Env s → ℕ)
    (v : Macro q (e+1)) (x : Env s) (a : ∀ z,pin1 z x=pin2 z x) (b : ∀ u,r1 u x=r2 u x) :
    BranchDP.advance pin1 r1 tbl prev v x = BranchDP.advance pin2 r2 tbl prev v x := by
  unfold BranchDP.advance
  apply Finset.sum_congr rfl
  intro j _
  apply choice_eq
  simp only [BranchDP.control,a,b]

theorem fullStep_prefix {s p n e q : ℕ} (hp : 0<p) (hn : 0<n) (r l : ℕ)
    (h : Env s → ℕ) (i : Fin n) (f : Macro q (e+1) → Env s → ℕ) (v : Macro q (e+1)) (x : Env s) :
    fullStep p l h i (BranchReport.rowBit hp hn r i)
      (fun U y => bit (PanelSetup.residual hp hn r (e+1) l h U i y)) f v x =
    fullStep p l (fun _ => h x) i (BranchReport.rowBit hp hn r i)
      (fun U y => bit (PanelSetup.residual hp hn r (e+1) l (fun _ => h x) U i y)) f v x := by
  apply advance_env
  · intro z; rfl
  · intro u
    simp only [PanelSetup.residual,BoundaryCircuit.fixedParity]

end PEqualNP.Outside.L_meta_33676_aux.FullColumn

namespace PEqualNP.Outside.L_meta_33676_aux.TerminalDP

open InitialDP StreamRows ColumnTransfer PinnedBoundary Ranking WeightedCircuit
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit Builder

def done (p n d l h : ℕ) (s : Macro (distinguished p n l) d) : Prop :=
  nextStart (p:=p) (n:=n) l h s.1 = s.2.1 ∧ ∀ c ∈ s.2.2.toMultiset, c.2.1=c.2.2

open Classical in
noncomputable def finishValue {s : ℕ} (p n d l : ℕ) (h : Env s → ℕ)
    (weights : Macro (distinguished p n l) d → Env s → ℕ) (x : Env s) :=
  ∑ v, if done p n d l (h x) v then weights v x else 0

open Classical in
theorem stateMatch {s d : ℕ} (B : Bank s) (o : B.Has (fun _ => true))
    (z : Env s → State d) (w : State d) (hw : ∀ i, B.Has (fun x => z x i)) :
    B.Grow (2*d) (fun E => E.Has (fun x => decide (z x=w))) := by
  let f := fun (i : Fin d) (x : Env s) => z x i == w i
  obtain ⟨D,e,c,ws⟩ := B.collectFin d f 1 (by
    intro E e i
    cases h : w i with
    | false =>
      obtain ⟨F,eF,cF,ans⟩ := Bank.inv (e (hw i))
      exact ⟨F,eF,cF,mapWire ans (fun x => by simp [f,h])⟩
    | true =>
      exact ⟨E,Bank.ext_refl E,by omega,mapWire (e (hw i)) (fun x => by simp [f,h])⟩)
  obtain ⟨E,eE,cE,v⟩ := allWires (List.finRange d) D f ws (e o)
  refine ⟨E,Bank.ext_trans e eE,by simp at c cE; omega,mapWire v (fun x => ?_)⟩
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true,List.mem_finRange,forall_true_left,f,beq_iff_eq,decide_eq_true_eq]
  exact ⟨fun h => funext h,fun h => congrFun h⟩

theorem nextWire {s p n d : ℕ} (B : Bank s) (z : B.Has (fun _ => false)) (o : B.Has (fun _ => true))
    (h : Env s → ℕ) (bh : ∀ x,h x<2^(p*n)) (hw : HasWord B (p*n) h)
    (l : ℕ) (U : State d) (j : Fin d) :
    B.Has (fun x => nextStart (p:=p) (n:=n) l (h x) U j) := by
  unfold nextStart
  by_cases inner : distinguished p n l+1<p
  · simp only [inner,↓reduceIte]
    exact BoundaryCircuit.fixedBitWire B h hw bh z _
  · simp only [inner,↓reduceIte]
    cases U j <;> first | exact z | exact o

theorem compileFinish {s p n d l width : ℕ} (B : Bank s)
    (h : Env s → ℕ) (bh : ∀ x,h x<2^(p*n)) (wh : HasWord B (p*n) h)
    (weights : Macro (distinguished p n l) d → Env s → ℕ) (wires : ∀ v,HasWord B width (weights v)) :
    B.Grow (2+(2^d)^2*(2*d)+Fintype.card (Macro (distinguished p n l) d)*(width*17))
      (fun E => HasWord E width (finishValue p n d l h weights)) := by
  classical
  obtain ⟨C,eC,cC,z⟩ := B.const false
  obtain ⟨D,eD,cD,o⟩ := C.const true
  have eBD : B.Ext D := Bank.ext_trans eC eD
  obtain ⟨J,eJ,cJ,matchWire⟩ := SensorBuilder.collectType D
    (fun v : State d × State d => fun x => decide (nextStart (p:=p) (n:=n) l (h x) v.1=v.2))
    (2*d) (fun F e v => stateMatch F (e o) _ v.2
      (fun i => nextWire F (e (eD z)) (e o) h bh (keep (Bank.ext_trans eBD e) wh) l v.1 i))
  have eBJ : B.Ext J := Bank.ext_trans eBD eJ
  obtain ⟨E,eE,cE,ws⟩ := sumWords (w:=width) J (eJ (eD z)) (eJ o) Finset.univ
    (fun v x => if done p n d l (h x) v then weights v x else 0) (width*4) (by
      intro v _ F e
      by_cases closed : ∀ c ∈ v.2.2.toMultiset,c.2.1=c.2.2
      · obtain ⟨T,et,ct,val⟩ := muxWord F _ (weights v) (fun _=>0)
          (e (matchWire (v.1,v.2.1))) (keep (Bank.ext_trans eBJ e) (wires v))
          (constWord F (e (eJ (eD z))) (e (eJ o)) 0)
        refine ⟨T,et,ct,fun j => mapWire (val j) (fun x => ?_)⟩
        by_cases same : nextStart (p:=p) (n:=n) l (h x) v.1 = v.2.1
        · have ok : done p n d l (h x) v := ⟨same,closed⟩
          simp [same,ok]
        · have bad : ¬done p n d l (h x) v := fun h => same h.1
          simp [same,bad]
      · refine ⟨F,Bank.ext_refl F,by omega,?_⟩
        simpa only [done,closed,and_false,ite_false] using constWord (w:=width) F (e (eJ (eD z))) (e (eJ o)) 0)
  refine ⟨E,Bank.ext_trans eBJ eE,?_,ws⟩
  simp [State,←pow_two] at cJ
  simp only [Finset.card_univ] at cE
  rw [show width*4+width*13=width*17 by omega] at cE
  omega

end PEqualNP.Outside.L_meta_33676_aux.TerminalDP

namespace PEqualNP.Outside.L_meta_33676_aux.OracleFold

open Translation ShiftCriterion GoodBank GoodLeastBank RankedC Ranking InitialDP WeightedCircuit
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit Builder
open scoped Classical

abbrev Coeff (s p n d : ℕ) := Env s → (l : ℕ) → ℕ → ℕ → Macro (distinguished p n l) d → Macro (distinguished p n l) d → ℕ

noncomputable def output {s p n d : ℕ} (K : Coeff s p n d) (x : Env s) (l h : ℕ) :=
  ∑ v, if TerminalDP.done p n d l h v then HistoryFold.count (initValue p n d l h) (K x l h) n v else 0

theorem extend {s p n r d : ℕ} {hp : 0<p} {hn : 0<n} {B E : Bank s}
    (e : B.Ext E) (b : PanelSetup.Prepared hp hn r d B) : PanelSetup.Prepared hp hn r d E :=
  ⟨⟨⟨fun i j => e (b.base.tables i j),fun i j => e (b.base.rows i j),fun i => e (b.base.rhs i),
    fun i => e (b.base.digits i),e b.base.feasible,e b.base.valid⟩,fun i => e (b.base.least i)⟩,
    fun i j => e (b.common i j),fun i => e (b.target i),e b.zero,e b.one⟩

theorem oracleSpec {p n r d : ℕ} (hp : 0<p) (hn : 0<n) (hk : n<p*n) (hd : d<n) (hr : 4≤r)
    (K : Coeff (numInputs p n r) p n d)
    (localK : ∀ x l h t m v, Nat.card {z : PanelCount.Bits (distinguished p n l) //
      PanelCount.enabled h (PanelCount.reportPass p n d l h (PanelSetup.normalizedTable hp hn r d x)
        (PanelSetup.bias hp hn r d x) (fun j => (target (p*n) n r x).val.testBit j.val)) t m z ∧
        PanelCount.project (PanelCount.step t m z)=v} = K x l h t (PanelCount.project m) v) :
    OracleSpec hp hn r d (output K) := by
  intro x hv hf l hl h bh
  let H := report hp hn r x
  let g := cfgLeast hp hn r d x
  have hT := reportTable_spec hp hn (hd.trans hk) hr x hv
  have existsG : ∃ w : Translation.Word (p*n), rawGood H n w := by
    apply (feasible_count_iff _).mp
    exact (cfgCount_correct hp hn hk hd hr x hv) ▸ hf
  obtain ⟨v,hv',hm⟩ := LeastCircuit.least_exists _ existsG
  have bits : keyBits hp hn r d x = fun i => v.val.testBit i.val :=
    LeastCircuit.least_key_bits hp hn hk hd H _ hT v hv' hm
  have eg : g = v := by
    apply encode_inj
    funext i
    change scalar ((cfgLeast hp hn r d x).val.testBit i.val) = scalar (v.val.testBit i.val)
    rw [cfgLeast_bit,bits]
  have hg : rawGood H n g := eg ▸ hv'
  have off : (fun i => scalar (H g.val i)) = PanelSetup.bias hp hn r d x := funext (hT g)
  apply Eq.symm
  apply PanelCount.ranked_slice hp hn hd H g (PanelSetup.normalizedTable hp hn r d x)
    (ShiftedReport.commonTable_spec hp hn hk hd H _ hT g hg) _ bh (K x l h)
  rw [off]
  exact localK x l h

theorem layers {s p n d l width cost : ℕ} (B : Bank s) (h : Env s → ℕ) (K : Coeff s p n d)
    (seed : ∀ v, HasWord B width (fun x => initValue p n d l (h x) v))
    (grow : ∀ E : Bank s, B.Ext E → ∀ i : Fin n, ∀ f : Macro (distinguished p n l) d → Env s → ℕ,
      (∀ v, HasWord E width (f v)) → E.Grow cost (fun G => ∀ v, HasWord G width
        (fun x => ∑ u, f u x * K x l (h x) i.val u v)))
    (t : ℕ) (ht : t≤n) : B.Grow (t*cost) (fun E => ∀ v, HasWord E width
      (fun x => HistoryFold.count (initValue p n d l (h x)) (K x l (h x)) t v)) := by
  induction t with
  | zero => exact ⟨B,Bank.ext_refl _,by simp,seed⟩
  | succ t ih =>
    obtain ⟨E,e,c,w⟩ := ih (by omega)
    obtain ⟨G,eG,cG,wG⟩ := grow E e ⟨t,by omega⟩ _ w
    exact ⟨G,Bank.ext_trans e eG,by rw [Nat.succ_mul]; omega,wG⟩

def queryCost (p n d l width cost boundary : ℕ) := boundary+(2+2^d*(2*d))+n*cost+
  (2+(2^d)^2*(2*d)+Fintype.card (Macro (distinguished p n l) d)*(width*17))

theorem emit {s p n r d q cost : ℕ} (hp : 0<p) (hn : 0<n) (hd : d≤n) (B : Bank s)
    (b : PanelSetup.Prepared hp hn r d B) (K : Coeff s p n d)
    (stepper : ∀ (l : ℕ) (h : Env s → ℕ) (E : Bank s), PanelSetup.Prepared hp hn r d E →
      HasWord E (p*n) h → (∀ x,h x<2^(p*n)) →
      (∀ U i, E.Has (fun x => EliminationCircuit.bit (PanelSetup.residual hp hn r d l h U i x))) →
      ∀ i : Fin n, ∀ f : Macro (distinguished p n l) d → Env s → ℕ,
      (∀ v,HasWord E (p*n+1) (f v)) → E.Grow cost (fun G => ∀ v,HasWord G (p*n+1)
        (fun x => ∑ u,f u x * K x l (h x) i.val u v)))
    (room : ∀ l, l≤p*n → queryCost p n d l (p*n+1) cost (BoundaryCircuit.boundaryCost p n d+2^d*n*4) ≤ q) :
    RankCircuit.PinnedCounter B (p*n) q (output K) := by
  intro D eD l hl h bh wh
  have bound (x : Env s) : h x < 2^(p*n) := (bh x).trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
  obtain ⟨E,eE,cE,res⟩ := PanelSetup.residualWires hp hn r l D (extend eD b) h wh bound
  obtain ⟨F,eF,cF,init⟩ := InitialDP.compileInitial (l:=l) hp hd E h (keep eE wh) (p*n+1)
  have eDF : D.Ext F := Bank.ext_trans eE eF
  obtain ⟨G,eG,cG,out⟩ := layers (cost:=cost) F h K init (by
    intro T eT i f wires
    have eDT : D.Ext T := Bank.ext_trans eDF eT
    exact stepper l h T (extend (Bank.ext_trans eD eDT) b) (keep eDT wh) bound
      (fun U j => eT (eF (res U j))) i f wires) n (le_refl n)
  have eDG : D.Ext G := Bank.ext_trans eDF eG
  obtain ⟨J,eJ,cJ,done⟩ := TerminalDP.compileFinish (l:=l) G h bound (keep eDG wh) _ out
  refine ⟨J,Bank.ext_trans eDG eJ,?_,done⟩
  have c := room l hl
  unfold queryCost at c
  omega

end PEqualNP.Outside.L_meta_33676_aux.OracleFold

namespace PEqualNP.Outside.L_meta_33676_aux.OracleBudget

open StreamRows ColumnTransfer InitialDP Ranking

def sizeBase (p n r e : ℕ) := p*n+r+2^(e+1)+5

def histBound (p e : ℕ) := (p+(2^(e+1))^3).choose p

def columnCost (p n r e : ℕ) := 2^14*(sizeBase p n r e)^10*histBound p e

def queryCost (p n r e : ℕ) := 2^24*(sizeBase p n r e)^12*histBound p e

theorem hist_pos (p e : ℕ) : 0<histBound p e := Nat.choose_pos (Nat.le_add_right _ _)

private theorem params {p n : ℕ} (hp : 0<p) (hn : 0<n) (r e : ℕ) :
    1 ≤ sizeBase p n r e ∧ n ≤ sizeBase p n r e ∧ p+1 ≤ sizeBase p n r e ∧
    p*n+1 ≤ sizeBase p n r e ∧ 2^(e+1) ≤ sizeBase p n r e ∧ e+1 ≤ sizeBase p n r e := by
  have nk : n≤p*n := by simpa using Nat.mul_le_mul_right n hp
  have pk : p≤p*n := by simpa using Nat.mul_le_mul_left p hn
  have de := Nat.lt_two_pow_self (n:=e+1)
  unfold sizeBase
  omega

theorem clusterCard (e : ℕ) : Fintype.card (Cluster e) ≤ (2^(e+1))^3 := by
  simp [Cluster,State,pow_three]
  gcongr
  omega

private theorem columnPoly (M H : ℕ) (hm : 1≤M) (hh : 1≤H) :
    M^3*(M^2*H*2*(2*M^2)*(60+M*(M*13)+M*4+M*13)) +
      (2+M^2*4*7+M^2*H*(4*(M*17))) ≤ 2^14*M^10*H := by
  obtain ⟨u,hu⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le hh
  rw [hu,hv]
  ring_nf
  omega

theorem column_room {p n q : ℕ} (hp : 0<p) (hn : 0<n) (r e : ℕ) (hq : q≤p) :
    FullColumn.cost q e (p*n+1) ≤ columnCost p n r e := by
  let M := sizeBase p n r e
  let H := histBound p e
  obtain ⟨hm,_,pm,wm,dm,_⟩ := params hp hn r e
  have ym : q+1≤M := (Nat.add_le_add_right hq 1).trans pm
  have cm : Fintype.card (Macro q (e+1)) ≤ M^2*H :=
    (histogram_card hq).trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left dm 2))
  have cl : Fintype.card (Cluster e) ≤ M^3 := (clusterCard e).trans (Nat.pow_le_pow_left dm 3)
  unfold FullColumn.cost FreePass.cost columnCost
  calc
    _ ≤ M^3*(M^2*H*2*(2*M^2)*(60+M*(M*13)+M*4+M*13))+
        (2+M^2*4*7+M^2*H*(4*(M*17))) := by
      gcongr
    _ ≤ _ := columnPoly M H hm (hist_pos p e)

private theorem queryPoly (M H : ℕ) (hm : 1≤M) (hh : 1≤H) :
    2^8*M^5+(2+M*(2*M))+M*(2^14*M^10*H)+(2+M^2*(2*M)+M^2*H*(M*17)) ≤
      2^24*M^12*H := by
  obtain ⟨u,hu⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le hh
  rw [hu,hv]
  ring_nf
  omega

theorem query_room {p n : ℕ} (hp : 0<p) (hn : 0<n) (r e l : ℕ) (_hl : l≤p*n) :
    OracleFold.queryCost p n (e+1) l (p*n+1) (columnCost p n r e)
      (BoundaryCircuit.boundaryCost p n (e+1)+2^(e+1)*n*4) ≤ queryCost p n r e := by
  let M := sizeBase p n r e
  let H := histBound p e
  obtain ⟨hm,nm,_,wm,dm,em⟩ := params hp hn r e
  have cm : Fintype.card (Macro (distinguished p n l) (e+1)) ≤ M^2*H :=
    (histogram_card (distinguished_lt hp n l).le).trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left dm 2))
  have bound : BoundaryCircuit.boundaryCost p n (e+1)+2^(e+1)*n*4 ≤ 2^8*M^5 :=
    PanelSetup.boundaryCost_bound p n r (e+1) hp hn
  unfold OracleFold.queryCost columnCost queryCost
  calc
    _ ≤ 2^8*M^5+(2+M*(2*M))+M*(2^14*M^10*H)+(2+M^2*(2*M)+M^2*H*(M*17)) := by
      gcongr
    _ ≤ _ := queryPoly M H hm (hist_pos p e)

theorem queryCost_bound (p n r e : ℕ) :
    queryCost p n r e ≤ 2^56*(p*n+r+2^(e+1)+5)^27*((p+(2^(e+1))^3).choose p) := by
  have hm : 1 ≤ sizeBase p n r e := Nat.le_trans (show 1 ≤ 5 by decide) (Nat.le_add_left 5 _)
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (by decide) (Nat.pow_le_pow_right hm (by decide)))

theorem prepCost_bound {p n : ℕ} (hp : 0<p) (hn : 0<n) (r e : ℕ) :
    PanelSetup.prepCost p n r (e+1) ≤ 2^56*(p*n+r+2^(e+1)+5)^27*((p+(2^(e+1))^3).choose p) := by
  have hm : 1 ≤ sizeBase p n r e := Nat.le_trans (show 1 ≤ 5 by decide) (Nat.le_add_left 5 _)
  calc
    _ ≤ 2^17*(sizeBase p n r e)^5 := PanelSetup.prepCost_bound hp hn r (e+1)
    _ ≤ 2^56*(sizeBase p n r e)^27 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_right hm (by decide))
    _ ≤ _ := Nat.le_mul_of_pos_right _ (hist_pos p e)

end PEqualNP.Outside.L_meta_33676_aux.OracleBudget

namespace PEqualNP.Outside.L_meta_33676_aux.CounterAssembly

open StreamRows InitialDP Ranking PanelSetup OracleFold BranchReport RankedC WeightedCircuit
open PEqualNP.Outside.L_meta_33676_aux.SensorCircuit Builder
open scoped Classical

noncomputable def coeff {s p n : ℕ} (hp : 0<p) (hn : 0<n) (r e : ℕ) : Coeff s p n (e+1) :=
  fun x l b t src dst => if ht : t<n then
    FullColumn.fullStep p l (fun _ => b) ⟨t,ht⟩ (rowBit hp hn r ⟨t,ht⟩)
      (fun u y => EliminationCircuit.bit (residual hp hn r (e+1) l (fun _ => b) u ⟨t,ht⟩ y))
      (FreeColumn.singletonSeed src) dst x else 0

theorem coeff_at {s p n : ℕ} (hp : 0<p) (hn : 0<n) (r e l : ℕ) (h : Env s → ℕ) (i : Fin n)
    (u v : Macro (distinguished p n l) (e+1)) (x : Env s) : coeff hp hn r e x l (h x) i.val u v =
      FullColumn.fullStep p l h i (rowBit hp hn r i)
        (fun u y => EliminationCircuit.bit (residual hp hn r (e+1) l h u i y)) (FreeColumn.singletonSeed u) v x := by
  simp only [coeff,dite_eq_left i.isLt]
  exact (FullColumn.fullStep_prefix hp hn r l h i (FreeColumn.singletonSeed u) v x).symm

theorem realize {p n : ℕ} (hp : 0<p) (hn : 0<n) (hk : n<p*n) (r e : ℕ) (hd : e+1<n) (hr : 4≤r) :
    CounterPackage hp hn r (e+1) := by
  let K := coeff (s:=numInputs p n r) hp hn r e
  refine ⟨OracleFold.output K,OracleBudget.queryCost p n r e,prepCost p n r (e+1),?_,?_,?_⟩
  · obtain ⟨B,eB,cB,b⟩ := prepare hp hn r (e+1)
    refine ⟨B,eB,cB,b.base,emit (cost:=OracleBudget.columnCost p n r e) hp hn hd.le B b K ?_ (OracleBudget.query_room hp hn r e)⟩
    intro l h E setup wh bound res i f prev
    obtain ⟨G,ext,len,w⟩ := FullColumn.grow p l h i (rowBit hp hn r i)
      (fun u y => EliminationCircuit.bit (residual hp hn r (e+1) l h u i y)) f E setup.zero setup.one
      bound wh (rowWires hp hn r E setup i) (fun u => res u i) prev
    have qle : distinguished p n l ≤ p := (min_le_right _ _).trans (Nat.sub_le _ _)
    have room := OracleBudget.column_room hp hn r e qle
    refine ⟨G,ext,len.trans (Nat.add_le_add_left room _),fun v j => MatrixCircuit.has_iff (w v j) fun x => ?_⟩
    apply congrArg (fun a : ℕ => a.testBit j.val)
    rw [FullColumn.fullStep_sum]
    exact Finset.sum_congr rfl (fun u _ => congrArg (fun a => f u x * a) (coeff_at hp hn r e l h i u v x).symm)
  · apply oracleSpec hp hn hk hd hr K
    intro x l h t m v
    by_cases ht : t<n
    · simpa only [K,coeff,dite_eq_left ht] using (FullColumn.fullStep_single hp hn r l (fun _ => h) ⟨t,ht⟩ m v x).symm
    · simp [K,coeff,ht,PanelCount.enabled]
  · have hm : p*n+2≤p*n+r+2^(e+1)+5 := by
      generalize 2^(e+1) = D
      omega
    exact budget_room hm (OracleBudget.hist_pos p e) (OracleBudget.prepCost_bound hp hn r e)
      (OracleBudget.queryCost_bound p n r e)

theorem all_parameters (p n r d : Nat) (hp : 2≤p) (hd : 0<d) (hn : d<n) (hr : 4≤r) :
    CounterPackage (p:=p) (n:=n) (by omega) (by omega) r d := by
  cases d with
  | zero => omega
  | succ e =>
    have hk : n<p*n := by have a := Nat.mul_le_mul_right n hp; omega
    exact realize (by omega) (by omega) hk r e hn hr

end PEqualNP.Outside.L_meta_33676_aux.CounterAssembly

theorem PEqualNP.Outside.L_meta_33676 : (∀ (p n r d : Nat) (hp : 2 ≤ p) (hd : 0 < d) (hn : d < n), 4 ≤ r →
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  let k := p*n
  let D := 2^d
  let W := Fin (2^k)
  let Y := Fin (2^n)
  let rot := fun (h w : Nat) =>
    ((w <<< (h % k)) ||| (w >>> (k - h % k))) % 2^k
  let step := fun (w : Nat) =>
    (List.range k).foldl (fun acc i => acc ||| ((xor (w.testBit i)
      (!(w.testBit ((i+1)%k)) && w.testBit ((i+2)%k))).toNat <<< i)) 0
  let state := fun (col : Bool) (w name : Nat) (c : Fin r → W) =>
    let b := if col then 2 else 1
    (List.finRange r).foldl (fun x j =>
      step (x ^^^ rot b x ^^^ rot (k-b) x) ^^^
        rot (if col then 3*(j.val+1)+1 else 2*j.val) w ^^^ (c j).val)
      (rot (if col then 3 else 1) w ^^^ name)
  let reach := fun col : Bool => if col then 7*r-2 else 5*r-3
  let delay := fun col : Bool => if col then 3*r+1 else 2*r-2
  let bits := fun (a x : Nat) => (List.range a).map (fun i => x.testBit i)
  let sched := fun (c : Fin r → W) => (List.finRange r).flatMap (fun j => bits k (c j).val)
  ∃ A C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo A ∧ PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (3*k+2*r*k+(k+1)+1) A ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (3*k+2*r*k+n+2*(k+1)+1) C ∧
    A.size ≤ 2^40*(k+r+D+5)^13 ∧
    C.size ≤ 2^60*(k+r+D+5)^28*((p+D^3).choose p) ∧
    ∀ (nr nc : W) (cr cc : Fin r → W) (bank : Fin k → Bool) (y : Y)
      (t : Fin (2^(k+1))) (j : Fin (k+1)) (countMode : Bool),
      let valid := ∀ i, reach (bank i) ≤ d
      let report := fun (w : Nat) (i : Fin n) => (List.finRange p).foldl (fun bit a =>
        let pos := a.val*n+i.val
        let col := bank ⟨pos % k, Nat.mod_lt _ (Nat.mul_pos (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hp) (Nat.lt_trans hd hn))⟩
        xor bit ((state col w (if col then nc.val else nr.val)
          (if col then cc else cr)).testBit ((pos+delay col)%k))) false
      let good := fun g : W => ∀ w : W,
        report ((rot n w.val) ^^^ g.val) = report (w.val ^^^ g.val)
      let hit := fun w : W => ∀ i : Fin n, report w.val i = y.val.testBit i.val
      let cfg := bits k nr.val ++ bits k nc.val ++ sched cr ++ sched cc ++ List.ofFn bank
      (A.eval (cfg ++ bits (k+1) j.val ++ [countMode]) =
        decide (valid ∧ (if countMode then (Nat.card {g : W // good g}).testBit j.val = true
          else ∃ g : W, good g ∧ (∀ h : W, good h → g ≤ h) ∧
            (j.val = 0 ∨ g.val.testBit (j.val-1) = true)))) ∧
      (C.eval (cfg ++ bits n y.val ++ bits (k+1) t.val ++ bits (k+1) j.val ++ [countMode]) =
        decide (valid ∧ (∃ g : W, good g) ∧
          (if countMode then (Nat.card {w : W // hit w}).testBit j.val = true else
           ∃ w : W, hit w ∧ Nat.card {z : W // z < w ∧ hit z} = t.val ∧
             (j.val = 0 ∨ w.val.testBit (j.val-1) = true))))) := by
  exact PEqualNP.Outside.L_meta_33676_aux.RankedC.posted_of_counter PEqualNP.Outside.L_meta_33676_aux.CounterAssembly.all_parameters
