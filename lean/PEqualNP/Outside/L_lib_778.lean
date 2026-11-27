import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_778_aux

abbrev W (h : ℕ) := Fin (h + 4) → ZMod 2
abbrev D (h : ℕ) := W h →ₗ[ZMod 2] ZMod 2

def operand (h : ℕ) (x : W h) (i : Fin h) (mask : Fin 32) : ZMod 2 :=
  ∑ j : Fin 5, if mask.val.testBit j.val then x (Fin.ofNat (h + 4) (i.val + j.val)) else 0

def run (h d : ℕ) (ask : Fin d → ℕ → D h) (x : W h) : ℕ :=
  (List.finRange d).foldl (fun tr j => 2 * tr + (if ask j tr x = 0 then 0 else 1)) (0 : ℕ)

def advance (t : ℕ) (st : ℕ × Finset ℕ) (atSite : Fin t → ℕ) : ℕ × Finset ℕ :=
  let extended := (List.finRange t).foldl (fun (s : Finset ℕ) j => s ∪ s.image (fun v => v ^^^ atSite j)) st.2
  let even := extended.filter (fun v => v % 2 = 0)
  (st.1 + (if even = extended then 0 else 1), even.image (fun v => v / 2))

def selectMask (u v : Fin 32) (c : Fin 3) : ℕ :=
  if c.val = 0 then u.val else if c.val = 1 then v.val else u.val ^^^ v.val

def last (h t : ℕ) (a b : Fin h → Fin t → Fin 32) (pick : Fin h → Fin t → Fin 3) : ℕ × Finset ℕ :=
  (List.finRange h).foldl (fun st i => advance t st (fun j => selectMask (a i j) (b i j) (pick i j)))
    ((0, {0}) : ℕ × Finset ℕ)

def enc (h i v : ℕ) : D h :=
  ∑ k : Fin 5, if v.testBit k.val then
    (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin (h + 4) => ZMod 2) (Fin.ofNat (h + 4) (i + k.val))) else 0

theorem enc_apply (h i v : ℕ) (x : W h) :
    enc h i v x = ∑ k : Fin 5, if v.testBit k.val then x (Fin.ofNat (h + 4) (i + k.val)) else 0 := by
  rw [enc, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  split_ifs <;> simp

theorem operand_eq (h : ℕ) (x : W h) (i : Fin h) (m : Fin 32) : operand h x i m = enc h i.val m.val x := by
  rw [enc_apply]; rfl

theorem two_smul_zero (h : ℕ) (p : D h) : p + p = 0 := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.add_apply, LinearMap.zero_apply]; exact CharTwo.add_self_eq_zero _

theorem enc_xor (h i v w : ℕ) : enc h i (v ^^^ w) = enc h i v + enc h i w := by
  simp only [enc, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Nat.testBit_xor]
  cases v.testBit k.val <;> cases w.testBit k.val <;> simp [two_smul_zero]

theorem enc_shift (h i v : ℕ) (hev : v % 2 = 0) (hv : v < 32) : enc h i v = enc h (i + 1) (v / 2) := by
  have b0 : v.testBit 0 = false := by simp [Nat.testBit_zero, hev]
  have b5 : v.testBit 5 = false := Nat.testBit_lt_two_pow (by omega)
  have sh : ∀ k, (v / 2).testBit k = v.testBit (k + 1) := fun k => Nat.testBit_div_two (x := v) (i := k)
  simp only [enc, Fin.sum_univ_five, Fin.val_zero, Fin.val_one, Fin.val_two, sh, b0, b5]
  simp only [show ((3 : Fin 5) : ℕ) = 3 from rfl, show ((4 : Fin 5) : ℕ) = 4 from rfl, add_zero, Nat.add_assoc]
  simp [b5]

def XC (s : Finset ℕ) : Prop := ∀ v ∈ s, ∀ w ∈ s, v ^^^ w ∈ s

def extStep (m : ℕ) (s : Finset ℕ) : Finset ℕ := s ∪ s.image (fun v => v ^^^ m)

theorem extStep_xc {m : ℕ} {s : Finset ℕ} (hs : XC s) : XC (extStep m s) := by
  intro v hv w hw
  simp only [extStep, Finset.mem_union, Finset.mem_image] at hv hw ⊢
  rcases hv with hv | ⟨v', hv', rfl⟩ <;> rcases hw with hw | ⟨w', hw', rfl⟩
  · exact Or.inl (hs v hv w hw)
  · right; refine ⟨v ^^^ w', hs v hv w' hw', ?_⟩; ac_rfl
  · right; refine ⟨v' ^^^ w, hs v' hv' w hw, ?_⟩; ac_rfl
  · left
    have : v' ^^^ m ^^^ (w' ^^^ m) = v' ^^^ w' := by
      calc v' ^^^ m ^^^ (w' ^^^ m) = v' ^^^ w' ^^^ (m ^^^ m) := by ac_rfl
        _ = v' ^^^ w' := by rw [Nat.xor_self, Nat.xor_zero]
    rw [this]; exact hs v' hv' w' hw'

theorem extStep_lt {m : ℕ} {s : Finset ℕ} (hs : ∀ v ∈ s, v < 32) (hm : m < 32) : ∀ v ∈ extStep m s, v < 32 := by
  intro v hv
  simp only [extStep, Finset.mem_union, Finset.mem_image] at hv
  rcases hv with hv | ⟨v', hv', rfl⟩
  · exact hs v hv
  · exact Nat.xor_lt_two_pow (n := 5) (hs v' hv') hm

theorem extStep_span (h n m : ℕ) {s : Finset ℕ} (h0 : 0 ∈ s) :
    Submodule.span (ZMod 2) (enc h n '' (extStep m s : Set ℕ)) =
      Submodule.span (ZMod 2) (enc h n '' (s : Set ℕ)) ⊔ Submodule.span (ZMod 2) {enc h n m} := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    simp only [extStep, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image, Finset.mem_coe] at hv
    rcases hv with hv | ⟨v', hv', rfl⟩
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨v, hv, rfl⟩)
    · rw [enc_xor]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨v', hv', rfl⟩) (Submodule.subset_span rfl)
  · apply sup_le
    · apply Submodule.span_mono
      exact Set.image_mono (fun v hv => by simp [extStep, Finset.mem_coe.1 hv])
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      apply Submodule.subset_span
      refine ⟨0 ^^^ m, ?_, by rw [Nat.zero_xor]⟩
      simp only [extStep, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image, Finset.mem_coe]
      exact Or.inr ⟨0, h0, rfl⟩

theorem extFold (h n t : ℕ) (ms : Fin t → ℕ) (hms : ∀ j, ms j < 32) :
    ∀ (L : List (Fin t)) (s : Finset ℕ), XC s → 0 ∈ s → (∀ v ∈ s, v < 32) →
      XC (L.foldl (fun s j => extStep (ms j) s) s) ∧ 0 ∈ L.foldl (fun s j => extStep (ms j) s) s ∧
      s ⊆ L.foldl (fun s j => extStep (ms j) s) s ∧
      (∀ v ∈ L.foldl (fun s j => extStep (ms j) s) s, v < 32) ∧
      Submodule.span (ZMod 2) (enc h n '' ((L.foldl (fun s j => extStep (ms j) s) s : Finset ℕ) : Set ℕ)) =
        Submodule.span (ZMod 2) (enc h n '' (s : Set ℕ)) ⊔
          Submodule.span (ZMod 2) {f | ∃ j ∈ L, f = enc h n (ms j)} := by
  intro L
  induction L with
  | nil =>
    intro s hs h0 hlt
    simp only [List.foldl_nil]
    refine ⟨hs, h0, subset_rfl, hlt, ?_⟩
    simp
  | cons j L ih =>
    intro s hs h0 hlt
    have h0' : 0 ∈ extStep (ms j) s := by simp [extStep, h0]
    obtain ⟨a1, a2, a3, a4, a5⟩ := ih (extStep (ms j) s) (extStep_xc hs) h0' (extStep_lt hlt (hms j))
    simp only [List.foldl_cons]
    refine ⟨a1, a2, (Finset.subset_union_left : s ⊆ extStep (ms j) s).trans a3, a4, ?_⟩
    rw [a5, extStep_span h n (ms j) h0, sup_assoc]
    congr 1
    rw [← Submodule.span_union]
    congr 1
    ext f; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, List.mem_cons]
    constructor
    · rintro (rfl | ⟨j', hj', rfl⟩)
      · exact ⟨j, Or.inl rfl, rfl⟩
      · exact ⟨j', Or.inr hj', rfl⟩
    · rintro ⟨j', hj' | hj', rfl⟩
      · subst hj'; exact Or.inl rfl
      · exact Or.inr ⟨j', hj', rfl⟩

theorem enc_zero (h i : ℕ) : enc h i 0 = 0 := by simp [enc]

def uvec (h c : ℕ) : W h := Pi.single (Fin.ofNat (h + 4) c) (1 : ZMod 2)

theorem ofNat_eq_iff (h p q : ℕ) (hp : p < h + 4) (hq : q < h + 4) :
    Fin.ofNat (h + 4) p = Fin.ofNat (h + 4) q ↔ p = q := by
  rw [Fin.ext_iff, Fin.val_ofNat, Fin.val_ofNat, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq]

theorem enc_ev (h i v c : ℕ) : enc h i v (uvec h c) =
    ∑ k : Fin 5, if v.testBit k.val then (if Fin.ofNat (h + 4) (i + k.val) = Fin.ofNat (h + 4) c then 1 else 0) else 0 := by
  rw [enc_apply]; refine Finset.sum_congr rfl (fun k _ => ?_); simp [uvec, Pi.single_apply]

theorem enc_ev_self (h n v : ℕ) (hn : n < h) : enc h n v (uvec h n) = if v.testBit 0 then 1 else 0 := by
  rw [enc_ev, Fin.sum_univ_five]
  simp (disch := omega) only [ofNat_eq_iff, Fin.val_zero, Fin.val_one, Fin.val_two,
    show ((3 : Fin 5) : ℕ) = 3 from rfl, show ((4 : Fin 5) : ℕ) = 4 from rfl]
  simp

theorem enc_ev_other (h n i v : ℕ) (hni : n < i) (hi : i < h) : enc h i v (uvec h n) = 0 := by
  rw [enc_ev]
  apply Finset.sum_eq_zero
  intro k _
  have hk := k.isLt
  have hne : i + k.val ≠ n := by omega
  simp (disch := omega) only [ofNat_eq_iff, hne, if_false, ite_self]

theorem enc_ev_top (h v k : ℕ) (hv : v < 16) (hk : k < 4) : enc h h v (uvec h (h + k)) = if v.testBit k then 1 else 0 := by
  rw [enc_ev]
  have b4 : v.testBit 4 = false := Nat.testBit_lt_two_pow (by omega)
  rw [Fin.sum_univ_five]
  simp (disch := omega) only [Fin.val_zero, Fin.val_one, Fin.val_two, show ((3 : Fin 5) : ℕ) = 3 from rfl,
    show ((4 : Fin 5) : ℕ) = 4 from rfl, b4, Bool.false_eq_true, if_false, add_zero, ofNat_eq_iff]
  interval_cases k <;> simp

theorem finrank_sup_single {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (S : Submodule (ZMod 2) V) (u : V) (hu : u ∉ S) :
    Module.finrank (ZMod 2) ↥(S ⊔ Submodule.span (ZMod 2) {u}) = Module.finrank (ZMod 2) S + 1 := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ S.zero_mem)
  have hd : Disjoint S (Submodule.span (ZMod 2) {u}) := (Submodule.disjoint_span_singleton' hu0).2 hu
  have := Submodule.finrank_sup_add_finrank_inf_eq S (Submodule.span (ZMod 2) {u})
  rw [hd.eq_bot, finrank_bot, add_zero, finrank_span_singleton hu0] at this
  exact this

theorem img_addm (h : ℕ) {B : Finset ℕ} (hx : XC B) {f g : D h} (hf : f ∈ enc h h '' (B : Set ℕ))
    (hg : g ∈ enc h h '' (B : Set ℕ)) : f + g ∈ enc h h '' (B : Set ℕ) := by
  obtain ⟨v, hv, rfl⟩ := hf
  obtain ⟨w, hw, rfl⟩ := hg
  exact ⟨v ^^^ w, hx v hv w hw, enc_xor h h v w⟩

theorem img_smulm (h : ℕ) {B : Finset ℕ} (h0 : 0 ∈ B) (c : ZMod 2) {f : D h} (hf : f ∈ enc h h '' (B : Set ℕ)) :
    c • f ∈ enc h h '' (B : Set ℕ) := by
  obtain ⟨v, hv, rfl⟩ := hf
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases h01 c with rfl | rfl
  · exact ⟨0, h0, by rw [enc_zero, zero_smul]⟩
  · exact ⟨v, hv, by rw [one_smul]⟩

def imgSub (h : ℕ) (B : Finset ℕ) (hx : XC B) (h0 : 0 ∈ B) : Submodule (ZMod 2) (D h) :=
  { carrier := enc h h '' (B : Set ℕ), add_mem' := fun hf hg => img_addm h hx hf hg, zero_mem' := ⟨0, h0, enc_zero h h⟩, smul_mem' := fun c _ hf => img_smulm h h0 c hf }

theorem enc_top_inj (h : ℕ) {v w : ℕ} (hv : v < 16) (hw : w < 16) (he : enc h h v = enc h h w) : v = w := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 4
  · have h1 := enc_ev_top h v k hv hk
    have h2 := enc_ev_top h w k hw hk
    rw [he, h2] at h1
    cases hv' : v.testBit k <;> cases hw' : w.testBit k <;> simp_all
  · have h16 : 16 ≤ 2 ^ k := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hv h16), Nat.testBit_lt_two_pow (lt_of_lt_of_le hw h16)]

theorem finrank_top (h : ℕ) (B : Finset ℕ) (hx : XC B) (h0 : 0 ∈ B) (hlt : ∀ v ∈ B, v < 16) :
    Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) (enc h h '' (B : Set ℕ))) = Nat.log2 B.card := by
  have hsp : Submodule.span (ZMod 2) (enc h h '' (B : Set ℕ)) = imgSub h B hx h0 :=
    Submodule.span_eq (imgSub h B hx h0)
  rw [hsp]
  have : Finite (D h) := Module.finite_of_finite (ZMod 2)
  haveI : Fintype ↥(imgSub h B hx h0) := Fintype.ofFinite _
  have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := ↥(imgSub h B hx h0))
  rw [ZMod.card] at hc
  have hcard : Fintype.card ↥(imgSub h B hx h0) = B.card := by
    rw [← Nat.card_eq_fintype_card]
    have : Nat.card ↥(imgSub h B hx h0) = Nat.card ↥(enc h h '' (B : Set ℕ)) := rfl
    have hinj : Set.InjOn (enc h h) (B : Set ℕ) := by
      intro v hv w hw he; exact enc_top_inj h (hlt v hv) (hlt w hw) he
    rw [this, Nat.card_coe_set_eq, hinj.ncard_image, Set.ncard_coe_finset]
  rw [hcard] at hc
  rw [hc, Nat.log2_two_pow]

section Sweep
variable (h t : ℕ) (a b : Fin h → Fin t → Fin 32) (pick : Fin h → Fin t → Fin 3)

def sel (i : Fin h) (j : Fin t) : ℕ := selectMask (a i j) (b i j) (pick i j)

theorem sel_lt (i : Fin h) (j : Fin t) : sel h t a b pick i j < 32 := by
  unfold sel selectMask
  split_ifs
  · exact (a i j).isLt
  · exact (b i j).isLt
  · exact Nat.xor_lt_two_pow (n := 5) (a i j).isLt (b i j).isLt

def Rest (n : ℕ) : Set (D h) := {f | ∃ (i : Fin h) (j : Fin t), n ≤ i.val ∧ f = enc h i.val (sel h t a b pick i j)}

def Gs (n : ℕ) (B : Finset ℕ) : Submodule (ZMod 2) (D h) :=
  Submodule.span (ZMod 2) (enc h n '' (B : Set ℕ) ∪ Rest h t a b pick n)

def stepF (st : ℕ × Finset ℕ) (i : Fin h) : ℕ × Finset ℕ := advance t st (fun j => sel h t a b pick i j)

def lastN (n : ℕ) : ℕ × Finset ℕ := ((List.finRange h).take n).foldl (stepF h t a b pick) ((0, {0}) : ℕ × Finset ℕ)

theorem lastN_succ (n : ℕ) (hn : n < h) : lastN h t a b pick (n + 1) = stepF h t a b pick (lastN h t a b pick n) ⟨n, hn⟩ := by
  unfold lastN
  rw [List.take_succ, List.foldl_append]
  have : (List.finRange h)[n]? = some ⟨n, hn⟩ := by
    rw [List.getElem?_eq_getElem (by rw [List.length_finRange]; exact hn)]
    congr 1; exact Fin.ext (by simp)
  rw [this]; rfl

theorem last_eq : last h t a b pick = lastN h t a b pick h := by
  unfold last lastN; rw [List.take_of_length_le (by simp)]; rfl

theorem rest_split (n : ℕ) (hn : n < h) : Rest h t a b pick n =
    {f | ∃ j ∈ List.finRange t, f = enc h n (sel h t a b pick ⟨n, hn⟩ j)} ∪ Rest h t a b pick (n + 1) := by
  ext f
  simp only [Rest, Set.mem_union, Set.mem_setOf_eq, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, j, hi, rfl⟩
    by_cases hin : i.val = n
    · left; refine ⟨j, ?_⟩; have : i = ⟨n, hn⟩ := Fin.ext hin; subst this; rfl
    · right; exact ⟨i, j, by omega, rfl⟩
  · rintro (⟨j, rfl⟩ | ⟨i, j, hi, rfl⟩)
    · exact ⟨⟨n, hn⟩, j, le_rfl, rfl⟩
    · exact ⟨i, j, by omega, rfl⟩

theorem rest_top : Rest h t a b pick h = ∅ := by
  ext f; simp only [Rest, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨i, j, hi, -⟩; have := i.isLt; omega

theorem xor_div_two (v w : ℕ) : (v ^^^ w) / 2 = v / 2 ^^^ w / 2 := by
  apply Nat.eq_of_testBit_eq; intro k; simp [Nat.testBit_div_two]

theorem xor_mod_two (v w : ℕ) : (v ^^^ w) % 2 = (v % 2 + w % 2) % 2 := by
  have h1 : (v ^^^ w).testBit 0 = (v.testBit 0 ^^ w.testBit 0) := Nat.testBit_xor v w 0
  simp only [Nat.testBit_zero] at h1
  rcases Nat.mod_two_eq_zero_or_one v with hv | hv <;> rcases Nat.mod_two_eq_zero_or_one w with hw | hw <;>
    rcases Nat.mod_two_eq_zero_or_one (v ^^^ w) with hx | hx <;> simp_all

theorem step (n : ℕ) (hn : n < h) (st : ℕ × Finset ℕ) (hx : XC st.2) (h0 : 0 ∈ st.2) (hlt : ∀ v ∈ st.2, v < 16) :
    XC (stepF h t a b pick st ⟨n, hn⟩).2 ∧ 0 ∈ (stepF h t a b pick st ⟨n, hn⟩).2 ∧
    (∀ v ∈ (stepF h t a b pick st ⟨n, hn⟩).2, v < 16) ∧
    (stepF h t a b pick st ⟨n, hn⟩).1 + Module.finrank (ZMod 2) ↥(Gs h t a b pick (n + 1) (stepF h t a b pick st ⟨n, hn⟩).2) =
      st.1 + Module.finrank (ZMod 2) ↥(Gs h t a b pick n st.2) := by
  set ms : Fin t → ℕ := fun j => sel h t a b pick ⟨n, hn⟩ j with hms
  have hms32 : ∀ j, ms j < 32 := fun j => sel_lt h t a b pick _ j
  set E := (List.finRange t).foldl (fun s j => extStep (ms j) s) st.2 with hE
  obtain ⟨eX, e0, eSub, eLt, eSpan⟩ := extFold h n t ms hms32 (List.finRange t) st.2 hx h0
    (fun v hv => by have := hlt v hv; omega)
  rw [← hE] at eX e0 eSub eLt eSpan
  set ev := E.filter (fun v => v % 2 = 0) with hev
  have hstep : stepF h t a b pick st ⟨n, hn⟩ = (st.1 + (if ev = E then 0 else 1), ev.image (fun v => v / 2)) := rfl
  rw [hstep]
  simp only

  have bX : XC (ev.image (fun v => v / 2)) := by
    intro v' hv' w' hw'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hv'
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hw'
    rw [hev, Finset.mem_filter] at hv hw
    refine Finset.mem_image.2 ⟨v ^^^ w, ?_, xor_div_two v w⟩
    rw [hev, Finset.mem_filter]
    refine ⟨eX v hv.1 w hw.1, ?_⟩
    rw [xor_mod_two, hv.2, hw.2]
  have b0 : 0 ∈ ev.image (fun v => v / 2) :=
    Finset.mem_image.2 ⟨0, by rw [hev, Finset.mem_filter]; exact ⟨e0, rfl⟩, rfl⟩
  have bLt : ∀ v ∈ ev.image (fun v => v / 2), v < 16 := by
    intro v' hv'; obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hv'
    have := eLt v (Finset.mem_filter.1 hv).1; omega
  refine ⟨bX, b0, bLt, ?_⟩

  have hGn : Gs h t a b pick n st.2 =
      Submodule.span (ZMod 2) (enc h n '' (E : Set ℕ)) ⊔ Submodule.span (ZMod 2) (Rest h t a b pick (n + 1)) := by
    unfold Gs
    rw [rest_split h t a b pick n hn, ← Set.union_assoc, Submodule.span_union, Submodule.span_union, eSpan]
  have himg : enc h (n + 1) '' ((ev.image (fun v => v / 2) : Finset ℕ) : Set ℕ) = enc h n '' (ev : Set ℕ) := by
    ext f
    simp only [Set.mem_image, Finset.coe_image, Finset.mem_coe]
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      have hv' := Finset.mem_filter.1 hv
      exact ⟨v, hv, (enc_shift h n v hv'.2 (eLt v hv'.1))⟩
    · rintro ⟨v, hv, rfl⟩
      have hv' := Finset.mem_filter.1 hv
      exact ⟨v / 2, ⟨v, hv, rfl⟩, (enc_shift h n v hv'.2 (eLt v hv'.1)).symm⟩
  have hGn1 : Gs h t a b pick (n + 1) (ev.image (fun v => v / 2)) =
      Submodule.span (ZMod 2) (enc h n '' (ev : Set ℕ)) ⊔ Submodule.span (ZMod 2) (Rest h t a b pick (n + 1)) := by
    unfold Gs; rw [Submodule.span_union, himg]
  by_cases hsame : ev = E
  · rw [if_pos hsame, hGn, hGn1, hsame, Nat.add_zero]
  · rw [if_neg hsame]
    obtain ⟨v0, hv0E, hv0⟩ : ∃ v0 ∈ E, v0 % 2 ≠ 0 := by
      by_contra hc; push_neg at hc
      exact hsame (Finset.filter_true_of_mem hc)
    have hodd : v0 % 2 = 1 := by omega

    have hker : Gs h t a b pick (n + 1) (ev.image (fun v => v / 2)) ≤
        LinearMap.ker (LinearMap.applyₗ (R := ZMod 2) (uvec h n) : D h →ₗ[ZMod 2] ZMod 2) := by
      rw [hGn1, sup_le_iff, Submodule.span_le, Submodule.span_le]
      constructor
      · rintro _ ⟨v, hv, rfl⟩
        have hv' := Finset.mem_filter.1 (Finset.mem_coe.1 hv)
        simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.applyₗ_apply_apply]
        rw [enc_ev_self h n v hn]; simp [Nat.testBit_zero, hv'.2]
      · rintro _ ⟨i, j, hi, rfl⟩
        simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.applyₗ_apply_apply]
        exact enc_ev_other h n i.val _ (by omega) i.isLt
    have hnot : enc h n v0 ∉ Gs h t a b pick (n + 1) (ev.image (fun v => v / 2)) := by
      intro hm
      have := hker hm
      simp only [LinearMap.mem_ker, LinearMap.applyₗ_apply_apply] at this
      rw [enc_ev_self h n v0 hn] at this
      simp [Nat.testBit_zero, hodd] at this
    have hsup : Gs h t a b pick n st.2 =
        Gs h t a b pick (n + 1) (ev.image (fun v => v / 2)) ⊔ Submodule.span (ZMod 2) {enc h n v0} := by
      apply le_antisymm
      · rw [hGn, sup_le_iff]
        constructor
        · rw [Submodule.span_le]
          rintro _ ⟨v, hv, rfl⟩
          by_cases hve : v % 2 = 0
          · apply Submodule.mem_sup_left
            rw [hGn1]
            exact Submodule.mem_sup_left (Submodule.subset_span ⟨v, Finset.mem_coe.2
              (Finset.mem_filter.2 ⟨Finset.mem_coe.1 hv, hve⟩), rfl⟩)
          · have hw : v ^^^ v0 ∈ ev := by
              rw [hev, Finset.mem_filter]
              refine ⟨eX v (Finset.mem_coe.1 hv) v0 hv0E, ?_⟩
              rw [xor_mod_two]; omega
            have hv_eq : v = (v ^^^ v0) ^^^ v0 := by
              rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
            rw [hv_eq, enc_xor]
            refine Submodule.add_mem_sup ?_ (Submodule.subset_span rfl)
            rw [hGn1]
            exact Submodule.mem_sup_left (Submodule.subset_span ⟨_, Finset.mem_coe.2 hw, rfl⟩)
        · rw [hGn1]; exact le_sup_of_le_left le_sup_right
      · rw [sup_le_iff, hGn1, hGn, sup_le_iff]
        refine ⟨⟨le_sup_of_le_left (Submodule.span_mono (Set.image_mono
          (fun v hv => Finset.mem_coe.2 (Finset.mem_filter.1 (Finset.mem_coe.1 hv)).1))), le_sup_right⟩, ?_⟩
        rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.mem_sup_left (Submodule.subset_span ⟨v0, Finset.mem_coe.2 hv0E, rfl⟩)
    rw [hsup, finrank_sup_single _ _ hnot]
    ring

theorem sweep_eq : (last h t a b pick).1 + Nat.log2 (last h t a b pick).2.card =
    Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) (Rest h t a b pick 0)) := by
  have inv : ∀ n ≤ h, XC (lastN h t a b pick n).2 ∧ 0 ∈ (lastN h t a b pick n).2 ∧
      (∀ v ∈ (lastN h t a b pick n).2, v < 16) ∧
      (lastN h t a b pick n).1 + Module.finrank (ZMod 2) ↥(Gs h t a b pick n (lastN h t a b pick n).2) =
        Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) (Rest h t a b pick 0)) := by
    intro n
    induction n with
    | zero =>
      intro _
      have h00 : lastN h t a b pick 0 = ((0, {0}) : ℕ × Finset ℕ) := by simp [lastN]
      rw [h00]
      refine ⟨fun v hv w hw => by simp_all, by simp, by simp, ?_⟩
      rw [zero_add]
      show Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2)
        (enc h 0 '' (((({0} : Finset ℕ)) : Set ℕ)) ∪ Rest h t a b pick 0)) = _
      have e : enc h 0 '' (((({0} : Finset ℕ)) : Set ℕ)) ∪ Rest h t a b pick 0 = insert 0 (Rest h t a b pick 0) := by
        ext f; simp [enc_zero, eq_comm]
      rw [e, Submodule.span_insert_zero]
    | succ n ih =>
      intro hn
      obtain ⟨i1, i2, i3, i4⟩ := ih (by omega)
      rw [lastN_succ h t a b pick n (by omega)]
      obtain ⟨s1, s2, s3, s4⟩ := step h t a b pick n (by omega) _ i1 i2 i3
      exact ⟨s1, s2, s3, by rw [s4, i4]⟩
  obtain ⟨i1, i2, i3, i4⟩ := inv h le_rfl
  rw [last_eq, ← i4]
  congr 1
  unfold Gs
  rw [rest_top, Set.union_empty, finrank_top h _ i1 i2 i3]

end Sweep

theorem z2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
theorem z2_sq : ∀ c : ZMod 2, c * c = c := by decide
theorem z2_lemma1 : ∀ p q r u : ZMod 2, p * q + r * u = 0 → r = 1 → u = p * q := by decide
theorem z2_lemma2 : ∀ p q s : ZMod 2, p + q = s → p * q = (s + 1) * p := by decide

theorem run_zero (h d : ℕ) (ask : Fin d → ℕ → D h) (x : W h) (hx : ∀ j, ask j 0 x = 0) : run h d ask x = 0 := by
  unfold run
  suffices ∀ L : List (Fin d), L.foldl (fun tr j => 2 * tr + (if ask j tr x = 0 then 0 else 1)) 0 = 0 from this _
  intro L
  induction L with
  | nil => rfl
  | cons j L ih => simp only [List.foldl_cons]; rw [hx j]; simpa using ih

theorem fold_inj {ι : Type} (bf cf : ι → ℕ) (hb : ∀ j, bf j ≤ 1) (hc : ∀ j, cf j ≤ 1) :
    ∀ (L : List ι), L.foldl (fun tr j => 2 * tr + bf j) 0 = L.foldl (fun tr j => 2 * tr + cf j) 0 →
      ∀ j ∈ L, bf j = cf j := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro _ j hj; simp at hj
  | append_singleton L j ih =>
    intro he k hk
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at he
    have hbj := hb j; have hcj := hc j
    have e1 : bf j = cf j := by omega
    have e2 : L.foldl (fun tr j => 2 * tr + bf j) 0 = L.foldl (fun tr j => 2 * tr + cf j) 0 := by omega
    rcases List.mem_append.1 hk with hk | hk
    · exact ih e2 k hk
    · rw [List.mem_singleton.1 hk]; exact e1

theorem strat_to_pick (h t : ℕ) (a b : Fin h → Fin t → Fin 32) (d : ℕ) (ask : Fin d → ℕ → D h)
    (readout : ℕ → Fin h → Fin t → D h) (bias : ℕ → Fin h → Fin t → ZMod 2)
    (hv : ∀ x i j, operand h x i (a i j) * operand h x i (b i j) = readout (run h d ask x) i j x + bias (run h d ask x) i j) :
    ∃ pick : Fin h → Fin t → Fin 3, (last h t a b pick).1 + Nat.log2 (last h t a b pick).2.card ≤ d := by
  classical
  let K : W h → Prop := fun x => ∀ j, ask j 0 x = 0
  have hK0 : K 0 := fun j => by simp
  have hKadd : ∀ x y, K x → K y → K (x + y) := fun x y hx hy j => by simp [hx j, hy j]

  have hlin : ∀ i j x, K x → enc h i.val (a i j).val x * enc h i.val (b i j).val x = readout 0 i j x := by
    intro i j x hx
    have h1 := hv x i j
    have h0 := hv 0 i j
    rw [run_zero h d ask x hx] at h1
    rw [run_zero h d ask 0 hK0] at h0
    rw [operand_eq, operand_eq] at h1 h0
    simp only [map_zero, mul_zero, zero_add] at h0
    rw [h1, ← h0, add_zero]
  have hcross : ∀ i j x y, K x → K y →
      enc h i.val (a i j).val x * enc h i.val (b i j).val y + enc h i.val (a i j).val y * enc h i.val (b i j).val x = 0 := by
    intro i j x y hx hy
    have e := hlin i j (x + y) (hKadd x y hx hy)
    rw [map_add, map_add, map_add, ← hlin i j x hx, ← hlin i j y hy] at e
    have : ∀ p q r u : ZMod 2, (p + r) * (q + u) = p * q + r * u → p * u + r * q = 0 := by decide
    exact this _ _ _ _ e
  let pick : Fin h → Fin t → Fin 3 := fun i j =>
    if (∀ x, K x → enc h i.val (a i j).val x = 0) then 0
    else if (∀ x, K x → enc h i.val (b i j).val x = 0) then 1 else 2
  refine ⟨pick, ?_⟩
  rw [sweep_eq]

  have hvan : ∀ i j x, K x → enc h i.val (sel h t a b pick i j) x = 0 := by
    intro i j x hx
    by_cases hA : ∀ x, K x → enc h i.val (a i j).val x = 0
    · have hp : pick i j = 0 := if_pos hA
      have : sel h t a b pick i j = (a i j).val := by unfold sel selectMask; rw [hp]; rfl
      rw [this]; exact hA x hx
    · by_cases hB : ∀ x, K x → enc h i.val (b i j).val x = 0
      · have hp : pick i j = 1 := by show (if _ then _ else _) = _; rw [if_neg hA, if_pos hB]
        have : sel h t a b pick i j = (b i j).val := by unfold sel selectMask; rw [hp]; rfl
        rw [this]; exact hB x hx
      · have hp : pick i j = 2 := by show (if _ then _ else _) = _; rw [if_neg hA, if_neg hB]
        have : sel h t a b pick i j = (a i j).val ^^^ (b i j).val := by unfold sel selectMask; rw [hp]; rfl
        rw [this, enc_xor, LinearMap.add_apply]
        push_neg at hA hB
        obtain ⟨y0, hy0, hay0⟩ := hA
        obtain ⟨y1, hy1, hby1⟩ := hB
        have hay : enc h i.val (a i j).val y0 = 1 := by rcases z2_cases (enc h i.val (a i j).val y0) with e | e <;> simp_all
        have hbx : ∀ z, K z → enc h i.val (b i j).val z = enc h i.val (a i j).val z * enc h i.val (b i j).val y0 :=
          fun z hz => z2_lemma1 _ _ _ _ (hcross i j z y0 hz hy0) hay
        have hby0 : enc h i.val (b i j).val y0 = 1 := by
          rcases z2_cases (enc h i.val (b i j).val y0) with e | e
          · exfalso; apply hby1; rw [hbx y1 hy1, e, mul_zero]
          · exact e
        rw [hbx x hx, hby0, mul_one]; exact CharTwo.add_self_eq_zero _

  have hle : Submodule.span (ZMod 2) (Rest h t a b pick 0) ≤
      Submodule.span (ZMod 2) (Set.range (fun j : Fin d => ask j 0)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, j, -, rfl⟩
    apply mem_span_of_iInf_ker_le_ker
    intro x hx
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hx
    exact hvan i j x hx
  calc Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) (Rest h t a b pick 0))
      ≤ Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) (Set.range (fun j : Fin d => ask j 0))) :=
        Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin d) := finrank_range_le_card _
    _ = d := Fintype.card_fin d

theorem z2_bit_inj : ∀ u w : ZMod 2, (if u = 0 then 0 else 1 : ℕ) = (if w = 0 then 0 else 1 : ℕ) → u = w := by decide

theorem pick_to_strat (h t : ℕ) (a b : Fin h → Fin t → Fin 32) (d : ℕ) (pick : Fin h → Fin t → Fin 3)
    (hp : (last h t a b pick).1 + Nat.log2 (last h t a b pick).2.card ≤ d) :
    ∃ (ask : Fin d → ℕ → D h) (readout : ℕ → Fin h → Fin t → D h) (bias : ℕ → Fin h → Fin t → ZMod 2),
      ∀ x i j, operand h x i (a i j) * operand h x i (b i j) =
        readout (run h d ask x) i j x + bias (run h d ask x) i j := by
  classical
  rw [sweep_eq] at hp
  set C := Submodule.span (ZMod 2) (Rest h t a b pick 0) with hC
  have : Module.Free (ZMod 2) ↥C := Module.Free.of_divisionRing (ZMod 2) ↥C
  let bas := Module.finBasis (ZMod 2) ↥C
  let e : Fin d → D h := fun j => if hj : j.val < Module.finrank (ZMod 2) ↥C then (bas ⟨j.val, hj⟩ : D h) else 0
  have hCe : C ≤ Submodule.span (ZMod 2) (Set.range e) := by
    intro f hf
    have hspan := bas.mem_span (⟨f, hf⟩ : ↥C)
    have hm := Submodule.apply_mem_span_image_of_mem_span C.subtype hspan
    refine Submodule.span_mono ?_ hm
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨⟨k.val, lt_of_lt_of_le k.isLt hp⟩, ?_⟩
    simp only [e, dif_pos k.isLt]
    rfl
  let ask : Fin d → ℕ → D h := fun j _ => e j
  let rep : ℕ → W h := fun τ => if hτ : ∃ x, run h d ask x = τ then Classical.choose hτ else 0
  have hrep : ∀ x, run h d ask (rep (run h d ask x)) = run h d ask x := by
    intro x
    have hτ : ∃ y, run h d ask y = run h d ask x := ⟨x, rfl⟩
    simp only [rep, dif_pos hτ]; exact Classical.choose_spec hτ
  have hsame : ∀ x, ∀ φ ∈ Submodule.span (ZMod 2) (Set.range e), φ x = φ (rep (run h d ask x)) := by
    intro x φ hφ
    have hbits : ∀ j : Fin d, e j x = e j (rep (run h d ask x)) := by
      intro j
      have hr := hrep x
      have hfold := fold_inj (fun j => if e j (rep (run h d ask x)) = 0 then 0 else 1)
        (fun j => if e j x = 0 then 0 else 1) (fun j => by split_ifs <;> omega) (fun j => by split_ifs <;> omega)
        (List.finRange d) hr j (List.mem_finRange j)
      exact (z2_bit_inj _ _ hfold).symm
    let L : D h →ₗ[ZMod 2] ZMod 2 := LinearMap.applyₗ (R := ZMod 2) x - LinearMap.applyₗ (R := ZMod 2) (rep (run h d ask x))
    have hle : Submodule.span (ZMod 2) (Set.range e) ≤ LinearMap.ker L := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, L, LinearMap.sub_apply, LinearMap.applyₗ_apply_apply, hbits j,
        sub_self]
    have := hle hφ
    simp only [LinearMap.mem_ker, L, LinearMap.sub_apply, LinearMap.applyₗ_apply_apply] at this
    exact sub_eq_zero.1 this
  have hchosen : ∀ i j, enc h i.val (sel h t a b pick i j) ∈ Submodule.span (ZMod 2) (Set.range e) :=
    fun i j => hCe (Submodule.subset_span ⟨i, j, Nat.zero_le _, rfl⟩)
  let readout : ℕ → Fin h → Fin t → D h := fun τ i j =>
    if (pick i j).val = 0 then (enc h i.val (a i j).val (rep τ)) • enc h i.val (b i j).val
    else if (pick i j).val = 1 then (enc h i.val (b i j).val (rep τ)) • enc h i.val (a i j).val
    else ((enc h i.val (a i j).val + enc h i.val (b i j).val) (rep τ) + 1) • enc h i.val (a i j).val
  refine ⟨ask, readout, fun _ _ _ => 0, fun x i j => ?_⟩
  rw [operand_eq, operand_eq, add_zero]
  have hc := hchosen i j
  simp only [readout]
  by_cases h0 : (pick i j).val = 0
  · have hsel : sel h t a b pick i j = (a i j).val := by simp [sel, selectMask, h0]
    rw [hsel] at hc
    rw [if_pos h0, LinearMap.smul_apply, smul_eq_mul, ← hsame x _ hc]
  · by_cases h1 : (pick i j).val = 1
    · have hsel : sel h t a b pick i j = (b i j).val := by simp [sel, selectMask, h1]
      rw [hsel] at hc
      rw [if_neg h0, if_pos h1, LinearMap.smul_apply, smul_eq_mul, ← hsame x _ hc, mul_comm]
    · have hsel : sel h t a b pick i j = (a i j).val ^^^ (b i j).val := by simp [sel, selectMask, h0, h1]
      rw [hsel, enc_xor] at hc
      rw [if_neg h0, if_neg h1, LinearMap.smul_apply, smul_eq_mul, ← hsame x _ hc]
      exact z2_lemma2 _ _ _ (by rw [LinearMap.add_apply])

theorem main (h t : ℕ) (a b : Fin h → Fin t → Fin 32) (d : ℕ) :
    (∃ (ask : Fin d → ℕ → D h) (readout : ℕ → Fin h → Fin t → D h) (bias : ℕ → Fin h → Fin t → ZMod 2),
      ∀ x i j, operand h x i (a i j) * operand h x i (b i j) =
        readout (run h d ask x) i j x + bias (run h d ask x) i j) ↔
    ∃ pick : Fin h → Fin t → Fin 3, (last h t a b pick).1 + Nat.log2 (last h t a b pick).2.card ≤ d := by
  constructor
  · rintro ⟨ask, readout, bias, hv⟩
    exact strat_to_pick h t a b d ask readout bias hv
  · rintro ⟨pick, hp⟩
    exact pick_to_strat h t a b d pick hp

end PEqualNP.Outside.L_lib_778_aux

open PEqualNP.Outside.L_lib_778_aux in
theorem PEqualNP.Outside.L_lib_778 : (∀ (h t : ℕ) (a b : Fin h → Fin t → Fin 32) (d : ℕ),
  let F := ZMod 2
  let W := Fin (h+4) → F
  let D := W →ₗ[F] F
  let operand := fun (x : W) (i : Fin h) (mask : Fin 32) =>
    ∑ j : Fin 5, if mask.val.testBit j.val then x (Fin.ofNat (h+4) (i.val+j.val)) else 0
  let run := fun (ask : Fin d → ℕ → D) (x : W) =>
    (List.finRange d).foldl (fun tr j => 2*tr + (if ask j tr x = 0 then 0 else 1)) (0 : ℕ)
  let advance := fun (st : ℕ × Finset ℕ) (atSite : Fin t → ℕ) =>
    let extended := (List.finRange t).foldl (fun (s : Finset ℕ) j =>
      s ∪ s.image (fun v => v ^^^ atSite j)) st.2
    let even := extended.filter (fun v => v % 2 = 0)
    (st.1 + (if even = extended then 0 else 1), even.image (fun v => v / 2))
  let selectMask := fun (u v : Fin 32) (c : Fin 3) =>
    if c.val = 0 then u.val else if c.val = 1 then v.val else u.val ^^^ v.val
  (∃ (ask : Fin d → ℕ → D) (readout : ℕ → Fin h → Fin t → D)
      (bias : ℕ → Fin h → Fin t → F),
    ∀ x i j, operand x i (a i j) * operand x i (b i j) =
      readout (run ask x) i j x + bias (run ask x) i j) ↔
  ∃ pick : Fin h → Fin t → Fin 3,
    let last := (List.finRange h).foldl (fun st i =>
      advance st (fun j => selectMask (a i j) (b i j) (pick i j))) ((0, {0}) : ℕ × Finset ℕ)
    last.1 + Nat.log2 last.2.card ≤ d) := by
  intro h t a b d F W D operand run advance selectMask
  exact main h t a b d
