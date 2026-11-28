import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48861

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def fullMask : Nat := 0xffffffffffffffff
abbrev Masked (mask w : Nat) : Prop := w &&& mask = w
def bsel {α : Type} (c : Bool) (t f : α) : α := Bool.rec f t c
theorem bsel_true {α : Type} (t f : α) : bsel true t f = t := rfl
theorem bsel_false {α : Type} (t f : α) : bsel false t f = f := rfl
theorem beq_false_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h
theorem ne_of_beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro e; subst e; rw [Nat.beq_refl] at h; exact Bool.noConfusion h
theorem masked_self (mask : Nat) : Masked mask mask := by
  unfold Masked; simp
theorem masked_land_right (mask w : Nat) : Masked mask (w &&& mask) := by
  unfold Masked; apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and]
theorem xor_cancel_left (mask v : Nat) : mask ^^^ (mask ^^^ v) = v := by
  apply Nat.eq_of_testBit_eq; intro i; simp
theorem masked_sub_and {mask cut w : Nat} (sub : mask &&& cut = cut) :
    (w &&& mask) &&& cut = w &&& cut := by
  apply Nat.eq_of_testBit_eq; intro i
  have es := congrArg (fun x => x.testBit i) sub
  simp only [Nat.testBit_and] at es ⊢
  cases hc : cut.testBit i <;> simp_all
theorem masked_sub_xor {mask cut w : Nat} (sub : mask &&& cut = cut) :
    (mask ^^^ w) &&& cut = cut ^^^ (w &&& cut) := by
  apply Nat.eq_of_testBit_eq; intro i
  have es := congrArg (fun x => x.testBit i) sub
  simp only [Nat.testBit_and, Nat.testBit_xor] at es ⊢
  cases hc : cut.testBit i <;> simp_all
def canon (mask w : Nat) : Nat :=
  let v := w &&& mask
  bsel (Nat.beq v 0 || Nat.beq v mask) 0
    (let iv := mask ^^^ v; bsel (Nat.blt v iv) v iv)
theorem canon_zero (mask : Nat) : canon mask 0 = 0 := by
  unfold canon; simp [bsel]
theorem canon_self (mask : Nat) : canon mask mask = 0 := by
  unfold canon; simp [bsel]
theorem canon_land (mask w : Nat) : canon mask (w &&& mask) = canon mask w := by
  unfold canon; dsimp only; rw [masked_land_right mask w]
theorem canon_cases (mask w : Nat) :
    (canon mask w = 0 ∧ (w &&& mask = 0 ∨ w &&& mask = mask)) ∨
    (canon mask w ≠ 0 ∧ (canon mask w = w &&& mask ∨ canon mask w = mask ^^^ (w &&& mask))) := by
  unfold canon; dsimp only
  set v := w &&& mask
  by_cases hv0 : v = 0
  · left; rw [hv0]; simp [bsel]
  · by_cases hvm : v = mask
    · left; rw [hvm]; simp [bsel]
    · right
      rw [beq_false_ne hv0, beq_false_ne hvm]
      simp only [Bool.or_false, bsel_false]
      cases hlt : Nat.blt v (mask ^^^ v)
      · rw [bsel_false]
        refine ⟨?_, Or.inr rfl⟩
        intro hz
        have e := congrArg (fun x => mask ^^^ x) hz
        rw [xor_cancel_left] at e
        exact hvm (by simpa using e)
      · rw [bsel_true]; exact ⟨hv0, Or.inl rfl⟩
theorem canon_xor_mask (mask w : Nat) : canon mask (mask ^^^ w) = canon mask w := by
  have hsub : (mask ^^^ w) &&& mask = mask ^^^ (w &&& mask) := masked_sub_xor (masked_self mask)
  unfold canon; dsimp only
  rw [hsub]
  generalize hv : w &&& mask = v
  set iv := mask ^^^ v
  have hiv : mask ^^^ iv = v := xor_cancel_left mask v
  rw [hiv]
  by_cases hv0 : v = 0
  · have hivm : iv = mask := by simp [iv, hv0]
    rw [hv0, hivm]; simp [bsel]
  · by_cases hvm : v = mask
    · have hiv0 : iv = 0 := by simp [iv, hvm]
      rw [hvm, hiv0]; simp [bsel]
    · have hiv0 : iv ≠ 0 := by
        intro h; apply hvm
        have e := congrArg (fun x => mask ^^^ x) h
        rw [hiv] at e; simpa using e
      have hivm : iv ≠ mask := by
        intro h; apply hv0
        have e := congrArg (fun x => mask ^^^ x) h
        rw [hiv] at e; simpa using e
      rw [beq_false_ne hv0, beq_false_ne hvm, beq_false_ne hiv0, beq_false_ne hivm]
      simp only [Bool.or_false, bsel_false]
      have hne : v ≠ iv := by
        intro h
        have hm0 : mask = 0 := by
          apply Nat.eq_of_testBit_eq; intro i
          have ei := congrArg (fun x => x.testBit i) h
          simp only [iv, Nat.testBit_xor] at ei
          cases hv' : v.testBit i <;> cases hm' : mask.testBit i <;> simp_all
        have : v = 0 := by rw [← hv, hm0]; simp
        exact hv0 this
      by_cases hlt : v < iv
      · have h1 : Nat.blt v iv = true := Nat.blt_eq.mpr hlt
        have h2 : Nat.blt iv v = false := by cases h : Nat.blt iv v; rfl; have := Nat.blt_eq.mp h; omega
        rw [h1, h2, bsel_true, bsel_false]
      · have hgt : iv < v := by omega
        have h1 : Nat.blt v iv = false := by cases h : Nat.blt v iv; rfl; have := Nat.blt_eq.mp h; omega
        have h2 : Nat.blt iv v = true := Nat.blt_eq.mpr hgt
        rw [h1, h2, bsel_false, bsel_true]
theorem canon_idem (mask w : Nat) : canon mask (canon mask w) = canon mask w := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · rw [h0, canon_zero]
  · calc canon mask (canon mask w) = canon mask (w &&& mask) := by rw [h1]
      _ = canon mask w := canon_land mask w
  · calc canon mask (canon mask w) = canon mask (mask ^^^ (w &&& mask)) := by rw [h2]
      _ = canon mask (w &&& mask) := canon_xor_mask mask (w &&& mask)
      _ = canon mask w := canon_land mask w
theorem canon_submask {mask cut w : Nat} (sub : mask &&& cut = cut) (hc : canon mask w ≠ 0) :
    canon cut (canon mask w) = canon cut w := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · exact absurd h0 hc
  · rw [h1, ← canon_land cut (w &&& mask), masked_sub_and sub, canon_land]
  · rw [h2, ← canon_land cut (mask ^^^ (w &&& mask)), masked_sub_xor sub, masked_sub_and sub]
    rw [← masked_sub_xor (masked_self cut), canon_land, canon_xor_mask]
theorem canon_submask_zero {mask cut w : Nat} (sub : mask &&& cut = cut) (hc : canon mask w = 0) :
    canon cut w = 0 := by
  rcases canon_cases mask w with ⟨_, h0 | hm⟩ | ⟨hne, _⟩
  · rw [← canon_land cut w, ← masked_sub_and sub, h0]; simp [canon_zero]
  · rw [← canon_land cut w, ← masked_sub_and sub, hm, sub, canon_self]
  · exact absurd hc hne
theorem canon_testBit_eq {mask w p n : Nat} (hp : mask.testBit p = true) (hn : mask.testBit n = true) :
    ((canon mask w).testBit p = (canon mask w).testBit n) ↔ (w.testBit p = w.testBit n) := by
  rcases canon_cases mask w with ⟨h0, h1 | h2⟩ | ⟨_, h1 | h2⟩
  · rw [h0]
    have e1 := congrArg (fun x => x.testBit p) h1
    have e2 := congrArg (fun x => x.testBit n) h1
    simp [Nat.testBit_and, hp, hn] at e1 e2 ⊢; simp [e1, e2]
  · rw [h0]
    have e1 := congrArg (fun x => x.testBit p) h2
    have e2 := congrArg (fun x => x.testBit n) h2
    simp [Nat.testBit_and, hp, hn] at e1 e2 ⊢; simp [e1, e2]
  · rw [h1]; simp [Nat.testBit_and, hp, hn]
  · rw [h2]; simp [Nat.testBit_xor, Nat.testBit_and, hp, hn]
def binOp (mask op a b : Nat) : Nat :=
  bsel (Nat.beq op 0) (canon mask (a &&& b))
    (bsel (Nat.beq op 1) (canon mask (a ||| b))
      (bsel (Nat.beq op 2) (canon mask (a &&& (mask ^^^ b)))
        (canon mask ((mask ^^^ a) &&& b))))
theorem binOp_canon (mask op a b : Nat) : canon mask (binOp mask op a b) = binOp mask op a b := by
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false] <;> exact canon_idem mask _
theorem binOp_comm (mask op a b : Nat) (hop : op < 4) :
    ∃ op' < 4, binOp mask op a b = binOp mask op' b a := by
  have hland : a &&& b = b &&& a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  have hlor : a ||| b = b ||| a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_or, Bool.or_comm]
  have h23 : a &&& (mask ^^^ b) = (mask ^^^ b) &&& a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  have h32 : (mask ^^^ a) &&& b = b &&& (mask ^^^ a) := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  rcases (show op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 by omega) with rfl | rfl | rfl | rfl
  · exact ⟨0, by omega, by change canon mask (a &&& b) = canon mask (b &&& a); rw [hland]⟩
  · exact ⟨1, by omega, by change canon mask (a ||| b) = canon mask (b ||| a); rw [hlor]⟩
  · exact ⟨3, by omega, by change canon mask (a &&& (mask ^^^ b)) = canon mask ((mask ^^^ b) &&& a); rw [h23]⟩
  · exact ⟨2, by omega, by change canon mask ((mask ^^^ a) &&& b) = canon mask (b &&& (mask ^^^ a)); rw [h32]⟩
theorem binOp_zero_left (mask op b : Nat) : binOp mask op 0 b = 0 ∨ binOp mask op 0 b = canon mask b := by
  unfold binOp
  have hmb : (mask ^^^ 0) &&& b = b &&& mask := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · right; rw [hmb, canon_land]
  · left; simp [canon_zero]
  · right; simp
  · right; simp
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
theorem binOp_zero_right (mask op a : Nat) : binOp mask op a 0 = 0 ∨ binOp mask op a 0 = canon mask a := by
  unfold binOp
  have hma : a &&& (mask ^^^ 0) = a &&& mask := by simp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · left; simp [canon_zero]
  · right; rw [hma, canon_land]
  · right; simp
  · right; simp
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
theorem binOp_self (mask op a : Nat) : binOp mask op a a = 0 ∨ binOp mask op a a = canon mask a := by
  have h2 : canon mask (a &&& (mask ^^^ a)) = 0 := by
    rw [← canon_land]
    have : (a &&& (mask ^^^ a)) &&& mask = 0 := by
      apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
      cases a.testBit i <;> cases mask.testBit i <;> rfl
    rw [this, canon_zero]
  have h3 : canon mask ((mask ^^^ a) &&& a) = 0 := by
    rw [← canon_land]
    have : ((mask ^^^ a) &&& a) &&& mask = 0 := by
      apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
      cases a.testBit i <;> cases mask.testBit i <;> rfl
    rw [this, canon_zero]
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · left; exact h3
  · left; exact h2
  · right; simp
  · right; simp
  · right; simp
  · right; simp
  · right; simp
  · right; simp
theorem deMorgan_or_mask {mask a b : Nat} (ha : Masked mask a) (hb : Masked mask b) :
    mask ^^^ (a &&& b) = (mask ^^^ a) ||| (mask ^^^ b) := by
  unfold Masked at ha hb
  apply Nat.eq_of_testBit_eq; intro i
  have ea := congrArg (fun x => x.testBit i) ha
  have eb := congrArg (fun x => x.testBit i) hb
  simp only [Nat.testBit_and] at ea eb
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
  cases hm : mask.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
theorem canon_and_in_binOp (mask x y : Nat) :
    canon mask (x &&& y) = 0 ∨
    canon mask (x &&& y) = canon mask x ∨
    canon mask (x &&& y) = canon mask y ∨
    ∃ op < 4, canon mask (x &&& y) = binOp mask op (canon mask x) (canon mask y) := by
  have hxy : canon mask (x &&& y) = canon mask ((x &&& mask) &&& (y &&& mask)) := by
    rw [← canon_land mask (x &&& y), ← canon_land mask ((x &&& mask) &&& (y &&& mask))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and]
    cases x.testBit i <;> cases y.testBit i <;> cases mask.testBit i <;> rfl
  rw [hxy]
  have hvxm : Masked mask (x &&& mask) := masked_land_right mask x
  have hvym : Masked mask (y &&& mask) := masked_land_right mask y
  rcases canon_cases mask x with ⟨hx0, hx1 | hx2⟩ | ⟨_, hx1 | hx2⟩
  · left; rw [hx1]; simp [canon_zero]
  · right; right; left; rw [hx2]
    have : mask &&& (y &&& mask) = y &&& mask := by
      apply Nat.eq_of_testBit_eq; intro i
      have e := congrArg (fun t => t.testBit i) hvym
      simp only [Nat.testBit_and] at e ⊢; rw [Bool.and_comm]; exact e
    rw [this, canon_land]
  · rcases canon_cases mask y with ⟨hy0, hy1 | hy2⟩ | ⟨_, hy1 | hy2⟩
    · left; rw [hy1]; simp [canon_zero]
    · right; left; rw [hy2, hvxm, canon_land]
    · right; right; right; refine ⟨0, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x &&& canon mask y)
      rw [hx1, hy1]
    · right; right; right; refine ⟨2, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x &&& (mask ^^^ canon mask y))
      rw [hx1, hy2, xor_cancel_left]
  · rcases canon_cases mask y with ⟨hy0, hy1 | hy2⟩ | ⟨_, hy1 | hy2⟩
    · left; rw [hy1]; simp [canon_zero]
    · right; left; rw [hy2, hvxm, canon_land]
    · right; right; right; refine ⟨3, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask ((mask ^^^ canon mask x) &&& canon mask y)
      rw [hx2, hy1, xor_cancel_left]
    · right; right; right; refine ⟨1, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x ||| canon mask y)
      rw [hx2, hy2, ← deMorgan_or_mask hvxm hvym, canon_xor_mask]
theorem canon_or_in_binOp (mask x y : Nat) :
    canon mask (x ||| y) = 0 ∨
    canon mask (x ||| y) = canon mask x ∨
    canon mask (x ||| y) = canon mask y ∨
    ∃ op < 4, canon mask (x ||| y) = binOp mask op (canon mask x) (canon mask y) := by
  have hxy : canon mask (x ||| y) = canon mask ((mask ^^^ x) &&& (mask ^^^ y)) := by
    rw [← canon_xor_mask mask (x ||| y), ← canon_land mask (mask ^^^ (x ||| y))]
    rw [← canon_land mask ((mask ^^^ x) &&& (mask ^^^ y))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
    cases mask.testBit i <;> cases x.testBit i <;> cases y.testBit i <;> rfl
  rw [hxy]
  have h := canon_and_in_binOp mask (mask ^^^ x) (mask ^^^ y)
  rwa [canon_xor_mask, canon_xor_mask] at h
theorem canon_sub_binOp {mask cut op a b : Nat} (sub : mask &&& cut = cut) :
    canon cut (binOp mask op a b) = 0 ∨
    canon cut (binOp mask op a b) = canon cut a ∨
    canon cut (binOp mask op a b) = canon cut b ∨
    ∃ op' < 4, canon cut (binOp mask op a b) = binOp cut op' (canon cut a) (canon cut b) := by
  have go (u : Nat) : canon cut (canon mask u) = canon cut u := by
    by_cases h : canon mask u = 0
    · rw [h, canon_zero, (canon_submask_zero sub h).symm]
    · exact canon_submask sub h
  have hmx1 : canon cut ((mask ^^^ a) &&& b) = canon cut ((cut ^^^ a) &&& b) := by
    rw [← canon_land cut ((mask ^^^ a) &&& b), ← canon_land cut ((cut ^^^ a) &&& b)]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    have es := congrArg (fun t => t.testBit i) sub
    simp only [Nat.testBit_and] at es
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases hc : cut.testBit i
    · simp
    · simp only [hc, Bool.and_true] at es ⊢; rw [es]
  have hmx2 : canon cut (a &&& (mask ^^^ b)) = canon cut (a &&& (cut ^^^ b)) := by
    rw [← canon_land cut (a &&& (mask ^^^ b)), ← canon_land cut (a &&& (cut ^^^ b))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    have es := congrArg (fun t => t.testBit i) sub
    simp only [Nat.testBit_and] at es
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases hc : cut.testBit i
    · simp
    · simp only [hc, Bool.and_true] at es ⊢; rw [es]
  have hsub_case1 : canon cut ((cut ^^^ a) &&& b) = 0 ∨ canon cut ((cut ^^^ a) &&& b) = canon cut a ∨
      canon cut ((cut ^^^ a) &&& b) = canon cut b ∨
      ∃ op' < 4, canon cut ((cut ^^^ a) &&& b) = binOp cut op' (canon cut a) (canon cut b) := by
    have h := canon_and_in_binOp cut (cut ^^^ a) b
    rwa [canon_xor_mask] at h
  have hsub_case2 : canon cut (a &&& (cut ^^^ b)) = 0 ∨ canon cut (a &&& (cut ^^^ b)) = canon cut a ∨
      canon cut (a &&& (cut ^^^ b)) = canon cut b ∨
      ∃ op' < 4, canon cut (a &&& (cut ^^^ b)) = binOp cut op' (canon cut a) (canon cut b) := by
    have h := canon_and_in_binOp cut a (cut ^^^ b)
    rwa [canon_xor_mask] at h
  have hbin_eq : binOp mask op a b = canon mask (a &&& b) ∨ binOp mask op a b = canon mask (a ||| b) ∨
      binOp mask op a b = canon mask (a &&& (mask ^^^ b)) ∨ binOp mask op a b = canon mask ((mask ^^^ a) &&& b) := by
    unfold binOp
    cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp [bsel]
  rcases hbin_eq with h | h | h | h <;> rw [h, go]
  · exact canon_and_in_binOp cut a b
  · exact canon_or_in_binOp cut a b
  · rw [hmx2]; exact hsub_case2
  · rw [hmx1]; exact hsub_case1
def Avail (bank : List Nat) (w : Nat) : Prop := w = 0 ∨ w ∈ bank
def GateBin (mask : Nat) (bank : List Nat) (v : Nat) : Prop :=
  ∃ a b op, op < 4 ∧ Avail bank a ∧ Avail bank b ∧ v = binOp mask op a b
def BuildsBin (mask : Nat) (bank : List Nat) : List Nat → Prop
  | [] => True
  | v :: vs => GateBin mask bank v ∧ BuildsBin mask (v :: bank) vs
def LowerBin (mask : Nat) (stock : List Nat) (goal m : Nat) : Prop :=
  ∀ vs, BuildsBin mask stock vs → Avail (vs ++ stock) goal → m ≤ vs.length
theorem avail_weaken {b1 b2 : List Nat} (sub : ∀ w ∈ b1, w ∈ b2) {w : Nat} (h : Avail b1 w) :
    Avail b2 w := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (sub w h)
theorem gate_weaken {mask : Nat} {b1 b2 : List Nat} (sub : ∀ w ∈ b1, w ∈ b2) {v : Nat}
    (h : GateBin mask b1 v) : GateBin mask b2 v := by
  obtain ⟨a, b, op, hop, ha, hb, hv⟩ := h
  exact ⟨a, b, op, hop, avail_weaken sub ha, avail_weaken sub hb, hv⟩
theorem builds_weaken {mask : Nat} {b1 b2 vs : List Nat} (sub : ∀ w ∈ b1, w ∈ b2)
    (h : BuildsBin mask b1 vs) : BuildsBin mask b2 vs := by
  induction vs generalizing b1 b2 with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gate_weaken sub h.1, ih ?_ h.2⟩
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (sub w hw)
theorem builds_append {mask : Nat} {roots first second : List Nat}
    (h1 : BuildsBin mask roots first) (h2 : BuildsBin mask (first ++ roots) second) :
    BuildsBin mask roots (first ++ second) := by
  induction first generalizing roots with
  | nil => exact h2
  | cons v vs ih =>
    refine ⟨h1.1, ih h1.2 ?_⟩
    exact builds_weaken (fun w hw => by simp only [List.mem_append, List.mem_cons] at hw ⊢; tauto) h2
def dropIf (drop : Bool) (x : Nat) (S : Finset Nat) : Finset Nat :=
  if drop then S.erase x else S
theorem dropIf_subset (drop : Bool) (x : Nat) (S : Finset Nat) : dropIf drop x S ⊆ S := by
  unfold dropIf; split; exact Finset.erase_subset _ _; exact Finset.Subset.refl _
theorem dropIf_card_le (drop : Bool) (x : Nat) (S : Finset Nat) :
    S.card ≤ (dropIf drop x S).card + 1 := by
  unfold dropIf; split
  · by_cases hx : x ∈ S
    · have := Finset.card_erase_add_one hx; omega
    · rw [Finset.erase_eq_of_notMem hx]; omega
  · omega
inductive LiveBin (mask goal : Nat) : Nat → Finset Nat → Prop
  | done : LiveBin mask goal 0 {goal}
  | step {k : Nat} {S : Finset Nat} {a b op : Nat}
      (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hop : op < 4)
      (hz : binOp mask op a b ≠ 0) (hf : binOp mask op a b ∉ S)
      (keepA keepB : Bool) :
      LiveBin mask goal k (insert (binOp mask op a b) (dropIf (!keepA) a (dropIf (!keepB) b S))) →
      LiveBin mask goal (k + 1) S
theorem liveBin_zero_not_mem {mask goal k : Nat} {S : Finset Nat} (hg : goal ≠ 0)
    (h : LiveBin mask goal k S) : 0 ∉ S := by
  induction h with
  | done => simp [hg.symm]
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    intro h0; apply ih
    apply Finset.mem_insert_of_mem
    unfold dropIf
    split
    · apply Finset.mem_erase.mpr; refine ⟨ha0.symm, ?_⟩
      split
      · exact Finset.mem_erase.mpr ⟨hb0.symm, h0⟩
      · exact h0
    · split
      · exact Finset.mem_erase.mpr ⟨hb0.symm, h0⟩
      · exact h0
theorem liveBin_card_le {mask goal k : Nat} {S : Finset Nat} (h : LiveBin mask goal k S) :
    S.card ≤ k + 1 := by
  induction h with
  | done => simp
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    set z := binOp mask op a b
    have h1 := dropIf_card_le (!keepB) b S
    have h2 := dropIf_card_le (!keepA) a (dropIf (!keepB) b S)
    have hz' : z ∉ dropIf (!keepA) a (dropIf (!keepB) b S) := fun hm =>
      hf (dropIf_subset _ _ _ (dropIf_subset _ _ _ hm))
    have h3 : (insert z (dropIf (!keepA) a (dropIf (!keepB) b S))).card =
        (dropIf (!keepA) a (dropIf (!keepB) b S)).card + 1 := Finset.card_insert_of_notMem hz'
    omega
theorem extractLiveBin_aux {mask goal : Nat} (hg : goal ≠ 0) :
    ∀ (vs bank : List Nat) (k : Nat) (L : Finset Nat),
      BuildsBin mask bank vs → (∀ w ∈ bank, canon mask w = w) →
      L ⊆ (vs ++ bank).toFinset → LiveBin mask goal k L →
      ∃ k' S, k' ≤ k + vs.length ∧ S ⊆ bank.toFinset ∧ LiveBin mask goal k' S
  | [], bank, k, L, _, _, hsub, hlive => ⟨k, L, by simp, hsub, hlive⟩
  | v :: vs, bank, k, L, hbuild, hcb, hsub, hlive => by
    have hcv : canon mask v = v := by
      obtain ⟨a, b, op, _, _, _, rfl⟩ := hbuild.1; exact binOp_canon mask op a b
    have hcb' : ∀ w ∈ v :: bank, canon mask w = w := by
      intro w hw; rcases List.mem_cons.mp hw with rfl | hw; exact hcv; exact hcb w hw
    have hsub' : L ⊆ (vs ++ (v :: bank)).toFinset := by
      intro w hw
      have := hsub hw
      simp only [List.toFinset_append, List.toFinset_cons, Finset.mem_union, Finset.mem_insert] at this ⊢
      tauto
    obtain ⟨k1, L1, hk1, hL1sub, hlive1⟩ := extractLiveBin_aux hg vs (v :: bank) k L hbuild.2 hcb' hsub' hlive
    by_cases hv : v ∈ L1 ∧ v ∉ bank
    · obtain ⟨hvL, hvb⟩ := hv
      have hv0 : v ≠ 0 := fun h0 => liveBin_zero_not_mem hg hlive1 (h0 ▸ hvL)
      obtain ⟨a, b, op, hop, haA, hbA, hvEq⟩ := hbuild.1
      have ha0 : a ≠ 0 := by
        intro h0; subst h0
        rcases binOp_zero_left mask op b with h | h
        · exact hv0 (hvEq.trans h)
        · rcases hbA with rfl | hbM
          · rw [canon_zero] at h; exact hv0 (hvEq.trans h)
          · rw [hcb b hbM] at h; exact hvb ((hvEq.trans h) ▸ hbM)
      have hb0 : b ≠ 0 := by
        intro h0; subst h0
        rcases binOp_zero_right mask op a with h | h
        · exact hv0 (hvEq.trans h)
        · rcases haA with rfl | haM
          · rw [canon_zero] at h; exact hv0 (hvEq.trans h)
          · rw [hcb a haM] at h; exact hvb ((hvEq.trans h) ▸ haM)
      have haM : a ∈ bank := haA.resolve_left ha0
      have hbM : b ∈ bank := hbA.resolve_left hb0
      have hab : a ≠ b := by
        intro h; subst h
        rcases binOp_self mask op a with h0 | ha'
        · exact hv0 (hvEq.trans h0)
        · rw [hcb a haM] at ha'; exact hvb ((hvEq.trans ha') ▸ haM)
      set R := L1.erase v
      set S := insert a (insert b R)
      have hSsub : S ⊆ bank.toFinset := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact List.mem_toFinset.mpr haM
        · rcases Finset.mem_insert.mp hw with rfl | hw
          · exact List.mem_toFinset.mpr hbM
          · have h1 := hL1sub (Finset.mem_of_mem_erase hw)
            simp only [List.toFinset_cons, Finset.mem_insert] at h1
            exact h1.resolve_left (Finset.ne_of_mem_erase hw)
      have hvNotS : v ∉ S := by
        intro hm
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact hvb haM
        · rcases Finset.mem_insert.mp hm with rfl | hm
          · exact hvb hbM
          · exact (Finset.notMem_erase v L1) hm
      have hL1eq : insert v (dropIf (!(decide (a ∈ R))) a (dropIf (!(decide (b ∈ R))) b S)) = L1 := by
        ext w
        by_cases haR : a ∈ R <;> by_cases hbR : b ∈ R
        · simp only [haR, hbR, decide_true, Bool.not_true, Bool.false_eq_true, dropIf, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | rfl | rfl | ⟨_, hw⟩); exact hvL; exact (Finset.mem_erase.mp haR).2; exact (Finset.mem_erase.mp hbR).2; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h; exact Or.inr (Or.inr (Or.inr ⟨h, hw⟩))
        · simp only [haR, hbR, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, dropIf, ite_true, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwb, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact (Finset.mem_erase.mp haR).2; exact absurd rfl hwb; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            intro hwb; subst hwb; exact hbR (Finset.mem_erase.mpr ⟨h, hw⟩)
        · simp only [haR, hbR, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, dropIf, ite_true, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwa, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact absurd rfl hwa; exact (Finset.mem_erase.mp hbR).2; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            intro hwa; subst hwa; exact haR (Finset.mem_erase.mpr ⟨h, hw⟩)
        · simp only [haR, hbR, decide_false, Bool.not_false, dropIf, ite_true, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwa, hwb, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact absurd rfl hwa; exact absurd rfl hwb; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, ?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            · intro hwa; subst hwa; exact haR (Finset.mem_erase.mpr ⟨h, hw⟩)
            · intro hwb; subst hwb; exact hbR (Finset.mem_erase.mpr ⟨h, hw⟩)
      refine ⟨k1 + 1, S, by simp only [List.length_cons]; omega, hSsub, ?_⟩
      apply LiveBin.step (a := a) (b := b) (op := op)
        (Finset.mem_insert_self a _) (Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
        hab ha0 hb0 hop (hvEq ▸ hv0) (hvEq ▸ hvNotS) (decide (a ∈ R)) (decide (b ∈ R))
      rw [← hvEq, hL1eq]; exact hlive1
    · refine ⟨k1, L1, by simp only [List.length_cons]; omega, ?_, hlive1⟩
      intro w hw
      have h1 := hL1sub hw
      simp only [List.toFinset_cons, Finset.mem_insert] at h1
      rcases h1 with rfl | h1
      · have hvb : w ∈ bank := by by_contra hnb; exact hv ⟨hw, hnb⟩
        exact List.mem_toFinset.mpr hvb
      · exact h1
theorem extractLiveBin {mask goal : Nat} {stock vs : List Nat}
    (hg : goal ≠ 0) (hcs : ∀ w ∈ stock, canon mask w = w)
    (hbuild : BuildsBin mask stock vs) (hhit : Avail (vs ++ stock) goal) :
    ∃ k S, k ≤ vs.length ∧ S ⊆ stock.toFinset ∧ LiveBin mask goal k S := by
  have hmem : goal ∈ vs ++ stock := hhit.resolve_left hg
  have hsub : ({goal} : Finset Nat) ⊆ (vs ++ stock).toFinset := by
    intro w hw; rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hmem
  obtain ⟨k, S, hk, hS, hL⟩ := extractLiveBin_aux hg vs stock 0 {goal} hbuild hcs hsub LiveBin.done
  exact ⟨k, S, by omega, hS, hL⟩
theorem liveBin_agrees {mask goal k p n : Nat} {S : Finset Nat}
    (hp : mask.testBit p = true) (hn : mask.testBit n = true)
    (h : LiveBin mask goal k S) (hag : ∀ w ∈ S, w.testBit p = w.testBit n) :
    goal.testBit p = goal.testBit n := by
  induction h with
  | done => exact hag goal (Finset.mem_singleton_self goal)
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    apply ih; intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · have ea := hag a ha
      have eb := hag b hb
      unfold binOp
      cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
      all_goals rw [canon_testBit_eq hp hn]
      all_goals simp [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, hp, hn, ea, eb]
    · exact hag w (dropIf_subset _ _ _ (dropIf_subset _ _ _ hw))
def forceW {α : Type} (w : Nat) (k : Nat → α) : α :=
  Nat.rec (k 0) (fun m _ => k (m + 1)) w
theorem forceW_eq {α : Type} (w : Nat) (k : Nat → α) : forceW w k = k w := by
  cases w <;> rfl
def forceWs (ws : List Nat) (k : List Nat → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun w _ next k => forceW w (fun v => next (fun rest => k (v :: rest)))) ws) k
theorem forceWs_eq (ws : List Nat) (k : List Nat → Bool) : forceWs ws k = k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceW w (fun v => forceWs ws (fun rest => k (v :: rest))) = _
    rw [forceW_eq, ih]
def dagPart (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      (Nat.beq p 0 || Nat.beq n 0) ||
        forceW (p &&& w) (fun up =>
          forceW (n &&& w) (fun down =>
            rest up down &&
              forceW (p ^^^ up) (fun offP =>
                forceW (n ^^^ down) (rest offP))))) ws
theorem offBits {v w i : Nat} (h : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor, Nat.testBit_and] at h
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv, hw] at h ⊢
theorem dagPart_sound {ws : List Nat} {pos neg : Nat} (fail : dagPart ws pos neg = false) :
    ∃ p n, pos.testBit p = true ∧ neg.testBit n = true ∧ ∀ w ∈ ws, w.testBit p = w.testBit n := by
  have nonempty {w : Nat} (hn : w ≠ 0) : ∃ j, w.testBit j = true := by
    by_contra! all; apply hn; apply Nat.eq_of_testBit_eq; intro i; simp [all i]
  induction ws generalizing pos neg with
  | nil =>
    change (Nat.beq pos 0 || Nat.beq neg 0) = false at fail
    simp only [Bool.or_eq_false_iff] at fail
    obtain ⟨p, hp⟩ := nonempty (ne_of_beq_false fail.1)
    obtain ⟨n, hn⟩ := nonempty (ne_of_beq_false fail.2)
    exact ⟨p, n, hp, hn, by simp⟩
  | cons w ws ih =>
    change ((Nat.beq pos 0 || Nat.beq neg 0) ||
      forceW (pos &&& w) (fun up =>
        forceW (neg &&& w) (fun down =>
          dagPart ws up down &&
            forceW (pos ^^^ up) (fun offP =>
              forceW (neg ^^^ down) (dagPart ws offP))))) = false at fail
    simp only [forceW_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p, n, hp, hn, ag⟩ := ih on
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hn
      refine ⟨p, n, hp.1, hn.1, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [hp.2, hn.2]
      · exact ag a ha
    · obtain ⟨p, n, hp, hn, ag⟩ := ih off
      have hp' := offBits hp
      have hn' := offBits hn
      refine ⟨p, n, hp'.1, hn'.1, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [hp'.2, hn'.2]
      · exact ag a ha
theorem dagPart_live {mask goal k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset) :
    dagPart ws goal (mask ^^^ goal) = true := by
  by_contra hf
  have hfalse : dagPart ws goal (mask ^^^ goal) = false := by
    cases h : dagPart ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p, n, hp, hn, ag⟩ := dagPart_sound hfalse
  have hpm : mask.testBit p = true := by
    have e := congrArg (fun x => x.testBit p) hgm
    simp only [Nat.testBit_and, hp, Bool.true_and] at e; exact e
  have hnm : mask.testBit n = true ∧ goal.testBit n = false := by
    rw [Nat.testBit_xor] at hn
    have imp : goal.testBit n = true → mask.testBit n = true := by
      intro hg
      have e := congrArg (fun x => x.testBit n) hgm
      simp only [Nat.testBit_and, hg, Bool.true_and] at e; exact e
    cases hm : mask.testBit n <;> cases hg : goal.testBit n <;> simp_all
  have eq := liveBin_agrees hpm hnm.1 hlive (fun w hw => ag w (List.mem_toFinset.mp hw))
  rw [hp, hnm.2] at eq; exact Bool.noConfusion eq
def flatSet (cut : Nat) (S : Finset Nat) : Finset Nat :=
  S.filter (fun w => Nat.beq (canon cut w) 0)
theorem flatSet_insert_notMem {cut w : Nat} {S : Finset Nat} (hw : w ∉ S) :
    (flatSet cut (insert w S)).card =
      if canon cut w = 0 then (flatSet cut S).card + 1 else (flatSet cut S).card := by
  unfold flatSet
  rw [Finset.filter_insert]
  by_cases hc : canon cut w = 0
  · simp only [hc, Nat.beq_refl, ite_true]
    exact Finset.card_insert_of_notMem (fun h => hw (Finset.mem_filter.mp h).1)
  · simp only [beq_false_ne hc, Bool.false_eq_true, ite_false, hc]
theorem flatSet_erase {cut w : Nat} {S : Finset Nat} :
    (flatSet cut S).card ≤ (flatSet cut (S.erase w)).card + (if canon cut w = 0 then 1 else 0) := by
  unfold flatSet
  rw [Finset.filter_erase]
  by_cases hm : w ∈ S.filter (fun x => Nat.beq (canon cut x) 0)
  · have hcw : canon cut w = 0 := Nat.eq_of_beq_eq_true (Finset.mem_filter.mp hm).2
    have hcard := Finset.card_erase_add_one hm
    simp only [hcw, ite_true]; omega
  · rw [Finset.erase_eq_of_notMem hm]; omega
theorem maskedBuildBin {mask cut goal k : Nat} {S : Finset Nat}
    (sub : mask &&& cut = cut) (hgnf : canon cut goal ≠ 0)
    (h : LiveBin mask goal k S) :
    ∀ (bank : List Nat), (∀ w ∈ S, Avail bank (canon cut w)) →
      ∃ vs, vs.length + (flatSet cut S).card ≤ k ∧ BuildsBin cut bank vs ∧
        Avail (vs ++ bank) (canon cut goal) := by
  induction h with
  | done =>
    intro bank hsup
    have hfl : (flatSet cut {goal}).card = 0 := by
      unfold flatSet
      simp [hgnf]
    exact ⟨[], by simp [hfl], trivial, hsup goal (Finset.mem_singleton_self goal)⟩
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB tail ih =>
    intro bank hsup
    set z := binOp mask op a b
    set S1 := dropIf (!keepB) b S
    set S2 := dropIf (!keepA) a S1
    set S' := insert z S2
    have hS2sub : S2 ⊆ S := Finset.Subset.trans (dropIf_subset _ _ _) (dropIf_subset _ _ _)
    have hzNotS2 : z ∉ S2 := fun hm => hf (hS2sub hm)
    have hfl1 : (flatSet cut S).card ≤ (flatSet cut S1).card + (if canon cut b = 0 then 1 else 0) := by
      unfold S1 dropIf; split; exact flatSet_erase; omega
    have hfl2 : (flatSet cut S1).card ≤ (flatSet cut S2).card + (if canon cut a = 0 then 1 else 0) := by
      unfold S2 dropIf; split; exact flatSet_erase; omega
    have hfl3 : (flatSet cut S').card =
        if canon cut z = 0 then (flatSet cut S2).card + 1 else (flatSet cut S2).card :=
      flatSet_insert_notMem hzNotS2
    have hcz : canon cut z = 0 ∨ canon cut z = canon cut a ∨ canon cut z = canon cut b ∨
        ∃ op' < 4, canon cut z = binOp cut op' (canon cut a) (canon cut b) :=
      canon_sub_binOp sub
    by_cases hfa : canon cut a = 0
    · by_cases hfb : canon cut b = 0
      · have hfz : canon cut z = 0 := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact h
          · exact h.trans hfa
          · exact h.trans hfb
          · rw [hfa, hfb] at h
            rcases binOp_zero_left cut op' 0 with h0 | h0
            · exact h.trans h0
            · exact h.trans (h0.trans (canon_zero cut))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact Or.inl hfz
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, hfz, ite_true] at hfl1 hfl2 hfl3
        exact ⟨vs, by omega, hbd, hhit⟩
      · have hfz : canon cut z = 0 ∨ canon cut z = canon cut b := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact Or.inl h
          · exact Or.inl (h.trans hfa)
          · exact Or.inr h
          · rw [hfa] at h
            rcases binOp_zero_left cut op' (canon cut b) with h0 | h0
            · exact Or.inl (h.trans h0)
            · exact Or.inr (h.trans (h0.trans (canon_idem cut b)))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rcases hfz with h0 | hb'
            · exact Or.inl h0
            · rw [hb']; exact hsup b hb
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, ite_true, ite_false] at hfl1 hfl2
        have : (flatSet cut S2).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        exact ⟨vs, by omega, hbd, hhit⟩
    · by_cases hfb : canon cut b = 0
      · have hfz : canon cut z = 0 ∨ canon cut z = canon cut a := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact Or.inl h
          · exact Or.inr h
          · exact Or.inl (h.trans hfb)
          · rw [hfb] at h
            rcases binOp_zero_right cut op' (canon cut a) with h0 | h0
            · exact Or.inl (h.trans h0)
            · exact Or.inr (h.trans (h0.trans (canon_idem cut a)))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rcases hfz with h0 | ha'
            · exact Or.inl h0
            · rw [ha']; exact hsup a ha
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, ite_true, ite_false] at hfl1 hfl2
        have : (flatSet cut S2).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        exact ⟨vs, by omega, hbd, hhit⟩
      · simp only [hfa, hfb, ite_false] at hfl1 hfl2
        have hfl_le : (flatSet cut S).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        rcases hcz with h0 | ha' | hb' | ⟨op', hop', hbin⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Or.inl h0
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · rw [ha']; exact hsup a ha
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · rw [hb']; exact hsup b hb
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · set cz := canon cut z
          have hgate : GateBin cut bank cz := ⟨canon cut a, canon cut b, op', hop', hsup a ha, hsup b hb, hbin⟩
          have hsup' : ∀ w ∈ S', Avail (cz :: bank) (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Or.inr List.mem_cons_self
            · exact avail_weaken (fun u hu => List.mem_cons_of_mem _ hu) (hsup w (hS2sub hw))
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih (cz :: bank) hsup'
          refine ⟨cz :: vs, by simp only [List.length_cons]; omega, ⟨hgate, hbd⟩, ?_⟩
          exact avail_weaken (fun u hu => by simp only [List.mem_append, List.mem_cons] at hu ⊢; tauto) hhit
def flatCount (cut : Nat) (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ cnt => bsel (Nat.beq (canon cut w) 0) (cnt + 1) cnt) ws
theorem flatCount_card (cut : Nat) {ws : List Nat} (nd : ws.Nodup) :
    flatCount cut ws = (flatSet cut ws.toFinset).card := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hnd := List.nodup_cons.mp nd
    have fresh : w ∉ ws.toFinset := by simpa using hnd.1
    change bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws) = _
    rw [List.toFinset_cons, flatSet_insert_notMem fresh, ih hnd.2]
    by_cases hc : canon cut w = 0
    · simp [hc, bsel]
    · rw [beq_false_ne hc, bsel_false]; simp [hc]
def availB (bank : List Nat) (w : Nat) : Bool :=
  Nat.beq w 0 || bank.contains w
theorem availB_spec {bank : List Nat} {w : Nat} : availB bank w = true ↔ Avail bank w := by
  unfold availB Avail; simp [Nat.beq_eq]
def addUniq (w : Nat) (l : List Nat) : List Nat :=
  if l.contains w then l else w :: l
def recipeStart (cut : Nat) (stock ws : List Nat) : List Nat :=
  List.rec [] (fun w _ acc =>
    let v := canon cut w
    if availB stock v then acc else addUniq v acc) ws
def recipeClose (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      let v := canon cut w
      if acc.contains v then
        let va := canon cut a
        let vb := canon cut b
        let acc1 := if availB stock va then acc else addUniq va acc
        let acc2 := if availB stock vb then acc1 else addUniq vb acc1
        next acc2
      else next acc) hist needed
def KnownBin (bounds : List (Nat × List Nat × Nat × Nat)) : Prop :=
  ∀ b ∈ bounds, LowerBin b.1 b.2.1 b.2.2.2 b.2.2.1
def insertSorted (x : Nat) (l : List Nat) : List Nat :=
  List.rec [x] (fun y ys ih => bsel (Nat.ble x y) (x :: y :: ys) (y :: ih)) l
theorem insertSorted_mem {x w : Nat} {l : List Nat} :
    w ∈ insertSorted x l ↔ w = x ∨ w ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    change w ∈ bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys) ↔ _
    cases Nat.ble x y
    · rw [bsel_false]; simp only [List.mem_cons, ih]; tauto
    · rw [bsel_true]; simp only [List.mem_cons]
theorem insertSorted_nodup {x : Nat} {l : List Nat} (hx : x ∉ l) (nd : l.Nodup) :
    (insertSorted x l).Nodup := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    have hnd := List.nodup_cons.mp nd
    have hxy : x ≠ y := fun h => hx (h ▸ List.mem_cons_self)
    have hxs : x ∉ ys := fun h => hx (List.mem_cons_of_mem _ h)
    change (bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys)).Nodup
    cases Nat.ble x y
    · rw [bsel_false]
      apply List.nodup_cons.mpr
      refine ⟨fun hm => ?_, ih hxs hnd.2⟩
      rcases insertSorted_mem.mp hm with h | h
      · exact hxy h.symm
      · exact hnd.1 h
    · rw [bsel_true]; exact List.nodup_cons.mpr ⟨hx, nd⟩
def dropVal (drop : Bool) (x : Nat) (l : List Nat) : List Nat :=
  bsel drop (List.rec [] (fun y _ ih => bsel (Nat.beq y x) ih (y :: ih)) l) l
theorem dropVal_mem {drop : Bool} {x w : Nat} {l : List Nat} :
    w ∈ dropVal drop x l ↔ w ∈ l ∧ (drop = true → w ≠ x) := by
  cases drop
  · simp [dropVal, bsel]
  · induction l with
    | nil => simp [dropVal, bsel]
    | cons y ys ih =>
      change w ∈ bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys) ↔ _
      cases hb : Nat.beq y x
      · rw [bsel_false]
        have hne : y ≠ x := ne_of_beq_false hb
        simp only [List.mem_cons, ih, true_implies]
        constructor
        · rintro (rfl | ⟨hw, hwx⟩); exact ⟨Or.inl rfl, hne⟩; exact ⟨Or.inr hw, hwx⟩
        · rintro ⟨rfl | hw, hwx⟩; exact Or.inl rfl; exact Or.inr ⟨hw, hwx⟩
      · rw [bsel_true]
        have heq : y = x := Nat.eq_of_beq_eq_true hb
        subst heq
        simp only [List.mem_cons, ih, true_implies]
        constructor
        · rintro ⟨hw, hwx⟩; exact ⟨Or.inr hw, hwx⟩
        · rintro ⟨rfl | hw, hwx⟩; exact absurd rfl hwx; exact ⟨hw, hwx⟩
theorem dropVal_nodup {drop : Bool} {x : Nat} {l : List Nat} (nd : l.Nodup) :
    (dropVal drop x l).Nodup := by
  cases drop
  · exact nd
  · induction l with
    | nil => simp [dropVal, bsel]
    | cons y ys ih =>
      have hnd := List.nodup_cons.mp nd
      change (bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys)).Nodup
      cases Nat.beq y x
      · rw [bsel_false]
        exact List.nodup_cons.mpr ⟨fun hm => hnd.1 (dropVal_mem.mp hm).1, ih hnd.2⟩
      · rw [bsel_true]; exact ih hnd.2
theorem dropVal_toFinset (drop : Bool) (x : Nat) (l : List Nat) :
    (dropVal drop x l).toFinset = dropIf drop x l.toFinset := by
  ext w; simp only [List.mem_toFinset, dropVal_mem, dropIf]
  cases drop <;> simp [Finset.mem_erase, and_comm]
def subsetWords (stock : List Nat) (bits : Nat) : List Nat :=
  (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih b =>
      let rest := ih (b >>> 1)
      bsel (Nat.beq (b &&& 1) 1) (insertSorted w rest) rest) stock) bits
theorem subsetWords_subset (stock : List Nat) (bits : Nat) :
    ∀ w ∈ subsetWords stock bits, w ∈ stock := by
  induction stock generalizing bits with
  | nil => intro w hw; simp [subsetWords] at hw
  | cons x xs ih =>
    intro w hw
    change w ∈ bsel (Nat.beq (bits &&& 1) 1)
      (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1)) at hw
    cases hb : Nat.beq (bits &&& 1) 1
    · rw [hb, bsel_false] at hw; exact List.mem_cons_of_mem _ (ih _ w hw)
    · rw [hb, bsel_true] at hw
      rcases insertSorted_mem.mp hw with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ w hm)
theorem subsetWords_nodup {stock : List Nat} (nd : stock.Nodup) (bits : Nat) :
    (subsetWords stock bits).Nodup := by
  induction stock generalizing bits with
  | nil => simp [subsetWords]
  | cons x xs ih =>
    have hnd := List.nodup_cons.mp nd
    change (bsel (Nat.beq (bits &&& 1) 1)
      (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1))).Nodup
    cases Nat.beq (bits &&& 1) 1
    · rw [bsel_false]; exact ih hnd.2 _
    · rw [bsel_true]; exact insertSorted_nodup (fun hm => hnd.1 (subsetWords_subset xs _ x hm)) (ih hnd.2 _)
theorem exists_subsetToken (stock : List Nat) (S : Finset Nat) :
    ∃ bits < 2 ^ stock.length, (subsetWords stock bits).toFinset = S ∩ stock.toFinset := by
  induction stock with
  | nil => exact ⟨0, by simp, by simp [subsetWords]⟩
  | cons x xs ih =>
    obtain ⟨b, hb, heq⟩ := ih
    by_cases hx : x ∈ S
    · refine ⟨2 * b + 1, by simp only [List.length_cons, Nat.pow_succ]; omega, ?_⟩
      have hdiv : (2 * b + 1) >>> 1 = b := by change (2 * b + 1) / 2 = b; omega
      have hmod : ((2 * b + 1) &&& 1) = 1 := by rw [Nat.and_one_is_mod]; omega
      change (bsel (Nat.beq ((2 * b + 1) &&& 1) 1)
        (insertSorted x (subsetWords xs ((2 * b + 1) >>> 1)))
        (subsetWords xs ((2 * b + 1) >>> 1))).toFinset = _
      rw [hdiv, hmod, Nat.beq_refl, bsel_true]
      ext w; simp only [List.mem_toFinset, insertSorted_mem, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert]
      have hw : w ∈ subsetWords xs b ↔ w ∈ S ∧ w ∈ xs := by
        have e := congrArg (fun t => w ∈ t) heq; simpa [List.mem_toFinset] using e
      rw [hw]; constructor
      · rintro (rfl | ⟨hs, hxs⟩); exact ⟨hx, Or.inl rfl⟩; exact ⟨hs, Or.inr hxs⟩
      · rintro ⟨hs, rfl | hxs⟩; exact Or.inl rfl; exact Or.inr ⟨hs, hxs⟩
    · refine ⟨2 * b, by simp only [List.length_cons, Nat.pow_succ]; omega, ?_⟩
      have hdiv : (2 * b) >>> 1 = b := by change (2 * b) / 2 = b; omega
      have hmod : ((2 * b) &&& 1) = 0 := by rw [Nat.and_one_is_mod]; omega
      change (bsel (Nat.beq ((2 * b) &&& 1) 1)
        (insertSorted x (subsetWords xs ((2 * b) >>> 1)))
        (subsetWords xs ((2 * b) >>> 1))).toFinset = _
      rw [hdiv, hmod]
      change (subsetWords xs b).toFinset = _
      ext w; simp only [List.mem_toFinset, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert]
      have hw : w ∈ subsetWords xs b ↔ w ∈ S ∧ w ∈ xs := by
        have e := congrArg (fun t => w ∈ t) heq; simpa [List.mem_toFinset] using e
      rw [hw]; constructor
      · rintro ⟨hs, hxs⟩; exact ⟨hs, Or.inr hxs⟩
      · rintro ⟨hs, rfl | hxs⟩; exact absurd hs hx; exact ⟨hs, hxs⟩
def rootState (stock : List Nat) (fuel token : Nat) : Nat × List Nat × List (Nat × Nat × Nat) :=
  (fuel, subsetWords stock token, [])
def childState (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, hist) := state
  let keep := token &&& 3
  let op := (token >>> 2) &&& 3
  let b := (token >>> 4) &&& 15
  let a := token >>> 8
  if Nat.beq fuel 0 || !(Nat.blt a b) || !(Nat.blt b ws.length) then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let z := binOp mask op x y
    if Nat.beq z 0 || ws.contains z then none
    else
      let keepA := Nat.beq (keep &&& 1) 1
      let keepB := Nat.beq ((keep >>> 1) &&& 1) 1
      let rest := dropVal (!keepA) x (dropVal (!keepB) y ws)
      some (fuel - 1, insertSorted z rest, (z, x, y) :: hist)
theorem childState_wf {mask token : Nat} {st ch : Nat × List Nat × List (Nat × Nat × Nat)}
    (nd : st.2.1.Nodup) (h : childState mask token st = some ch) :
    ch.1 < st.1 ∧ ch.2.1.Nodup := by
  obtain ⟨fuel, ws, hist⟩ := st
  dsimp only at nd
  unfold childState at h; dsimp only at h
  split at h
  · contradiction
  · rename_i hok
    split at h
    · contradiction
    · rename_i hfresh
      have heq := Option.some.inj h
      subst ch
      simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hok hfresh
      have hfpos : fuel ≠ 0 := fun hf => hok (Or.inl (Or.inl hf))
      have hznot : ¬(ws.contains (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0)
          (ws.getD ((token >>> 4) &&& 15) 0)) = true) := fun hm => hfresh (Or.inr hm)
      refine ⟨by dsimp; omega, ?_⟩
      apply insertSorted_nodup
      · intro hm
        have hmem := (dropVal_mem.mp (dropVal_mem.mp hm).1).1
        exact hznot (List.contains_iff_mem.mpr hmem)
      · exact dropVal_nodup (dropVal_nodup nd)
def dagTrace (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ prev j =>
      let (parent, token) := forest j
      if Nat.beq parent 0 then
        if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
      else (prev (parent - 1)).bind (childState mask token)) (fuel + 1)) i
theorem dagTrace_nodup {mask fuel : Nat} {stock : List Nat} {forest : Nat → Nat × Nat}
    (nd : stock.Nodup) {i : Nat} {st : Nat × List Nat × List (Nat × Nat × Nat)}
    (h : dagTrace mask stock fuel forest i = some st) : st.2.1.Nodup := by
  unfold dagTrace at h
  suffices ∀ steps j s,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j = some s → s.2.1.Nodup from
    this (fuel + 1) i st h
  intro steps
  induction steps with
  | zero => intro j s h; contradiction
  | succ n ih =>
    intro j s h; dsimp only at h
    split at h
    · split at h
      · have e := Option.some.inj h; subst s; exact subsetWords_nodup nd _
      · contradiction
    · cases hp : (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) n) ((forest j).1 - 1) with
      | none => rw [hp] at h; contradiction
      | some p => rw [hp] at h; exact (childState_wf (ih _ _ hp) h).2
def treeBlock (lo hi : Nat) (f : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      if Nat.blt a b then
        let m := (a + b) / 2
        if Nat.beq a m then f a else next a m && next m b
      else true) (hi - lo + 1)) lo hi
theorem treeBlock_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlock lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  unfold treeBlock at h
  suffices ∀ steps a b, b - a ≤ steps →
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b = true →
      ∀ i, a ≤ i → i < b → f i = true by
    intro i h1 h2; exact this (hi - lo + 1) lo hi (by omega) h i h1 h2
  intro steps
  induction steps with
  | zero => intro a b hba _ i h1 h2; omega
  | succ s ih =>
    intro a b hba h i h1 h2
    dsimp only at h
    have hab : Nat.blt a b = true := Nat.blt_eq.mpr (by omega)
    simp only [hab, ite_true] at h
    set m := (a + b) / 2
    by_cases ham : a = m
    · have hbm : Nat.beq a m = true := Nat.beq_eq.mpr ham
      simp only [hbm, ite_true] at h
      have hia : i = a := by omega
      subst hia; exact h
    · have hbm : Nat.beq a m = false := beq_false_ne ham
      simp only [hbm, Bool.false_eq_true, ite_false] at h
      rcases Bool.and_eq_true_iff.mp h with ⟨hl, hr⟩
      by_cases him : i < m
      · exact ih a m (by omega) hl i h1 him
      · exact ih m b (by omega) hr i (by omega) h2
theorem block_join {a m b : Nat} {f : Nat → Bool}
    (h1 : ∀ i, a ≤ i → i < m → f i = true)
    (h2 : ∀ i, m ≤ i → i < b → f i = true) :
    ∀ i, a ≤ i → i < b → f i = true := by
  intro i hi1 hi2
  by_cases h : i < m
  · exact h1 i hi1 h
  · exact h2 i (by omega) hi2
theorem getElem_index_lt {l : List Nat} {x : Nat} (hx : x ∈ l) :
    ∃ i < l.length, l.getD i 0 = x := by
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hx
  refine ⟨i, hi, ?_⟩
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, heq]
theorem list_len_child {x y z : Nat} {ws : List Nat} {keepA keepB : Bool}
    (nd : ws.Nodup) (hx : x ∈ ws) (hy : y ∈ ws) (hxy : x ≠ y) (hz : z ∉ ws) :
    (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).length =
      ws.length - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0) := by
  have nd' : (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).Nodup :=
    insertSorted_nodup (fun hm => hz (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
  have h1 := List.toFinset_card_of_nodup nd'
  have h2 := List.toFinset_card_of_nodup nd
  have hset : (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).toFinset =
      insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
    ext w
    simp only [List.mem_toFinset, insertSorted_mem, Finset.mem_insert, ← dropVal_toFinset]
  rw [hset] at h1
  have hz' : z ∉ dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset) :=
    fun hm => hz (List.mem_toFinset.mp (dropIf_subset _ _ _ (dropIf_subset _ _ _ hm)))
  rw [Finset.card_insert_of_notMem hz'] at h1
  set T := dropIf (!keepB) y ws.toFinset
  have hxb : x ∈ T := by
    unfold T dropIf; split
    · exact Finset.mem_erase.mpr ⟨hxy, List.mem_toFinset.mpr hx⟩
    · exact List.mem_toFinset.mpr hx
  have hcb : T.card = ws.toFinset.card - (if keepB then 0 else 1) := by
    unfold T dropIf; cases keepB
    · have := Finset.card_erase_add_one (List.mem_toFinset.mpr hy); simp; omega
    · simp
  have hca : (dropIf (!keepA) x T).card = T.card - (if keepA then 0 else 1) := by
    unfold dropIf; cases keepA
    · have := Finset.card_erase_add_one hxb; simp only [Bool.not_false, Bool.false_eq_true, ite_true, ite_false]; omega
    · simp
  have hlen2 : 2 ≤ ws.toFinset.card := by
    have hsub : ({x, y} : Finset Nat) ⊆ ws.toFinset := by
      intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
      · exact List.mem_toFinset.mpr hx
      · rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hy
    have hpair : ({x, y} : Finset Nat).card = 2 := Finset.card_pair hxy
    have := Finset.card_le_card hsub; omega
  rw [← h1, hca, hcb, h2]
  cases keepA <;> cases keepB <;> simp <;> omega
def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) : Nat := (gs.filter isBinary).length
def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
def evalBit (k : Nat) (w : Nat) : Bool := w.testBit k
def stepBool (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def actionWord (w : List Nat) (g : Gate) : Nat := match g.op with
  | .not => fullMask ^^^ ((g.inputs.head?.map (fun i => w.getD i 0)).getD 0)
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) fullMask
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0
theorem fullMask_eq : fullMask = 2 ^ 64 - 1 := by decide
theorem fullMask_bit {k : Nat} (hk : k < 64) : fullMask.testBit k = true := by
  rw [fullMask_eq, Nat.testBit_two_pow_sub_one]; simp [hk]
theorem readBit (w : List Nat) (i k : Nat) :
    (w.map (evalBit k)).getD i false = evalBit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), evalBit]
theorem actionWord_spec (w : List Nat) (g : Gate) (hg : legal g) {k : Nat} (hk : k < 64) :
    stepBool (w.map (evalBit k)) g = (w ++ [actionWord w g]).map (evalBit k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hcap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hcap
  have hfm := fullMask_bit hk
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at hcap
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [stepBool, List.map_cons, List.map_nil, readBit, List.map_append, actionWord,
      GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some,
      Option.getD_none, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
      Bool.and_true, Bool.or_false, evalBit, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
      Nat.zero_testBit, hfm, Bool.true_xor]
def rawVars : List Nat :=
  [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def rootStock : List Nat :=
  [0x5555555555555555, 0x3333333333333333, 0x0f0f0f0f0f0f0f0f,
   0x00ff00ff00ff00ff, 0x0000ffff0000ffff, 0x00000000ffffffff]
theorem rawVars_avail : ∀ u ∈ rawVars, Avail rootStock (canon fullMask u) := by
  intro u hu
  simp only [rawVars, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Or.inr (by decide)
theorem compileBin_aux (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w bank : List Nat)
    (hw : ∀ u ∈ w, Avail bank (canon fullMask u)) :
    ∃ vs, vs.length ≤ binaryCost gs ∧ BuildsBin fullMask bank vs ∧
      ∀ u ∈ gs.foldl (fun acc g => acc ++ [actionWord acc g]) w, Avail (vs ++ bank) (canon fullMask u) := by
  induction gs generalizing w bank with
  | nil => exact ⟨[], Nat.le_refl _, trivial, by simpa using hw⟩
  | cons g gs ih =>
    have hg0 := hg g List.mem_cons_self
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    set z := actionWord w g
    have hread (i : Nat) : Avail bank (canon fullMask (w.getD i 0)) := by
      by_cases hi : i < w.length
      · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi), canon_zero]; exact Or.inl rfl
    have hstep : Avail bank (canon fullMask z) ∨ (isBinary g = true ∧ GateBin fullMask bank (canon fullMask z)) := by
      obtain ⟨op, args⟩ := g
      obtain ⟨hop, hcap⟩ := hg0
      change op = .and ∨ op = .or ∨ op = .not at hop
      change args.length ≤ 2 at hcap
      rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at hcap
      · rcases hop with rfl | rfl | rfl
        · left; simp [z, actionWord, canon_self]; exact Or.inl rfl
        · left; simp [z, actionWord, canon_zero]; exact Or.inl rfl
        · left; simp [z, actionWord, canon_self]; exact Or.inl rfl
      · rcases hop with rfl | rfl | rfl
        · left; simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          rw [canon_land]; exact hread i
        · left; simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero]
          exact hread i
        · left; simp only [z, actionWord, List.head?_cons, Option.map_some, Option.getD_some]
          rw [canon_xor_mask]; exact hread i
      · rcases hop with rfl | rfl | rfl
        · simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          have h1 : canon fullMask (w.getD i 0 &&& (w.getD j 0 &&& fullMask)) =
              canon fullMask (w.getD i 0 &&& w.getD j 0) := by
            rw [← canon_land fullMask (w.getD i 0 &&& (w.getD j 0 &&& fullMask))]
            rw [← canon_land fullMask (w.getD i 0 &&& w.getD j 0)]
            congr 1; apply Nat.eq_of_testBit_eq; intro k; simp only [Nat.testBit_and]
            cases (w.getD i 0).testBit k <;> cases (w.getD j 0).testBit k <;> cases fullMask.testBit k <;> rfl
          rw [h1]
          rcases canon_and_in_binOp fullMask (w.getD i 0) (w.getD j 0) with h0 | hi' | hj' | ⟨op', hop', hbin⟩
          · left; exact Or.inl h0
          · left; rw [hi']; exact hread i
          · left; rw [hj']; exact hread j
          · right; exact ⟨rfl, canon fullMask (w.getD i 0), canon fullMask (w.getD j 0), op', hop', hread i, hread j, hbin⟩
        · simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero]
          rcases canon_or_in_binOp fullMask (w.getD i 0) (w.getD j 0) with h0 | hi' | hj' | ⟨op', hop', hbin⟩
          · left; exact Or.inl h0
          · left; rw [hi']; exact hread i
          · left; rw [hj']; exact hread j
          · right; exact ⟨rfl, canon fullMask (w.getD i 0), canon fullMask (w.getD j 0), op', hop', hread i, hread j, hbin⟩
        · left; simp only [z, actionWord, List.head?_cons, Option.map_some, Option.getD_some]
          rw [canon_xor_mask]; exact hread i
    rcases hstep with hav | ⟨hbin, hgate⟩
    · have hw' : ∀ u ∈ w ++ [z], Avail bank (canon fullMask u) := by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact hw u hu
        · rw [List.mem_singleton.mp hu]; exact hav
      obtain ⟨vs, hlen, hbd, hall⟩ := ih hgs (w ++ [z]) bank hw'
      have hbc : binaryCost gs ≤ binaryCost (g :: gs) := by
        unfold binaryCost; simp only [List.filter]; cases isBinary g <;> simp
      exact ⟨vs, Nat.le_trans hlen hbc, hbd, hall⟩
    · set cz := canon fullMask z
      have hw' : ∀ u ∈ w ++ [z], Avail (cz :: bank) (canon fullMask u) := by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact avail_weaken (fun a ha => List.mem_cons_of_mem _ ha) (hw u hu)
        · rw [List.mem_singleton.mp hu]; exact Or.inr List.mem_cons_self
      obtain ⟨vs, hlen, hbd, hall⟩ := ih hgs (w ++ [z]) (cz :: bank) hw'
      have hbc : binaryCost (g :: gs) = binaryCost gs + 1 := by
        unfold binaryCost; simp [hbin]
      refine ⟨cz :: vs, by simp only [List.length_cons, hbc]; omega, ⟨hgate, hbd⟩, ?_⟩
      intro u hu
      exact avail_weaken (fun a ha => by simp only [List.mem_append, List.mem_cons] at ha ⊢; tauto) (hall u hu)
theorem foldl_evalBit (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w : List Nat) {k : Nat} (hk : k < 64) :
    gs.foldl stepBool (w.map (evalBit k)) =
      (gs.foldl (fun acc g => acc ++ [actionWord acc g]) w).map (evalBit k) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [actionWord_spec w g (hg g List.mem_cons_self) hk]
    exact ih (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (w ++ [actionWord w g])
theorem rawVars_ofFn (x : Fin 6 → Bool) :
    List.ofFn x = rawVars.map (evalBit (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) := by
  have hx : ∀ (b0 b1 b2 b3 b4 b5 : Bool),
      [b0, b1, b2, b3, b4, b5] =
      rawVars.map (evalBit ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
        (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0))) := by
    decide +kernel
  have hsum : (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) =
      (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) +
      (if x 3 then 8 else 0) + (if x 4 then 16 else 0) + (if x 5 then 32 else 0) := by
    simp [Fin.sum_univ_six]
  rw [hsum, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  exact hx (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
theorem sum_bits_6 (n : Nat) (hn : n < 64) :
    (∑ i : Fin 6, if n.testBit i.val then 2 ^ (i : Nat) else 0) = n := by
  simp only [Fin.sum_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two]
  change (if n.testBit 0 then 1 else 0) + (if n.testBit 1 then 2 else 0) +
    (if n.testBit 2 then 4 else 0) + (if n.testBit 3 then 8 else 0) +
    (if n.testBit 4 then 16 else 0) + (if n.testBit 5 then 32 else 0) = n
  revert n; decide +kernel
theorem table2_from_lowerBin (target m : Nat)
    (hlow : LowerBin fullMask rootStock (canon fullMask target) (m - 1))
    (wg : List Gate) (wout : Nat) (hsz : wg.length = m)
    (hmono : Monotone2 ⟨wg, wout⟩)
    (heval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, wout⟩ (List.ofFn x) =
      Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) :
    ∀ s : Nat, HasCircuitSize 6 (fun x : Fin 6 → Bool =>
      Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) s →
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool,
      C.eval (List.ofFn x) = Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) := by
  intro s ⟨C, hfan, hsize, hC⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, hgm, hgop⟩ := hasNot
    have hshort : binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g, hgm, by simp [isBinary, hgop]⟩
    have hleg : ∀ g ∈ C.gates, legal g := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hfan g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      exact ⟨hop, hlen⟩
    obtain ⟨vs, hvlen, hvbd, hvhit⟩ := compileBin_aux C.gates hleg rawVars rootStock rawVars_avail
    set finalW := C.gates.foldl (fun acc g => acc ++ [actionWord acc g]) rawVars
    have hout_eq : finalW.getD C.output 0 &&& fullMask = target &&& fullMask := by
      apply Nat.eq_of_testBit_eq; intro k
      by_cases hk : k < 64
      · have hfm := fullMask_bit hk
        simp only [Nat.testBit_and, hfm, Bool.and_true]
        let x : Fin 6 → Bool := fun i => k.testBit i.val
        have hxidx : (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) = k := sum_bits_6 k hk
        have h1 := hC x
        dsimp only at h1
        rw [hxidx, rawVars_ofFn x, hxidx] at h1
        change (C.gates.foldl stepBool (rawVars.map (evalBit k))).getD C.output false = target.testBit k at h1
        rw [foldl_evalBit C.gates hleg rawVars hk, readBit] at h1
        exact h1
      · have hfm0 : fullMask.testBit k = false := by
          rw [fullMask_eq, Nat.testBit_two_pow_sub_one]; simp [hk]
        simp [Nat.testBit_and, hfm0]
    have hout_avail : Avail (vs ++ rootStock) (canon fullMask target) := by
      rw [← canon_land fullMask target, ← hout_eq, canon_land]
      by_cases hi : C.output < finalW.length
      · exact hvhit _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi), canon_zero]; exact Or.inl rfl
    have hge := hlow vs hvbd hout_avail
    have hcsz : C.size = C.gates.length := rfl
    have hwsz : (⟨wg, wout⟩ : Circuit).size = m := hsz
    exact ⟨⟨wg, wout⟩, hmono, by omega, heval⟩
  · refine ⟨C, ?_, hsize, hC⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
def memN (z : Nat) (l : List Nat) : Bool :=
  List.rec false (fun w _ ih => Bool.rec ih true (Nat.beq z w)) l
theorem memN_eq (z : Nat) (l : List Nat) : memN z l = l.contains z := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem]
  induction l with
  | nil => simp [memN]
  | cons w ws ih =>
    change Bool.rec (memN z ws) true (Nat.beq z w) = true ↔ z ∈ w :: ws
    cases h : Nat.beq z w
    · have hne : z ≠ w := ne_of_beq_false h
      simp [ih, hne]
    · have heq : z = w := Nat.eq_of_beq_eq_true h
      simp [heq]
def lenN (l : List Nat) : Nat :=
  List.rec 0 (fun _ _ ih => Nat.add ih 1) l
theorem lenN_eq (l : List Nat) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons _ ws ih => change Nat.add (lenN ws) 1 = ws.length + 1; rw [ih]
def getDN (l : List Nat) (i : Nat) : Nat :=
  (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun w _ ih k => Nat.rec w (fun m _ => ih m) k) l) i
theorem getDN_eq (l : List Nat) (i : Nat) : getDN l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons w ws ih =>
    cases i with
    | zero => rfl
    | succ m => change getDN ws m = (w :: ws).getD (m + 1) 0; rw [ih]; rfl
def eqListN (l1 : List Nat) : List Nat → Bool :=
  List.rec
    (fun l2 => List.rec true (fun _ _ _ => false) l2)
    (fun x _ ih l2 => List.rec false (fun y ys _ => Bool.rec false (ih ys) (Nat.beq x y)) l2) l1
theorem eqListN_eq (l1 l2 : List Nat) : eqListN l1 l2 = (l1 == l2) := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> rfl
  | cons x xs ih =>
    cases l2 with
    | nil => rfl
    | cons y ys =>
      change Bool.rec false (eqListN xs ys) (Nat.beq x y) = ((x :: xs) == (y :: ys))
      rw [ih]
      by_cases h : x = y
      · subst h; simp [Nat.beq_refl]
      · have h1 : Nat.beq x y = false := beq_false_ne h
        have h2 : (x == y) = false := beq_false_of_ne h
        simp [h1, h2]
def canonF (mask w : Nat) : Nat :=
  let v := Nat.land w mask
  Bool.rec
    (Bool.rec
      (let iv := Nat.xor mask v
       Bool.rec iv v (Nat.blt v iv))
      0 (Nat.beq v mask))
    0 (Nat.beq v 0)
theorem canonF_eq (mask w : Nat) : canonF mask w = canon mask w := by
  unfold canonF canon bsel; dsimp only
  change (Bool.rec (Bool.rec (Bool.rec (mask ^^^ (w &&& mask)) (w &&& mask) ((w &&& mask).blt (mask ^^^ (w &&& mask)))) 0 ((w &&& mask).beq mask)) 0 ((w &&& mask).beq 0) : Nat) = _
  cases Nat.beq (w &&& mask) 0 <;> cases Nat.beq (w &&& mask) mask <;> rfl
def binOpF (mask op a b : Nat) : Nat :=
  Bool.rec
    (Bool.rec
      (Bool.rec (canonF mask (Nat.land (Nat.xor mask a) b))
        (canonF mask (Nat.land a (Nat.xor mask b))) (Nat.beq op 2))
      (canonF mask (Nat.lor a b)) (Nat.beq op 1))
    (canonF mask (Nat.land a b)) (Nat.beq op 0)
theorem binOpF_eq (mask op a b : Nat) : binOpF mask op a b = binOp mask op a b := by
  unfold binOpF binOp bsel
  simp only [canonF_eq]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> rfl
def dagPartF (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Bool.rec (Nat.beq n 0) true (Nat.beq p 0))
    (fun w _ rest p n =>
      Bool.rec
        (Bool.rec
          (forceW (Nat.land p w) (fun up =>
            forceW (Nat.land n w) (fun down =>
              Bool.rec false
                (forceW (Nat.xor p up) (fun offP =>
                  forceW (Nat.xor n down) (rest offP)))
                (rest up down))))
          true (Nat.beq n 0))
        true (Nat.beq p 0)) ws
theorem dagPartF_eq (ws : List Nat) (p n : Nat) : dagPartF ws p n = dagPart ws p n := by
  induction ws generalizing p n with
  | nil =>
    change Bool.rec (Nat.beq n 0) true (Nat.beq p 0) = (Nat.beq p 0 || Nat.beq n 0)
    cases Nat.beq p 0 <;> rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (forceW (Nat.land p w) (fun up =>
      forceW (Nat.land n w) (fun down =>
        Bool.rec false (forceW (Nat.xor p up) (fun offP => forceW (Nat.xor n down) (dagPartF ws offP)))
          (dagPartF ws up down)))) true (Nat.beq n 0)) true (Nat.beq p 0) =
      ((Nat.beq p 0 || Nat.beq n 0) || forceW (p &&& w) (fun up =>
        forceW (n &&& w) (fun down => dagPart ws up down &&
          forceW (p ^^^ up) (fun offP => forceW (n ^^^ down) (dagPart ws offP)))))
    simp only [forceW_eq]
    cases Nat.beq p 0
    · cases Nat.beq n 0
      · change Bool.rec false (dagPartF ws _ _) (dagPartF ws _ _) = (dagPart ws _ _ && dagPart ws _ _)
        rw [ih, ih]; cases dagPart ws (p &&& w) (n &&& w) <;> rfl
      · rfl
    · rfl
def insertSortedF (x : Nat) (l : List Nat) : List Nat :=
  List.rec [x] (fun y ys ih => Bool.rec (y :: ih) (x :: y :: ys) (Nat.ble x y)) l
theorem insertSortedF_eq (x : Nat) (l : List Nat) : insertSortedF x l = insertSorted x l := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    change Bool.rec (y :: insertSortedF x ys) (x :: y :: ys) (Nat.ble x y) =
      bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys)
    rw [ih]; cases Nat.ble x y <;> rfl
def dropValF (drop : Bool) (x : Nat) (l : List Nat) : List Nat :=
  Bool.rec l (List.rec [] (fun y _ ih => Bool.rec (y :: ih) ih (Nat.beq y x)) l) drop
theorem dropValF_eq (drop : Bool) (x : Nat) (l : List Nat) : dropValF drop x l = dropVal drop x l := by
  cases drop
  · rfl
  · induction l with
    | nil => rfl
    | cons y ys ih =>
      change Bool.rec (y :: dropValF true x ys) (dropValF true x ys) (Nat.beq y x) =
        bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys)
      rw [ih]; cases Nat.beq y x <;> rfl
def subsetWordsF (stock : List Nat) (bits : Nat) : List Nat :=
  (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih b =>
      let rest := ih (Nat.shiftRight b 1)
      Bool.rec rest (insertSortedF w rest) (Nat.beq (Nat.land b 1) 1)) stock) bits
theorem subsetWordsF_eq (stock : List Nat) (bits : Nat) : subsetWordsF stock bits = subsetWords stock bits := by
  induction stock generalizing bits with
  | nil => rfl
  | cons x xs ih =>
    change Bool.rec (subsetWordsF xs (Nat.shiftRight bits 1))
      (insertSortedF x (subsetWordsF xs (Nat.shiftRight bits 1))) (Nat.beq (Nat.land bits 1) 1) =
      bsel (Nat.beq (bits &&& 1) 1) (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1))
    rw [ih, insertSortedF_eq]; cases Nat.beq (bits &&& 1) 1 <;> rfl
def childStateF (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, hist) := state
  let keep := Nat.land token 3
  let op := Nat.land (Nat.shiftRight token 2) 3
  let b := Nat.land (Nat.shiftRight token 4) 15
  let a := Nat.shiftRight token 8
  Bool.rec
    (Bool.rec none
      (Bool.rec none
        (let x := getDN ws a
         let y := getDN ws b
         let z := binOpF mask op x y
         Bool.rec
           (Bool.rec
             (let keepA := Nat.beq (Nat.land keep 1) 1
              let keepB := Nat.beq (Nat.land (Nat.shiftRight keep 1) 1) 1
              let rest := dropValF (Bool.rec true false keepA) x (dropValF (Bool.rec true false keepB) y ws)
              some (Nat.sub fuel 1, insertSortedF z rest, (z, x, y) :: hist))
             none (memN z ws))
           none (Nat.beq z 0))
        (Nat.blt b (lenN ws)))
      (Nat.blt a b))
    none (Nat.beq fuel 0)
theorem childStateF_eq (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    childStateF mask token state = childState mask token state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold childStateF childState
  simp only [lenN_eq, getDN_eq, binOpF_eq, memN_eq, dropValF_eq, insertSortedF_eq]
  cases Nat.beq fuel 0
  · cases Nat.blt (token >>> 8) ((token >>> 4) &&& 15)
    · rfl
    · cases Nat.blt ((token >>> 4) &&& 15) ws.length
      · rfl
      · cases Nat.beq (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0) (ws.getD ((token >>> 4) &&& 15) 0)) 0
        · cases ws.contains (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0) (ws.getD ((token >>> 4) &&& 15) 0))
          · cases Nat.beq ((token &&& 3) &&& 1) 1 <;> cases Nat.beq (((token &&& 3) >>> 1) &&& 1) 1 <;> rfl
          · rfl
        · rfl
  · rfl
def dagTraceF (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ prev j =>
      let (parent, token) := forest j
      Bool.rec
        (match prev (Nat.sub parent 1) with
         | none => none
         | some st => childStateF mask token st)
        (Bool.rec none (some (fuel, subsetWordsF stock token, []))
          (Nat.blt token (Nat.shiftLeft 1 (lenN stock))))
        (Nat.beq parent 0)) (Nat.add fuel 1)) i
theorem dagTraceF_eq (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    dagTraceF mask stock fuel forest i = dagTrace mask stock fuel forest i := by
  unfold dagTraceF dagTrace
  suffices ∀ steps j,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          Bool.rec
            (match prev (Nat.sub parent 1) with
             | none => none
             | some st => childStateF mask token st)
            (Bool.rec none (some (fuel, subsetWordsF stock token, []))
              (Nat.blt token (Nat.shiftLeft 1 (lenN stock))))
            (Nat.beq parent 0)) steps) j =
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j from
    this (fuel + 1) i
  intro steps
  induction steps with
  | zero => intro j; rfl
  | succ n ih =>
    intro j
    dsimp only
    have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
      rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
    cases Nat.beq (forest j).1 0
    · dsimp only
      rw [ih]
      cases (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          if Nat.beq (forest k).1 0 then
            if Nat.blt (forest k).2 (2 ^ stock.length) then some (rootState stock fuel (forest k).2) else none
          else (prev ((forest k).1 - 1)).bind (childState mask (forest k).2)) n) ((forest j).1 - 1)
      · rfl
      · exact childStateF_eq mask (forest j).2 _
    · dsimp only
      rw [hpow, subsetWordsF_eq]
      cases Nat.blt (forest j).2 (2 ^ stock.length) <;> rfl
def nthBound (bounds : List (Nat × List Nat × Nat × Nat)) (i : Nat) :
    Option (Nat × List Nat × Nat × Nat) :=
  (List.rec (motive := fun _ => Nat → Option (Nat × List Nat × Nat × Nat))
    (fun _ => none)
    (fun b _ ih k => Nat.rec (some b) (fun m _ => ih m) k) bounds) i
theorem nthBound_mem {bounds : List (Nat × List Nat × Nat × Nat)} {i : Nat} {b : Nat × List Nat × Nat × Nat}
    (h : nthBound bounds i = some b) : b ∈ bounds := by
  induction bounds generalizing i with
  | nil => simp [nthBound] at h
  | cons x xs ih =>
    cases i with
    | zero => cases h; exact List.mem_cons_self
    | succ m => exact List.mem_cons_of_mem _ (ih h)
def forceWP {α : Type} (w : Nat) (k : Nat → α) : α :=
  match w with
  | 0 => k 0
  | m + 1 => k (m + 1)
theorem forceWP_eq {α : Type} (w : Nat) (k : Nat → α) : forceWP w k = k w := by
  cases w <;> rfl
def forceCons {α : Type} (l : List Nat) (k : List Nat → α) : α :=
  match l with
  | [] => k []
  | x :: xs => k (x :: xs)
theorem forceCons_eq {α : Type} (l : List Nat) (k : List Nat → α) : forceCons l k = k l := by
  cases l <;> rfl
def forceList {α : Type} (ws : List Nat) (k : List Nat → α) : α :=
  (List.rec (motive := fun _ => (List Nat → α) → α) (fun k => k [])
    (fun w _ next k => next (fun rest => k (w :: rest))) ws) k
theorem forceList_eq {α : Type} (ws : List Nat) (k : List Nat → α) : forceList ws k = k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceList ws (fun rest => k (w :: rest)) = _
    rw [ih]
def canonV2 (mask w : Nat) : Nat :=
  forceWP (Nat.land w mask) (fun v =>
    Bool.rec
      (Bool.rec
        (forceWP (Nat.xor mask v) (fun iv => Bool.rec iv v (Nat.blt v iv)))
        0 (Nat.beq v mask))
      0 (Nat.beq v 0))
theorem canonV2_eq (mask w : Nat) : canonV2 mask w = canon mask w := by
  unfold canonV2 canon bsel; dsimp only
  rw [forceWP_eq]
  change Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (forceWP (Nat.xor mask (w &&& mask)) (fun iv => Bool.rec (motive := fun _ => Nat) iv (w &&& mask) (Nat.blt (w &&& mask) iv)))
      0 (Nat.beq (w &&& mask) mask)) 0 (Nat.beq (w &&& mask) 0) = _
  rw [forceWP_eq]
  cases Nat.beq (w &&& mask) 0 <;> cases Nat.beq (w &&& mask) mask <;> rfl
def HistValid (mask : Nat) (stock : List Nat) : List (Nat × Nat × Nat) → Prop
  | [] => True
  | (z, x, y) :: rest =>
    (∃ op < 4, z = binOp mask op x y) ∧
    (x ∈ stock ∨ ∃ a b, (x, a, b) ∈ rest) ∧
    (y ∈ stock ∨ ∃ a b, (y, a, b) ∈ rest) ∧
    HistValid mask stock rest
def WsCovered (stock : List Nat) (hist : List (Nat × Nat × Nat)) (ws : List Nat) : Prop :=
  ∀ w ∈ ws, w ∈ stock ∨ ∃ a b, (w, a, b) ∈ hist
theorem getD_mem_of_lt {l : List Nat} {i : Nat} (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi
theorem childState_valid {mask token : Nat} {stock : List Nat}
    {st ch : Nat × List Nat × List (Nat × Nat × Nat)}
    (hv : HistValid mask stock st.2.2) (hc : WsCovered stock st.2.2 st.2.1)
    (h : childState mask token st = some ch) :
    HistValid mask stock ch.2.2 ∧ WsCovered stock ch.2.2 ch.2.1 := by
  obtain ⟨fuel, ws, hist⟩ := st
  dsimp only at hv hc
  unfold childState at h; dsimp only at h
  split at h
  · contradiction
  · rename_i hok
    split at h
    · contradiction
    · have heq := Option.some.inj h
      subst ch
      simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hok
      have hab : (token >>> 8) < ((token >>> 4) &&& 15) := by
        cases h1 : Nat.blt (token >>> 8) ((token >>> 4) &&& 15)
        · exfalso; exact hok (Or.inl (Or.inr h1))
        · exact Nat.blt_eq.mp h1
      have hbl : ((token >>> 4) &&& 15) < ws.length := by
        cases h2 : Nat.blt ((token >>> 4) &&& 15) ws.length
        · exfalso; exact hok (Or.inr h2)
        · exact Nat.blt_eq.mp h2
      have hx : ws.getD (token >>> 8) 0 ∈ ws := getD_mem_of_lt (by omega)
      have hy : ws.getD ((token >>> 4) &&& 15) 0 ∈ ws := getD_mem_of_lt hbl
      have hop : ((token >>> 2) &&& 3) < 4 := by
        have := Nat.and_lt_two_pow (token >>> 2) (n := 2) (by omega : 3 < 2 ^ 2)
        simpa using this
      refine ⟨⟨⟨(token >>> 2) &&& 3, hop, rfl⟩, hc _ hx, hc _ hy, hv⟩, ?_⟩
      intro w hw
      rcases insertSorted_mem.mp hw with rfl | hrest
      · exact Or.inr ⟨_, _, List.mem_cons_self⟩
      · have hwm : w ∈ ws := (dropVal_mem.mp (dropVal_mem.mp hrest).1).1
        rcases hc w hwm with hst | ⟨a, b, hmem⟩
        · exact Or.inl hst
        · exact Or.inr ⟨a, b, List.mem_cons_of_mem _ hmem⟩
theorem dagTrace_valid {mask fuel : Nat} {stock : List Nat} {forest : Nat → Nat × Nat}
    {i : Nat} {st : Nat × List Nat × List (Nat × Nat × Nat)}
    (h : dagTrace mask stock fuel forest i = some st) :
    HistValid mask stock st.2.2 ∧ WsCovered stock st.2.2 st.2.1 := by
  unfold dagTrace at h
  suffices ∀ steps j s,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j = some s →
      HistValid mask stock s.2.2 ∧ WsCovered stock s.2.2 s.2.1 from
    this (fuel + 1) i st h
  intro steps
  induction steps with
  | zero => intro j s h; contradiction
  | succ n ih =>
    intro j s h; dsimp only at h
    split at h
    · split at h
      · have e := Option.some.inj h; subst s
        exact ⟨trivial, fun w hw => Or.inl (subsetWords_subset stock _ w hw)⟩
      · contradiction
    · cases hp : (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) n) ((forest j).1 - 1) with
      | none => rw [hp] at h; contradiction
      | some p =>
        rw [hp] at h
        have ⟨hv, hc⟩ := ih _ _ hp
        exact childState_valid hv hc h
theorem addUniq_mem {w u : Nat} {l : List Nat} : u ∈ addUniq w l ↔ u = w ∨ u ∈ l := by
  unfold addUniq
  cases h : l.contains w
  · simp [List.mem_cons]
  · simp only [ite_true]
    have hw : w ∈ l := List.contains_iff_mem.mp h
    constructor
    · exact Or.inr
    · rintro (rfl | hu); exact hw; exact hu
theorem recipeStart_mem {cut : Nat} {stock ws : List Nat} {u : Nat} :
    u ∈ recipeStart cut stock ws ↔ ∃ w ∈ ws, canon cut w = u ∧ ¬Avail stock u := by
  induction ws with
  | nil => simp [recipeStart]
  | cons w ws ih =>
    change u ∈ (if availB stock (canon cut w) then recipeStart cut stock ws
                else addUniq (canon cut w) (recipeStart cut stock ws)) ↔ _
    cases ha : availB stock (canon cut w)
    · simp only [Bool.false_eq_true, ite_false, addUniq_mem, ih]
      have hna : ¬Avail stock (canon cut w) := fun h => by rw [availB_spec.mpr h] at ha; exact Bool.noConfusion ha
      constructor
      · rintro (rfl | ⟨w', hw', rfl, hnu⟩)
        · exact ⟨w, List.mem_cons_self, rfl, hna⟩
        · exact ⟨w', List.mem_cons_of_mem _ hw', rfl, hnu⟩
      · rintro ⟨w', hw', rfl, hnu⟩
        rcases List.mem_cons.mp hw' with rfl | hw'
        · exact Or.inl rfl
        · exact Or.inr ⟨w', hw', rfl, hnu⟩
    · simp only [ite_true, ih]
      have hya : Avail stock (canon cut w) := availB_spec.mp ha
      constructor
      · rintro ⟨w', hw', rfl, hnu⟩; exact ⟨w', List.mem_cons_of_mem _ hw', rfl, hnu⟩
      · rintro ⟨w', hw', rfl, hnu⟩
        rcases List.mem_cons.mp hw' with rfl | hw'
        · exact absurd hya hnu
        · exact ⟨w', hw', rfl, hnu⟩
theorem recipeClose_sub {cut : Nat} {stock : List Nat} {hist : List (Nat × Nat × Nat)} {acc : List Nat} :
    ∀ u ∈ acc, u ∈ recipeClose cut stock hist acc := by
  induction hist generalizing acc with
  | nil => intro u hu; exact hu
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    intro u hu
    change u ∈ (if acc.contains (canon cut w) then
      let va := canon cut a; let vb := canon cut b
      let acc1 := if availB stock va then acc else addUniq va acc
      let acc2 := if availB stock vb then acc1 else addUniq vb acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist acc)
    split
    · apply ih
      have h1 : u ∈ (if availB stock (canon cut a) then acc else addUniq (canon cut a) acc) := by
        split; exact hu; exact addUniq_mem.mpr (Or.inr hu)
      split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
    · exact ih u hu
theorem recipeClose_nil (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) :
    recipeClose cut stock hist [] = [] := by
  induction hist with
  | nil => rfl
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    change (if [].contains (canon cut w) then _ else recipeClose cut stock hist []) = []
    exact ih
theorem recipeClose_mono {cut : Nat} {stock : List Nat} {hist : List (Nat × Nat × Nat)} :
    ∀ {A B : List Nat}, (∀ u ∈ A, u ∈ B) →
      ∀ u ∈ recipeClose cut stock hist A, u ∈ recipeClose cut stock hist B := by
  induction hist with
  | nil => intro A B hAB u hu; exact hAB u hu
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    intro A B hAB u hu
    change u ∈ (if A.contains (canon cut w) then
      let acc1 := if availB stock (canon cut a) then A else addUniq (canon cut a) A
      let acc2 := if availB stock (canon cut b) then acc1 else addUniq (canon cut b) acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist A) at hu
    change u ∈ (if B.contains (canon cut w) then
      let acc1 := if availB stock (canon cut a) then B else addUniq (canon cut a) B
      let acc2 := if availB stock (canon cut b) then acc1 else addUniq (canon cut b) acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist B)
    cases hA : A.contains (canon cut w)
    · simp only [hA, Bool.false_eq_true, ite_false] at hu
      cases hB : B.contains (canon cut w)
      · simp only [Bool.false_eq_true, ite_false]; exact ih hAB u hu
      · simp only [ite_true]
        apply ih _ u hu
        intro x hx
        have h1 : x ∈ (if availB stock (canon cut a) then B else addUniq (canon cut a) B) := by
          split; exact hAB x hx; exact addUniq_mem.mpr (Or.inr (hAB x hx))
        split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
    · have hwB : B.contains (canon cut w) = true := List.contains_iff_mem.mpr (hAB _ (List.contains_iff_mem.mp hA))
      simp only [hA, ite_true] at hu
      simp only [hwB, ite_true]
      apply ih _ u hu
      intro x hx
      have h1 : ∀ y, y ∈ (if availB stock (canon cut a) then A else addUniq (canon cut a) A) →
          y ∈ (if availB stock (canon cut a) then B else addUniq (canon cut a) B) := by
        intro y hy
        cases hca : availB stock (canon cut a)
        · simp only [hca, Bool.false_eq_true, ite_false, addUniq_mem] at hy ⊢
          rcases hy with rfl | hy; exact Or.inl rfl; exact Or.inr (hAB y hy)
        · simp only [hca, ite_true] at hy ⊢; exact hAB y hy
      cases hcb : availB stock (canon cut b)
      · simp only [hcb, Bool.false_eq_true, ite_false, addUniq_mem] at hx ⊢
        rcases hx with rfl | hx; exact Or.inl rfl; exact Or.inr (h1 x hx)
      · simp only [hcb, ite_true] at hx ⊢; exact h1 x hx
noncomputable def buildFrom (cut : Nat) (bstock : List Nat) (S : Finset Nat) :
    List (Nat × Nat × Nat) → List Nat
  | [] => []
  | (z, x, y) :: rest =>
    let vs := buildFrom cut bstock S rest
    let v := canon cut z
    let := Classical.propDecidable
    if v ∈ S ∧ ¬Avail (vs ++ bstock) v ∧ Avail (vs ++ bstock) (canon cut x) ∧ Avail (vs ++ bstock) (canon cut y)
    then vs ++ [v] else vs
theorem buildFrom_builds {mask cut : Nat} {stock bstock : List Nat} {S : Finset Nat}
    (sub : mask &&& cut = cut) :
    ∀ {hist : List (Nat × Nat × Nat)}, HistValid mask stock hist →
      BuildsBin cut bstock (buildFrom cut bstock S hist)
  | [], _ => trivial
  | (z, x, y) :: rest, ⟨⟨op, hop, hz⟩, _, _, hrest⟩ => by
    unfold buildFrom; dsimp only
    have ih := buildFrom_builds (bstock := bstock) (S := S) sub hrest
    split
    · rename_i hcond
      obtain ⟨_, hna, hax, hay⟩ := hcond
      have hgate : GateBin cut (buildFrom cut bstock S rest ++ bstock) (canon cut z) := by
        have hsub := canon_sub_binOp (op := op) (a := x) (b := y) sub
        rw [← hz] at hsub
        rcases hsub with h0 | hx | hy | ⟨op', hop', heq⟩
        · exact absurd (Or.inl h0) hna
        · exact absurd (hx ▸ hax) hna
        · exact absurd (hy ▸ hay) hna
        · exact ⟨canon cut x, canon cut y, op', hop', hax, hay, heq⟩
      exact builds_append ih ⟨hgate, trivial⟩
    · exact ih
theorem buildFrom_nodup_sub (cut : Nat) (bstock : List Nat) (S : Finset Nat) :
    ∀ (hist : List (Nat × Nat × Nat)),
      (buildFrom cut bstock S hist).Nodup ∧ ∀ u ∈ buildFrom cut bstock S hist, u ∈ S
  | [] => ⟨List.nodup_nil, fun _ h => nomatch h⟩
  | (z, x, y) :: rest => by
    unfold buildFrom; dsimp only
    obtain ⟨hnd, hsub⟩ := buildFrom_nodup_sub cut bstock S rest
    split
    · rename_i hcond
      obtain ⟨hvS, hna, _, _⟩ := hcond
      have hnm : canon cut z ∉ buildFrom cut bstock S rest := fun hm =>
        hna (Or.inr (List.mem_append_left bstock hm))
      refine ⟨List.nodup_append.mpr ⟨hnd, List.nodup_singleton _, fun a ha b hb heq => by
        rw [List.mem_singleton.mp hb] at heq; exact hnm (heq ▸ ha)⟩, ?_⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact hsub u hu
      · rw [List.mem_singleton.mp hu]; exact hvS
    · exact ⟨hnd, hsub⟩
theorem buildFrom_mono_avail (cut : Nat) (bstock : List Nat) (S : Finset Nat)
    (r : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) {u : Nat}
    (hu : Avail (buildFrom cut bstock S rest ++ bstock) u) :
    Avail (buildFrom cut bstock S (r :: rest) ++ bstock) u := by
  obtain ⟨z, x, y⟩ := r
  unfold buildFrom; dsimp only
  split
  · exact avail_weaken (fun w hw => by simp only [List.mem_append] at hw ⊢; tauto) hu
  · exact hu
theorem buildFrom_covers {mask cut : Nat} {stock bstock : List Nat} {S : Finset Nat}
    (hstk : ∀ s ∈ stock, Avail bstock (canon cut s)) :
    ∀ {hist : List (Nat × Nat × Nat)}, HistValid mask stock hist →
      ∀ (acc : List Nat),
        (∀ u ∈ acc, Avail bstock u ∨ ∃ z x y, (z, x, y) ∈ hist ∧ canon cut z = u) →
        (∀ u ∈ recipeClose cut bstock hist acc, u ∈ S) →
        ∀ u ∈ acc, Avail (buildFrom cut bstock S hist ++ bstock) u
  | [], _, acc, hcov, _, u, hu => by
    rcases hcov u hu with ha | ⟨_, _, _, hm, _⟩
    · exact avail_weaken (fun w hw => List.mem_append_right _ hw) ha
    · exact nomatch hm
  | (z, x, y) :: rest, ⟨_, hxc, hyc, hrest⟩, acc, hcov, hS, u, hu => by
    cases hcz : acc.contains (canon cut z)
    · have hnz : canon cut z ∉ acc := fun hm => by rw [List.contains_iff_mem.mpr hm] at hcz; exact Bool.noConfusion hcz
      have hS' : ∀ v ∈ recipeClose cut bstock rest acc, v ∈ S := by
        intro v hv; apply hS v
        change v ∈ (if acc.contains (canon cut z) then _ else recipeClose cut bstock rest acc)
        simp only [hcz, Bool.false_eq_true, ite_false]; exact hv
      have hcov' : ∀ v ∈ acc, Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v := by
        intro v hv
        rcases hcov v hv with ha | ⟨z', x', y', hm, heq⟩
        · exact Or.inl ha
        · rcases List.mem_cons.mp hm with hhead | htail
          · rcases Prod.mk.inj hhead with ⟨rfl, _⟩
            exact absurd (heq ▸ hv) hnz
          · exact Or.inr ⟨z', x', y', htail, heq⟩
      exact buildFrom_mono_avail cut bstock S (z, x, y) rest
        (buildFrom_covers hstk hrest acc hcov' hS' u hu)
    · have hzacc : canon cut z ∈ acc := List.contains_iff_mem.mp hcz
      have hzS : canon cut z ∈ S := hS _ (recipeClose_sub _ hzacc)
      set acc1 := if availB bstock (canon cut x) then acc else addUniq (canon cut x) acc
      set acc2 := if availB bstock (canon cut y) then acc1 else addUniq (canon cut y) acc1
      have hS2 : ∀ v ∈ recipeClose cut bstock rest acc2, v ∈ S := by
        intro v hv; apply hS v
        change v ∈ (if acc.contains (canon cut z) then recipeClose cut bstock rest acc2 else _)
        simp only [hcz, ite_true]; exact hv
      let := Classical.propDecidable
      set acc' := acc2.filter (fun v => decide (Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v))
      have hsub' : ∀ v ∈ acc', v ∈ acc2 := fun v hv => (List.mem_filter.mp hv).1
      have hcov' : ∀ v ∈ acc', Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v :=
        fun v hv => of_decide_eq_true (List.mem_filter.mp hv).2
      have hS' : ∀ v ∈ recipeClose cut bstock rest acc', v ∈ S :=
        fun v hv => hS2 v (recipeClose_mono hsub' v hv)
      have hIH := buildFrom_covers hstk hrest acc' hcov' hS'
      have hacc_sub2 : ∀ v ∈ acc, v ∈ acc2 := by
        intro v hv
        have h1 : v ∈ acc1 := by
          unfold acc1; split; exact hv; exact addUniq_mem.mpr (Or.inr hv)
        unfold acc2; split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
      have hax : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut x) := by
        cases hbx : availB bstock (canon cut x)
        · have hx2 : canon cut x ∈ acc2 := by
            have hx1 : canon cut x ∈ acc1 := by
              unfold acc1; simp only [hbx, Bool.false_eq_true, ite_false]; exact addUniq_mem.mpr (Or.inl rfl)
            unfold acc2; split; exact hx1; exact addUniq_mem.mpr (Or.inr hx1)
          have hpx : Avail bstock (canon cut x) ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = canon cut x := by
            rcases hxc with hs | ⟨a, b, hm⟩
            · exact Or.inl (hstk x hs)
            · exact Or.inr ⟨x, a, b, hm, rfl⟩
          exact hIH _ (List.mem_filter.mpr ⟨hx2, decide_eq_true hpx⟩)
        · exact avail_weaken (fun w hw => List.mem_append_right _ hw) (availB_spec.mp hbx)
      have hay : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut y) := by
        cases hby : availB bstock (canon cut y)
        · have hy2 : canon cut y ∈ acc2 := by
            unfold acc2; simp only [hby, Bool.false_eq_true, ite_false]; exact addUniq_mem.mpr (Or.inl rfl)
          have hpy : Avail bstock (canon cut y) ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = canon cut y := by
            rcases hyc with hs | ⟨a, b, hm⟩
            · exact Or.inl (hstk y hs)
            · exact Or.inr ⟨y, a, b, hm, rfl⟩
          exact hIH _ (List.mem_filter.mpr ⟨hy2, decide_eq_true hpy⟩)
        · exact avail_weaken (fun w hw => List.mem_append_right _ hw) (availB_spec.mp hby)
      by_cases huz : u = canon cut z
      · subst huz
        unfold buildFrom; dsimp only
        split
        · exact Or.inr (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))
        · rename_i hneg
          by_cases ha : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut z)
          · exact ha
          · exact absurd ⟨hzS, ha, hax, hay⟩ hneg
      · have hpu : Avail bstock u ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = u := by
          rcases hcov u hu with ha | ⟨z', x', y', hm, heq⟩
          · exact Or.inl ha
          · rcases List.mem_cons.mp hm with hhead | htail
            · rcases Prod.mk.inj hhead with ⟨rfl, _⟩; exact absurd heq.symm huz
            · exact Or.inr ⟨z', x', y', htail, heq⟩
        exact buildFrom_mono_avail cut bstock S (z, x, y) rest
          (hIH u (List.mem_filter.mpr ⟨hacc_sub2 u hu, decide_eq_true hpu⟩))
def flatStartF (cut : Nat) (stock ws : List Nat) : Nat × List Nat :=
  List.rec (0, []) (fun w _ ih =>
    match ih with
    | (fl, acc) =>
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec
          (Bool.rec
            (Bool.rec (fl, v :: acc) (fl, acc) (memN v acc))
            (fl, acc) (memN v stock))
          (forceWP (Nat.add fl 1) (fun fl1 => (fl1, acc)))
          (Nat.beq v 0))) ws
theorem flatStartF_eq (cut : Nat) (stock ws : List Nat) :
    flatStartF cut stock ws = (flatCount cut ws, recipeStart cut stock ws) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hstep : flatStartF cut stock (w :: ws) =
      match flatStartF cut stock ws with
      | (fl, acc) =>
        forceWP (canonV2 cut w) (fun v =>
          Bool.rec
            (Bool.rec
              (Bool.rec (fl, v :: acc) (fl, acc) (memN v acc))
              (fl, acc) (memN v stock))
            (forceWP (Nat.add fl 1) (fun fl1 => (fl1, acc)))
            (Nat.beq v 0)) := rfl
    rw [hstep, ih]; dsimp only; rw [forceWP_eq, canonV2_eq, forceWP_eq]
    change Bool.rec
        (Bool.rec
          (Bool.rec (flatCount cut ws, canon cut w :: recipeStart cut stock ws)
            (flatCount cut ws, recipeStart cut stock ws) (memN (canon cut w) (recipeStart cut stock ws)))
          (flatCount cut ws, recipeStart cut stock ws) (memN (canon cut w) stock))
        (Nat.add (flatCount cut ws) 1, recipeStart cut stock ws) (Nat.beq (canon cut w) 0) =
      (bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws),
       if availB stock (canon cut w) then recipeStart cut stock ws else addUniq (canon cut w) (recipeStart cut stock ws))
    simp only [memN_eq, availB, addUniq]
    have haux (b1 b2 b3 : Bool) :
        Bool.rec (Bool.rec (Bool.rec (flatCount cut ws, canon cut w :: recipeStart cut stock ws)
          (flatCount cut ws, recipeStart cut stock ws) b3)
          (flatCount cut ws, recipeStart cut stock ws) b2)
          (Nat.add (flatCount cut ws) 1, recipeStart cut stock ws) b1 =
        (bsel b1 (flatCount cut ws + 1) (flatCount cut ws),
         if (b1 || b2) = true then recipeStart cut stock ws
         else if b3 = true then recipeStart cut stock ws else canon cut w :: recipeStart cut stock ws) := by
      cases b1 <;> cases b2 <;> cases b3 <;> rfl
    exact haux _ _ _
def recipeCloseV2 (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec (next acc)
          (forceWP (canonV2 cut a) (fun va =>
            forceCons
              (Bool.rec (Bool.rec (Bool.rec (va :: acc) acc (memN va acc)) acc (memN va stock)) acc (Nat.beq va 0))
              (fun acc1 =>
                forceWP (canonV2 cut b) (fun vb =>
                  forceCons
                    (Bool.rec (Bool.rec (Bool.rec (vb :: acc1) acc1 (memN vb acc1)) acc1 (memN vb stock)) acc1 (Nat.beq vb 0))
                    next))))
          (memN v acc))) hist needed
theorem recipeCloseV2_eq (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) :
    recipeCloseV2 cut stock hist needed = recipeClose cut stock hist needed := by
  induction hist generalizing needed with
  | nil => rfl
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    have hstep : recipeCloseV2 cut stock ((w, a, b) :: hist) needed =
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec (recipeCloseV2 cut stock hist needed)
          (forceWP (canonV2 cut a) (fun va =>
            forceCons
              (Bool.rec (Bool.rec (Bool.rec (va :: needed) needed (memN va needed)) needed (memN va stock)) needed (Nat.beq va 0))
              (fun acc1 =>
                forceWP (canonV2 cut b) (fun vb =>
                  forceCons
                    (Bool.rec (Bool.rec (Bool.rec (vb :: acc1) acc1 (memN vb acc1)) acc1 (memN vb stock)) acc1 (Nat.beq vb 0))
                    (recipeCloseV2 cut stock hist)))))
          (memN v needed)) := rfl
    rw [hstep]
    simp only [forceWP_eq, forceCons_eq, canonV2_eq, memN_eq]
    change Bool.rec (recipeCloseV2 cut stock hist needed) _ (needed.contains (canon cut w)) =
      (if needed.contains (canon cut w) then
        let va := canon cut a; let vb := canon cut b
        let acc1 := if availB stock va then needed else addUniq va needed
        let acc2 := if availB stock vb then acc1 else addUniq vb acc1
        recipeClose cut stock hist acc2
      else recipeClose cut stock hist needed)
    cases needed.contains (canon cut w)
    · exact ih needed
    · dsimp only [ite_true]
      rw [ih]
      congr 1
      have hadd (v : Nat) (l : List Nat) :
          Bool.rec (Bool.rec (Bool.rec (v :: l) l (l.contains v)) l (stock.contains v)) l (Nat.beq v 0) =
          if availB stock v then l else addUniq v l := by
        dsimp only [availB, addUniq]
        have haux (b1 b2 b3 : Bool) :
            Bool.rec (Bool.rec (Bool.rec (v :: l) l b3) l b2) l b1 =
            if (b1 || b2) = true then l else if b3 = true then l else v :: l := by
          cases b1 <;> cases b2 <;> cases b3 <;> rfl
        exact haux _ _ _
      rw [hadd (canon cut a) needed, hadd (canon cut b)]
def boundClosesV2 (fuel : Nat) (ws : List Nat) (hist : List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, bstock, lower, _) := bound
  match flatStartF cut bstock ws with
  | (fl, start0) =>
    forceWP (Nat.sub fuel fl) (fun rem =>
      Bool.rec false
        (match start0 with
         | [] => true
         | s0 :: sr =>
           forceList (s0 :: sr) (fun start =>
             Bool.rec false
               (Nat.blt (Nat.add (lenN (recipeCloseV2 cut bstock hist start)) rem) lower)
               (Nat.blt (Nat.add (lenN start) rem) lower)))
        (Nat.blt rem lower))
theorem boundClosesV2_sound {mask goal : Nat} {stock : List Nat}
    {fuel : Nat} {ws : List Nat} {hist : List (Nat × Nat × Nat)}
    {bound : Nat × List Nat × Nat × Nat}
    (hlow : LowerBin bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (sub : mask &&& bound.1 = bound.1)
    (hg : canon bound.1 goal = bound.2.2.2) (hnz : bound.2.2.2 ≠ 0)
    (hstk : ∀ s ∈ stock, Avail bound.2.1 (canon bound.1 s))
    (hv : HistValid mask stock hist) (hc : WsCovered stock hist ws)
    (nd : ws.Nodup) {k : Nat} (hk : k ≤ fuel)
    (hlive : LiveBin mask goal k ws.toFinset) :
    boundClosesV2 fuel ws hist bound = false := by
  obtain ⟨cut, bstock, lower, bgoal⟩ := bound
  dsimp only at hlow sub hg hnz hstk
  apply Bool.eq_false_iff.mpr
  intro hbc
  unfold boundClosesV2 at hbc; dsimp only at hbc
  rw [flatStartF_eq] at hbc; dsimp only at hbc
  simp only [forceWP_eq] at hbc
  cases h1 : Nat.blt (Nat.sub fuel (flatCount cut ws)) lower
  · rw [h1] at hbc; exact Bool.noConfusion hbc
  · rw [h1] at hbc; dsimp only at hbc
    have hlen_lt : (recipeClose cut bstock hist (recipeStart cut bstock ws)).length + (fuel - flatCount cut ws) < lower := by
      cases hs : recipeStart cut bstock ws with
      | nil =>
        rw [recipeClose_nil]; simp only [List.length_nil, Nat.zero_add]
        exact Nat.blt_eq.mp h1
      | cons s0 sr =>
        rw [hs] at hbc; dsimp only at hbc
        simp only [forceList_eq, recipeCloseV2_eq, lenN_eq] at hbc
        cases h2 : Nat.blt (Nat.add (s0 :: sr).length (Nat.sub fuel (flatCount cut ws))) lower
        · rw [h2] at hbc; exact Bool.noConfusion hbc
        · rw [h2] at hbc; dsimp only at hbc
          exact Nat.blt_eq.mp hbc
    set needed := recipeClose cut bstock hist (recipeStart cut bstock ws)
    set S := needed.toFinset
    set vs := buildFrom cut bstock S hist
    have hvbd : BuildsBin cut bstock vs := buildFrom_builds sub hv
    obtain ⟨hvnd, hvsub⟩ := buildFrom_nodup_sub cut bstock S hist
    have hvlen : vs.length ≤ needed.length := by
      rw [← List.toFinset_card_of_nodup hvnd]
      have hsubf : vs.toFinset ⊆ S := fun u hu => hvsub u (List.mem_toFinset.mp hu)
      exact Nat.le_trans (Finset.card_le_card hsubf) (List.toFinset_card_le needed)
    have hcov_start : ∀ u ∈ recipeStart cut bstock ws,
        Avail bstock u ∨ ∃ z x y, (z, x, y) ∈ hist ∧ canon cut z = u := by
      intro u hu
      obtain ⟨w, hww, rfl, hna⟩ := recipeStart_mem.mp hu
      rcases hc w hww with hws | ⟨a, b, hmem⟩
      · exact absurd (hstk w hws) hna
      · exact Or.inr ⟨w, a, b, hmem, rfl⟩
    have hvs_start := buildFrom_covers hstk hv (recipeStart cut bstock ws) hcov_start
      (fun u hu => List.mem_toFinset.mpr hu)
    have hsup : ∀ w ∈ ws.toFinset, Avail (vs ++ bstock) (canon cut w) := by
      intro w hw
      have hww : w ∈ ws := List.mem_toFinset.mp hw
      by_cases ha : Avail bstock (canon cut w)
      · exact avail_weaken (fun u hu => List.mem_append_right _ hu) ha
      · exact hvs_start _ (recipeStart_mem.mpr ⟨w, hww, rfl, ha⟩)
    have hgnf : canon cut goal ≠ 0 := hg.symm ▸ hnz
    obtain ⟨ys, hylen, hybd, hyhit⟩ := maskedBuildBin sub hgnf hlive (vs ++ bstock) hsup
    rw [← flatCount_card cut nd] at hylen
    have hboth := builds_append hvbd hybd
    have hfinal : Avail ((vs ++ ys) ++ bstock) bgoal := by
      rw [← hg]
      exact avail_weaken (fun u hu => by simp only [List.mem_append] at hu ⊢; tauto) hyhit
    have heno := hlow (vs ++ ys) hboth hfinal
    simp only [List.length_append] at heno
    omega
def edgeAxis (mask goal stride lm : Nat) : Nat :=
  let neg := Nat.xor mask goal
  Nat.land (Nat.lor (Nat.land (Nat.shiftRight goal stride) neg)
    (Nat.land goal (Nat.shiftRight neg stride))) lm
def edgePack (mask goal : Nat) : Nat :=
  Nat.lor (edgeAxis mask goal 1 0x5555555555555555)
    (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 2 0x3333333333333333) 64)
      (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 4 0x0f0f0f0f0f0f0f0f) 128)
        (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 8 0x00ff00ff00ff00ff) 192)
          (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 16 0x0000ffff0000ffff) 256)
            (Nat.shiftLeft (edgeAxis mask goal 32 0x00000000ffffffff) 320)))))
def sepAxis (stride lm w : Nat) : Nat :=
  Nat.land (Nat.xor (Nat.shiftRight w stride) w) lm
def sepPack (w : Nat) : Nat :=
  Nat.lor (sepAxis 1 0x5555555555555555 w)
    (Nat.lor (Nat.shiftLeft (sepAxis 2 0x3333333333333333 w) 64)
      (Nat.lor (Nat.shiftLeft (sepAxis 4 0x0f0f0f0f0f0f0f0f w) 128)
        (Nat.lor (Nat.shiftLeft (sepAxis 8 0x00ff00ff00ff00ff w) 192)
          (Nat.lor (Nat.shiftLeft (sepAxis 16 0x0000ffff0000ffff w) 256)
            (Nat.shiftLeft (sepAxis 32 0x00000000ffffffff w) 320)))))
def orSep (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ ih => Nat.lor (sepPack w) ih) ws
theorem edgeAxis_live {mask goal stride lm k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset)
    {n : Nat} (he : (edgeAxis mask goal stride lm).testBit n = true) :
    ∃ w ∈ ws, (sepAxis stride lm w).testBit n = true := by
  unfold edgeAxis at he
  change (((goal >>> stride &&& (mask ^^^ goal)) ||| (goal &&& ((mask ^^^ goal) >>> stride))) &&& lm).testBit n = true at he
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight, Bool.and_eq_true, Bool.or_eq_true] at he
  obtain ⟨hcases, hlm⟩ := he
  have hpm : ∀ j, goal.testBit j = true → mask.testBit j = true := fun j hg => by
    have e := congrArg (fun x => x.testBit j) hgm
    simp only [Nat.testBit_and, hg, Bool.true_and] at e; exact e
  have hnm : ∀ j, (mask ^^^ goal).testBit j = true → mask.testBit j = true ∧ goal.testBit j = false := fun j hn => by
    rw [Nat.testBit_xor] at hn
    cases hm : mask.testBit j <;> cases hg : goal.testBit j <;> simp_all
  have hsep : ∃ w ∈ ws, w.testBit (stride + n) ≠ w.testBit n := by
    by_contra! hall
    rcases hcases with ⟨hg1, hn0⟩ | ⟨hg0, hn1⟩
    · have h1 := hpm (stride + n) hg1
      have h0 := hnm n hn0
      have eq := liveBin_agrees h1 h0.1 hlive (fun w hw => hall w (List.mem_toFinset.mp hw))
      rw [hg1, h0.2] at eq; exact Bool.noConfusion eq
    · have h0 := hpm n hg0
      have h1 := hnm (stride + n) hn1
      have eq := liveBin_agrees h0 h1.1 hlive (fun w hw => (hall w (List.mem_toFinset.mp hw)).symm)
      rw [hg0, h1.2] at eq; exact Bool.noConfusion eq
  obtain ⟨w, hw, hne⟩ := hsep
  refine ⟨w, hw, ?_⟩
  unfold sepAxis
  change (((w >>> stride) ^^^ w) &&& lm).testBit n = true
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight, hlm, Bool.and_true]
  cases hb1 : w.testBit (stride + n) <;> cases hb2 : w.testBit n <;> simp_all
theorem orSep_testBit {ws : List Nat} {w j : Nat}
    (hw : w ∈ ws) (hb : (sepPack w).testBit j = true) : (orSep ws).testBit j = true := by
  induction ws with
  | nil => cases hw
  | cons x xs ih =>
    change (sepPack x ||| orSep xs).testBit j = true
    rw [Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.mp hw with rfl | htl
    · exact Or.inl hb
    · exact Or.inr (ih htl)
theorem sepPack_live {mask goal k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset) :
    Nat.beq (Nat.land (edgePack mask goal) (orSep ws)) (edgePack mask goal) = true := by
  apply Nat.beq_eq.mpr
  apply Nat.eq_of_testBit_eq; intro j
  change ((edgePack mask goal) &&& (orSep ws)).testBit j = (edgePack mask goal).testBit j
  rw [Nat.testBit_and]
  cases he : (edgePack mask goal).testBit j
  · rfl
  · simp only [Bool.true_and]
    have hlane (stride lm shift : Nat)
        (hl : (edgeAxis mask goal stride lm <<< shift).testBit j = true)
        (hs : ∀ w, (sepAxis stride lm w <<< shift).testBit j = true → (sepPack w).testBit j = true) :
        (orSep ws).testBit j = true := by
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at hl
      obtain ⟨w, hw, hsw⟩ := edgeAxis_live hgm hlive hl.2
      apply orSep_testBit hw
      apply hs w
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hl.1, hsw⟩
    unfold edgePack at he
    change (edgeAxis mask goal 1 0x5555555555555555 |||
      ((edgeAxis mask goal 2 0x3333333333333333 <<< 64) |||
        ((edgeAxis mask goal 4 0x0f0f0f0f0f0f0f0f <<< 128) |||
          ((edgeAxis mask goal 8 0x00ff00ff00ff00ff <<< 192) |||
            ((edgeAxis mask goal 16 0x0000ffff0000ffff <<< 256) |||
              (edgeAxis mask goal 32 0x00000000ffffffff <<< 320)))))).testBit j = true at he
    simp only [Nat.testBit_or, Bool.or_eq_true] at he
    rcases he with h0 | h1 | h2 | h3 | h4 | h5
    · obtain ⟨w, hw, hsw⟩ := edgeAxis_live hgm hlive h0
      exact orSep_testBit hw (by
        unfold sepPack
        change (sepAxis 1 0x5555555555555555 w ||| _).testBit j = true
        simp [Nat.testBit_or, hsw])
    · exact hlane 2 0x3333333333333333 64 h1 (fun w hw => by
        unfold sepPack
        change (_ ||| ((sepAxis 2 0x3333333333333333 w <<< 64) ||| _)).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 4 0x0f0f0f0f0f0f0f0f 128 h2 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| ((sepAxis 4 0x0f0f0f0f0f0f0f0f w <<< 128) ||| _))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 8 0x00ff00ff00ff00ff 192 h3 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| ((sepAxis 8 0x00ff00ff00ff00ff w <<< 192) ||| _)))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 16 0x0000ffff0000ffff 256 h4 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| (_ ||| ((sepAxis 16 0x0000ffff0000ffff w <<< 256) ||| _))))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 32 0x00000000ffffffff 320 h5 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| (_ ||| (_ ||| (sepAxis 32 0x00000000ffffffff w <<< 320)))))).testBit j = true
        simp [Nat.testBit_or, hw])
def mapSep (ws : List Nat) : List (Nat × Nat) :=
  List.rec [] (fun w _ ih => (w, sepPack w) :: ih) ws
def forceSepPairs : List Nat → (List (Nat × Nat) → Bool) → Bool
  | [], k => k []
  | w :: ws, k => forceW (sepPack w) (fun sp => forceSepPairs ws (fun rest => k ((w, sp) :: rest)))
theorem forceSepPairs_eq (ws : List Nat) (k : List (Nat × Nat) → Bool) :
    forceSepPairs ws k = k (mapSep ws) := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceW (sepPack w) (fun sp => forceSepPairs ws (fun rest => k ((w, sp) :: rest))) = _
    rw [forceW_eq, ih]; rfl
def orSepAll (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Nat.lor p.2 ih) ps
def orSepSkip (x : Nat) (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Bool.rec (Nat.lor p.2 ih) ih (Nat.beq p.1 x)) ps
def orSepSkip2 (x y : Nat) (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Bool.rec (Bool.rec (Nat.lor p.2 ih) ih (Nat.beq p.1 y)) ih (Nat.beq p.1 x)) ps
theorem orSepAll_mapSep (ws : List Nat) : orSepAll (mapSep ws) = orSep ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => change Nat.lor (sepPack w) (orSepAll (mapSep ws)) = Nat.lor (sepPack w) (orSep ws); rw [ih]
theorem orSepSkip_mapSep (x : Nat) (ws : List Nat) :
    orSepSkip x (mapSep ws) = orSep (dropVal true x ws) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (Nat.lor (sepPack w) (orSepSkip x (mapSep ws))) (orSepSkip x (mapSep ws)) (Nat.beq w x) =
      orSep (bsel (Nat.beq w x) (dropVal true x ws) (w :: dropVal true x ws))
    rw [ih]
    cases Nat.beq w x <;> rfl
theorem dropVal_comm (x y : Nat) (l : List Nat) :
    dropVal true y (dropVal true x l) = dropVal true x (dropVal true y l) := by
  induction l with
  | nil => rfl
  | cons u us ih =>
    change dropVal true y (bsel (Nat.beq u x) (dropVal true x us) (u :: dropVal true x us)) =
      dropVal true x (bsel (Nat.beq u y) (dropVal true y us) (u :: dropVal true y us))
    cases hux : Nat.beq u x <;> cases huy : Nat.beq u y
    · simp only [bsel_false]
      change bsel (Nat.beq u y) (dropVal true y (dropVal true x us)) (u :: dropVal true y (dropVal true x us)) =
        bsel (Nat.beq u x) (dropVal true x (dropVal true y us)) (u :: dropVal true x (dropVal true y us))
      rw [huy, hux, bsel_false, bsel_false, ih]
    · simp only [bsel_false, bsel_true]
      change bsel (Nat.beq u y) (dropVal true y (dropVal true x us)) (u :: dropVal true y (dropVal true x us)) = _
      rw [huy, bsel_true, ih]
    · simp only [bsel_true, bsel_false]
      change _ = bsel (Nat.beq u x) (dropVal true x (dropVal true y us)) (u :: dropVal true x (dropVal true y us))
      rw [hux, bsel_true, ih]
    · simp only [bsel_true]; exact ih
theorem orSepSkip2_mapSep (x y : Nat) (ws : List Nat) :
    orSepSkip2 x y (mapSep ws) = orSep (dropVal true y (dropVal true x ws)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (Nat.lor (sepPack w) (orSepSkip2 x y (mapSep ws))) (orSepSkip2 x y (mapSep ws)) (Nat.beq w y))
      (orSepSkip2 x y (mapSep ws)) (Nat.beq w x) =
      orSep (dropVal true y (bsel (Nat.beq w x) (dropVal true x ws) (w :: dropVal true x ws)))
    rw [ih]
    cases hx : Nat.beq w x
    · rw [bsel_false]
      change Bool.rec (Nat.lor (sepPack w) (orSep (dropVal true y (dropVal true x ws))))
        (orSep (dropVal true y (dropVal true x ws))) (Nat.beq w y) =
        orSep (bsel (Nat.beq w y) (dropVal true y (dropVal true x ws)) (w :: dropVal true y (dropVal true x ws)))
      cases Nat.beq w y <;> rfl
    · rw [bsel_true]
def treeBlockF (lo hi : Nat) (f : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      Bool.rec true
        (let m := Nat.shiftRight (Nat.add a b) 1
         Bool.rec (Bool.rec false (next m b) (next a m)) (f a) (Nat.beq a m))
        (Nat.blt a b)) (Nat.add (Nat.sub hi lo) 1)) lo hi
theorem treeBlockF_eq (lo hi : Nat) (f : Nat → Bool) : treeBlockF lo hi f = treeBlock lo hi f := by
  unfold treeBlockF treeBlock
  suffices ∀ steps a b,
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          Bool.rec true
            (let m := Nat.shiftRight (Nat.add x y) 1
             Bool.rec (Bool.rec false (next m y) (next x m)) (f x) (Nat.beq x m))
            (Nat.blt x y)) steps) a b =
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b from
    this (hi - lo + 1) lo hi
  intro steps
  induction steps with
  | zero => intro a b; rfl
  | succ s ih =>
    intro a b
    dsimp only
    have hdiv : Nat.shiftRight (Nat.add a b) 1 = (a + b) / 2 := by
      change (a + b) >>> 1 = (a + b) / 2; rw [Nat.shiftRight_eq_div_pow]
    rw [hdiv]
    cases Nat.blt a b
    · rfl
    · cases Nat.beq a ((a + b) / 2)
      · rw [ih, ih]
        change Bool.rec false _ _ = (_ && _)
        cases (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true) _ s) a ((a + b) / 2) <;> rfl
      · rfl
theorem treeBlockF_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlockF lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  rw [treeBlockF_eq] at h; exact treeBlock_at h
def checkHintBoundV5 (goal negGoal fuel1 : Nat) (ws1 : List Nat) (hist1 : List (Nat × Nat × Nat))
    (bounds : List (Nat × List Nat × Nat × Nat)) (cid : Nat) : Bool :=
  match nthBound bounds cid with
  | some b => boundClosesV2 fuel1 ws1 hist1 b
  | none => Bool.rec true false (dagPartF ws1 goal negGoal)
theorem checkHintBoundV5_open {mask goal fuel1 cid : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {ws1 : List Nat} {hist1 : List (Nat × Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 ws1)
    (nd : ws1.Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k ws1.toFinset) :
    checkHintBoundV5 goal (Nat.xor mask goal) fuel1 ws1 hist1 bounds cid = false := by
  unfold checkHintBoundV5
  cases hb : nthBound bounds cid with
  | some b =>
    dsimp only
    have hmem := nthBound_mem hb
    have hg := hgoals b hmem
    exact boundClosesV2_sound (hknown b hmem) (hsub b hmem) hg.1 hg.2 (hstk b hmem) hv hc nd hk hlive
  | none =>
    dsimp only
    have hdp : dagPartF ws1 goal (Nat.xor mask goal) = true := by
      have heq : dagPartF ws1 goal (Nat.xor mask goal) = dagPart ws1 goal (mask ^^^ goal) :=
        dagPartF_eq ws1 goal (mask ^^^ goal)
      rw [heq]; exact dagPart_live hgm hlive
    rw [hdp]
def hintCloseLeafV5 (goal negGoal ep cutBits cutMask : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (fuel1 : Nat) (ws1 : List Nat) (hist1 : List (Nat × Nat × Nat))
    (sp : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  Bool.rec (some (cur, h))
    (forceWP (Nat.land h 3) (fun tag =>
      Bool.rec
        (Bool.rec none
          (forceWP (Nat.shiftRight h 2) (fun h' => some (cur, h')))
          (checkHintBoundV5 goal negGoal fuel1 ws1 hist1 bounds tag))
        (forceWP (Nat.shiftRight h 2) (fun h1 =>
          forceWP (Nat.add 3 (Nat.land h1 cutMask)) (fun cid =>
            Bool.rec none
              (forceWP (Nat.shiftRight h1 cutBits) (fun h' => some (cur, h')))
              (checkHintBoundV5 goal negGoal fuel1 ws1 hist1 bounds cid))))
        (Nat.beq tag 3)))
    (Nat.beq (Nat.land ep sp) ep)
theorem hintCloseLeafV5_open {mask goal cutBits cutMask fuel1 : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {ws1 : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)} {h : Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 ws1)
    (nd : ws1.Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k ws1.toFinset) :
    hintCloseLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask bounds fuel1 ws1 hist1 (orSep ws1) cur h = none := by
  unfold hintCloseLeafV5
  rw [sepPack_live hgm hlive]; dsimp only
  rw [forceWP_eq]
  cases Nat.beq (Nat.land h 3) 3
  · dsimp only
    rw [checkHintBoundV5_open hgm hknown hsub hgoals hstk hv hc nd hk hlive]
  · dsimp only
    rw [forceWP_eq, forceWP_eq]
    rw [checkHintBoundV5_open hgm hknown hsub hgoals hstk hv hc nd hk hlive]
def stepLeafV5 (goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel1 z spZ baseSp : Nat) (rest : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tok : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match cur with
  | (t, dest) :: tl =>
    Bool.rec
      (hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel1 (z :: rest) hist1 (Nat.lor spZ baseSp) cur h)
      (Bool.rec none
        (match states dest with
         | none => none
         | some saved =>
           Bool.rec none (Bool.rec none (some (tl, h)) (eqListN saved.2.1 (insertSortedF z rest)))
             (Nat.beq saved.1 fuel1))
        (Nat.blt dest count))
      (Nat.beq tok t)
  | [] =>
    hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel1 (z :: rest) hist1 (Nat.lor spZ baseSp) [] h
theorem stepLeafV5_ref {mask goal cutBits cutMask count fuel1 z tok h : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {rest : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)}
    {res : List (Nat × Nat) × Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 (z :: rest))
    (nd : (z :: rest).Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k (z :: rest).toFinset)
    (hok : stepLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds states
      fuel1 z (sepPack z) (orSep rest) rest hist1 tok cur h = some res) :
    ∃ dest < count, ∃ saved, states dest = some saved ∧ saved.1 = fuel1 ∧ saved.2.1 = insertSorted z rest := by
  have hcl := hintCloseLeafV5_open (cutBits := cutBits) (cutMask := cutMask) (cur := cur) (h := h)
    hgm hknown hsub hgoals hstk hv hc nd hk hlive
  unfold stepLeafV5 at hok
  have hor : Nat.lor (sepPack z) (orSep rest) = orSep (z :: rest) := rfl
  rw [hor] at hok
  cases cur with
  | nil => dsimp only at hok; rw [hcl] at hok; cases hok
  | cons hd tl =>
    obtain ⟨t, dest⟩ := hd
    dsimp only at hok
    cases ht : Nat.beq tok t
    · rw [ht] at hok; dsimp only at hok; rw [hcl] at hok; cases hok
    · rw [ht] at hok; dsimp only at hok
      cases hlt : Nat.blt dest count
      · rw [hlt] at hok; dsimp only at hok; cases hok
      · rw [hlt] at hok; dsimp only at hok
        cases hst : states dest with
        | none => rw [hst] at hok; dsimp only at hok; cases hok
        | some saved =>
          rw [hst] at hok; dsimp only at hok
          cases hf : Nat.beq saved.1 fuel1
          · rw [hf] at hok; dsimp only at hok; cases hok
          · rw [hf] at hok; dsimp only at hok
            cases heq : eqListN saved.2.1 (insertSortedF z rest)
            · rw [heq] at hok; dsimp only at hok; cases hok
            · rw [eqListN_eq, insertSortedF_eq, beq_iff_eq] at heq
              exact ⟨dest, Nat.blt_eq.mp hlt, saved, hst, Nat.beq_eq.mp hf, heq⟩
def checkKeepsV5 (goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n z spZ spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tokBase : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match (Bool.rec
    (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur h)
    (some (cur, h)) (Nat.blt fuel (Nat.sub n 1)) : Option (List (Nat × Nat) × Nat)) with
  | none => none
  | some (c1, h1) =>
    match (Bool.rec
      (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1 h1)
      (some (c1, h1)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
    | none => none
    | some (c2, h2) =>
      match (Bool.rec
        (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2 h2)
        (some (c2, h2)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
      | none => none
      | some (c3, h3) =>
        Bool.rec
          (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spAll ws0 hist1 (Nat.add tokBase 3) c3 h3)
          (some (c3, h3)) (Nat.blt fuel (Nat.add n 1))
theorem checkKeepsV5_at {goal negGoal ep cutBits cutMask count fuel fuel1 n z spZ spAll spNoA spNoB spNoAB tokBase h : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist1 : List (Nat × Nat × Nat)}
    {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hok : checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
      ws0 wsNoA wsNoB wsNoAB hist1 tokBase cur h = some res)
    (keepA keepB : Bool) :
    match keepA, keepB with
    | false, false => Nat.blt fuel (n - 1) = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase c hh = some r
    | true, false => Nat.blt fuel n = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (tokBase + 1) c hh = some r
    | false, true => Nat.blt fuel n = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (tokBase + 2) c hh = some r
    | true, true => Nat.blt fuel (n + 1) = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spAll ws0 hist1 (tokBase + 3) c hh = some r := by
  unfold checkKeepsV5 at hok
  cases hp0 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur h)
    (some (cur, h)) (Nat.blt fuel (Nat.sub n 1)) : Option (List (Nat × Nat) × Nat)) with
  | none => rw [hp0] at hok; dsimp only at hok; cases hok
  | some p1 =>
    obtain ⟨c1, h1⟩ := p1
    rw [hp0] at hok; dsimp only at hok
    cases hp1 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1 h1)
      (some (c1, h1)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
    | none => rw [hp1] at hok; dsimp only at hok; cases hok
    | some p2 =>
      obtain ⟨c2, h2⟩ := p2
      rw [hp1] at hok; dsimp only at hok
      cases hp2 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2 h2)
        (some (c2, h2)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
      | none => rw [hp2] at hok; dsimp only at hok; cases hok
      | some p3 =>
        obtain ⟨c3, h3⟩ := p3
        rw [hp2] at hok; dsimp only at hok
        cases keepA <;> cases keepB
        · cases hw : Nat.blt fuel (n - 1)
          · have hw' : Nat.blt fuel (Nat.sub n 1) = false := hw
            rw [hw'] at hp0; exact Or.inr ⟨cur, h, (c1, h1), hp0⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp2; exact Or.inr ⟨c2, h2, (c3, h3), hp2⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp1; exact Or.inr ⟨c1, h1, (c2, h2), hp1⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel (n + 1)
          · have hw' : Nat.blt fuel (Nat.add n 1) = false := hw
            rw [hw'] at hok; exact Or.inr ⟨c3, h3, res, hok⟩
          · exact Or.inl rfl
def checkOpV5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x y rawZ op : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  forceWP (canonV2 mask rawZ) (fun z =>
    Bool.rec
      (Bool.rec
        (forceWP (sepPack z) (fun spZ =>
          checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
            ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) cur h))
        (some (cur, h)) (memN z ws0))
      (some (cur, h)) (Nat.beq z 0))
def check4OpsV5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x nx y : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
  | none => none
  | some (c1, h1) =>
    match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1 h1 with
    | none => none
    | some (c2, h2) =>
      match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2 h2 with
      | none => none
      | some (c3, h3) =>
        checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land nx y) 3 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c3 h3
theorem check4OpsV5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n x y spAll spNoA spNoB spNoAB tokAB op h : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist : List (Nat × Nat × Nat)}
    {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hop : op < 4)
    (hok : check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x (Nat.xor mask x) y
      spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h = some res) :
    let z := binOp mask op x y
    z = 0 ∨ ws0.contains z = true ∨
      ∃ c hh r, checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z (sepPack z)
        spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) c hh = some r := by
  unfold check4OpsV5 at hok
  have extract (rawZ op' : Nat) (c0 : List (Nat × Nat)) (h0 : Nat) (r0 : List (Nat × Nat) × Nat)
      (hz : canon mask rawZ = binOp mask op' x y)
      (hrun : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y rawZ op'
        spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c0 h0 = some r0) :
      binOp mask op' x y = 0 ∨ ws0.contains (binOp mask op' x y) = true ∨
        ∃ c hh r, checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n (binOp mask op' x y)
          (sepPack (binOp mask op' x y)) spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB
          ((binOp mask op' x y, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op') 2) c hh = some r := by
    unfold checkOpV5 at hrun
    rw [forceWP_eq, canonV2_eq, hz] at hrun
    cases hz0 : Nat.beq (binOp mask op' x y) 0
    · rw [hz0] at hrun; dsimp only at hrun
      cases hm : memN (binOp mask op' x y) ws0
      · rw [hm] at hrun; dsimp only at hrun
        rw [forceWP_eq] at hrun
        exact Or.inr (Or.inr ⟨c0, h0, r0, hrun⟩)
      · rw [memN_eq] at hm; exact Or.inr (Or.inl hm)
    · exact Or.inl (Nat.beq_eq.mp hz0)
  cases hp0 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
  | none => rw [hp0] at hok; dsimp only at hok; cases hok
  | some p1 =>
    obtain ⟨c1, h1⟩ := p1; rw [hp0] at hok; dsimp only at hok
    cases hp1 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1 h1 with
    | none => rw [hp1] at hok; dsimp only at hok; cases hok
    | some p2 =>
      obtain ⟨c2, h2⟩ := p2; rw [hp1] at hok; dsimp only at hok
      cases hp2 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2 h2 with
      | none => rw [hp2] at hok; dsimp only at hok; cases hok
      | some p3 =>
        obtain ⟨c3, h3⟩ := p3; rw [hp2] at hok; dsimp only at hok
        rcases (by omega : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3) with rfl | rfl | rfl | rfl
        · exact extract _ 0 cur h (c1, h1) rfl hp0
        · exact extract _ 1 c1 h1 (c2, h2) rfl hp1
        · exact extract _ 2 c2 h2 (c3, h3) rfl hp2
        · exact extract _ 3 c3 h3 res rfl hok
def loopB_V5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n a x nx spAll spNoA : Nat) (ws0 wsNoA : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, b, cur, h =>
    forceWP (getDN ws0 b) (fun y =>
      forceList (dropValF true y ws0) (fun wsNoB =>
        forceList (dropValF true y wsNoA) (fun wsNoAB =>
          forceWP (orSepSkip y ps) (fun spNoB =>
            forceWP (orSepSkip2 x y ps) (fun spNoAB =>
              forceWP (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) (fun tokAB =>
                match check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx y spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
                | none => none
                | some (cur1, h1) =>
                  loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem (Nat.add b 1) cur1 h1))))))
theorem loopB_V5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n a x nx spAll spNoA : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem b0 b h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hb1 : b0 ≤ b) (hb2 : b < b0 + rem)
    (hok : loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem b0 cur h = some res) :
    let y := getDN ws0 b
    ∃ c hh r, check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx y spAll spNoA
      (orSepSkip y ps) (orSepSkip2 x y ps) ws0 wsNoA (dropValF true y ws0) (dropValF true y wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) c hh = some r := by
  induction rem generalizing b0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopB_V5 at hok
    rw [forceWP_eq, forceList_eq, forceList_eq, forceWP_eq, forceWP_eq, forceWP_eq] at hok
    cases hp : check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx (getDN ws0 b0) spAll spNoA
      (orSepSkip (getDN ws0 b0) ps) (orSepSkip2 x (getDN ws0 b0) ps) ws0 wsNoA
      (dropValF true (getDN ws0 b0) ws0) (dropValF true (getDN ws0 b0) wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b0) 2) cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : b = b0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change b0 + 1 ≤ b; omega) (by change b < (b0 + 1) + r; omega) hok
def loopA_V5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n spAll : Nat) (ws0 : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, a, cur, h =>
    forceWP (getDN ws0 a) (fun x =>
      forceList (dropValF true x ws0) (fun wsNoA =>
        forceWP (Nat.xor mask x) (fun nx =>
          forceWP (orSepSkip x ps) (fun spNoA =>
            match loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) cur h with
            | none => none
            | some (cur1, h1) =>
              loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist rem (Nat.add a 1) cur1 h1))))
theorem loopA_V5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n spAll : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem a0 a h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (ha1 : a0 ≤ a) (ha2 : a < a0 + rem)
    (hok : loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist rem a0 cur h = some res) :
    let x := getDN ws0 a
    ∃ c hh r, loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x (Nat.xor mask x) spAll
      (orSepSkip x ps) ws0 (dropValF true x ws0) ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) c hh = some r := by
  induction rem generalizing a0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopA_V5 at hok
    rw [forceWP_eq, forceList_eq, forceWP_eq, forceWP_eq] at hok
    cases hp : loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a0 (getDN ws0 a0) (Nat.xor mask (getDN ws0 a0)) spAll
      (orSepSkip (getDN ws0 a0) ps) ws0 (dropValF true (getDN ws0 a0) ws0) ps hist (Nat.sub n (Nat.add a0 1)) (Nat.add a0 1) cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : a = a0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change a0 + 1 ≤ a; omega) (by change a < (a0 + 1) + r; omega) hok
def dagCheckNodeV5 (mask goal ep cutBits cutMask : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (cursors : Nat → List (Nat × Nat)) (nodeHints : Nat → Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, hist) =>
    forceWs ws (fun ws0 =>
      forceWP (lenN ws0) (fun n =>
        Bool.rec
          (Bool.rec
            (Bool.rec false
              (forceW (Nat.xor mask goal) (fun negGoal =>
                forceW (Nat.sub fuel 1) (fun fuel1 =>
                  forceSepPairs ws0 (fun ps =>
                    forceW (orSepAll ps) (fun spAll =>
                      forceW (nodeHints (Nat.add i 1)) (fun h0 =>
                        match loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist n 0 (cursors (Nat.add i 1)) h0 with
                        | none => false
                        | some _ => true))))))
              (Nat.blt n 17))
            true (Nat.beq fuel 0))
          false (memN goal ws0)))
def stepRootV5 (goal negGoal ep cutBits cutMask count fuel : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (ws : List Nat) (tok : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  Bool.rec
    (match cur with
     | (t, dest) :: tl =>
       Bool.rec
         (hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel ws [] (orSep ws) cur h)
         (Bool.rec none
           (match states dest with
            | none => none
            | some saved =>
              Bool.rec none (Bool.rec none (some (tl, h)) (eqListN saved.2.1 ws)) (Nat.beq saved.1 fuel))
           (Nat.blt dest count))
         (Nat.beq tok t)
     | [] =>
       hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel ws [] (orSep ws) [] h)
    (some (cur, h)) (Nat.blt (Nat.add fuel 1) (lenN ws))
def loopRootsV5 (goal negGoal ep cutBits cutMask count fuel : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (stock : List Nat) : Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, tok, cur, h =>
    forceList (subsetWordsF stock tok) (fun ws =>
      match stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states ws tok cur h with
      | none => none
      | some (cur1, h1) =>
        loopRootsV5 goal negGoal ep cutBits cutMask count fuel bounds states stock rem (Nat.add tok 1) cur1 h1)
def dagCheckRootsV5 (mask goal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (rootCur : List (Nat × Nat)) (rootHint : Nat) (stock : List Nat) (fuel : Nat) : Bool :=
  match loopRootsV5 goal (Nat.xor mask goal) ep cutBits cutMask count fuel bounds states stock (Nat.shiftLeft 1 (lenN stock)) 0 rootCur rootHint with
  | none => false
  | some _ => true
theorem loopRootsV5_at {goal negGoal ep cutBits cutMask count fuel : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {stock : List Nat} {rem t0 tok h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (ht1 : t0 ≤ tok) (ht2 : tok < t0 + rem)
    (hok : loopRootsV5 goal negGoal ep cutBits cutMask count fuel bounds states stock rem t0 cur h = some res) :
    ∃ c hh r, stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states (subsetWordsF stock tok) tok c hh = some r := by
  induction rem generalizing t0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopRootsV5 at hok
    rw [forceList_eq] at hok
    cases hp : stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states (subsetWordsF stock t0) t0 cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : tok = t0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change t0 + 1 ≤ tok; omega) (by change tok < (t0 + 1) + r; omega) hok
theorem dagAllNodesV5 {mask goal cutBits cutMask fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)} {nodeHints : Nat → Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (snd : stock.Nodup)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV5 mask goal (edgePack mask goal) cutBits cutMask bounds count
      (dagTrace mask stock fuel forest) cursors nodeHints i = true) :
    ∀ cap i st, i < count → dagTrace mask stock fuel forest i = some st →
      st.1 = cap → ∀ k, k ≤ cap → ¬LiveBin mask goal k st.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i st hi htr hcap k hk hlive
    obtain ⟨rem, ws, hist⟩ := st
    dsimp only at hcap hlive
    have nd : ws.Nodup := dagTrace_nodup snd htr
    obtain ⟨hv, hcov⟩ := dagTrace_valid htr
    dsimp only at hv hcov
    have hchk := hnodes i (Nat.zero_le i) hi
    unfold dagCheckNodeV5 at hchk
    rw [htr] at hchk; dsimp only at hchk
    rw [forceWs_eq, forceWP_eq, lenN_eq, memN_eq] at hchk
    generalize hS : ws.toFinset = S at hlive
    cases hlive with
    | done =>
      have hgm' : goal ∈ ws := List.mem_toFinset.mp (hS.symm ▸ Finset.mem_singleton_self goal)
      have hc : ws.contains goal = true := List.contains_iff_mem.mpr hgm'
      rw [hc] at hchk; exact Bool.noConfusion hchk
    | @step k' _ a0 b0 op0 ha0 hb0 hab0 _ _ hop0 hz0 hf0 keepA0 keepB0 tail0 =>
      rw [← hS] at ha0 hb0 hf0 tail0
      have hrem_pos : rem ≠ 0 := by omega
      cases hcg : ws.contains goal
      · rw [hcg] at hchk; dsimp only at hchk
        have hrem0 : Nat.beq rem 0 = false := beq_false_ne hrem_pos
        rw [hrem0] at hchk; dsimp only at hchk
        cases h17 : Nat.blt ws.length 17
        · rw [h17] at hchk; exact Bool.noConfusion hchk
        · rw [h17] at hchk; dsimp only at hchk
          rw [forceW_eq, forceW_eq, forceSepPairs_eq, forceW_eq, forceW_eq] at hchk
          cases hloop : loopA_V5 mask goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds
              (dagTrace mask stock fuel forest) rem (Nat.sub rem 1) ws.length (orSepAll (mapSep ws)) ws (mapSep ws) hist
              ws.length 0 (cursors (Nat.add i 1)) (nodeHints (Nat.add i 1)) with
          | none => rw [hloop] at hchk; exact Bool.noConfusion hchk
          | some resA =>
            have haM : a0 ∈ ws := List.mem_toFinset.mp ha0
            have hbM : b0 ∈ ws := List.mem_toFinset.mp hb0
            obtain ⟨ia0, hia0, hea0⟩ := getElem_index_lt haM
            obtain ⟨ib0, hib0, heb0⟩ := getElem_index_lt hbM
            have hiab_ne : ia0 ≠ ib0 := fun heq => hab0 (hea0.symm.trans (heq ▸ heb0))
            have ⟨a, b, op, keepA, keepB, ha_lt, hab_lt, hb_lt, hop_lt, hax, hby, hzeq, htail⟩ :
                ∃ a b op keepA keepB, a < ws.length ∧ a < b ∧ b < ws.length ∧ op < 4 ∧
                  ws.getD a 0 = (if ia0 < ib0 then a0 else b0) ∧
                  ws.getD b 0 = (if ia0 < ib0 then b0 else a0) ∧
                  binOp mask op (ws.getD a 0) (ws.getD b 0) = binOp mask op0 a0 b0 ∧
                  LiveBin mask goal k' (insert (binOp mask op (ws.getD a 0) (ws.getD b 0))
                    (dropIf (!keepA) (ws.getD a 0) (dropIf (!keepB) (ws.getD b 0) ws.toFinset))) := by
              by_cases hlt : ia0 < ib0
              · exact ⟨ia0, ib0, op0, keepA0, keepB0, hia0, hlt, hib0, hop0,
                  by simp only [hlt, ite_true]; exact hea0,
                  by simp only [hlt, ite_true]; exact heb0,
                  by rw [hea0, heb0], by rw [hea0, heb0]; exact tail0⟩
              · obtain ⟨op1, hop1, hopEq⟩ := binOp_comm mask op0 a0 b0 hop0
                have hswap : dropIf (!keepB0) b0 (dropIf (!keepA0) a0 ws.toFinset) =
                    dropIf (!keepA0) a0 (dropIf (!keepB0) b0 ws.toFinset) := by
                  ext w; simp only [dropIf]; cases keepA0 <;> cases keepB0 <;> simp [Finset.mem_erase, and_left_comm]
                exact ⟨ib0, ia0, op1, keepB0, keepA0, hib0, by omega, hia0, hop1,
                  by simp only [hlt, ite_false]; exact heb0,
                  by simp only [hlt, ite_false]; exact hea0,
                  by rw [hea0, heb0, hopEq],
                  by rw [hea0, heb0, ← hopEq, hswap]; exact tail0⟩
            obtain ⟨cA, hA, rA, hB⟩ := loopA_V5_at (a := a) (Nat.zero_le a) (by omega) hloop
            obtain ⟨cB, hB', rB, hO⟩ := loopB_V5_at (b := b) (by change a + 1 ≤ b; omega) (by change b < (a + 1) + (ws.length - (a + 1)); omega) hB
            simp only [getDN_eq, dropValF_eq, orSepAll_mapSep, orSepSkip_mapSep, orSepSkip2_mapSep] at hO
            set x := ws.getD a 0
            set y := ws.getD b 0
            set z := binOp mask op x y
            have hznz : z ≠ 0 := hzeq.symm ▸ hz0
            have hznm : ws.contains z = false := by
              cases h : ws.contains z
              · rfl
              · exact absurd (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)) (hzeq.symm ▸ hf0)
            rcases check4OpsV5_at hop_lt hO with hz' | hcm | ⟨cK, hK', rK, hK⟩
            · exact hznz hz'
            · rw [hznm] at hcm; exact Bool.noConfusion hcm
            · have hxM : x ∈ ws := by simp only [x, hax]; split; exact haM; exact hbM
              have hyM : y ∈ ws := by simp only [y, hby]; split; exact hbM; exact haM
              have hxy : x ≠ y := by simp only [x, y, hax, hby]; split; exact hab0; exact hab0.symm
              have hzNotW : z ∉ ws := fun hm => by
                have := List.contains_iff_mem.mpr hm; rw [hznm] at this; exact Bool.noConfusion this
              have hdropComm : dropVal true y (dropVal true x ws) = dropVal true x (dropVal true y ws) :=
                dropVal_comm x y ws
              set rest := dropVal (!keepA) x (dropVal (!keepB) y ws)
              have hv' : HistValid mask stock ((z, x, y) :: hist) :=
                ⟨⟨op, hop_lt, rfl⟩, hcov x hxM, hcov y hyM, hv⟩
              have hcov' : WsCovered stock ((z, x, y) :: hist) (z :: rest) := by
                intro w hw
                rcases List.mem_cons.mp hw with rfl | hw'
                · exact Or.inr ⟨x, y, List.mem_cons_self⟩
                · have hwm : w ∈ ws := (dropVal_mem.mp (dropVal_mem.mp hw').1).1
                  rcases hcov w hwm with hst | ⟨u, v, hm⟩
                  · exact Or.inl hst
                  · exact Or.inr ⟨u, v, List.mem_cons_of_mem _ hm⟩
              have hnd_u : (z :: rest).Nodup :=
                List.nodup_cons.mpr ⟨fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1,
                  dropVal_nodup (dropVal_nodup nd)⟩
              have hset_u : (z :: rest).toFinset = insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
                ext w; simp only [rest, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, ← dropVal_toFinset]
              have hlive_u : LiveBin mask goal k' (z :: rest).toFinset := by rwa [hset_u]
              have hset_s : (insertSorted z rest).toFinset = (z :: rest).toFinset := by
                ext w; simp only [List.mem_toFinset, insertSorted_mem, List.mem_cons]
              have hlive_s : LiveBin mask goal k' (insertSorted z rest).toFinset := by rwa [hset_s]
              have hlen' : (insertSorted z rest).length =
                  ws.length - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0) :=
                list_len_child (z := z) (keepA := keepA) (keepB := keepB) nd hxM hyM hxy hzNotW
              have hcard' : (insertSorted z rest).length ≤ rem := by
                have hnd_s : (insertSorted z rest).Nodup :=
                  insertSorted_nodup (fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
                have := liveBin_card_le hlive_s
                rw [List.toFinset_card_of_nodup hnd_s] at this; omega
              have h2len : 2 ≤ ws.length := by
                have hsub2 : ({x, y} : Finset Nat) ⊆ ws.toFinset := by
                  intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
                  · exact List.mem_toFinset.mpr hxM
                  · rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hyM
                have hpair : ({x, y} : Finset Nat).card = 2 := Finset.card_pair hxy
                have hc := Finset.card_le_card hsub2
                rw [List.toFinset_card_of_nodup nd] at hc; omega
              have hka := checkKeepsV5_at hK keepA keepB
              have finish {tok' hh' : Nat} {c' : List (Nat × Nat)} {rr : List (Nat × Nat) × Nat}
                  (hstep : stepLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds
                    (dagTrace mask stock fuel forest) (Nat.sub rem 1) z (sepPack z) (orSep rest) rest ((z, x, y) :: hist) tok' c' hh' = some rr) : False := by
                obtain ⟨dest, hdest, saved, htr2, hfEq, hwEq⟩ :=
                  stepLeafV5_ref hgm hknown hsub hgoals hstk hv' hcov' hnd_u (k := k') (by change k' ≤ rem - 1; omega) hlive_u hstep
                exact ih (rem - 1) (by omega) dest saved hdest htr2 hfEq k' (by omega) (hwEq ▸ hlive_s)
              cases keepA <;> cases keepB
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false] at hlen'; omega
                · rw [hdropComm] at hst; exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
                · exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
                · exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [ite_true] at hlen'; omega
                · exact finish hst
      · rw [hcg] at hchk; exact Bool.noConfusion hchk
def nodupB : List Nat → Bool
  | [] => true
  | w :: ws => !memN w ws && nodupB ws
theorem nodupB_spec {l : List Nat} (h : nodupB l = true) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons w ws ih =>
    unfold nodupB at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', memN_eq] at h
    exact List.nodup_cons.mpr ⟨fun hm => by rw [List.contains_iff_mem.mpr hm] at h; exact Bool.noConfusion h.1, ih h.2⟩
theorem kn_nil : KnownBin [] := fun _ h => nomatch h
theorem kn_cons {m : Nat} {s : List Nat} {l g : Nat} {bs : List (Nat × List Nat × Nat × Nat)}
    (h : LowerBin m s g l) (hs : KnownBin bs) : KnownBin ((m, s, l, g) :: bs) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact h
  · exact hs b hb
def checkSliceMetaV5 (mask goal ep : Nat) (stock : List Nat)
    (bounds : List (Nat × List Nat × Nat × Nat)) : Bool :=
  Nat.beq (Nat.land goal mask) goal &&
  !Nat.beq goal 0 &&
  stock.all (fun w => Nat.beq (canon mask w) w) &&
  nodupB stock &&
  Nat.beq ep (edgePack mask goal) &&
  bounds.all (fun b =>
    Nat.beq (Nat.land mask b.1) b.1 &&
    Nat.beq (canon b.1 goal) b.2.2.2 &&
    !Nat.beq b.2.2.2 0 &&
    stock.all (fun s => availB b.2.1 (canon b.1 s)))
theorem lowerDagV5 {mask goal ep cutBits cutMask fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)} {nodeHints : Nat → Nat}
    (hknown : KnownBin bounds)
    (hroots : dagCheckRootsV5 mask goal ep cutBits cutMask count bounds
      (dagTraceF mask stock fuel forest) (cursors 0) (nodeHints 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV5 mask goal ep cutBits cutMask bounds count
      (dagTraceF mask stock fuel forest) cursors nodeHints i = true)
    (hmeta : checkSliceMetaV5 mask goal ep stock bounds = true) :
    LowerBin mask stock goal (fuel + 1) := by
  unfold checkSliceMetaV5 at hmeta
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hmeta
  obtain ⟨⟨⟨⟨⟨hgmB, hgnzB⟩, hcs⟩, hndB⟩, hepB⟩, hbdB⟩ := hmeta
  have hgm : Masked mask goal := Nat.beq_eq.mp hgmB
  have hgnz : goal ≠ 0 := fun h => by rw [h] at hgnzB; exact Bool.noConfusion hgnzB
  have snd : stock.Nodup := nodupB_spec hndB
  have hep : ep = edgePack mask goal := Nat.beq_eq.mp hepB
  have hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1 := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true] at h
    exact Nat.beq_eq.mp h.1.1.1
  have hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨Nat.beq_eq.mp h.1.1.2, fun h0 => by rw [h0] at h; exact Bool.noConfusion h.1.2⟩
  have hstkB : ∀ b ∈ bounds, stock.all (fun s => availB b.2.1 (canon b.1 s)) = true := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true] at h
    exact h.2
  subst hep
  have hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s) := fun b hb s hs =>
    availB_spec.mp (List.all_eq_true.mp (hstkB b hb) s hs)
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr] at hroots hnodes
  intro vs hbuild hhit
  by_contra! hlt
  have hcs' : ∀ w ∈ stock, canon mask w = w := fun w hw =>
    Nat.beq_eq.mp (List.all_eq_true.mp hcs w hw)
  obtain ⟨k, S, hk, hSsub, hlive⟩ := extractLiveBin hgnz hcs' hbuild hhit
  obtain ⟨tok, htok, hteq⟩ := exists_subsetToken stock S
  rw [Finset.inter_eq_left.mpr hSsub] at hteq
  unfold dagCheckRootsV5 at hroots
  have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
    rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [hpow] at hroots
  cases hrl : loopRootsV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count fuel bounds
      (dagTrace mask stock fuel forest) stock (2 ^ stock.length) 0 (cursors 0) (nodeHints 0) with
  | none => rw [hrl] at hroots; exact Bool.noConfusion hroots
  | some resR =>
    obtain ⟨c, hh, rr, hsr⟩ := loopRootsV5_at (tok := tok) (Nat.zero_le tok) (by omega) hrl
    rw [subsetWordsF_eq] at hsr
    have hnd : (subsetWords stock tok).Nodup := subsetWords_nodup snd tok
    have hlive' : LiveBin mask goal k (subsetWords stock tok).toFinset := by rwa [hteq]
    have hcard : (subsetWords stock tok).length ≤ fuel + 1 := by
      have := liveBin_card_le hlive'
      rw [List.toFinset_card_of_nodup hnd] at this; omega
    have hnw : Nat.blt (Nat.add fuel 1) (lenN (subsetWords stock tok)) = false := by
      rw [lenN_eq]
      cases h : Nat.blt (Nat.add fuel 1) (subsetWords stock tok).length
      · rfl
      · have hlt' : fuel + 1 < (subsetWords stock tok).length := Nat.blt_eq.mp h
        omega
    have hcov0 : WsCovered stock [] (subsetWords stock tok) :=
      fun w hw => Or.inl (subsetWords_subset stock tok w hw)
    have hcl := hintCloseLeafV5_open (cutBits := cutBits) (cutMask := cutMask) (fuel1 := fuel) (hist1 := []) (cur := c) (h := hh)
      hgm hknown hsub hgoals hstk trivial hcov0 hnd (k := k) (by omega) hlive'
    unfold stepRootV5 at hsr
    rw [hnw] at hsr; dsimp only at hsr
    cases c with
    | nil => dsimp only at hsr; rw [hcl] at hsr; cases hsr
    | cons hd tl =>
      obtain ⟨t, dest⟩ := hd
      dsimp only at hsr
      cases ht : Nat.beq tok t
      · rw [ht] at hsr; dsimp only at hsr; rw [hcl] at hsr; cases hsr
      · rw [ht] at hsr; dsimp only at hsr
        cases hltc : Nat.blt dest count
        · rw [hltc] at hsr; dsimp only at hsr; cases hsr
        · rw [hltc] at hsr; dsimp only at hsr
          cases htr2 : dagTrace mask stock fuel forest dest with
          | none => rw [htr2] at hsr; dsimp only at hsr; cases hsr
          | some saved =>
            rw [htr2] at hsr; dsimp only at hsr
            cases hf : Nat.beq saved.1 fuel
            · rw [hf] at hsr; dsimp only at hsr; cases hsr
            · rw [hf] at hsr; dsimp only at hsr
              cases heq : eqListN saved.2.1 (subsetWords stock tok)
              · rw [heq] at hsr; dsimp only at hsr; cases hsr
              · rw [eqListN_eq, beq_iff_eq] at heq
                exact dagAllNodesV5 hgm hknown hsub hgoals hstk snd hnodes fuel dest saved
                  (Nat.blt_eq.mp hltc) htr2 (Nat.beq_eq.mp hf) k (by omega) (heq ▸ hlive')
def unpackF (data width idx : Nat) : Nat :=
  Nat.land (Nat.shiftRight data (Nat.mul idx width)) (Nat.sub (Nat.shiftLeft 1 width) 1)
def unpackForestF (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := Nat.add pBits tBits
  let code := unpackF data w i
  (Nat.shiftRight code tBits, Nat.land code (Nat.sub (Nat.shiftLeft 1 tBits) 1))
def unpackListAux (data off w wMask tokBits tokMask : Nat) : Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, acc => acc
  | k + 1, acc =>
    forceWP (Nat.land (Nat.shiftRight data (Nat.mul (Nat.add off k) w)) wMask) (fun code =>
      unpackListAux data off w wMask tokBits tokMask k ((Nat.land code tokMask, Nat.shiftRight code tokBits) :: acc))
def unpackCursorV5 (index data idxW idxMask sizeBits sizeMask tokBits tokMask w wMask : Nat) :
    Nat → List (Nat × Nat) :=
  fun parent =>
    forceWP (Nat.land (Nat.shiftRight index (Nat.mul parent idxW)) idxMask) (fun entry =>
      unpackListAux data (Nat.shiftRight entry sizeBits) w wMask tokBits tokMask (Nat.land entry sizeMask) [])
def unpackHintV5 (index data idxW idxMask lenBits lenMask : Nat) : Nat → Nat :=
  fun parent =>
    forceWP (Nat.land (Nat.shiftRight index (Nat.mul parent idxW)) idxMask) (fun entry =>
      forceWP (Nat.land entry lenMask) (fun hlen =>
        Bool.rec
          (Nat.land (Nat.shiftRight data (Nat.shiftRight entry lenBits)) (Nat.sub (Nat.shiftLeft 1 hlen) 1))
          0 (Nat.beq hlen 0)))

def m_0 : Nat := 0xaaaa
def s_0 : List Nat := [0x2222, 0xa0a, 0xaa]
def g_0 : Nat := 0x22a
def ep_0 : Nat := 0x28000000000000020800000000000002200000000000000000
def bds_0 : List (Nat × List Nat × Nat × Nat) := []
def cur_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_0 : Nat → Nat := fun _ => 0
def f_0 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_0 : Nat → Bool := dagCheckNodeV5 m_0 g_0 ep_0 1 1 bds_0 1 (dagTraceF m_0 s_0 3 f_0) cur_0 nh_0
set_option maxHeartbeats 0 in
theorem rc_0 : dagCheckRootsV5 m_0 g_0 ep_0 1 1 1 bds_0 (dagTraceF m_0 s_0 3 f_0) (cur_0 0) (nh_0 0) s_0 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_0 : treeBlockF 0 1 ch_0 = true := by decide +kernel
theorem nc_0 : ∀ i, 0 ≤ i → i < 1 → ch_0 i = true := fun _ h1 h2 => treeBlockF_at nb_0 h1 h2
theorem lb_0 : LowerBin m_0 s_0 g_0 4 :=
  lowerDagV5 (kn_nil) rc_0 nc_0 (by decide +kernel)

def m_1 : Nat := 0x33003300
def s_1 : List Nat := [0x11001100, 0x3000300, 0x3300]
def g_1 : Nat := 0x1001300
def ep_1 : Nat := 0x12000000000000000000000000000100020000000000000000000000000001001000
def bds_1 : List (Nat × List Nat × Nat × Nat) := []
def cur_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_1 : Nat → Nat := fun _ => 0
def f_1 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_1 : Nat → Bool := dagCheckNodeV5 m_1 g_1 ep_1 1 1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) cur_1 nh_1
set_option maxHeartbeats 0 in
theorem rc_1 : dagCheckRootsV5 m_1 g_1 ep_1 1 1 1 bds_1 (dagTraceF m_1 s_1 3 f_1) (cur_1 0) (nh_1 0) s_1 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_1 : treeBlockF 0 1 ch_1 = true := by decide +kernel
theorem nc_1 : ∀ i, 0 ≤ i → i < 1 → ch_1 i = true := fun _ h1 h2 => treeBlockF_at nb_1 h1 h2
theorem lb_1 : LowerBin m_1 s_1 g_1 4 :=
  lowerDagV5 (kn_nil) rc_1 nc_1 (by decide +kernel)

def m_2 : Nat := 0x5500550000000000
def s_2 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_2 : Nat := 0x100150000000000
def ep_2 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
def bds_2 : List (Nat × List Nat × Nat × Nat) := []
def cur_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_2 : Nat → Nat := fun _ => 0
def f_2 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_2 : Nat → Bool := dagCheckNodeV5 m_2 g_2 ep_2 1 1 bds_2 1 (dagTraceF m_2 s_2 3 f_2) cur_2 nh_2
set_option maxHeartbeats 0 in
theorem rc_2 : dagCheckRootsV5 m_2 g_2 ep_2 1 1 1 bds_2 (dagTraceF m_2 s_2 3 f_2) (cur_2 0) (nh_2 0) s_2 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_2 : treeBlockF 0 1 ch_2 = true := by decide +kernel
theorem nc_2 : ∀ i, 0 ≤ i → i < 1 → ch_2 i = true := fun _ h1 h2 => treeBlockF_at nb_2 h1 h2
theorem lb_2 : LowerBin m_2 s_2 g_2 4 :=
  lowerDagV5 (kn_nil) rc_2 nc_2 (by decide +kernel)

def m_3 : Nat := 0x3030303000000000
def s_3 : List Nat := [0x1010101000000000, 0x30003000000000, 0x303000000000]
def g_3 : Nat := 0x10103000000000
def ep_3 : Nat := 0x1020000000000010002000000000000000000000000000000000000000000010100000000000
def bds_3 : List (Nat × List Nat × Nat × Nat) := []
def cur_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_3 : Nat → Nat := fun _ => 0
def f_3 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_3 : Nat → Bool := dagCheckNodeV5 m_3 g_3 ep_3 1 1 bds_3 1 (dagTraceF m_3 s_3 3 f_3) cur_3 nh_3
set_option maxHeartbeats 0 in
theorem rc_3 : dagCheckRootsV5 m_3 g_3 ep_3 1 1 1 bds_3 (dagTraceF m_3 s_3 3 f_3) (cur_3 0) (nh_3 0) s_3 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_3 : treeBlockF 0 1 ch_3 = true := by decide +kernel
theorem nc_3 : ∀ i, 0 ≤ i → i < 1 → ch_3 i = true := fun _ h1 h2 => treeBlockF_at nb_3 h1 h2
theorem lb_3 : LowerBin m_3 s_3 g_3 4 :=
  lowerDagV5 (kn_nil) rc_3 nc_3 (by decide +kernel)

def m_4 : Nat := 0x3333000000000000
def s_4 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_4 : Nat := 0x113000000000000
def ep_4 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
def bds_4 : List (Nat × List Nat × Nat × Nat) := []
def cur_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_4 : Nat → Nat := fun _ => 0
def f_4 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_4 : Nat → Bool := dagCheckNodeV5 m_4 g_4 ep_4 1 1 bds_4 1 (dagTraceF m_4 s_4 3 f_4) cur_4 nh_4
set_option maxHeartbeats 0 in
theorem rc_4 : dagCheckRootsV5 m_4 g_4 ep_4 1 1 1 bds_4 (dagTraceF m_4 s_4 3 f_4) (cur_4 0) (nh_4 0) s_4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_4 : treeBlockF 0 1 ch_4 = true := by decide +kernel
theorem nc_4 : ∀ i, 0 ≤ i → i < 1 → ch_4 i = true := fun _ h1 h2 => treeBlockF_at nb_4 h1 h2
theorem lb_4 : LowerBin m_4 s_4 g_4 4 :=
  lowerDagV5 (kn_nil) rc_4 nc_4 (by decide +kernel)

def m_5 : Nat := 0x5555000000000000
def s_5 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_5 : Nat := 0x115000000000000
def ep_5 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
def bds_5 : List (Nat × List Nat × Nat × Nat) := []
def cur_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_5 : Nat → Nat := fun _ => 0
def f_5 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_5 : Nat → Bool := dagCheckNodeV5 m_5 g_5 ep_5 1 1 bds_5 1 (dagTraceF m_5 s_5 3 f_5) cur_5 nh_5
set_option maxHeartbeats 0 in
theorem rc_5 : dagCheckRootsV5 m_5 g_5 ep_5 1 1 1 bds_5 (dagTraceF m_5 s_5 3 f_5) (cur_5 0) (nh_5 0) s_5 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_5 : treeBlockF 0 1 ch_5 = true := by decide +kernel
theorem nc_5 : ∀ i, 0 ≤ i → i < 1 → ch_5 i = true := fun _ h1 h2 => treeBlockF_at nb_5 h1 h2
theorem lb_5 : LowerBin m_5 s_5 g_5 4 :=
  lowerDagV5 (kn_nil) rc_5 nc_5 (by decide +kernel)

def m_6 : Nat := 0xa0a00000a0a
def s_6 : List Nat := [0x20200000202, 0xa0000000a, 0xa0a]
def g_6 : Nat := 0x20000020a
def ep_6 : Nat := 0x20800000000000000000000000200000008000000000000000000000002000002000000000000000000
def bds_6 : List (Nat × List Nat × Nat × Nat) := []
def cur_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_6 : Nat → Nat := fun _ => 0
def f_6 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_6 : Nat → Bool := dagCheckNodeV5 m_6 g_6 ep_6 1 1 bds_6 1 (dagTraceF m_6 s_6 3 f_6) cur_6 nh_6
set_option maxHeartbeats 0 in
theorem rc_6 : dagCheckRootsV5 m_6 g_6 ep_6 1 1 1 bds_6 (dagTraceF m_6 s_6 3 f_6) (cur_6 0) (nh_6 0) s_6 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_6 : treeBlockF 0 1 ch_6 = true := by decide +kernel
theorem nc_6 : ∀ i, 0 ≤ i → i < 1 → ch_6 i = true := fun _ h1 h2 => treeBlockF_at nb_6 h1 h2
theorem lb_6 : LowerBin m_6 s_6 g_6 4 :=
  lowerDagV5 (kn_nil) rc_6 nc_6 (by decide +kernel)

def m_7 : Nat := 0xcc000000cc
def s_7 : List Nat := [0x4400000044, 0xc0000000c, 0xcc]
def g_7 : Nat := 0x40000004c
def ep_7 : Nat := 0x4800000000000000000000000000000000000000040000000800000000000000000000000400000040
def bds_7 : List (Nat × List Nat × Nat × Nat) := []
def cur_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_7 : Nat → Nat := fun _ => 0
def f_7 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_7 : Nat → Bool := dagCheckNodeV5 m_7 g_7 ep_7 1 1 bds_7 1 (dagTraceF m_7 s_7 3 f_7) cur_7 nh_7
set_option maxHeartbeats 0 in
theorem rc_7 : dagCheckRootsV5 m_7 g_7 ep_7 1 1 1 bds_7 (dagTraceF m_7 s_7 3 f_7) (cur_7 0) (nh_7 0) s_7 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_7 : treeBlockF 0 1 ch_7 = true := by decide +kernel
theorem nc_7 : ∀ i, 0 ≤ i → i < 1 → ch_7 i = true := fun _ h1 h2 => treeBlockF_at nb_7 h1 h2
theorem lb_7 : LowerBin m_7 s_7 g_7 4 :=
  lowerDagV5 (kn_nil) rc_7 nc_7 (by decide +kernel)

def m_8 : Nat := 0xff000000000000
def s_8 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_8 : Nat := 0x17000000000000
def ep_8 : Nat := 0x600000000000000120000000000000014000000000000
def bds_8 : List (Nat × List Nat × Nat × Nat) := []
def cur_8 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_8 : Nat → Nat := fun _ => 0
def f_8 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_8 : Nat → Bool := dagCheckNodeV5 m_8 g_8 ep_8 1 1 bds_8 1 (dagTraceF m_8 s_8 3 f_8) cur_8 nh_8
set_option maxHeartbeats 0 in
theorem rc_8 : dagCheckRootsV5 m_8 g_8 ep_8 1 1 1 bds_8 (dagTraceF m_8 s_8 3 f_8) (cur_8 0) (nh_8 0) s_8 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_8 : treeBlockF 0 1 ch_8 = true := by decide +kernel
theorem nc_8 : ∀ i, 0 ≤ i → i < 1 → ch_8 i = true := fun _ h1 h2 => treeBlockF_at nb_8 h1 h2
theorem lb_8 : LowerBin m_8 s_8 g_8 4 :=
  lowerDagV5 (kn_nil) rc_8 nc_8 (by decide +kernel)

def m_9 : Nat := 0xf0f000000000000
def s_9 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_9 : Nat := 0x107000000000000
def ep_9 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
def bds_9 : List (Nat × List Nat × Nat × Nat) := []
def cur_9 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_9 : Nat → Nat := fun _ => 0
def f_9 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_9 : Nat → Bool := dagCheckNodeV5 m_9 g_9 ep_9 1 1 bds_9 1 (dagTraceF m_9 s_9 3 f_9) cur_9 nh_9
set_option maxHeartbeats 0 in
theorem rc_9 : dagCheckRootsV5 m_9 g_9 ep_9 1 1 1 bds_9 (dagTraceF m_9 s_9 3 f_9) (cur_9 0) (nh_9 0) s_9 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_9 : treeBlockF 0 1 ch_9 = true := by decide +kernel
theorem nc_9 : ∀ i, 0 ≤ i → i < 1 → ch_9 i = true := fun _ h1 h2 => treeBlockF_at nb_9 h1 h2
theorem lb_9 : LowerBin m_9 s_9 g_9 4 :=
  lowerDagV5 (kn_nil) rc_9 nc_9 (by decide +kernel)

def m_10 : Nat := 0x4400440044004400
def s_10 : List Nat := [0x400040004000400, 0x440000004400, 0x44004400]
def g_10 : Nat := 0x40004004400
def ep_10 : Nat := 0x400400000000400000040000000000000000000000004000400000000000000000000000000000000000000
def bds_10 : List (Nat × List Nat × Nat × Nat) := []
def cur_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_10 : Nat → Nat := fun _ => 0
def f_10 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_10 : Nat → Bool := dagCheckNodeV5 m_10 g_10 ep_10 1 1 bds_10 1 (dagTraceF m_10 s_10 3 f_10) cur_10 nh_10
set_option maxHeartbeats 0 in
theorem rc_10 : dagCheckRootsV5 m_10 g_10 ep_10 1 1 1 bds_10 (dagTraceF m_10 s_10 3 f_10) (cur_10 0) (nh_10 0) s_10 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_10 : treeBlockF 0 1 ch_10 = true := by decide +kernel
theorem nc_10 : ∀ i, 0 ≤ i → i < 1 → ch_10 i = true := fun _ h1 h2 => treeBlockF_at nb_10 h1 h2
theorem lb_10 : LowerBin m_10 s_10 g_10 4 :=
  lowerDagV5 (kn_nil) rc_10 nc_10 (by decide +kernel)

def m_11 : Nat := 0xaa000000aa0000
def s_11 : List Nat := [0x22000000220000, 0xa0000000a0000, 0xaa0000]
def g_11 : Nat := 0x20000002a0000
def ep_11 : Nat := 0x28000000000000000000000000000000000000000200000008000000020000002000000000000000000000
def bds_11 : List (Nat × List Nat × Nat × Nat) := []
def cur_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_11 : Nat → Nat := fun _ => 0
def f_11 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_11 : Nat → Bool := dagCheckNodeV5 m_11 g_11 ep_11 1 1 bds_11 1 (dagTraceF m_11 s_11 3 f_11) cur_11 nh_11
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsV5 m_11 g_11 ep_11 1 1 1 bds_11 (dagTraceF m_11 s_11 3 f_11) (cur_11 0) (nh_11 0) s_11 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_11 : treeBlockF 0 1 ch_11 = true := by decide +kernel
theorem nc_11 : ∀ i, 0 ≤ i → i < 1 → ch_11 i = true := fun _ h1 h2 => treeBlockF_at nb_11 h1 h2
theorem lb_11 : LowerBin m_11 s_11 g_11 4 :=
  lowerDagV5 (kn_nil) rc_11 nc_11 (by decide +kernel)

def m_12 : Nat := 0xc0c00000c0c0000
def s_12 : List Nat := [0x404000004040000, 0xc0000000c0000, 0xc0c0000]
def g_12 : Nat := 0x40000040c0000
def ep_12 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000000
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
def cur_12 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_12 : Nat → Nat := fun _ => 0
def f_12 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_12 : Nat → Bool := dagCheckNodeV5 m_12 g_12 ep_12 1 1 bds_12 1 (dagTraceF m_12 s_12 3 f_12) cur_12 nh_12
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsV5 m_12 g_12 ep_12 1 1 1 bds_12 (dagTraceF m_12 s_12 3 f_12) (cur_12 0) (nh_12 0) s_12 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12 : treeBlockF 0 1 ch_12 = true := by decide +kernel
theorem nc_12 : ∀ i, 0 ≤ i → i < 1 → ch_12 i = true := fun _ h1 h2 => treeBlockF_at nb_12 h1 h2
theorem lb_12 : LowerBin m_12 s_12 g_12 4 :=
  lowerDagV5 (kn_nil) rc_12 nc_12 (by decide +kernel)

def m_13 : Nat := 0xff00ff0
def s_13 : List Nat := [0x5500550, 0x3300330, 0xf000f0, 0xff0]
def g_13 : Nat := 0x5300770
def ep_13 : Nat := 0x2400000000000000000000000000000000000000000003002200000000005000440
def bds_13 : List (Nat × List Nat × Nat × Nat) := []
def cur_13 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x175a8f 4 15 2 3 5 31 7 127
def nh_13 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_13 : Nat → Nat × Nat := unpackForestF 0x3dd4f 1 5
def ch_13 : Nat → Bool := dagCheckNodeV5 m_13 g_13 ep_13 1 1 bds_13 3 (dagTraceF m_13 s_13 4 f_13) cur_13 nh_13
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsV5 m_13 g_13 ep_13 1 1 3 bds_13 (dagTraceF m_13 s_13 4 f_13) (cur_13 0) (nh_13 0) s_13 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_13 : treeBlockF 0 3 ch_13 = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 3 → ch_13 i = true := fun _ h1 h2 => treeBlockF_at nb_13 h1 h2
theorem lb_13 : LowerBin m_13 s_13 g_13 5 :=
  lowerDagV5 (kn_nil) rc_13 nc_13 (by decide +kernel)

def m_14 : Nat := 0xff000000ff00000
def s_14 : List Nat := [0x550000005500000, 0x330000003300000, 0xf0000000f00000, 0xff00000]
def g_14 : Nat := 0x110000005300000
def ep_14 : Nat := 0x420000000000000000000000000000000000000000000000000000001100000003000000110000005000000
def bds_14 : List (Nat × List Nat × Nat × Nat) := []
def cur_14 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x16588f 4 15 2 3 5 31 7 127
def nh_14 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_14 : Nat → Nat × Nat := unpackForestF 0x39c4f 1 5
def ch_14 : Nat → Bool := dagCheckNodeV5 m_14 g_14 ep_14 1 1 bds_14 3 (dagTraceF m_14 s_14 4 f_14) cur_14 nh_14
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsV5 m_14 g_14 ep_14 1 1 3 bds_14 (dagTraceF m_14 s_14 4 f_14) (cur_14 0) (nh_14 0) s_14 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14 : treeBlockF 0 3 ch_14 = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 3 → ch_14 i = true := fun _ h1 h2 => treeBlockF_at nb_14 h1 h2
theorem lb_14 : LowerBin m_14 s_14 g_14 5 :=
  lowerDagV5 (kn_nil) rc_14 nc_14 (by decide +kernel)

def m_15 : Nat := 0x330033003300330
def s_15 : List Nat := [0x110011001100110, 0x30003000300030, 0x33000000330, 0x3300330]
def g_15 : Nat := 0x110013001300330
def ep_15 : Nat := 0x20020000000020000002000000000000000000000000000000000000000000000000000110010001000000
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
def cur_15 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44890e8701 0x192430919242090d24209263a88d9d3a54d903a10d800f 7 127 3 7 10 1023 14 16383
def nh_15 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_15 : Nat → Nat × Nat := unpackForestF 0xc7463629d6490a6c43a492209086c00f 3 10
def ch_15 : Nat → Bool := dagCheckNodeV5 m_15 g_15 ep_15 1 1 bds_15 10 (dagTraceF m_15 s_15 4 f_15) cur_15 nh_15
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV5 m_15 g_15 ep_15 1 1 10 bds_15 (dagTraceF m_15 s_15 4 f_15) (cur_15 0) (nh_15 0) s_15 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15 : treeBlockF 0 10 ch_15 = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 10 → ch_15 i = true := fun _ h1 h2 => treeBlockF_at nb_15 h1 h2
theorem lb_15 : LowerBin m_15 s_15 g_15 5 :=
  lowerDagV5 (kn_nil) rc_15 nc_15 (by decide +kernel)

def m_16 : Nat := 0x33003300cc00cc
def s_16 : List Nat := [0x11001100440044, 0xcc00cc, 0x30003000c000c, 0x33000000cc]
def g_16 : Nat := 0x130033000c004c
def ep_16 : Nat := 0x2000000040000000000000000000020000000c000800000000000000000010000000000040
def bds_16 : List (Nat × List Nat × Nat × Nat) := []
def cur_16 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x192440a19343061234349263d88d5d2a549882a109800f 7 127 3 7 10 1023 14 16383
def nh_16 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_16 : Nat → Nat × Nat := unpackForestF 0xc7a63529564d0a4ce3469210a884c00f 3 10
def ch_16 : Nat → Bool := dagCheckNodeV5 m_16 g_16 ep_16 1 1 bds_16 10 (dagTraceF m_16 s_16 4 f_16) cur_16 nh_16
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV5 m_16 g_16 ep_16 1 1 10 bds_16 (dagTraceF m_16 s_16 4 f_16) (cur_16 0) (nh_16 0) s_16 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16 : treeBlockF 0 10 ch_16 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 10 → ch_16 i = true := fun _ h1 h2 => treeBlockF_at nb_16 h1 h2
theorem lb_16 : LowerBin m_16 s_16 g_16 5 :=
  lowerDagV5 (kn_nil) rc_16 nc_16 (by decide +kernel)

def m_17 : Nat := 0xaa00aaaa00aa00
def s_17 : List Nat := [0x22002222002200, 0xa000a0a000a00, 0xaa00aa00, 0xaa0000aa00]
def g_17 : Nat := 0x2002200000200
def ep_17 : Nat := 0x20000002000000000000000000000200000000020000020022000002000000000000000000
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
def cur_17 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x193040f1a3030f113030c263e88c9d3e54c883e10c800f 7 127 3 7 10 1023 14 16383
def nh_17 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_17 : Nat → Nat × Nat := unpackForestF 0xc7c63229f68c0a64d3061810f886400f 3 10
def ch_17 : Nat → Bool := dagCheckNodeV5 m_17 g_17 ep_17 1 1 bds_17 10 (dagTraceF m_17 s_17 4 f_17) cur_17 nh_17
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV5 m_17 g_17 ep_17 1 1 10 bds_17 (dagTraceF m_17 s_17 4 f_17) (cur_17 0) (nh_17 0) s_17 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17 : treeBlockF 0 10 ch_17 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 10 → ch_17 i = true := fun _ h1 h2 => treeBlockF_at nb_17 h1 h2
theorem lb_17 : LowerBin m_17 s_17 g_17 5 :=
  lowerDagV5 (kn_nil) rc_17 nc_17 (by decide +kernel)

def m_18 : Nat := 0xf0f000000f0f
def s_18 : List Nat := [0x505000000505, 0x303000000303, 0xf0f, 0xf00000000f]
def g_18 : Nat := 0x10300000070f
def ep_18 : Nat := 0x2000000008000000000000000000001030000002000000100000000400
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
def cur_18 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb34b34d3d93a73653533400f 7 127 3 7 9 511 12 4095
def nh_18 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_18 : Nat → Nat × Nat := unpackForestF 0x33db3433a33633533400f 3 9
def ch_18 : Nat → Bool := dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 7 (dagTraceF m_18 s_18 4 f_18) cur_18 nh_18
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 7 bds_18 (dagTraceF m_18 s_18 4 f_18) (cur_18 0) (nh_18 0) s_18 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18 : treeBlockF 0 7 ch_18 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 7 → ch_18 i = true := fun _ h1 h2 => treeBlockF_at nb_18 h1 h2
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagV5 (kn_nil) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0xffff000000000000
def s_19 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_19 : Nat := 0x117000000000000
def ep_19 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
def bds_19 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9), (m_8, s_8, 4, g_8), (m_5, s_5, 4, g_5), (m_4, s_4, 4, g_4)]
def cc_19_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_19_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_19 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_19_1 (Nat.sub p 32)) (cc_19_0 p) (Nat.blt p 32)
def hc_19_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_19_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_19 : Nat → Nat := fun p => Bool.rec (hc_19_1 (Nat.sub p 32)) (hc_19_0 p) (Nat.blt p 32)
def f_19 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_19 : Nat → Bool := dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 43 (dagTraceF m_19 s_19 6 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 43 bds_19 (dagTraceF m_19 s_19 6 f_19) (cur_19 0) (nh_19 0) s_19 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_0 : treeBlockF 0 32 ch_19 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19_1 : treeBlockF 32 43 ch_19 = true := by decide +kernel
theorem nj_19_1 : ∀ i, 0 ≤ i → i < 43 → ch_19 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_19_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_19_1 h1 h2)
theorem nc_19 : ∀ i, 0 ≤ i → i < 43 → ch_19 i = true := nj_19_1
theorem lb_19 : LowerBin m_19 s_19 g_19 7 :=
  lowerDagV5 (kn_cons lb_9 (kn_cons lb_8 (kn_cons lb_5 (kn_cons lb_4 (kn_nil))))) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0xffff00000000
def s_20 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_20 : Nat := 0x153700000000
def ep_20 : Nat := 0x2200000000000004040000000000001032000000000000150400000000
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
def cur_20 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_20 : Nat → Nat := fun _ => 0
def f_20 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_20 : Nat → Bool := dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 1 (dagTraceF m_20 s_20 3 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 1 bds_20 (dagTraceF m_20 s_20 3 f_20) (cur_20 0) (nh_20 0) s_20 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20 : treeBlockF 0 1 ch_20 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 1 → ch_20 i = true := fun _ h1 h2 => treeBlockF_at nb_20 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 4 :=
  lowerDagV5 (kn_nil) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xff00ff00000000
def s_21 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_21 : Nat := 0x17003700000000
def ep_21 : Nat := 0x20000000000000000000000000000600040000000000120032000000000014000400000000
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_21 : Nat → List (Nat × Nat) := fun _ => []
def nh_21 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_21 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 0 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) (nh_21 0) s_21 4 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 0 (dagTraceF m_21 s_21 4 f_21) cur_21 nh_21 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xf0f0f0f000000000
def s_22 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_22 : Nat := 0x10103000000000
def ep_22 : Nat := 0x1020000000000010002000000000000000000000000000101030000000000010100000000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_22 : Nat → List (Nat × Nat) := fun _ => []
def nh_22 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 0 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) (nh_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 0 (dagTraceF m_22 s_22 4 f_22) cur_22 nh_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0xf0f0f0f00000000
def s_23 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_23 : Nat := 0x107050700000000
def ep_23 : Nat := 0x400000000000006000200000000000000000000000001020002000000000104050400000000
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_23 : Nat → List (Nat × Nat) := fun _ => []
def nh_23 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 0 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) (nh_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 0 (dagTraceF m_23 s_23 4 f_23) cur_23 nh_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0x3333333300000000
def s_24 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_24 : Nat := 0x113113300000000
def ep_24 : Nat := 0x1020000000000012002200000000010200000000000000000000000000000110110000000000
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def nh_24 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0xaa00aa00aa00aa
def s_25 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_25 : Nat := 0x20022002a002a
def ep_25 : Nat := 0x28000800000020000000000000000000000000000200000008000800020022002000200000000000000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def nh_25 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) (nh_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 nh_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0x6666666600000000
def s_26 : List Nat := [0x2222222200000000, 0x606060600000000, 0x66006600000000, 0x666600000000]
def g_26 : Nat := 0x6042600000000
def ep_26 : Nat := 0x420000000000006002200000000000604040000000000000000000000000000000000000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := []
def cur_26 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xb9710f 4 15 2 3 6 63 8 255
def nh_26 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_26 : Nat → Nat × Nat := unpackForestF 0x1e788f 1 6
def ch_26 : Nat → Bool := dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 3 (dagTraceF m_26 s_26 4 f_26) cur_26 nh_26
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 3 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) (nh_26 0) s_26 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26 : treeBlockF 0 3 ch_26 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 3 → ch_26 i = true := fun _ h1 h2 => treeBlockF_at nb_26 h1 h2
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV5 (kn_nil) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0x666600006666
def s_27 : List Nat := [0x222200002222, 0x60600000606, 0x6600000066, 0x6666]
def g_27 : Nat := 0x42600004666
def ep_27 : Nat := 0x424000000000000000000000002200000020000004040000020000000000000000000000000000000000
def bds_27 : List (Nat × List Nat × Nat × Nat) := []
def cc_27_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xc0780300600c01612c0580b0148e90520a41406614c0943282504a0902f95f03e07c0f81f03e07c0d901d001 0x228e10c687d4c3a1e1c0d0d858682430a617500b27840201e1e0b05078482c24209a0e1306888302c14120513020880c3c041a4b8fe34770e378519c14fdea7ced3b749bb54cd5a64a92f5295a849d1a46783f321d950dca0664c2f24159109c4846201f0e0d8605c0826000f 11 2047 5 31 10 1023 17 131071
def cc_27_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x84379b0d164b2182c05ca55208240200e470381c0c436180c06030180c06014080241001 0xf23ece3dfd3df9357c3d5835f12cd14cc53cb93cce4ce53ce134dc18d814c524b814c53cb414b83cb424d13ecd3dc92dc125bc1ab0169d4c994494189014812c8134 9 511 3 7 10 1023 16 65535
def cc_27_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a30cb912244858a14132024401 0x803c7f4c9a3898349528932490288e248b4c89407d3c67408024 7 127 3 7 9 511 16 65535
def cur_27 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_27_2 (Nat.sub p 64)) (cc_27_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_27_0 p) (Nat.blt p 32)
def hc_27_0 : Nat → Nat := unpackHintV5 0x94224848e223048a1214a83120448009f087729b1661595d451313c44b2124447110c83d30d502e389521c486c219105c414183ca0170002 0x0 14 16383 5 31
def hc_27_1 : Nat → Nat := unpackHintV5 0x9e14a2a4851868634112004f847a13a19c84dc46c13601b00d426a03501a80b124691c389a44822020e1058c18a0440108080002 0x0 13 8191 5 31
def hc_27_2 : Nat → Nat := unpackHintV5 0x12a241408788e11a22c8454790d212811409810002 0x0 11 2047 4 15
def nh_27 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_27_2 (Nat.sub p 64)) (hc_27_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_27_0 p) (Nat.blt p 32)
def f_27 : Nat → Nat × Nat := unpackForestF 0x260713034031fc74a23a491c288e12018ee22991140031b818cc0a7f00247c9ebe4d40a7cf12c029d814ddb278d9346c0c360500a66b13e589eac4b58a78b125580d2d0f16848b0160299014bc0a56052748a6245112030901402919f8e0fc6881343ea6010fcd078683434161a0900876594c2ca0164f0086e04330217810ac084e29341e120a1305088282c16120a0900846041f020d8105c10980844041e020d00826000f 7 10
def ch_27 : Nat → Bool := dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 78 (dagTraceF m_27 s_27 5 f_27) cur_27 nh_27
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 78 bds_27 (dagTraceF m_27 s_27 5 f_27) (cur_27 0) (nh_27 0) s_27 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_0 : treeBlockF 0 32 ch_27 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_1 : treeBlockF 32 64 ch_27 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_2 : treeBlockF 64 78 ch_27 = true := by decide +kernel
theorem nj_27_1 : ∀ i, 0 ≤ i → i < 64 → ch_27 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_27_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_27_1 h1 h2)
theorem nj_27_2 : ∀ i, 0 ≤ i → i < 78 → ch_27 i = true := block_join nj_27_1 (fun _ h1 h2 => treeBlockF_at nb_27_2 h1 h2)
theorem nc_27 : ∀ i, 0 ≤ i → i < 78 → ch_27 i = true := nj_27_2
theorem lb_27 : LowerBin m_27 s_27 g_27 6 :=
  lowerDagV5 (kn_nil) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0x66006600660066
def s_28 : List Nat := [0x22002200220022, 0x6000600060006, 0x6600000066, 0x660066]
def g_28 : Nat := 0x6002600260066
def ep_28 : Nat := 0x20004000000020000000400000000000000000000600040004000000000000000000000000000000000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := []
def cur_28 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44890e8701 0x192430919342050d34205263d88d5d2a549902a109800f 7 127 3 7 10 1023 14 16383
def nh_28 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_28 : Nat → Nat × Nat := unpackForestF 0xc7a63529564d0a4c42a49a205084c00f 3 10
def ch_28 : Nat → Bool := dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 10 (dagTraceF m_28 s_28 4 f_28) cur_28 nh_28
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 10 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) (nh_28 0) s_28 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28 : treeBlockF 0 10 ch_28 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 10 → ch_28 i = true := fun _ h1 h2 => treeBlockF_at nb_28 h1 h2
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV5 (kn_nil) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0x3030303030303030
def s_29 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_29 : Nat := 0x10103000301030
def ep_29 : Nat := 0x20000000001020000010000010002000300020000000000000000000000000000000000010100000001000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_29 : Nat → List (Nat × Nat) := fun _ => []
def nh_29 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 0 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) (nh_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 0 (dagTraceF m_29 s_29 4 f_29) cur_29 nh_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0xcccc0000cccc
def s_30 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_30 : Nat := 0x4040000444c
def ep_30 : Nat := 0x404800000000000000000000000000000008000004040000000800000000000000000000040400004440
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_30 : Nat → List (Nat × Nat) := fun _ => []
def nh_30 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 0 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) (nh_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 0 (dagTraceF m_30 s_30 4 f_30) cur_30 nh_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0x3333000033330000
def s_31 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_31 : Nat := 0x113000001330000
def ep_31 : Nat := 0x20000000000000000000000012000000320000010200000100000000000000000000000110000001000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def nh_31 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) (nh_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 nh_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0xaaaa0000aaaa0000
def s_32 : List Nat := [0x2222000022220000, 0xa0a00000a0a0000, 0xaa000000aa0000, 0xaaaa0000]
def g_32 : Nat := 0x20000002a0000
def ep_32 : Nat := 0x280000000000000000000000020000002a0000000200000008000000020000002000000000000000000000
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_32 : Nat → List (Nat × Nat) := fun _ => []
def nh_32 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 0 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) (nh_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 0 (dagTraceF m_32 s_32 4 f_32) cur_32 nh_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0x5555000055550000
def s_33 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_33 : Nat := 0x115000005150000
def ep_33 : Nat := 0x400000000000000000000000014000000100000010400000504000001100000001000000000000000000000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def nh_33 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) (nh_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 nh_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0xff000000ff00
def s_34 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_34 : Nat := 0x150000005700
def ep_34 : Nat := 0x420000000000000000000000000000000000000004000000020000001000000002000000150000005400
def bds_34 : List (Nat × List Nat × Nat × Nat) := []
def cc_34_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_34_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_34 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_34_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_34_0 p) (Nat.blt p 32)
def hc_34_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_34_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_34_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_34 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_34_2 (Nat.sub p 64)) (hc_34_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_34_0 p) (Nat.blt p 32)
def f_34 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_34 : Nat → Bool := dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 64 (dagTraceF m_34 s_34 5 f_34) cur_34 nh_34
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 64 bds_34 (dagTraceF m_34 s_34 5 f_34) (cur_34 0) (nh_34 0) s_34 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_0 : treeBlockF 0 32 ch_34 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_1 : treeBlockF 32 64 ch_34 = true := by decide +kernel
theorem nj_34_1 : ∀ i, 0 ≤ i → i < 64 → ch_34 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_34_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_34_1 h1 h2)
theorem nc_34 : ∀ i, 0 ≤ i → i < 64 → ch_34 i = true := nj_34_1
theorem lb_34 : LowerBin m_34 s_34 g_34 6 :=
  lowerDagV5 (kn_nil) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0xff000000ff
def s_35 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_35 : Nat := 0x370000007f
def ep_35 : Nat := 0x4800000000000000000000000000000000000000040000000800000032000000200000000400000040
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def nh_35 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) (nh_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 nh_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0xf0f00000f0f0
def s_36 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_36 : Nat := 0x103000005070
def ep_36 : Nat := 0x404000000000000000000000002000000020000000000000000000001030000000200000100000005040
def bds_36 : List (Nat × List Nat × Nat × Nat) := []
def cur_36 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_36 : Nat → Nat := fun _ => 0
def f_36 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_36 : Nat → Bool := dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 1 (dagTraceF m_36 s_36 3 f_36) cur_36 nh_36
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 1 bds_36 (dagTraceF m_36 s_36 3 f_36) (cur_36 0) (nh_36 0) s_36 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36 : treeBlockF 0 1 ch_36 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 1 → ch_36 i = true := fun _ h1 h2 => treeBlockF_at nb_36 h1 h2
theorem lb_36 : LowerBin m_36 s_36 g_36 4 :=
  lowerDagV5 (kn_nil) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0xf0f00000f0f
def s_37 : List Nat := [0x50500000505, 0x30300000303, 0xf0000000f, 0xf0f]
def g_37 : Nat := 0x5070000070f
def ep_37 : Nat := 0x20800000000000000000000000200000008000000000000000000000002000002000000050400000400
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def nh_37 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) (nh_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 nh_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0xcccc0000cccc0000
def s_38 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_38 : Nat := 0x40000040c0000
def ep_38 : Nat := 0x40800000000000000000000000400000008000000040000040c000000000000000000000004000004000000
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def nh_38 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0xaaaa0000aaaa
def s_39 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_39 : Nat := 0x220000022a
def ep_39 : Nat := 0x20800000000000000000000002200000028000000000000020800000022000002200000000000000000
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def nh_39 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) (nh_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 nh_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xcc00cc00cc00cc00
def s_40 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_40 : Nat := 0x40004004400
def ep_40 : Nat := 0x400400000000400000040000000000000000000000004000400000000000000000000000000040004004400
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def nh_40 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0xf000f000f000f00
def s_41 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_41 : Nat := 0x100050005000700
def ep_41 : Nat := 0x400020000000400000002000000000000000000000000000000000001000000000002000100050005000400
def bds_41 : List (Nat × List Nat × Nat × Nat) := []
def cc_41_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_41_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_41 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_41_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_41_0 p) (Nat.blt p 32)
def hc_41_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_41_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_41_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_41 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_41_2 (Nat.sub p 64)) (hc_41_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_41_0 p) (Nat.blt p 32)
def f_41 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_41 : Nat → Bool := dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 64 (dagTraceF m_41 s_41 5 f_41) cur_41 nh_41
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 64 bds_41 (dagTraceF m_41 s_41 5 f_41) (cur_41 0) (nh_41 0) s_41 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_0 : treeBlockF 0 32 ch_41 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_1 : treeBlockF 32 64 ch_41 = true := by decide +kernel
theorem nj_41_1 : ∀ i, 0 ≤ i → i < 64 → ch_41 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_41_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_41_1 h1 h2)
theorem nc_41 : ∀ i, 0 ≤ i → i < 64 → ch_41 i = true := nj_41_1
theorem lb_41 : LowerBin m_41 s_41 g_41 6 :=
  lowerDagV5 (kn_nil) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0x33333333
def s_42 : List Nat := [0x11111111, 0x3030303, 0x330033, 0x3333]
def g_42 : Nat := 0x1331333
def ep_42 : Nat := 0x12000000000000320020000000000100020000000000000000000000000001001000
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def nh_42 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) (nh_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 nh_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xcc00cc00cc00cc
def s_43 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_43 : Nat := 0x40004000c004c
def ep_43 : Nat := 0x800480000000000000040000000000000000000040004000c000800000000000000000004000400000040
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def nh_43 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) (nh_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 nh_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xffff0000
def s_44 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_44 : Nat := 0x53f0000
def ep_44 : Nat := 0x3a000000000000050c000000000000003000000000000005000000
def bds_44 : List (Nat × List Nat × Nat × Nat) := []
def cur_44 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_44 : Nat → Nat := fun _ => 0
def f_44 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_44 : Nat → Bool := dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 1 (dagTraceF m_44 s_44 3 f_44) cur_44 nh_44
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 1 bds_44 (dagTraceF m_44 s_44 3 f_44) (cur_44 0) (nh_44 0) s_44 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44 : treeBlockF 0 1 ch_44 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 1 → ch_44 i = true := fun _ h1 h2 => treeBlockF_at nb_44 h1 h2
theorem lb_44 : LowerBin m_44 s_44 g_44 4 :=
  lowerDagV5 (kn_nil) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0xffff
def s_45 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_45 : Nat := 0x577f
def ep_45 : Nat := 0x28000000000000020800000000000002200000000000005440
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def nh_45 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) (nh_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 nh_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xff00ff00
def s_46 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_46 : Nat := 0x5005700
def ep_46 : Nat := 0x52000000000000000000000000000500020000000000000002000000000005005400
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def nh_46 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) (nh_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 nh_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0xcccccccc
def s_47 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_47 : Nat := 0x40c444c
def ep_47 : Nat := 0x4040000000000008000800000000040c000800000000000000000000000004004440
def bds_47 : List (Nat × List Nat × Nat × Nat) := []
def cur_47 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_47 : Nat → Nat := fun _ => 0
def f_47 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_47 : Nat → Bool := dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 1 (dagTraceF m_47 s_47 3 f_47) cur_47 nh_47
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 1 bds_47 (dagTraceF m_47 s_47 3 f_47) (cur_47 0) (nh_47 0) s_47 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47 : treeBlockF 0 1 ch_47 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 1 → ch_47 i = true := fun _ h1 h2 => treeBlockF_at nb_47 h1 h2
theorem lb_47 : LowerBin m_47 s_47 g_47 4 :=
  lowerDagV5 (kn_nil) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0xaaaaaaaa
def s_48 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_48 : Nat := 0x2a022a
def ep_48 : Nat := 0x20000000000002a0028000000000008020800000000002002200000000000000000
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def nh_48 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xff000000ff0000
def s_49 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_49 : Nat := 0x170000003f0000
def ep_49 : Nat := 0x2800000000000000000000000000000000000000060000000c000000120000003000000014000000000000
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def nh_49 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) (nh_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 nh_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0xf000f000f000f0
def s_50 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_50 : Nat := 0x10003000300070
def ep_50 : Nat := 0x20004000000020000000400000000000000000000000000000000000100030003000200010000000000040
def bds_50 : List (Nat × List Nat × Nat × Nat) := []
def cc_50_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0x793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_50_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014 8 255 3 7 10 1023 16 65535
def cur_50 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_50_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_50_0 p) (Nat.blt p 32)
def hc_50_0 : Nat → Nat := unpackHintV5 0xa142548910a03a70c952850a142240810203460c1220405080400000 0x0 7 127 2 3
def hc_50_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3870c983054a1120344881020405081020402 0x0 7 127 2 3
def hc_50_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_50 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_50_2 (Nat.sub p 64)) (hc_50_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_50_0 p) (Nat.blt p 32)
def f_50 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def ch_50 : Nat → Bool := dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 64 (dagTraceF m_50 s_50 5 f_50) cur_50 nh_50
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 64 bds_50 (dagTraceF m_50 s_50 5 f_50) (cur_50 0) (nh_50 0) s_50 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_0 : treeBlockF 0 32 ch_50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_1 : treeBlockF 32 64 ch_50 = true := by decide +kernel
theorem nj_50_1 : ∀ i, 0 ≤ i → i < 64 → ch_50 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_50_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_50_1 h1 h2)
theorem nc_50 : ∀ i, 0 ≤ i → i < 64 → ch_50 i = true := nj_50_1
theorem lb_50 : LowerBin m_50 s_50 g_50 6 :=
  lowerDagV5 (kn_nil) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0xf0f00000f0f0000
def s_51 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_51 : Nat := 0x1070000050f0000
def ep_51 : Nat := 0x4080000000000000000000000060000000a0000000000000000000001020000000000000104000005000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def nh_51 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 0 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) (nh_51 0) s_51 4 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 0 (dagTraceF m_51 s_51 4 f_51) cur_51 nh_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0x4444444444444444
def s_52 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_52 : Nat := 0x4040404044444
def ep_52 : Nat := 0x400404000000400000040400004000000000000000404040404000000000000000000000000000000000000
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def nh_52 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 0 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) (nh_52 0) s_52 4 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 0 (dagTraceF m_52 s_52 4 f_52) cur_52 nh_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0x50505050a0a0a0a
def s_53 : List Nat := [0xa0a0a0a, 0x101010102020202, 0x50005000a000a, 0x50500000a0a]
def g_53 : Nat := 0x1050505000a020a
def ep_53 : Nat := 0x4000000020000040000000a0008000000000000000001000000000002000000000000000000
def bds_53 : List (Nat × List Nat × Nat × Nat) := []
def cur_53 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x192440a19343061234349263d88d5d2a549882a109800f 7 127 3 7 10 1023 14 16383
def nh_53 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_53 : Nat → Nat × Nat := unpackForestF 0xc7a63529564d0a4ce3469210a884c00f 3 10
def ch_53 : Nat → Bool := dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 10 (dagTraceF m_53 s_53 4 f_53) cur_53 nh_53
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 10 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) (nh_53 0) s_53 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53 : treeBlockF 0 10 ch_53 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 10 → ch_53 i = true := fun _ h1 h2 => treeBlockF_at nb_53 h1 h2
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV5 (kn_nil) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0x2222222222222222
def s_54 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_54 : Nat := 0x2002200220222
def ep_54 : Nat := 0x20020000000020000002000002002200220020000200000000020000000000000000000000000000000000
def bds_54 : List (Nat × List Nat × Nat × Nat) := []
def cc_54_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0x793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_54_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014 8 255 3 7 10 1023 16 65535
def cur_54 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_54_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_54_0 p) (Nat.blt p 32)
def hc_54_0 : Nat → Nat := unpackHintV5 0xa142548910a03a70c952850a142240810203460c1220405080400000 0x0 7 127 2 3
def hc_54_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3870c983054a1120344881020405081020402 0x0 7 127 2 3
def hc_54_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_54 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_54_2 (Nat.sub p 64)) (hc_54_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_54_0 p) (Nat.blt p 32)
def f_54 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def ch_54 : Nat → Bool := dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 64 (dagTraceF m_54 s_54 5 f_54) cur_54 nh_54
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 64 bds_54 (dagTraceF m_54 s_54 5 f_54) (cur_54 0) (nh_54 0) s_54 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_0 : treeBlockF 0 32 ch_54 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_1 : treeBlockF 32 64 ch_54 = true := by decide +kernel
theorem nj_54_1 : ∀ i, 0 ≤ i → i < 64 → ch_54 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_54_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_54_1 h1 h2)
theorem nc_54 : ∀ i, 0 ≤ i → i < 64 → ch_54 i = true := nj_54_1
theorem lb_54 : LowerBin m_54 s_54 g_54 6 :=
  lowerDagV5 (kn_nil) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0xa0a0a0a0a0a0a0a
def s_55 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_55 : Nat := 0x20002000a020a
def ep_55 : Nat := 0x80208000000000000020000020002000a0008000000000000000000020002000002000000000000000000
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_55 : Nat → List (Nat × Nat) := fun _ => []
def nh_55 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_55 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 1 1 0 bds_55 (dagTraceF m_55 s_55 4 f_55) (cur_55 0) (nh_55 0) s_55 4 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_55 g_55 ep_55 1 1 bds_55 0 (dagTraceF m_55 s_55 4 f_55) cur_55 nh_55 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_55 : LowerBin m_55 s_55 g_55 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0x5a5a5a5a
def s_56 : List Nat := [0xa0a0a0a, 0x12121212, 0x5a005a, 0x5a5a]
def g_56 : Nat := 0x1a525a
def ep_56 : Nat := 0x524000000000001a0008000000000000000000000000001002000000000000000000
def bds_56 : List (Nat × List Nat × Nat × Nat) := []
def cur_56 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xa3a63600f 4 15 2 3 10 1023 12 4095
def nh_56 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_56 : Nat → Nat × Nat := unpackForestF 0x18eb1b00f 1 10
def ch_56 : Nat → Bool := dagCheckNodeV5 m_56 g_56 ep_56 1 1 bds_56 3 (dagTraceF m_56 s_56 4 f_56) cur_56 nh_56
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 1 1 3 bds_56 (dagTraceF m_56 s_56 4 f_56) (cur_56 0) (nh_56 0) s_56 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56 : treeBlockF 0 3 ch_56 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 3 → ch_56 i = true := fun _ h1 h2 => treeBlockF_at nb_56 h1 h2
theorem lb_56 : LowerBin m_56 s_56 g_56 5 :=
  lowerDagV5 (kn_nil) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0xc0c0c0c0c0c0c0c
def s_57 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_57 : Nat := 0x40404040c040c
def ep_57 : Nat := 0x408000800000400000000000004000000080008000000000000000000000000000000000004040404000400
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_57 : Nat → List (Nat × Nat) := fun _ => []
def nh_57 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_57 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 1 1 0 bds_57 (dagTraceF m_57 s_57 4 f_57) (cur_57 0) (nh_57 0) s_57 4 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_57 g_57 ep_57 1 1 bds_57 0 (dagTraceF m_57 s_57 4 f_57) cur_57 nh_57 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_57 : LowerBin m_57 s_57 g_57 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0xaaaaaaaaaaaaaaaa
def s_58 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_58 : Nat := 0x20022002a022a
def ep_58 : Nat := 0x280208000000200000020000020022002a0028000200000008020800020022002002200000000000000000
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_54, s_54, 6, g_54), (m_0, s_0, 4, g_0), (m_25, s_25, 5, g_25), (m_55, s_55, 5, g_55), (m_32, s_32, 5, g_32), (m_17, s_17, 5, g_17), (m_11, s_11, 4, g_11), (m_6, s_6, 4, g_6)]
def cur_58 : Nat → List (Nat × Nat) := unpackCursorV5 0xb269246d86121c1 0x184180a5b4134c943e350884e78cd033108c01f 6 63 2 3 10 1023 14 16383
def nh_58 : Nat → Nat := unpackHintV5 0xbe008b66858b85805fcc588e58802ed4005d0000 0x875700a86033af39e6a71aad6e80c1411aaa802d2d551dc6c000b2dd400635aab3aaac00010e000469d9380235955 16 65535 7 127
def f_58 : Nat → Nat × Nat := unpackForestF 0x202918cd74150f8433250884e108c01f 4 10
def ch_58 : Nat → Bool := dagCheckNodeV5 m_58 g_58 ep_58 3 7 bds_58 9 (dagTraceF m_58 s_58 7 f_58) cur_58 nh_58
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 3 7 9 bds_58 (dagTraceF m_58 s_58 7 f_58) (cur_58 0) (nh_58 0) s_58 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58 : treeBlockF 0 9 ch_58 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 9 → ch_58 i = true := fun _ h1 h2 => treeBlockF_at nb_58 h1 h2
theorem lb_58 : LowerBin m_58 s_58 g_58 8 :=
  lowerDagV5 (kn_cons lb_54 (kn_cons lb_0 (kn_cons lb_25 (kn_cons lb_55 (kn_cons lb_32 (kn_cons lb_17 (kn_cons lb_11 (kn_cons lb_6 (kn_nil))))))))) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0x3333333333333333
def s_59 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_59 : Nat := 0x113113301331333
def ep_59 : Nat := 0x20020000001020000012000012002200320020010200000100020000000000000000000110110001001000
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_54, s_54, 6, g_54), (m_31, s_31, 5, g_31), (m_24, s_24, 5, g_24), (m_42, s_42, 5, g_42), (m_1, s_1, 4, g_1), (m_29, s_29, 5, g_29), (m_15, s_15, 5, g_15), (m_4, s_4, 4, g_4)]
def cur_59 : Nat → List (Nat × Nat) := unpackCursorV5 0xb269246d86121c1 0x214d54d5a4d58d49263d2894678dd137149c01f 6 63 2 3 10 1023 14 16383
def nh_59 : Nat → Nat := unpackHintV5 0xdf00a378a3009d8b71d8718069113666006c0000 0xe7059d6739eebd581c6386fa18dbb00029de7582d5aaa0387549d778016f5828274eadc0e31c39d23000059ce00b53a8000e1c38730d 16 65535 7 127
def f_59 : Nat → Nat × Nat := unpackForestF 0x214d18dd64d58d45372d28946149c01f 4 10
def ch_59 : Nat → Bool := dagCheckNodeV5 m_59 g_59 ep_59 3 7 bds_59 9 (dagTraceF m_59 s_59 7 f_59) cur_59 nh_59
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 3 7 9 bds_59 (dagTraceF m_59 s_59 7 f_59) (cur_59 0) (nh_59 0) s_59 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59 : treeBlockF 0 9 ch_59 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 9 → ch_59 i = true := fun _ h1 h2 => treeBlockF_at nb_59 h1 h2
theorem lb_59 : LowerBin m_59 s_59 g_59 8 :=
  lowerDagV5 (kn_cons lb_54 (kn_cons lb_31 (kn_cons lb_24 (kn_cons lb_42 (kn_cons lb_1 (kn_cons lb_29 (kn_cons lb_15 (kn_cons lb_4 (kn_nil))))))))) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0xcccccccccccccccc
def s_60 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_60 : Nat := 0x40404040c444c
def ep_60 : Nat := 0x40840480000040000004040000400000008000800040404040c000800000000000000000004040404004440
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_57, s_57, 5, g_57), (m_38, s_38, 5, g_38), (m_40, s_40, 5, g_40), (m_52, s_52, 5, g_52), (m_30, s_30, 5, g_30), (m_43, s_43, 5, g_43), (m_47, s_47, 4, g_47), (m_12, s_12, 4, g_12), (m_10, s_10, 4, g_10), (m_7, s_7, 4, g_7)]
def cur_60 : Nat → List (Nat × Nat) := unpackCursorV5 0x2b09d252942328c2308c2037c5f0785e0781775c1705c1434c530485204811144110440a706401 0xa0515041e8391831b04f9043682f4023bb49b23e383231509834a451934e614e2942884e18428035735e695e60523150484434505452425e395e2952205e18521025e343da3ed232c94ec142a84f7843583f0833001f 10 1023 4 15 11 2047 16 65535
def nh_60 : Nat → Nat := unpackHintV5 0x148c025db443784778f6cbe354fc8298075260a8a5a90c08a180041c1481c1d000398f713100e60c14bf029265822428448008405103051e81e3a03070838d30e1980e1c170003800000 0x30f80302bae5c346cce9d18f7802c635847da3660074e8c600b5ad69ce8017aa08f746cc026a6e31dc02a939d541830e1c70e3c797b0ae318c6739ce12d70318398e1cb985346a0aaa8c631cc272d72aa7f8de0f5cbae319d3a31fc6f18df57ffcfad77e1dc6378c63fd0de15e5ad7273a31cbffc6378f05cba674ebc3e3c167ff8fe7fffffffc3b2d3fd026f03ea318f96b99a739d0062e1cb08e8d38327463096b939d 19 524287 8 255
def f_60 : Nat → Nat × Nat := unpackForestF 0xe8390b430a3e0a32094e0942b349b23e084f84519834834e804e80350843635e615e6052083f14524844125e115e34501152105e105210250833001f 5 11
def ch_60 : Nat → Bool := dagCheckNodeV5 m_60 g_60 ep_60 3 7 bds_60 30 (dagTraceF m_60 s_60 7 f_60) cur_60 nh_60
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 3 7 30 bds_60 (dagTraceF m_60 s_60 7 f_60) (cur_60 0) (nh_60 0) s_60 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60 : treeBlockF 0 30 ch_60 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 30 → ch_60 i = true := fun _ h1 h2 => treeBlockF_at nb_60 h1 h2
theorem lb_60 : LowerBin m_60 s_60 g_60 8 :=
  lowerDagV5 (kn_cons lb_57 (kn_cons lb_38 (kn_cons lb_40 (kn_cons lb_52 (kn_cons lb_30 (kn_cons lb_43 (kn_cons lb_47 (kn_cons lb_12 (kn_cons lb_10 (kn_cons lb_7 (kn_nil))))))))))) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0xff00ff00ff00ff
def s_61 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_61 : Nat := 0x170037003f007f
def ep_61 : Nat := 0x2800480000002000000040000000000000000000060004000c000800120032003000200014000400000040
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_50, s_50, 6, g_50), (m_21, s_21, 5, g_21), (m_49, s_49, 5, g_49), (m_35, s_35, 5, g_35), (m_43, s_43, 5, g_43), (m_25, s_25, 5, g_25), (m_28, s_28, 5, g_28), (m_7, s_7, 4, g_7), (m_8, s_8, 4, g_8)]
def cur_61 : Nat → List (Nat × Nat) := unpackCursorV5 0xb269246d86121c1 0x10175422b35d568a40d8e2d1056768e811c41b801f 6 63 2 3 11 2047 15 32767
def nh_61 : Nat → Nat := unpackHintV5 0xdf00a378a3009d8b71d8718069113666006c0000 0xe759d6739f60000f18e1be86305eaddca9de758000e1d40b56aa849d7b96f5a8004c63877a04e9d5d82359ce00003870e1c000b53a8048d 16 65535 7 127
def f_61 : Nat → Nat × Nat := unpackForestF 0x405d168ead755a2884728b4415841b801f 4 11
def ch_61 : Nat → Bool := dagCheckNodeV5 m_61 g_61 ep_61 3 7 bds_61 9 (dagTraceF m_61 s_61 7 f_61) cur_61 nh_61
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 3 7 9 bds_61 (dagTraceF m_61 s_61 7 f_61) (cur_61 0) (nh_61 0) s_61 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61 : treeBlockF 0 9 ch_61 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 9 → ch_61 i = true := fun _ h1 h2 => treeBlockF_at nb_61 h1 h2
theorem lb_61 : LowerBin m_61 s_61 g_61 8 :=
  lowerDagV5 (kn_cons lb_50 (kn_cons lb_21 (kn_cons lb_49 (kn_cons lb_35 (kn_cons lb_43 (kn_cons lb_25 (kn_cons lb_28 (kn_cons lb_7 (kn_cons lb_8 (kn_nil)))))))))) rc_61 nc_61 (by decide +kernel)

def m_62 : Nat := 0xf0f0f0f0f0f0f0f
def s_62 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_62 : Nat := 0x1070507050f070f
def ep_62 : Nat := 0x4080208000004000000020000060002000a0008000000000000000001020002000002000104050405000400
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_41, s_41, 6, g_41), (m_23, s_23, 5, g_23), (m_51, s_51, 5, g_51), (m_57, s_57, 5, g_57), (m_37, s_37, 5, g_37), (m_55, s_55, 5, g_55), (m_53, s_53, 5, g_53), (m_12, s_12, 4, g_12), (m_6, s_6, 4, g_6)]
def cur_62 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x10174c1ab35d206c9168dab1056768ea11c41b801f 6 63 2 3 11 2047 15 32767
def nh_62 : Nat → Nat := unpackHintV5 0xdf00a378a300706670006a8b62113658006c0000 0x6358d6318f60001739e3ce86705e8d46f18003ce78efa05ab5768277723d8e5bd6350003c7a811a3550958c6000078f0e3c000b51a8049d 16 65535 7 127
def f_62 : Nat → Nat × Nat := unpackForestF 0x405d168ecd74423945a26ac415841b801f 4 11
def ch_62 : Nat → Bool := dagCheckNodeV5 m_62 g_62 ep_62 3 7 bds_62 9 (dagTraceF m_62 s_62 7 f_62) cur_62 nh_62
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 m_62 g_62 ep_62 3 7 9 bds_62 (dagTraceF m_62 s_62 7 f_62) (cur_62 0) (nh_62 0) s_62 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62 : treeBlockF 0 9 ch_62 = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 9 → ch_62 i = true := fun _ h1 h2 => treeBlockF_at nb_62 h1 h2
theorem lb_62 : LowerBin m_62 s_62 g_62 8 :=
  lowerDagV5 (kn_cons lb_41 (kn_cons lb_23 (kn_cons lb_51 (kn_cons lb_57 (kn_cons lb_37 (kn_cons lb_55 (kn_cons lb_53 (kn_cons lb_12 (kn_cons lb_6 (kn_nil)))))))))) rc_62 nc_62 (by decide +kernel)

def m_63 : Nat := 0xffffffff00000000
def s_63 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_63 : Nat := 0x117153700000000
def ep_63 : Nat := 0x1420000000000016002200000000010604040000000001121032000000000114150400000000
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_19, s_19, 7, g_19), (m_2, s_2, 4, g_2), (m_23, s_23, 5, g_23), (m_21, s_21, 5, g_21), (m_20, s_20, 4, g_20), (m_26, s_26, 5, g_26), (m_4, s_4, 4, g_4), (m_8, s_8, 4, g_8)]
def cc_63_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xf81aa6e3dc0b81702d0da0b03412804e19c1306604c094328240c80847082103e27c0f81d1343680c841c001 0xa91f94a3b2646e488cc5c9f1183b200663e0ac78119cb4f3769666d1cbda18b24e2b29c3a05065aa0b8141b8a634d78612f8b15214028251483d2f0694e096c00cd402da404c510849c0d148152f05453076a408d08080a51b4fa169736d1e61a1caa4f934972291e4121c7a3f8d477008ddd519b614f602967451c70a18a93f13276224dc40998712f0c2560649c04918001f 11 2047 5 31 11 2047 19 524287
def cc_63_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x98251942145e9525413244910440c5300c02c483200801c45214050140500c830084200802000800 0x7cd02012f7e4ade9277848efb5cbcd46bb50ac972aa50a68fe823b928de0a3376171715c54051c13452051695c50051b5606a571614c681713014620b19134600d120145b141724d5891544504e1012828440f10834 10 1023 4 15 11 2047 18 262143
def cc_63_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x8642211087d3e1d4cc6432190ba5c2e146a04924104803c9548440200e47038150140000 0x2a24da49266245909066c50b6132325cb2092ea3fb88eed237b08cea460801b29460a29b1f86c9b141f05c9b142584c969427c609d14263607a1b2504c8c97220248cd4223508654244608e9b22a5c781b21024 9 511 3 7 11 2047 18 262143
def cc_63_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x94a5094250942328c2306a5374c1304c13044910440f22d0b02c0a1280a0280731c0701485001400 0x3795d8a557d818f4053ea4ef852fc943dc13f184b8411d8043f007fb813fed7bf25eda57f115b8255d7953ec0939460e21337a6cdc093a23fe68ef8237da8cf5134d1583395ccc1732134c60d35b4fd2d2f2b47c4d0f094e 10 1023 4 15 11 2047 18 262143
def cc_63_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xd0340d02f5bc2f0a96a0a8264982519424190204801b56c1745c1705c152541323d0f03c0b406801 0xa04b93e94278ae4e9509c0b92e97e691b8d94f9926e1449e5da9cb3497f464304fe501249351742bed656d4cab9c9538e4bce657da4ada8157372a6e4575a0aca7155362a29b14220261695c86029144fe249dc393785266e213d9825a504734087191622e2942450702beca56d24ab99953832990450204263e824 10 1023 4 15 11 2047 19 524287
def cc_63_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x3440 0x28a2f5134e 3 7 1 1 11 2047 19 524287
def cur_63 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_63_5 (Nat.sub p 160)) (cc_63_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_63_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_63_2 (Nat.sub p 64)) (cc_63_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_63_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def hc_63_0 : Nat → Nat := unpackHintV5 0x8fa058a852810987ee227b23c7b200789297810875e236a8b6654545b3a1572414da9842dad3f93435d9c3293428d9c28d002622b25111251002143d20311203001c63d11da90c558020a50002000000 0x2eaaaaaa6aaaa955ad6b95aaaaaaab755555544545438a95555555555595dbeaab71e3cf22183288a954671ec1c7d95555407816483d51cf510007181c611ea0b614004705541555514555000000aa00000aa0000950020000aa0b6000040400000010aa0000aa00a0800000005016ea9554080000000000002a80e0016c01544004000154a2a2002aaa802d85055554782a1800aa8228aaaaaaa00000155410aa0000000100000015400016c0006aa00000220ab54500004000aa4544401550416e82aaaa00a8700aa8228aaaaabb818de0e3ef7b0f0e860f28aa225551eed814f060070000554818ea8631800c6400555470800a0b6aa82aaaa28aa004000154000015400012a0040001540000016c80800000021540001540141055555555 20 1048575 8 255
def hc_63_1 : Nat → Nat := unpackHintV5 0x9c40259189283dea60522892f194bc010f203e854ea1036c3cb52629044a4002682886141fc1c7f001e01c463210414350c0d40030050744c1d0004c280a09028000a00014140005 0x175db3db5de5577baea977baeaa569aaaaaaa2a2aaa8715455555556eaaa995555555555555dec184ef71c190ef6034d8b76b9dbd9e0806bbdabdaf7b214deea82a1832889577b8fbb6797b5ee77b 18 262143 8 255
def hc_63_2 : Nat → Nat := unpackHintV5 0x98654b816570b2b8091c848e023720f3d062ee27741340e8a2043c2a0c24eb366919308818400b2205900268c0e8985f2a279013c00901c480021850c0981498050a0005 0x551450c1955510aaaabbddb3cee8ed55554d55552aaaaaaaad5550c631d355552aaaaaaa8000005300002a80002a9b0818cdeddd6c19b23696cd8b419b6d9e66b066c8819bd9e5dee8e96d69bd8317b066c8b71d77b 17 131071 7 127
def hc_63_3 : Nat → Nat := unpackHintV5 0xf30cbc408eec27bb00eec03b605ec417ac05d694ac298ab456911ca281e8505994825e0796416401969271881c6200178105cc156a09594154a1b528013e0c47880e43a142500050 0xf1e5500d8ef6b000000016b000000005ac0000000360100000000010705500000050415481ef7b391b8e6f7107decf26f7b8e46daaaa2a23d5438a8ab755547aaaa555555555555dec6103dec8d9b376f6782760f7b8e0c868a2860caa22555aaaaab755555555115150e2a5555555555555000000a6000055000055 18 262143 8 255
def hc_63_4 : Nat → Nat := unpackHintV5 0x9f6509a254952508ada589914885147dea77bc227803c6cab6676545d5a1594414fc9844fad3b39c3793a2e5942955024b4a2460524105241002311023100221101d1501755c125500c560023a200023 0x2a80000000001555400000080002a8000154000156540000000002aaa80000200008d8000000000400155000002000aaa0000abb0019b2a3c1446c0a8200078c06154453cf47a21550555545154dbc00d831e000c0000f1e550080180c646e82a060550c7433d0450c955555504551540080001640002a80002a80008d8000100000055000001102a8000002820ab000501b0002aa1550028222a1d011b00aaaaaa8228555555411455000002360000c000002a80020008382a8000200882a80010030018001b0000001801002a800800802a800000001e3caa2000006c000200000000020e0aa000080220aa00000001540000aa00aa000000000078f2aaa8ef60cdbb01a0000000000000aa008aa739ce0000000000aaaa0000000001540000aa0000ab35cd60000000000b9cd60000040000000000001b0380040000aa08002800022a8010c0801 20 1048575 8 255
def hc_63_5 : Nat → Nat := unpackHintV5 0x1759c500d4a49c151400054 0x46c00000000000aa020e000400aa02200000aa21b010002aa5523614054100050430aa82aaaa2855415555145500000000aa00005500550000000aa000055000055 18 262143 8 255
def nh_63 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (hc_63_5 (Nat.sub p 160)) (hc_63_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_63_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_63_2 (Nat.sub p 64)) (hc_63_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_63_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_63 : Nat → Nat × Nat := unpackForestF 0x169f44d3805a5ce25c9c4a13857270a84e05c0168f328de649b80b43966a72cd240527ca0240149724d44052380a430147f1c978051dc0c58818a50a4fe149dc404c8526f0c0521499c0c508129902502042600a37766bcec979dd273b94b7a030f4051dca1bb81f77026ec0900519b6a3f6d476e3181c42636a376e4d8dc091b5198094f6169ed44d185a5b3560662b8cc17185a3b193463068c2d0d84a70094b3b6b876d45611fac23b5b098b08dd64122c2333b6a076970ed282a4603b47ea318145361da3b4a8c0951413628253604b4a094130ed1ba1460424d88cd41092e21b50432a084090ed199e12f3c2567cd00f0939e1233b0b80251c75a79c1341d69669580d0ae1a05c1d68e604d0c416180341d68658934b628162451d29c3c8fc791d93c50270803c8dc94140f2331e076420f0841a0f0331e0563c08c740a00943168a62cd7865aa0b25f170282c548049f8a0140127625148049b809330f4bc024bc34a70092b0b6900914c22288424e046a40b148152f023420124e0405004918001f 8 11
def ch_63 : Nat → Bool := dagCheckNodeV5 m_63 g_63 ep_63 3 7 bds_63 164 (dagTraceF m_63 s_63 8 f_63) cur_63 nh_63
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV5 m_63 g_63 ep_63 3 7 164 bds_63 (dagTraceF m_63 s_63 8 f_63) (cur_63 0) (nh_63 0) s_63 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_0 : treeBlockF 0 32 ch_63 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_1 : treeBlockF 32 64 ch_63 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_2 : treeBlockF 64 96 ch_63 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_3 : treeBlockF 96 128 ch_63 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_4 : treeBlockF 128 160 ch_63 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_5 : treeBlockF 160 164 ch_63 = true := by decide +kernel
theorem nj_63_1 : ∀ i, 0 ≤ i → i < 64 → ch_63 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_63_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_63_1 h1 h2)
theorem nj_63_2 : ∀ i, 0 ≤ i → i < 96 → ch_63 i = true := block_join nj_63_1 (fun _ h1 h2 => treeBlockF_at nb_63_2 h1 h2)
theorem nj_63_3 : ∀ i, 0 ≤ i → i < 128 → ch_63 i = true := block_join nj_63_2 (fun _ h1 h2 => treeBlockF_at nb_63_3 h1 h2)
theorem nj_63_4 : ∀ i, 0 ≤ i → i < 160 → ch_63 i = true := block_join nj_63_3 (fun _ h1 h2 => treeBlockF_at nb_63_4 h1 h2)
theorem nj_63_5 : ∀ i, 0 ≤ i → i < 164 → ch_63 i = true := block_join nj_63_4 (fun _ h1 h2 => treeBlockF_at nb_63_5 h1 h2)
theorem nc_63 : ∀ i, 0 ≤ i → i < 164 → ch_63 i = true := nj_63_5
theorem lb_63 : LowerBin m_63 s_63 g_63 9 :=
  lowerDagV5 (kn_cons lb_3 (kn_cons lb_19 (kn_cons lb_2 (kn_cons lb_23 (kn_cons lb_21 (kn_cons lb_20 (kn_cons lb_26 (kn_cons lb_4 (kn_cons lb_8 (kn_nil)))))))))) rc_63 nc_63 (by decide +kernel)

def m_64 : Nat := 0xffffffff
def s_64 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_64 : Nat := 0x53f577f
def ep_64 : Nat := 0x524000000000003a002800000000050c020800000000003002200000000005005440
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_45, s_45, 5, g_45), (m_46, s_46, 5, g_46), (m_44, s_44, 4, g_44), (m_42, s_42, 5, g_42), (m_0, s_0, 4, g_0), (m_47, s_47, 4, g_47), (m_13, s_13, 5, g_13), (m_1, s_1, 4, g_1), (m_56, s_56, 5, g_56)]
def cc_64_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9825188e208461080600802007c5a5681a0609805c570585334c13044910405003c4f03c0d207001 0x5545795d514574506f56665654505e5d4a595a51524531264a5a4656354636303f5a3b403156283e24361c2614260c3e0836874b7e4b72476a3f62334d47412f2d272033182b1023041b001f 10 1023 4 15 10 1023 16 65535
def cc_64_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x1082902 0x8e398a35492d8125 5 31 2 3 10 1023 16 65535
def cur_64 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_64_1 (Nat.sub p 32)) (cc_64_0 p) (Nat.blt p 32)
def hc_64_0 : Nat → Nat := unpackHintV5 0x88002169378d9de3006adc1a9045f9597e005ba7d6c055983135624d4013304429490a0040840ff853e03cc7e130238c080273209c801ed0c760a162ec5011140002fc10017c0000 0xb9ce5738d6359ce7b9cfb5e9ce11781633ace358c7b1ac6358d6cd1ac8896318f6759c6b18d56cd22dab1ecf1b77b51ac6b18de73a7577352239c086339d631ad66aedebd221abdd9f7b3bceb1bc635bc6355ebd5d916cdcb1a9106e0f1e0a69a5041b283c7970e06486b220d9e3cb870324b1ed2880d89e3cb875008c6739c633acd1aa1c383001 18 262143 7 127
def hc_64_1 : Nat → Nat := unpackHintV5 0x620ec400cb7d6c5005b 0x367818f6338c633ac6b5aad9a044359cfbb9cf758c6b39d4e7022 15 32767 7 127
def nh_64 : Nat → Nat := fun p => Bool.rec (hc_64_1 (Nat.sub p 32)) (hc_64_0 p) (Nat.blt p 32)
def f_64 : Nat → Nat × Nat := unpackForestF 0x8a398a35074b8125064b755d745006476f56063f66560633525d5251545052450547465a4656052f335a3340363031560527243e243604331c26042b14260423083e0836041b001f 6 10
def ch_64 : Nat → Bool := dagCheckNodeV5 m_64 g_64 ep_64 3 7 bds_64 36 (dagTraceF m_64 s_64 7 f_64) cur_64 nh_64
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV5 m_64 g_64 ep_64 3 7 36 bds_64 (dagTraceF m_64 s_64 7 f_64) (cur_64 0) (nh_64 0) s_64 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_0 : treeBlockF 0 32 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_1 : treeBlockF 32 36 ch_64 = true := by decide +kernel
theorem nj_64_1 : ∀ i, 0 ≤ i → i < 36 → ch_64 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_64_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_64_1 h1 h2)
theorem nc_64 : ∀ i, 0 ≤ i → i < 36 → ch_64 i = true := nj_64_1
theorem lb_64 : LowerBin m_64 s_64 g_64 8 :=
  lowerDagV5 (kn_cons lb_45 (kn_cons lb_46 (kn_cons lb_44 (kn_cons lb_42 (kn_cons lb_0 (kn_cons lb_47 (kn_cons lb_13 (kn_cons lb_1 (kn_cons lb_56 (kn_nil)))))))))) rc_64 nc_64 (by decide +kernel)

def m_65 : Nat := 0xffff0000ffff0000
def s_65 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_65 : Nat := 0x1170000053f0000
def ep_65 : Nat := 0x4280000000000000000000000160000003a000001060000050c000001120000003000000114000005000000
def bds_65 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 7, g_19), (m_51, s_51, 5, g_51), (m_49, s_49, 5, g_49), (m_38, s_38, 5, g_38), (m_12, s_12, 4, g_12), (m_32, s_32, 5, g_32), (m_33, s_33, 5, g_33), (m_31, s_31, 5, g_31), (m_11, s_11, 4, g_11), (m_44, s_44, 4, g_44), (m_14, s_14, 5, g_14), (m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5)]
def cc_65_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xc0f802f0de0b83702d0da0a4948280d009c338260cc0981302604c084b08210420786f01e03c0780c941c001 0x7ad64eda79d34b3668e64d0cb89f0f8141d068364d0641a0d35b18682088cc5c9f0aa411147c224b83dac073500d69018d002c1e04b60084c00e5b01a2b82b5b044960655c08a3d134fa069736d1e65a1cba4f954972691e4921c823f8f477048dde519b694f642967c51c78a18e13f16276284dc4c998912f102561449c04918001f 11 2047 5 31 11 2047 19 524287
def cc_65_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x86a01801e2709a2681a0555505414144d1044101388e0380e0380e0308c02c4b02c0b02c0b024809 0x63d7316a1865cc128d9942b47f523b9b1bc58cdf8b8b41478a22c0518a98ac14611e2a091cca0e15c5e9e371714028d02c6a9a330d13028c14063a52fd195280a4404e14221310888b649591fab8ed446e9a334a1da40cd18568023 10 1023 4 15 10 1023 17 131071
def cc_65_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c24520893d1e0f06db6194c85d2e154a8509f4d46834184c060290b45028140844004 0xa2502e84c944a2d824be8fef23bb88ded233b0db2ba60881b2ab60861b289409e1328a50841727950a71829260a0502086c9c132512890092525090942395098d825a6c924a2006c8c0921030884be192b8249e0123 9 511 3 7 11 2047 18 262143
def cc_65_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xa4290a42727a5775c1705856058160581334c130448c5300c0300c0288a028082110401004001000 0x3e85c7c0a90052dfca1b784f660968c11ccc218c8397e03ef604db8afb295b452ae6454c60a4c09297a048eed51d22c3994072098e0951bc123c2497647eea8edc51bb72336a4a0d21719d1c330346c69ed6d2da1a3b2b435769caad2949a326342 10 1023 4 15 11 2047 19 524287
def cc_65_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xc4b10bcac3b02b1ac2a1a82649825194250815c4701c070184601806016258142410c40a80200000 0x124c67c94842329d27d3c94670a8831239a06930110f4a88d14b052672c4a650a8bb15f6c2b6ac55ceca9c8939752bed656d50ab9d153734bcd4969412b1ca52514a110170c09e430148a29f1252e1ca3c29437209ed212d38239b8438e8b11b141c4afb415b4d2ae6c54e30a64594184281061319d2d24a56 10 1023 4 15 11 2047 19 524287
def cc_65_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x4688 0xa39268539 3 7 1 1 10 1023 18 262143
def cur_65 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_65_5 (Nat.sub p 160)) (cc_65_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_65_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_65_2 (Nat.sub p 64)) (cc_65_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_65_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def hc_65_0 : Nat → Nat := unpackHintV5 0xd468d64f2a2ed1d576800b781e5b4042c908957868990964911ba131acdf95062e672e81794099c9446043e321ef180de8c85f4802346311005083028418001d21d0ce0d85986c28822122110104080004000000 0x2cb2cb2cb2cb2e8b2e2eae5e5e5e5ea2c32cb2d32c32cb4b4b2cb3cb000000000000b0030c30d75d75c30071c71c30c30c71c71ea8aa822a830c30e2ea3ea0e1c71c70c30c39879aaa83abaaaaaa1c00000008000001eb0d3acb3cf4cf50c32c31c3a50d30c300c1c72cf3cb691d30c31df4343004d30d30d71c75c31d31c3979783aba0c387932d33d33d32ea4c747534c30c300000000000001d71c72cf3cb471daa0eaea64002a3ea2d30d30e931d71d79a9831c70eaaaaa83abaa0000000000000d70c30c31c71c70c31c30c39797a0c383ab871e1c70cb0c30cf0c3a831c343430c34c300000000000005c75c7575747478ba8fa83a93aaaaaa875ab5a540000000000015e1e16b2cf3cb0c71c360001c71c7555755979787875ab554b54f54354755540000000000015471c71d56a946a8000000015471c71d56a951aa8000000015471c71d56a946a8000000015430c30d56a9516a80000000071c71d75d75c71c71d555502aaaa014471c71d53d54b551d543555555aaaa59556ac0000400000000aeb4eacfadadab3cf7cb3c34eb2eb7e2cf8b8faeb7d0c34d0d1d97acb3d791eb0d31d71c757575d1d1e5e5e1e1c7a55ab5cb7cf3d72c70df4d31c3a9500000000000000000000 21 2097151 9 511
def hc_65_1 : Nat → Nat := unpackHintV5 0xb3b428a44a28025a308c8a2161c81049f2126f0d9a8146a0019c0c5e8896e0c5b801620c41970f61039048de0637800d8062f868be002c830ac0629818980e260009800248180092 0x28fa4eaa832cf3cba6a68b3cf2eaaa8babaaaa200000000000000b2e830d4f2cf2c0b0b3ebac34d2d2bad4c71cb034ebad1ad6cadb8cf2ebae52c34d0aeb1badbaeb0cb0c2b0cbacb2e5834d30cb2d75d3d3c00b2e8b3ebaeb3cbae6eb6eb6eb2cacb2cb2cb2cb2cba2e897979797806db6db3c0 18 262143 8 255
def hc_65_2 : Nat → Nat := unpackHintV5 0xbd81af600b805ae000b285a5a709402a4a068a08a20087d0b1d81c70859c2006b059ac00630815a324f8712c124b001200c480011a0640068ca3631018be062f8009e2023048008c 0xacf2eb8acb3e0b3cf2cb3cf2ea2aaaa8000000002abad30d96bacae4c36b1e93ac6aead6c3cbae130dac8db4c36b64f2d30daeb82b2cfab26b6c0ebad30d6eb4c36ba0cb3eb82bae76cf2ebab6e73c06e79db2cf3cb6e79db2cf3cb80a2aaaa 18 262143 8 255
def hc_65_3 : Nat → Nat := unpackHintV5 0xe540ee5400e5400e4806d2492af11aa4854a4800a24129d4289c00a9b4069a8069642296400940128e03075cc270c286c4246b4086a8066502c6380c62c065dc283a51c2a4801a4800e46000c6c00006 0xcaeb0c30c3474750d46db401c00c30c30c751db6c30c30d1d1d430d0dac32c30c33c30d50c70c30c30c31d470e0c3830c0000000000c0002cb2d4b0d34c3aaa9900096bac34eb931eadadaeb3cb5abae034eb0d3acb3e0eac8b8b2cb2ea0e4e8b2cb2e69a8babaaaaaaa80000000000000b3ebad3d76bad31c73eb6b3cbaeb9753cac3aebae0cf5c30b3cf2cb3cf3cb5e2eae8b2e5e5e5e5ea3c33cf3d33c33d73d3d3cf2cb2c000000000000b3cf2cb3cf2d34d34e8aaaa80000000030c30c71c71c30c30e8aaaa8000000015471c71d568956a800000000b3cf2d3cf434d30eaaaa6400002b 20 1048575 9 511
def hc_65_4 : Nat → Nat := unpackHintV5 0x8121b2048007dc1b1cfd3a6c93b18496e5be2a1524ea5151a11fd2c4481b8f74d6335540c2c542aa3088711c1dc2006708016c1804d86c1330184c00613000049416125000468160e21c02708c0343400185c00301800006 0xc33c71c7430d471d1cf1e9f0002cb3cf4d35e0c3a2cb95f3cf0000c30cb2cb2cb0c30cb0eb1d3cf1d3c73c72c31c70cf8f3cf8f2cf3cb0d34c35c71c00000000000030c30b0030071c71c71c30c30c71c71cb2cb2c30d70c30d75d75c71c71c30c30c32c3ac32c30c30c71c71c71c30c30c3431c3430cb2cb2c30d70c30c3835c3830c71c71c00000000c000002c01c71c71c71c715504552cb2cb5d75d71c71c7554b471c71d50d1d52dad555552cb2cb557651c71c7555700000100000000b2cf3d77e5834d30cb52cf3c00b1c73c71d2dad4b2d1d1d51c33cf3d31c32cb2cb3cf3cb1d71d753e3cf8f3c00000000000014b6b3cf1c758f3e0c71c355500053d1d550c71c71d5554b6b556554b3cf2c71c71d54000000000000b1c72c71d4b2d2dad1d1d51c32cb2d31c32cf2cb2d72cb2c75d71d757575cb8b5cb8b2c0000000000001430d4b3cf2c3a0d55400030c30d2d53d50d55436b555430c30d5655500000000000001c31c34747436b50c31c71cf1c71cb5430c30c74c70c71d471e1c71e1d30000000000000c71c351550c71c33cf3cf55000000000c71c351550c71c32cb2cb5500000000aa1c31c3aa5555510000000050c71c3552cf3cb871e55500000aeb4c36b2b0d341c31c3555450c71c3550000000008db8db1c31c31c05540516e38db0c71c35554f552d1c31c351d55555436b5955431c70d54004000000000000c31c72cf3cb691d470c300adb 22 4194303 9 511
def hc_65_5 : Nat → Nat := unpackHintV5 0x6307471aa4a91d000a900000 0xc31cb1c70d43471d1cb4c79797000c30c32c3acb2c30cb2cf1cb1cb1d2c74b2c31c70cb2cb2cb8b5cb8b2c34d34c35d71c75c000000000000b0c71cf3c30e3cf83a0c751c30c0032c3ac30c30c33c30c30c71c71c71c30c30c3431c3430cb3cf2c30c30c3830e0c31c71c7000000000000 19 524287 9 511
def nh_65 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (hc_65_5 (Nat.sub p 160)) (hc_65_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_65_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_65_2 (Nat.sub p 64)) (hc_65_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_65_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_65 : Nat → Nat × Nat := unpackForestF 0xa349202d3e849c80b4b9f25338946749f4e1510168f340d005a1cc0440149f2c4a40525ca1510148e0290e449c80a3f01477071620e284194c832830a53e14a5c405c8528f0c05214a1c194083098028dde894bd94b7b286f607df02e3e0547b026f40900519b7249776a8dc8fdb91db945872280e4131b91bb7a546f048dc8cc04a7b2b4f65696d2941a42e32b4766470cc0d195a18094b3f6b87ed40fd2e1fa515a47eb48ed74262d2375b048b48ccfd282bb6c574c07e8fd55b01fa3b4e8c09c9814528271404f2a09c130fd1ba3360464d894941189423a50472a08c090fd19a012f40256840c10093a01233f0b80251c7dac9e1441f69e3ed2cdd281b95c370b83ed1ccc9a1a02c330683ed0cbda5181402f68c3e4f881249023f2047652500a4201023727050408cc801d9003320056421308422100231f0280250c741a0093f1b2682ed6c641a0bb411727c024ec55208093701266024bc44970092b0b6b016d402da405b400b0780249c1db003a60072d80515c09ad8124b022ae0451c04918001f 8 11
def ch_65 : Nat → Bool := dagCheckNodeV5 m_65 g_65 ep_65 4 15 bds_65 164 (dagTraceF m_65 s_65 8 f_65) cur_65 nh_65
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV5 m_65 g_65 ep_65 4 15 164 bds_65 (dagTraceF m_65 s_65 8 f_65) (cur_65 0) (nh_65 0) s_65 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_0 : treeBlockF 0 32 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_1 : treeBlockF 32 64 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_2 : treeBlockF 64 96 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_3 : treeBlockF 96 128 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_4 : treeBlockF 128 160 ch_65 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65_5 : treeBlockF 160 164 ch_65 = true := by decide +kernel
theorem nj_65_1 : ∀ i, 0 ≤ i → i < 64 → ch_65 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_65_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_65_1 h1 h2)
theorem nj_65_2 : ∀ i, 0 ≤ i → i < 96 → ch_65 i = true := block_join nj_65_1 (fun _ h1 h2 => treeBlockF_at nb_65_2 h1 h2)
theorem nj_65_3 : ∀ i, 0 ≤ i → i < 128 → ch_65 i = true := block_join nj_65_2 (fun _ h1 h2 => treeBlockF_at nb_65_3 h1 h2)
theorem nj_65_4 : ∀ i, 0 ≤ i → i < 160 → ch_65 i = true := block_join nj_65_3 (fun _ h1 h2 => treeBlockF_at nb_65_4 h1 h2)
theorem nj_65_5 : ∀ i, 0 ≤ i → i < 164 → ch_65 i = true := block_join nj_65_4 (fun _ h1 h2 => treeBlockF_at nb_65_5 h1 h2)
theorem nc_65 : ∀ i, 0 ≤ i → i < 164 → ch_65 i = true := nj_65_5
theorem lb_65 : LowerBin m_65 s_65 g_65 9 :=
  lowerDagV5 (kn_cons lb_19 (kn_cons lb_51 (kn_cons lb_49 (kn_cons lb_38 (kn_cons lb_12 (kn_cons lb_32 (kn_cons lb_33 (kn_cons lb_31 (kn_cons lb_11 (kn_cons lb_44 (kn_cons lb_14 (kn_cons lb_4 (kn_cons lb_5 (kn_nil)))))))))))))) rc_65 nc_65 (by decide +kernel)

def m_66 : Nat := 0xffff0000ffff
def s_66 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_66 : Nat := 0x15370000577f
def ep_66 : Nat := 0x424800000000000000000000002200000028000004040000020800001032000002200000150400005440
def bds_66 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_45, s_45, 5, g_45), (m_39, s_39, 5, g_39), (m_0, s_0, 4, g_0), (m_34, s_34, 6, g_34), (m_37, s_37, 5, g_37), (m_6, s_6, 4, g_6), (m_20, s_20, 4, g_20), (m_36, s_36, 4, g_36), (m_27, s_27, 6, g_27), (m_18, s_18, 5, g_18)]
def cc_66_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xa4052028053829c04d066813019804c0250528094049064812408244102002b145802c01504a805402a0140490448023040c4001 0xf2380e94c0fa5c0e1340a9440c14c0b3500aa44091540d35a0cb560b95a0a1560994e089420813d07935069442cc5b2bc572b34a2a3462925a2825723a5622a4f21a471f14a1d1461a1341985a18857138561204f1004a0d84707046060270486c0303c0335602a560535b04357038560203e01232b434fb2b4bb1347ae343aca4fac24ba7247a2a43a0a3f9923b97a37952339494f9094a8f1478a1468013f769377492f739276f84f6c84b5d847540435203f4503b410373b0333682f3182b2d827058230181b008170001f 13 8191 6 63 11 2047 20 1048575
def cc_66_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x82c02010075b69b0d1683253c984c2452089442211088361a0c23d1c0c44420100801601 0x10b4a83a340969fcaca0567b1d3c8d9d89a983d3c1ab88e1b098e63a6e9fb54dd287e70371a0bb29516288b54258952b1094854a54461a2af8e9728aa944501d269212a688444472d22959088c7524 9 511 3 7 10 1023 17 131071
def cc_66_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xd8360c92e4b82c2ac674896207cdf06d1b0649905c96154541501404c48b20053104130401004001 0x2fea17a50ba28350831695814fb8a3b4080d0a968449ea24e952c0d8c05432225396a64ad094a7aa32f15a0a74f136aa26d3d2a02948c4a2e23511b170a93c5c2a1a2d1116088ac44921a4ed166ca5323a96a93f4ea50bd20526422aa111107450366e9a101523088d8246a9a441707888a444 10 1023 4 15 10 1023 17 131071
def cc_66_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x84c22030080401d6e85f2e170b8552a142a04c9d4e069341a0b4582894092250c8440400 0x790f9f6457bd59ea567956a075b7fd5dfa5a7c159e03e77079d24473121c65c6f095d646648f9c94f7051db84a6c0d9ab48691119c5c21119af4a6893d9a4765119901e390c0e03061d20dc20 9 511 3 7 10 1023 18 262143
def cc_66_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8578ec1d80b01602c0542a8138e704e09c1382704e09c138222c40462788f01a2340680921200cc18030003 0x41261200f100994703e230647e48a3417110229947b308d66928cba50960bb22d5a41a347a568e2b51a55a8e2bd135ba06af3ed2e79a3cea5a9c4ad3656a54ab3713e3e2652815e4c2b4903f8c07d160dc8019433462148c7a0c2201410c50864810a140f0103bb4d894830e8ee111bc194c3a045001b1f42a3d83c 11 2047 5 31 11 2047 19 524287
def cc_66_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xa82a0a09ea781a468164581605814250140489204810240100388e01a060180600cc300c03004801 0xbe9b2f428d8d775e5cd59474250cd8ef2633c34fefd37bc4be543ab5152e844af0f2b034b8172d044ae0f2ac34b54f6d135b24fec537af4feb937ac4fead37b993ede47b6132cc46b0112b43caa0d2a424a78e69a38a58d2846c910f10940 10 1023 4 15 10 1023 18 262143
def cc_66_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x8844221108837db0ca642e962b051280ec7038188c0603012c904820900721c0c0603003 0x379a5eeb43dc49fb691f691fcd94a330658e4bf0493eb2469a095321234ca64c038d447fa48df189fe0137d124f2e0eb3d3667028cc4d996953281462838c54a190db31d3663260c407185183053660260 9 511 3 7 11 2047 19 524287
def cc_66_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xb02a2a82a0a82a09ce709c2709c2348c23080e0074cef380e030884200711c0701c0611806010804 0xfe8b1e4903ee307d06cf90c1ee973d9227a828f4049e4d7bc52b2f035e12bcba4dbbc2b7fc5afd4bff896fe12bf9a53f0483c017f6c2ddf857b70a7dc105c017b302b5c04e8608ef4ab75856ec4adb416ef02bf5029e8063c8d538a2c70840e668bca5138c9ff0137 10 1023 4 15 11 2047 19 524287
def cc_66_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8f20c8311c42e3b82b3ac28382200801f17c1f07c1e1691a0681a0681645815154123480f303c00 0x482518f8a25008c9c09934218d032480449810c6019110224b48a2c17120228ec7b1c8de371ac65438ba571510d381591c13896a9068e21fb641638870d90d182172a42a4484851080920c2841756824ac6a0e588ab1cd3e810ad13d5a232fc425b864af0794e071cb8c5f6e0b6c315d7229c04393905e680acc01391423 10 1023 4 15 10 1023 19 524287
def cc_66_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xe81d03a0740e05a8f506a0d41a8302e007e2f81d12e6582b016026334c604c018030048c9010120002000000 0x9e03d9d8359f25d9e8519d0509325a8c25667156441469a856a04579fb5a9cb569c2579ba569295a8b9566f05b668574f84b43847358392b0319b02b9a0299982710021429461084696b4d9894c980414f03b420372a021658459225a65156960569725696a3e9195a6e85b648579582991144298319302911821920299434b93b4792a3b91a33911464e83b3f03329023 11 2047 5 31 11 2047 20 1048575
def cc_66_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xe83a0d5750d4314a9ea0a0a8098a51942328c1d64e93044910440f23c0d22c8380c0300c00300000 0x2c31c58234afa695e0e2ba1a56f45ad289114fdfa9bcff4a8829efc51d4425a0443198420a06e1c17be8279ee955511a79244ee38a92993a8ea1a9fbe537a987f510dea00bd5f5d9cc750c4fdf09bd585caa0a34f141401d9fc33040370b4f5ec9ad2d3fa526f094fdea9bc203f7a06f4d93299235264483a9ef351e909251c28a3049440e6861c50834 10 1023 4 15 10 1023 19 524287
def cc_66_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xe0c2c0c084808008000000 0x23aaa5a544b3c732856acc1c96423b24a3408ee4ea5471468da8963145461d95c23 8 255 4 15 10 1023 19 524287
def cur_66 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_66_11 (Nat.sub p 352)) (cc_66_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_66_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (cc_66_8 (Nat.sub p 256)) (cc_66_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_66_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_66_5 (Nat.sub p 160)) (cc_66_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_66_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_66_2 (Nat.sub p 64)) (cc_66_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_66_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def hc_66_0 : Nat → Nat := unpackHintV5 0xacc00ac006a8c1aa2c30a2c00a0414a04009f8069e00c9d4069c00a9b4069b4009b0029a40698c0c8c4648ac0c8900e629345d8285d40258c244b46c4a8064a4023f458274c01d450060ba0003000000 0x237d1d38d2d71cb53134e8d74c78c78c9b1c1c78e6db934c4575c07071c2c2d34e31c7070c30c33cb0c32d72d70c70c71d71cb1d3c3433d4d4d4b2d2d53470e4c384d3151c74c071cb2cb8e35cb5c3c63538c2c2c000b5cb5c0c80030010d0c30c113570978000700000134d1d1c0030c000700000010d0c0014d4c18c008000000002c0007030c03020c380000015540030c30c0000c08000002c000c000000154001541000631c71c71c71c7 20 1048575 9 511
def hc_66_1 : Nat → Nat := unpackHintV5 0x8c0d11582a290244a087dcb8f08b1e1003b40e76800e8849755c264864a820880d0fd131e6143844870008df011b8062c4ac57018a40a086c210c001c850271204e0008c100f820001f00000 0xc3a54cb2d32d3138d3140b02c63118d830d4c30cb550c350c341429430c30df7d8e38d38c30c30d559550c30c30c31c7550c30c30c34d357e31d31e973c30e930d2c3430d3136c0c31c070cf0e4b90d2cf0e4c34b238cf8c30e32e3478c78e30d4b1c76db3e0cf0e3c34b0d0cb638cb4c36c6c0e98358f838cf07070c30e434f0cb83838c34b0d0df638d74b4cb5326c1e4db935d31c074d3 19 524287 8 255
def hc_66_2 : Nat → Nat := unpackHintV5 0x94c0694006918146f1146e00867038670005ec425246451408424784100a2fc8a2f80227442274002401a234062200a20c0a1fc081fc001e80a0f8780f4020982e098000641a04c0c0380a01c0e0000e 0x4d340b8d0c30c354356455030c30c30cb2cb2d4b0c30c30c31c7454472c72c750d55555552d55078cf5cb0d34304c8cb5cf530c34db4e28b2cf3d5d755c5e35c4100b2d8e8f3cb5cf3cb2cf3d2cb53cf2c00b2d8ca3c31c71e834b0d0c70e0c381471c71c32c2d71e3530c138701cf0c36c418c2c07a1c1c30cfa3c3a0d2c343083830e050cb172e34d04c078c130718c18c2e30b8c 20 1048575 9 511
def hc_66_3 : Nat → Nat := unpackHintV5 0x7c8223da051d18dce740c7380139c001ba89cd10625dc562ae20157000ab8005400e29d0194703ca34024d4231df458ee00c6cc52366001b3000d08486780631e0f143260838f0119820143c00a0000002800000 0x18e03002c1c1c0c238e300002d72d70c000c043430c3018e34d5c25e0000000134d4d4c3034234530830e15cb2d3000000c30000000010d0c0018d4d4c008000000b000000830e0c350c313175d70c307071c744551231c638cb5c18e3430d0c13430c294b2d0c30c30c30c30c32d72d7654354551430c30c30c71d71cb1d11d15550d554b63555554ba2cb3cf3cf52cf02c172cb8e30b07238d4e302e3cf8f3cb2d10b2cf3c1c1c71cf3c4c4d34cb2c30d72c30d0d352d5830e1314701d2c33cf0c30cb2c30cb2cb2cb0c73cf3c31c72c72c7433d3c353534b6352cb53470e2cb2cf0e2c2cb2cb151c72c2c1c72cb0c32cb830e50b2c0c307070d552d4412307 21 2097151 9 511
def hc_66_4 : Nat → Nat := unpackHintV5 0xc8065751b2ba3050e669ec313d8027b004d6209a00d260e23c1040c6c7d444f9019ec063d6027ac00f5801be2d35a224e9cc8716108061de323b00c74818d613144680a1e80a0a0130100026 0x2307538d2d4cb00c318d031c3830e52cb1c71c70030000c308d0300830e12cb00c3838d394b2d40e30c0d3082232cb3c30e94b3e343054030da52cb14e3930d4c3440db2d72d707070c3440c358d344d32d38c7575e5e144d31c707074d3448d135cb4c300c300703000707434306350535340070e4db0e5532cb4c71c0071c00c35e0c384c50c307075111e32d78cb54c1e3638d2d2c0707400000c000c30c3000055000055543560c0c30c50c30c34b55400c3030c45051c700070750d5001418d554018e35cb5c3c63538c2c8b 19 524287 8 255
def hc_66_5 : Nat → Nat := unpackHintV5 0x89c0144b01a1d840f24e4788053b6071d8814e7c246e22e36e019b3020c70946320331203961140afc06578032742413880c9a80e434501ec170b52084d868200360c81c0339841442c0641f0310080c06400030 0x15cb5c48e354351520c394b555830e3cf45447830c30e1c71cf1d5556635554f55568e8e3081c28e38d4c207002a800200000198010d0c023a35341aaa2cf2cf3cf3cfa07071c7a030343430cf8e3536aaa3cf3cfaaa1c73c73c769a4343430d0cf43438e3aaa93cf3cfaaa1c73c73c7664343434343438e353aa6a2cb2cbaaa1c72c72c769a4343430d0cb434300aa0008000006600434300aaaa3cf3cfaaa1c73c73c75a6634343430d0cf4343562aa88faa2ea878788aa0e0c30c300830e0000c000005555000c30c30000c000005500055000c30c3000c0000c0000055550000000c200300030c30c00000b000c0000000005506300055402314e34369b638c3535cb5cf3d363538c32cb4cb8e34d5cb4b53 21 2097151 9 511
def hc_66_6 : Nat → Nat := unpackHintV5 0xa203e9d8249802c9481c9002467d425a46c4749845410300aa2e40e2e4002bc142b0061889418402178061242a120020f8140e00c09c2209c00090060800808000080000481c03c06030060240600012 0x238cf4d2d70d30d38e34d130c8e34d130c078e30c138e34d130c830e830e3cf830c30e1c71cf1d98d690d0c3433d0c34343543036c30c3030c32c30c30c30c0c0c7a80c3030d4b5cb5c30c1c1c71d1160c3a0c38b2cb2e0c30c38b1cb1c71d555555555c1e0c38f5cf5e0c385c50c35c73c70707652d3d552d558cf571cb63830e830e5d7830c30e1c75c71d5595553d555572d78d578cf5238e35e32d78c4a3638d101e38d8e38c48e3 20 1048575 9 511
def hc_66_7 : Nat → Nat := unpackHintV5 0xd5c05a3883390e66c06ccc0d9801b250b6400ac58298981b0a095ec28bd40576842c62757814a44ad2721a1a34432027b4b0c2b4155301ccde2d8c0461508b010fc1a1f4043e0086e0e000dc 0x828cb1c8e33c178e38e30b238c8e8b5e38cb5e38cb5c2231c08d4d70978000700001753532d7231c04c1309380172cb4c00000200002c000001c0000008c00400000000087873cf0072001c001c535340701305d3093800751c00000b3cb3c000800000007007000001c8c0003cf005cb2d7004000070f3c0b2c23cf8011c740000003c080000b2cb2c0000701c00000001c8cf3cf3c004002cb2cb00225a2cf2cf3cf0707a44954f200000000aa0000550055501c8e34047238d66a9514aa54f4b53cf3cfaaa451c751471cf1cf1d98d55555554f55 19 524287 8 255
def hc_66_8 : Nat → Nat := unpackHintV5 0xb79dd581726f4144e9089c00fb981f70038e6071c00cb9815a3d2486c48c048b068fe181fc003ec0c7a830e3121c00636c146c018d50318e1c31c0063800c7001444a288003c9482e4b0005c 0x700000000b0023cf800000707223000000700710020c380033c30300070800800aa0000aa000c30c30002808808cb3cb3e3cf83d0d0e0c380c00080003db3db00003c0db0db00000c0cf0c1c00b0233cf00b871e0003d41c000f3c232c008f3e0b03d40c010230c300c50c3800b2c071c70080f08f3e0f030830e03033c300002d72d7072001c0007535307a08c7238d72c5cf23078cb8c2c8cb078e3a8e38e3088c717097800070001753531c4c1309380172cb4c00000800000000b001c00230000001c00010000700002d72d70700000725353 19 524287 8 255
def hc_66_9 : Nat → Nat := unpackHintV5 0xb480359c042ce00167000b1412564132a805145874a0a1150400a698c53082287a853f9221e28d0c35705b0352a31a9510049ec4e43a5e1c12e0c90bc558782ac0011c1d08e0003e844192310782881e0f000078 0x2358c3a2cb3cf432cf02e8b2c0f3cb2cb50b5e3973cb5cf2c2c3db883cf2cb07073cf53538d75d32c54d35d31c79382cb050701d34e32c4d7573c0b3cb3c0b8cb2c0f976cf8b2cb001c1c000701c071c071cf3c172cb5d755c701c00f00000b2cb2c0000f3cf3c0000b2cb2cf3cf3d32cb8f3e13104701cb2cb8b3cb2cb8f0f3cf0b2cb2cf2cb2c002cb02e3073c3c70b071c072c71c000701cf3cf3cb4b2cb4b02cb2cb2c701c00023e3cf3c02e3000f014d4cf3cb08cb23cf82c0f0000b5d4d4d01305d3093801754c00000b3cb3c000b8c80000000000000003cf005cb2d700400080000000aa00f0b00022300000002a800c400030c30c02230800f0f2c007071c030340a888cb3cb3cf3c71c001c743430c33cf0b8cb23cf8b2c0071c71c71cf500b8e0f00f001c704080000002a80002a80030c30ea3cf8f3c71c71c71c71c71e0c3830c33c30c70c73cf0871e0001c00708c1c003d753530c00c300d3408d0c340172cb4c4000 21 2097151 9 511
def hc_66_10 : Nat → Nat := unpackHintV5 0x81d191fc45878c329d586c724191a69145e55a96ac7455f261554144f23193a4124e900137c144dc0191d0d03bc5c0e2864340250cf406334048b60b82a6190948a82122006111c1442003f88c0c61c014ce60370e00006e 0x2a8002000002a80030c30c000215402a801542000000000088c802a80000f02c020000001c0000aa00000c100c30c30022aa2c2ca2cb0707a43430c30c30800000aa0000aa00000c30c3aaaaa28a2e3aaa2cb2cb2eaaa2871e8a1c72c72c7aa9839a0c30c30c30c30c30c30c38f3ea2e32cba2cf2cf3cb2cb3c3db3cf3caa1cf3cf871cf1cb1cf071cf071e0c3830c30cb0c33c34f3c34f0c31c3cf0f3cb2e20b2cf3c1c1c71d4d4d55560c39560c38b2cb2d560c30c3871cb1cb1c1cb4e8b0c3830e0d30d30d0cb0d0cb0d30c7430d13168391c070cb0cb8d2c74e38f3ea2cba2cb2cb2e1cf3cf871cb1cb1e3cf934c30e2cb2c74c72cb3cb2c2cb2c8f3eaa8b2e8b8cb2cb2cb2c1c72c1c7873cf3e1c72c72c70cb4b2c34b2e0c3830c30cb0c32c30c700aa000800000aa000c30c30082aaaa0f0f2cf2cfa07071c743430c30c30c38cb5e3aaaaa2cf2cfaaa1c73c72c7aa0c30c30c30c30c30c30c300aa000800000aa000c30c300aaaa2cf2cfaaa1c73c72c7aa0c30c30c30c30c30c3aaaaa2cf2cf5555555aaa1c73c72c755aaaaa2e32cf2cfaa2aa88faaa871cf1cb1e2871e8aaa0c30c30c30c30c39a0e9a0c30c303c3cf3cf002cb2cb008f3e004b2d000002cb2cb00003c000003cf3cf002cb2cb00000c55000c30c3005500c0000000003c200f000b2cb2c0b8c000b03c0000000003cf3cf0000040b2cb2c0232d78e3cba6cb23e35e2cb2cb0f8cf2083cf053d7 22 4194303 9 511
def hc_66_11 : Nat → Nat := unpackHintV5 0xc4064a64ee97c7489474704c85d4984ac94269221a0640d06800068 0x800000aa0000aa00000c30c30088e829baaa8f8ba0f3c0a220a1c7228001c1eaa60e680c3030c30c300cf3c232c8f3e000b00f0000f5d4d4c3030c2340d30430d001172cb4c00088c006c023cf800f000b0000000000020c3800300100cf0c00f3cb5cf2e3820ba3e0f5cf3c71c1c1cf5d4d4c30c30d4c3630d30c7411a0e172cb4c701c34c0aa8088cf2db6cf2db8f3e0f3cf0071c071c0708001c1c35b6c35b830e030c3033c30c0700aa000800000aa000c30c300008aa000800000aa000c30c30000008000aa0000aa00000c30c3 20 1048575 9 511
def nh_66 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_66_11 (Nat.sub p 352)) (hc_66_10 (Nat.sub p 320)) (Nat.blt p 352)) (hc_66_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (hc_66_8 (Nat.sub p 256)) (hc_66_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_66_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_66_5 (Nat.sub p 160)) (hc_66_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_66_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_66_2 (Nat.sub p 64)) (hc_66_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_66_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_66 : Nat → Nat × Nat := unpackForestF 0xb494400b4fb3239b303900b4bb1a51b185100b47aea38aea34ae934ae838ae83400b43ad345ad14400a4f00a4ba7b5da785caa846a7851a803fa914ca8037a8017a785000a47a324ca3246a513fa5137a3244a3124a3028a302400a43a1039a1038a103400a3f99c5799b5a9d25d9d0519d83d9d8359d05099b5699a5799a569982b9a856998299982700a3b9814c9804100a3795a5695a3e960569582900a330094f9134b91347930299123b9202991233911460094a8fa518f851009478aa3d8aa378aa358d0198a9438c0198a92b8b02e8a8430094680b568935480a5f80a5b86b6c8686c8686080a578425484244840288402480a5383050823568225680a3981056808390093f7745a7f4587725f7725b7cc607c86c7c860772577a25c7a2447a0287a0247725378b5e78a56772417785677041009377525675856750290092f74031009277034570144723547013f70c5870840701370084f6d34b6d3436d24f6d2476d23f0084b5e35d5e25c6b2465e25168a3f6994c68a37689275e2506726c670285e23b6526c65254650285e2336236c6226c6226062a50620385e13f604606026c602605e1375ea6c5e8285e12f008475d04454a4f5c05c54a475484c5a13d5a135548465893f58937548445713f571375483c5593f5593754834548240084352a3952a3852a340083f45c5745b5b5086c45b5745b4b45b4745a5a45a564595a4b2514c23d4c2354b2504b05d4595645857458564583f46b5646b4646a564695a469564583e458370083b41a414402841a3b42a404285041a374194c008373bb5b4006c3bb573ba5a3ea453b8563cb563ca563c95a3b83e3b81e008333724639a44398483714f38a5c37147378253704a0082f360363234a34b48348443224f3385c32247320463201e0082b2e34a30b482e14f2eb502ea502e8502e147008272d0440645b2c06c064570634a2a84d0634629b4a0625a2886c062572785c24345242522423a241522405e248342405206256230440624f2205c062471fb4a1fb461fa5a1fa560614a1da3a1da361d84d061461aa3a1c2381a93f1b04c1a937061340605a1925406057143451423a14145159421592a1584214144149441403a0605613248129340604f10a5a10a56108460604a0e25c0ea380e94c0e1340604707b5a07b560c14c0795a0ab500aa44079560794e09154079420793d07935060460694406027008230235b0486c023570205602b5602a560203e0081b01232008170001f 9 11
def ch_66 : Nat → Bool := dagCheckNodeV5 m_66 g_66 ep_66 4 15 bds_66 362 (dagTraceF m_66 s_66 8 f_66) cur_66 nh_66
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV5 m_66 g_66 ep_66 4 15 362 bds_66 (dagTraceF m_66 s_66 8 f_66) (cur_66 0) (nh_66 0) s_66 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_0 : treeBlockF 0 32 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_1 : treeBlockF 32 64 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_2 : treeBlockF 64 96 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_3 : treeBlockF 96 128 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_4 : treeBlockF 128 160 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_5 : treeBlockF 160 192 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_6 : treeBlockF 192 224 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_7 : treeBlockF 224 256 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_8 : treeBlockF 256 288 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_9 : treeBlockF 288 320 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_10 : treeBlockF 320 352 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_11 : treeBlockF 352 362 ch_66 = true := by decide +kernel
theorem nj_66_1 : ∀ i, 0 ≤ i → i < 64 → ch_66 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_66_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_66_1 h1 h2)
theorem nj_66_2 : ∀ i, 0 ≤ i → i < 96 → ch_66 i = true := block_join nj_66_1 (fun _ h1 h2 => treeBlockF_at nb_66_2 h1 h2)
theorem nj_66_3 : ∀ i, 0 ≤ i → i < 128 → ch_66 i = true := block_join nj_66_2 (fun _ h1 h2 => treeBlockF_at nb_66_3 h1 h2)
theorem nj_66_4 : ∀ i, 0 ≤ i → i < 160 → ch_66 i = true := block_join nj_66_3 (fun _ h1 h2 => treeBlockF_at nb_66_4 h1 h2)
theorem nj_66_5 : ∀ i, 0 ≤ i → i < 192 → ch_66 i = true := block_join nj_66_4 (fun _ h1 h2 => treeBlockF_at nb_66_5 h1 h2)
theorem nj_66_6 : ∀ i, 0 ≤ i → i < 224 → ch_66 i = true := block_join nj_66_5 (fun _ h1 h2 => treeBlockF_at nb_66_6 h1 h2)
theorem nj_66_7 : ∀ i, 0 ≤ i → i < 256 → ch_66 i = true := block_join nj_66_6 (fun _ h1 h2 => treeBlockF_at nb_66_7 h1 h2)
theorem nj_66_8 : ∀ i, 0 ≤ i → i < 288 → ch_66 i = true := block_join nj_66_7 (fun _ h1 h2 => treeBlockF_at nb_66_8 h1 h2)
theorem nj_66_9 : ∀ i, 0 ≤ i → i < 320 → ch_66 i = true := block_join nj_66_8 (fun _ h1 h2 => treeBlockF_at nb_66_9 h1 h2)
theorem nj_66_10 : ∀ i, 0 ≤ i → i < 352 → ch_66 i = true := block_join nj_66_9 (fun _ h1 h2 => treeBlockF_at nb_66_10 h1 h2)
theorem nj_66_11 : ∀ i, 0 ≤ i → i < 362 → ch_66 i = true := block_join nj_66_10 (fun _ h1 h2 => treeBlockF_at nb_66_11 h1 h2)
theorem nc_66 : ∀ i, 0 ≤ i → i < 362 → ch_66 i = true := nj_66_11
theorem lb_66 : LowerBin m_66 s_66 g_66 9 :=
  lowerDagV5 (kn_cons lb_7 (kn_cons lb_45 (kn_cons lb_39 (kn_cons lb_0 (kn_cons lb_34 (kn_cons lb_37 (kn_cons lb_6 (kn_cons lb_20 (kn_cons lb_36 (kn_cons lb_27 (kn_cons lb_18 (kn_nil)))))))))))) rc_66 nc_66 (by decide +kernel)

def g_67 : Nat := 0x1171537053f577f
def ep_67 : Nat := 0x4284248000014200000524000160022003a002801060404050c020801121032003002200114150405005440
def bds_67 : List (Nat × List Nat × Nat × Nat) := [(m_50, s_50, 6, g_50), (m_63, s_63, 9, g_63), (m_54, s_54, 6, g_54), (m_66, s_66, 9, g_66), (m_65, s_65, 9, g_65), (m_2, s_2, 4, g_2), (m_60, s_60, 8, g_60), (m_64, s_64, 8, g_64), (m_62, s_62, 8, g_62), (m_61, s_61, 8, g_61), (m_41, s_41, 6, g_41), (m_58, s_58, 8, g_58), (m_25, s_25, 5, g_25), (m_29, s_29, 5, g_29), (m_10, s_10, 4, g_10), (m_59, s_59, 8, g_59), (m_52, s_52, 5, g_52), (m_1, s_1, 4, g_1), (m_3, s_3, 4, g_3), (m_57, s_57, 5, g_57), (m_48, s_48, 5, g_48), (m_13, s_13, 5, g_13), (m_16, s_16, 5, g_16), (m_56, s_56, 5, g_56)]
def cc_67_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x900c8024011827853c01e00e827403a01c82e406e13701a84d40680b401982cc0660300d800bc15e02e05700b80561a1280c0001 0xfb4b0ed6b0e56316d6f1656b15567145631346b124631145b104530f2660da4e0cb680c2680ab7009b5802b4208b680234007b7006b580437a05b6005260044570325402d630246e01a660bd6f0b56b0a567095630846f074670645f04c5703b6a01342c4c5fc345bc1c57bfc53beb5fbb35bb8b57b7353b534fb3b4bafb47ae343ac25fa5a5b9e2579ba5396a4f9424b912478c2438823f8423b7f2376ea336405f4c0573d84f2d8472303f178370d02f008270003f 13 8191 6 63 11 2047 20 1048575
def cc_67_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xf078385c0d8ec343a0c16030162b058284aa502450280389c0a450209006230090400200 0x7d5a5ed61771a1cc706f16192406b9e9a46064d798a66895be1d6b8359dfd63791a9d26f7099db25f6695d82415c990ea4e569f14a54389393a444a910fa76469110a44 9 511 4 15 11 2047 18 262143
def cc_67_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x986609099b64181601805c5705856058151541415014048920445103c8f016850104310c02108002 0x2fd70bc9daea6cf55abbb6be8d9f9351e09af6a67d6947423fca8ef0237b88ced364aedf2ab54a491282449c9da6a4496df2527692912cd6fb15aeb567a958e9b66a29ae7a639896e42538e8e62c687d1e214707b1e20458 10 1023 4 15 11 2047 18 262143
def cc_67_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x90a408c54f44d10440f23c0e1344d0304c02c4b02849124081200801886014441100401003100c00 0x202bb3fc587d4a92f19a55b7c9b6b916cf1ed8e35a4c5a6f894d70e99e1531c1a498247f028edf91bbe233796d2d48fd911bbce78786d8ec93dd6b839b66714d8ded3dbab8362666acf4d2dd99eb833276626d6c99e98e3d30c60 10 1023 4 15 11 2047 19 524287
def cc_67_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x88110210c20840f88ba14128048490101200384700c118028450081100184300410800841000100000000000 0x276384da7c9a4c98f16f122be1361c16b77ed5ef1a7dd34bb668f68d0ecd30d8a5bad4af5493e9d25d2a47a14873e8fe791dce23799467008de5a324a354928f920d5239b3464648a4a9111f2192a42266 11 2047 5 31 11 2047 19 524287
def cc_67_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xb8b8aaa8a1a0a0a08b88817270696861605250504240403230292828280c0801 0x17d1f2f5b85db7cb9ae170972dd285ab7cae6cd56d7ac9275837caf6e35c982b23e55a70a94f95093a9ab85034ea44f946992892750252 8 255 3 7 11 2047 19 524287
def cc_67_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xbc4e4dc03806c2d81a0b40680c8590320640a9150281500a0130a604c0888750c11802844088004608010001 0x70128df249f95bfeeb5fcd67f6ac7ead7bd1a979a6ff14d5e099fb5337625feb4afcc4ab84936486f990cef817d702bef027db8c9b2d935a326834ed44e9a6993492768252cd8d1969d329326e359da69fb0d0f5d2ceaa4fd14879e8ff391de6237c946786dc719be62b71c3ad78119af62f60360 11 2047 5 31 11 2047 19 524287
def cc_67_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x7e5f0749d0741b26c1b06499064163581514c9304c0e5308a2280a0280a015450140501400500000 0x8356f82d6b81d67805637fc6a6606f4e0673f05f3005777a747ea647d27c772647c2547b85479264751287292479266749287212477c5d774556585d4d0552f047741287192473928711247526e74a667425e73a56700257296e721667195e711566f815 10 1023 4 15 11 2047 20 1048575
def cc_67_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc312c0700b12a28661084210842017c5d24ad204812048111404f11685010440100310c03004801 0x8f83f8f0378ea448db636a05d518552503f6906f510679046b8e46388b4e7a3428d2668ca4e6886f508672404f8a054348476806f500678bd6f8b56b8ad6789d638936684b4e88a526786f4f8674105f3405786054330477926687d6f8756b86d6785d638526684a3e6706f4f0674085f3285783c6882470814588085431857 10 1023 4 15 11 2047 20 1048575
def cc_67_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xc42f292e408c6308c1e5781e0781c2701c0689a064518441013c4e125481200711c0610541000400 0x9fd709f2509c56da545ba4457a3361a1b57a034f9eb47568574384f368471c0379da449d4539ca4e9c23e4285f2784f9ac649a2689947c98a7097b669b46699b6f98367973497aa326a86f550671b037962442703f5406795c6b9526694a4e538672604f1a837935709236693d6a92b6791b51528671983790a44 10 1023 4 15 11 2047 20 1048575
def cc_67_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xac2b091e40902317d1e1781e0781d1741c1701c0701a2680ce2c4b0284a015450140230802000800 0xaf366a8a6b9d263aea396c06f5a0671002fad464adb59acb4f4584f1d037a724eaa244a9244a756b59067abd6bab567aac6ba9c5ba8c53a825fa7a57a6a4e78a42588674485f380572884fa6027a3b71a4a70a3d6ba2c66a0c5e793665786779670a2b60a2270a147ca0b70 10 1023 4 15 11 2047 20 1048575
def cc_67_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x822f51e83d07a0f41e83d05fcbc1782e156682d0020036a6c0d81a126e4c0980e51c0344680a314028039807 0x9a35ebf25999a4f4a84f08027be56bbdd67bd35fbcb57aaa6b95a5b90253bc23978a31608674985f3b857bb8371302fba370a236698b5e79266b856dbac5bb9c57b9261a1a579824f92a475f8574884f3a04707027b834e8e253b7a394785f1202fb6266b6c66aca6fa0267b5a496d06f5e06706027b4b66a9a6bb42395d0671102f5c0579f366b226605035b12575b857b0827b356a9ea67b2a5cb1a51b02505b06704827 11 2047 4 15 11 2047 20 1048575
def cc_67_12 : Nat → List (Nat × Nat) := unpackCursorV5 0x3b0e870ac030087df2784ff3c0f02d00b 0xc035c5b59c52598ba3f87a3b832377e2332c83f220371682f0b827be36bbab67c4349aba6ba5267c3a498b23f8723b82a377da33638672c03f218371602f0b027ba46662867a4b66c2b61bdb5bb9b57c2261ab25ba42578aa3f86a3b81a377ca33620572b03f208371502f0a0278a12f8612b809277b923c1349c0a4989a3f85a3b802377b233c00442a03f1f8371402f09027 10 1023 4 15 11 2047 20 1048575
def cur_67 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_67_12 (Nat.sub p 384)) (cc_67_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (cc_67_10 (Nat.sub p 320)) (cc_67_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (cc_67_8 (Nat.sub p 256)) (cc_67_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_67_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_67_5 (Nat.sub p 160)) (cc_67_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_67_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_67_2 (Nat.sub p 64)) (cc_67_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_67_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def hc_67_0 : Nat → Nat := unpackHintV5 0xad1214a99cdda59901a139189945fd93dd5a8ecd4484c6827b3e6275118b6b367765417d5b4e7d56ad284fbdbc4a2167421e013ca55e34a2012fd9322b8d1324b9b52168d41ae5a119685f15b8ec1258d80c9d6f08351a02497b000092000000 0x164c9af858f172f1e8c58b467cb8b05978e1f162d19f3ebc58a8a2c59f459f362cd8b362cd8b060c387060c387061c187061c187061c187061c187554555555555555163eb8b162c58f160102c1e40b05811000000000c3830e07062a88a0f162c7d7463c58b001e1720583c88801e1f00000000187061c0e0c551e9344515ab0000200f803c080000000000000061c187061c1870000380c001555401004400154f9f3e7cd9f367cd9f367cd9f367c9a3264c993264c793264d9931e4c993265c99354187061c187061c187061c187061c1830e1c1830e1d5555555ae93549aaad502c1e402c88160142c0a0aa1600b162cb85002c1c1c0e8381c180c0383061c383061c3aaaa8a20aaaaaab540b079042ca288584c0170b228582c582c58b838381d07038301830061c187061d55545116aaaaac3c7c2c7d785c3e162e059170465c079042d184e8805a316130a1703e85c42c78b1e130b84c560b20168c586c21640b00160e0e81870e0c1c1c1d07038301830380c3870601d555555545126a4c55aeab0b1f5e170b858b878b8160f2058b08b810b160ba07d10b160b0a17100b162c784c16130582c881610b0162c005838381d07060e0f030e1c0e0c060c0e030e1c1807555555551445a8b156baac2e61702c1e402c88160002c58b1701542c0162c5970a005838381d07038301807060c387060c3875555144588ad7555555858b85a385c2e163eb8b2e10b08160f2016142e20162c590b160ba07d10b16130584c1610b0162c16440b001418b060e0f030e2c387838381d07038301830380c3870601d555555545116a2c55aeab5302c1e402c88160142c0a163e0058b0162c5970a005838381d07038301807060c387060c3875555144582a2d55555587c2e163ebc8c7c2c5c0b07910f01e5c085a309d03e85c42c78b1e402c78b07850b826170980b220580b1610b00160e0e0741e061c3830707038301830380c3870601d55555551e9351449a93156baad5000000000000000b1f542c58000000041c1c0e83800003061c383061c3aaaa80002aaaaa81551787cce1e05705802c00011810005c0022020078005c000000000000020e0e81870e0c1c1c1d0700018001c01555555540010006baa8b162c582c0000000000000058f170b858b00000000061c187061c1870000060c387060c387555500000555555005b3162c58b163c58b162c1602c00ae00000b0b8002c0058101002c000000000000000060c387060c387061c187061c18700018001c01555555540010006baa8b162c580000000000b858b162c5c0000000000000c3830e0c3830e00000c1870e0c1870eaaaa00000aaaaaa3c78f1e3d18f163c58f1e000015c1e00f005e040400f00078000f0780000000000000000c3830e0c3830e0c1870e0c1870e00030003802aaaaaaa8002000d755aa0000000000a162c58ba000000000000160e0e0741c00001830e1c1830e1d555400005555556a80000016040400b0000858b8000005c1c1c0e838000c000e0c3830eaaaa000aaaaac5e170b91d500000f01e005700080088002e01003c00000000002e000001070703070781870e0e838000c000e00aaaaaaaa00080035d56a175230880ae00040b093a7aaa858baa00000741c187061d5555518b168d182c5e0080b0582c0004e3c5c9e163c05974e5c05c00a0c3830e0c3830e07060300e0c1870e0c1870eaaaaa2882aaaaaa2c5c00b02000000187061d5478b162eb8b1e2c5c0000040b07911003c00000187061c0e0c551e9344500aaaa0000000001605c00008383a0e0e0741c000155555540001540170b162e163c58b162c16000002c002b80000000000003061c383061c3830e0c3830e0c380002aaaaaaa80002aab162c0000000000020001e04000000030e0c3830e0c38000001c060aaaa008000220aa00132613268c1e4d984c98f0985c2606c361b0d800a0c3830e0c3830e070603060701870e0c03aaaa8a24d498ab5d54187061c187061c187061c187061d55543a0d 24 16777215 10 1023
def hc_67_1 : Nat → Nat := unpackHintV5 0xdfa5a3d9718dd1061bcc153cc4b1d9be9587b61e1eb02d7ca79e24a480c79f6d459825d2934d368bd1df84a5cb7cb1fd75b9be69d6f95e62dd5759c24b2f0b43e5d23846e83265782a12152511401d65eb18753c112dd20b3d7c02ea150000ba 0x878b1f43c58ba2e2c58baa175c58b17542e172a2e858ba162c58b162c58b160e8383a0e0c3830e0c3830e0c3830eaaaaaaaaaaaab0b163e87c3c78f2f0faa163c7af951f42e163e2e2cb8b162c58b0741e0e0e061c187061c187061c187555547a4d55555555462c5a32e5d165cb972e5cb8b264d78f172f858f2e2aa0b162c5af16bc597165c58b059f160b3e0c3830e0c3830e0c3830e0c1870e0c1870e0c3830eaaaaaaa8aaaaaab54000142c58b1742c7d50b1600000000000001070703a0e000c1870e0c1870e00aaaa00000000aa1f2a801e330a162c58ba0002604c980131f544c780000000081f2b8000000000010707001c0600e8383061c383061c380002a80882a80020570055462c5a30000270b162c5939f8f773b9f8f00000000000000061c187061c18700060c387060c3870055550100ae000000aa07c66000f462c5a30264c00000993858b162c9c4c79389c4c7800000000800007cae00000000030003830e0c3830e0c383061c383061c38000c004005555400102b802a8f1e3c780003b9d8b762ddc3c78f87c3c580000000000000030e0c3830e0c38003061c383061c3802aaa8000000002a8f1e3c788c07600f09c4d793264e1e3c7c3e1e3c000981326000000000020003cae000000004c000061c187061c18700380c01830e1c1830e1c00015554044000102b802ad05550b1755550b175550b16008000000e83830e0c3aa80857aa0000a5e2d78ba1e3ea878f000000000780000041c1c0e838003061c383061c3802aaa800000002a80023aa03f44d79327404c980000131e3ea878f0000000010000000795c0000020e0e018001c1d07060c387060c38700005510015500040ae00aa3c58b1e000b0000000058b162c78b87c2c0f800030e0c3830e0c38000030e0c3aaaa80200002a8b162c5c2c58b858f16bc58b162c5970162c0582c2e170058b0162c162c162c160b00060c387060c387061c187061c187038301807505455551441555e2c5af2e0b0b85c0582c160b3e05c2e0b859f162e3e3c5c7e163c1540593260c3830e0c3830e07060300e0c1870e0c1870eaaaa28a0a00aaaa4c993264c9a3263c9b3264c98f2e5cb972e5cb9754f9f3e7c99b264c993265cb972e0c3830e0c3830e0c1870e0c1870e0c3830e0c3830eaaaa93526aad75555a162c58ba6aa1e3e858b858b8f975e1f2ebc1f43e162e85451f42cd8b362e0e0e060c387060c3870741c187061c187061d551515555555561e3e163ebc2e1f0b170b1745d187cbc0fa1f0b1740b462cf9b461b858fa166c59b1742c98b47544e164c593268c9d0b878faa163c9ab164c997164d58383a061c38307070741c187061c187061c1830e1c1830e1d55555555555ae93549aab0b1f5e170b858b878b858b87d0f162e22e2c858b85d0b1642e058b162c58ba162c58ba163ea858b162c58fa1750b858b163c58b162cb8b16ac1c1c0e8383070781870e0c3830e0c3830e0c1870e0c1870eaaaaaaaaaaad745aa2d55162e858baa162e858fa6165c582c58b2162e1f43d1616162e1742c58b162c1830e1c1830e1e0e0e0741c187061c187061d151555555555556162e168e170b858fae2cbc42c590b170fa1e2c85c0b170b170ba162c58b162c58ba1750b858b164e858b162e858faa162c5ab162c597162d5062c18383c0c38b0e1e0e0e0741c187061c187061c1830e1c1830e1d1693555555555556ba2d516aad4d0b162c5d0b17543c7c2c5c3e879f2ebc3e5d790b170fa170a8a6c59b17070703a0e0c1870e0c1870e0c3830e0c3830eaaaa8aa931555549aab0f85c2c7d7918f858b858b87d0f878f07978858b87d0b8162c790b362cd8ba164c5a3a1e3ea858fa1f0b1e2c98f1e4e85c4c593265c593560e0e0741e061c3830707061c187061c187060c387060c387555555547a4d5555ae93549aaa2c58b1600002e162c58b170b1e2e170b16000000000000000c3830e0c3830e000c1870e0c1870e00aaaa00000000aa2c58b160b2b800002c0780bc000000000000170b162c58b858f170b858b0000000164c0580020c3830e0c3830e000070180003061c383061c3aaaa800088015c04055aa0000a162c58ba5e3ea978f00000000000000838381d0700060c387060c38700555500000000055aa000595c002e03c066000000000007c036142c98b4744c7d50b1e00000002c981300060e0e0741c0000e03000060c387060c387555500011002b8080ab5400014bc5af1743c7d50f1600000000000001070703a0e000c1870e0c1870e00aaaa00000000ab54000f2b8008c016017000000000000a264c9d0f1f543c780000000b2604c001838381d070000380c0001830e1c1830e1d55540004400ae0202a8f1e3c780002f978b5e2d7c3c78f87c3c780000000000000030e0c3830e0c38003061c383061c3802aaa8000000002a8f1e3c7800003cae23005803c0000000000009c4c9935e4e1e3c7c3e1e3c0000000593026000830e0c3830e0c380001c060000c1870e0c1870eaaaa0002200570101549d540115c1790c0160b02220000000187061c0e0c01514 24 16777215 10 1023
def hc_67_2 : Nat → Nat := unpackHintV5 0xdec0f9d8f972cddec7c7e97dc2815ab9165baf8e62a9d96d9fb68999c17d900e6d896da884055a7bde0a772d2c7069b16df89c69592862b1aa616c515d690157e1624fa2104b0926451d7b3dedcc327add26aaf41f29e01346f90bfdd20002ff 0x150b85d42ea2750baaa96200b900b217102c187061c1d075516935649ccad7aaa162c58ba05548160f209c1400b220580b1602c58041c1c0e8383061c383061c381c180c03aa935554150510556270b85c8ea95816132e11301e402c82610b0164c59f07c0b1e1b0b85cdd7a158b2264d59051382603c7ab1e54ae0786cd85cbc1c1c0c1c1e061c383a0e07060300e030eac38706ac18303aa9351ea3d55ae28822aa93498aac4e89c8ea95a265e2713263e87d13371389931f43e0e0e060e0f030e1c1d07061c187061c1875526a3d47aab5d55555680994d543ca082e50280f204640ac582b1640f00838381830e1c1830e1c1d0703830180755555555144155878f918faf2387c8d5c1722e05cb80f228264d1951382604d193201e3ca81e288c8119f08f903c00262f0d84e0e0e81870e0c1c1c1d0703830061c38306070601d555555555ae93149a82ab231f5e1f0f958f878f8160f2058f08b8502c58b21e3ca81e2c58f1e4144e0580a0b2205847c058f000982c360b838381d07060e0f030e1c0e0c01870e0c181c18075555555556ba4c526a0aa8b1602c5c5050f29942820583c80162c058b059102c001830e1c1830e1e0e0e0741c0e0c0601d5555555454505561e3e468e470f918fae5cb845c20583c826ac990513826140b162c878f2a078a11f0167c16440b000982c360b06ac18383c0c3ab0e1e0e0e0741c0e0c01870e0c181c180749a4d555555555ae93149a82ab53404ca1e2c2078f82e0f22814046440f0762c1d8b00838381d07060c387060c387038301807555555549aa2a4c415587c3e463ebc8c7c3c7c1707910f01e5c28264d190f1e540fa1f03c078f2640288c881e03cf843c00262f0d84e0e0e0741e061c383070703830061c38306070601d55555551e93556ba4c526a0aa80be163c5cbc7a3162d1978140b8205c2e00b3e02cf82c160b058003061c383061c3830e0c3830e0c381c180c03aaaaaaaaa8a20aaa3162d18000271e9e4f271e0000000000000000000c3830e0c3830e0c1870e0c1870e0000aaaaaaaa0000aa8c58b460000400b0078100005700f80000000007c78b3e7d58b1e00000002cf81f0003e0c3830e0c3830e0000701800c001830e1c1830e1d55541ae000802aaaaad500003b1f54ec780000000000000000041c1c0e8383061c383061c380002aaaaaaa800002ad500001002c01e0400007c0ae00000000043e3f2b878000000501f0003f070703a0e000070180040c387060e0eaaaa0d700040155555680a80220205811110000001070701c18aa35c06aa858b162e800000000000000000000020e0e0741c1830e1c1830e1c000155555554000156a80000801600f02000000ae00f00000091c7e8f800000001407c0007c1c1c0e8380001c06001030e1c18383aaaa835c00100555555058400000030e0c3aaaa0b17002c78000b00160b0220582c1e4000000030e0c3830607060b49aaaa35c0478b163ddc2c58b16ee00000000000000000000000061c187061c187060c387060c38700005555555500000551e2c58f00002005803c080000007815c00000005a3163c58b1e000000f2e00002c780f0001e0c3830e0c3830e000070180003061c383061c3aaaa835c001005555555e2c5af0000000000000f8101003c00000061c187061c1870000018001d555400400400554b85c2e1709a3099309931e1326cc1e2800004c0d84c187061c187061c0e0c01870e0c181c1807555556ba4c526a0aab0fa1f172f0fa1f44c5931743c7d50f1f0aa91f470fa1e5cb972ebc3e2d787c5c1c1c0e83830e0c383061c383061c3830e0c3aaaaaaa2a2aaaac3c7c8c7d791c3e46ce89a3264ea89c4d193264c993a270f1f543c7c5cbd172e172f03e87ab1f4741f3e8c8f8fa1e4cd93264c9935e5cb972f070740c387060e0e0e8383061c383061c3830e0c3830e0c3aaaaaaaaa4d49aab5d5556463ebc3e1f331f0f1f42c593162e89c3c7d50f1e2c58f1f44ea270b163c7c2c5c3e878b1f117162b0b170fa162c8fc0b1e4cd8b164c98b165c59717070703a0e0c1c1e061c383061c383061c3830e0c3830e0c3aaaaaaaaa4d49aab5d555687b0f858b87d0fa162c58ba1e3ea878f8554858b87d0b2e2cb8b760b16ec162e0e0e0741c187061c1830e1c1830e1c187061d555526aab5d151555561e3e468e470f918fae4c9932744ea2713664e858b162e878faa1e3cb9788b972162e1f43d51647e059f858b87d0b266c58b264c58b2e2cb8b06cc18383c0c3b30e1e0e0e0741c1830e1c1830e1c187061c187061d5555555526a4d55aeaaab53172f0fa1f44c5931743c7d50f170aa91f470fa1e5cb972efc3e2df87c5c1c1c0e83830e0c383061c383061c3830e0c3aaaaa4d55262a2aaaaac3e1f231f5e463e1e3e89a3264c9d13878faa1e3e87c3c7931e3c993a1f45cbc3e87c3c783cbc2b1f470fa1f03cf8f21e4cd93264c9935e5cb972f070703a0f030e1c1838383061c383061c3830e0c3830e0c3aaaaaaaa3d26a93526aad75555 24 16777215 10 1023
def hc_67_3 : Nat → Nat := unpackHintV5 0xa4b2f29d5dd590d3238969da85011a8144ef7c85307585c07528176f6d6f675a05631d0f5f30fb59717051261350dc124bc54644b9c33ea186379dc13408e530fcc326f68225d4482328ab199a6415ccf311e4fa11b80b0bf97001fe7f00007f 0x78f1e3c7a31e3c78f1ea9175e172f03c7c5d990f1e3c783c078f2e0f01e3c78f2e170783c1e3c079700b970d86c1e0f01e6c078f0b9b0b85c2e6eb830e0c3830e0c383061c383061c383060701870e07060300eaaad747aa3d51151441555f0b162c5af878b163c1514b82c1e3c078f01e0f0160b0162c058b078b058f00061c187060c387060c387061c187038301807555450551e8a20aa8f162c78f462c58b163c7aa5c160f0783c780f2e00b0583c582c780b1602c586c2e17375c5c2f16bc878f1e3c87cbd983c78f1e3c1e03c7af07806cd85cb830e0c3830e0c383061c383061c381c180c0380c3af0e1c1af060c0eaaad747aa3d14411551551e3c78f1e8c78f1e3c7aa3c78f1e3c78f1e5c78f1e3c78f1e3c78f363c7830e0c3830e0c383061c383061c3830e0c3830e0c3aaab5d1ea8f55555569aaaa555aaaaa2f15155551511f162eaaaa075507061c187061c1875555555555555559588859555c8a8859550511110000555501c1807060300eaaaa282a882ab5555540aa9445114140444402c580b160155540c1870e0c1870e07060300eab2aaa0a82882ab555548ea95aabc5ca2e1411145e95905510515114441410b22000d8ec362baa81d541ea80e0c01870e0c181c180755965955ae282aa282aa2eb8b2aaa22a9556a2ed55eaaa2a2aaa8162e982c597165c5d55503061c383061c3830e0c3830e0c3aacb2aaaaaaaaaaac5eaa85c5eaa2f55555555552b5545eaaf178a8aa166c597165c5bbaa8a885d517165c583061c383061c3d540eaa0f540c3830e0c3830eaaaaab2cb2ab5d5555540aaaaaa2000008002b800000000000003061c383061c3d55500002aaaaaaa80002ad510000410000f0100000000000020e0e0741c0000e03000555500401100055aaa88aa555aaaa3e5d387cba729aaaa2a28d8b362eaaa81830e1c1830e1c187061c1830e0c187559555555555555aaaaaa56aa2f151555578dd45442ea8d8b362e8dd27aaaaa167eaaa8fab165cf9716aeaaa81d541ea8187061c1830e0c187060c387060c38755965955aeaaaaaaaaaa05ebd5555502aa44441709e5c0a2888282802aaa81830e1c1830e1c0e0c060c01875596555aea0a82882ab1baa820223755555115552a170d85c5711170a08828a375570a085910003060701870f5503aa83d501c180c18030ea22aab2cb2ab5c510556175454550b2e2c162c59542eaaa2a2aaa17555ea458b162c1830e1c1830e1eaaa8187061c1830e0c18754545555555555aa858b87d0fa162e87d526cf8b362cfd0b3e2e878aaa7c165cf971655070703a0e0c3830e0c187060c383061c383061c3aaaaaaaaaaa2aaad54a80b22aaaa162e0aa0162e88162c5d72e2cb8b0741c187061d555542a170ba85c9eaaa96200b9044040b061c1870741d55a656bc4e89c8ea9582e132e11301e4506cd913266cf9051382603c79503c566c36413089813266cf83e078f0b9bae170d85cbc1c1c0c1c1e061c383a0e070600c387060c0e0c03aa9351ea3d55ae282aa282ab542000000c3830ec80450001542ea4704a00000000000c0383a0e82d32b5e270b85c8ea95816132e11301e402c821602c5902c2e6eb85c2e42cb94130a17100b262cb83e8858f0b9715978383818383c0c3870741c0e0c0601c1830380c3875526a3d47aab5c5105445556aa56858baaaa82a82162c05902c5902cb8b2e2c58bae0e83830e0c3aaaaad42ea46b0b2e4042d3d5542c5d502e00816441e0741c187061da656b8b49aab0baaa0b83c8a172c5d02aa017164c9806c881e1700b85013a0e0e0741c0e0c060c387060c3870601d555451415105562744e4754a9170bd04c289c404c99707d178878f2e3e0b84cb844c0790172e1b20898133640f0b9b0b85c2e6ebc1c1c0c1c1e061c383a0e0c181c061c381c180c03aa9351ea3d55ae934988aa8a20aad500b295088059030e0c3acd79549a3d 24 16777215 10 1023
def hc_67_4 : Nat → Nat := unpackHintV5 0x7a27823b35779c27dccd9e9d56988db3176d397db380b7b9c858e4be2a5d855472af099da6f4998d521bfc3503fa807a51eb3ae4911c4a4a0d85280647deb2eead5146cc249782f841868f1dcabe0cd08545763c82362140bcd790302b900e3a760001c7 0x2a2d78b162c58b1e2c58b162c5972e02c582c0582c2e170058b0162c160b0582c2e2eb82c160b0162c5930580b162cb90b160b1703c5c42c585c582c583061c383061c3830e0c3830e0c381c180c0383060701870e8b516aad755268a20a88aaaa3162d1970585c2e02aa2f1eee772f1e02c5932600b0582c1602c0580b1602c5830e0c3830e0c381c180c1870e0c1870e0c03a4d55549a28a0a882aaa93662c78b264c7a3162d184c058b264c1604c9972162c165e079788b8f265c059302e0b0b85c058b0164c059b0582c160b0b9b0b82c2e2eb83061c383061c3830e0c3830e0c383060701870e07060300e93526aad75526a88a8a20aa82aa0b162c58b858b170b1e2c160b2602c58170b80b0580b1602c58bc582c580030e0c383061c383061c3830e0c381c180c03aaa82a2a9345105541544162c58b16ac58b162c582c162c0582c0b85c0582c162c162c160b00061c187061c187061c18703830180745aaad745aaa4d144155545ab162c58b163c58b162c58b2e5c058b0580b0585c2e00b1602c582c162f160b160b0585c5d7162c582c058b164c1602e168c162c58b2163c85c0b0d8b058b060c387060c387061c187061c1870383018070187161c383160c181d16a2d55aeaa4d144115545a4c555526cc98f264c98f468c997264c993268d193364c993264d1a3060c387060c387061c187061c187061c187061c18749a93556baa93555555458f1f4aab43d87bf2e2c165df90b170fa1e2c167c582cfc2c5c3e85bf162c1830e1c1830e1e0e0e0741c187061c187061d5555555565555556a2a29556a878f1e17163c6aaa7e1f16fc3e2eaaa8b972e5c1830e1c1830e1eaaa8187061c187061d555555565555556aaaaaaaaaaaaaa1e3e87d52b45ebd5517aa1e3c783cb8f2aaa5f1baaa1e0f3e3c1e3cb972e5eaaa0f03aaa060c387060c387061c187061c18755555556bb2b2aaaaab42c58b175540a8b02c1e3c078f01e402c8058b0162c81601070703061c383061c383a0e07060300eaaa8a0aa2882ab5542c58b174ad17ae2cb90f2078f01e5c05972e3c79503c78f1e3c1e03c7af078140b220580b1602c58006c5e1b17c1c1c0e8383061c383061c381c18030e1c183038300eaaad7656450554505568582caaa55a585b50f07c3c1f43e162e5e0b16bc162c7d0b2e2cb8b838381830e1c1830e1c1d07061c187061c18755555555555555165d7d0b1f43c7d50f2e3c58b1e3c58b1e5c78f1e3e858b162e95aa8597a2f5c7d0f1e3c783cb8f059b165c59716be162e1f42c782c58f058b2e2cb8b060c387060c387838381d07060c387060c387061c187061c18749a4d5555555aecacaaaaaad5555502a2c40f1e03c78441102f160bc591005503061c383061c3d501c180c03aaaa282ac8a20aad555552b4545ebc40f1e03cb85550f2a99943e1e410f8805f111100f3e03c78010bc36555540c1870e0c1870e0706141e0640c03aaab5d959141551415502858ba163ea800000000000000000001830e1c1830e1e0e0e0741c00015555555400015478f1e3c001e0040008100000000000000c3830e0c3830e000c00380c001555401004400156aaa81516a85970162c22220058b0162c8888001830e1c1830e1eaaa80e0c0601d514155564510556aaa2a87d4ccaaaa822878fa1e10ac410bc2e5103c780f2e146eb9511b220162c058b00aa283c0caa81830e1c1830e1c0e0c0601d5455455aecac8a20aad0b0595554aab0b171f2e9c3e5d383e87c8b87943c170fa166c59b17070703061c383061c383a0e0c3830e0c3830eaaaaaaaaaaaaab5542c58b174ac2c5c3e878f1e3c1e5c7946eb8b3743e858f058b1e0b166c59b162cd9b1e3ea858f1e3c78f163c59f1e3d38b1e2c79f7e2cb9f2e2d7d5070703a0e0c1870e0c1870e0c3830e0c187060c383061c383061c3aaab5d9595555555555a162c58baaa45058162f2e0bcb80f2016402c580b1640b00838381830e1c1830e1c1d07038301807555054555144155166d7d03c878faa1e6c780f00783c78f1f42c58b174a85c36171fc0b07903c780f2e0510b3746eb902c058b0162c001830380c387838381d07060c387060c387038301830061d269311555556bb2b22882ab1551554aab547cbaf0f975e55548f058b1e0b17546c59b17540c1870e0c1870f540c3830e0c3830eaaaaaaab2aaaaab555554ad5550f1e3c1e5c795546ebd50f058b1e0b166c59b175555543e1f550faaa7f517a97d55540c1870e0c1870e0c3830e0c3830f50781d2aab5d9595555555555162c5c0b1702c7c3e85c2cb8b058b1642c5c3e87c0b162c162e162c5c2c5b0b162c58b060c387060c387838381d07061c187061c187545455555555551e2c58f3e2c59f1e3c78f162c58b1e3d1e2c79b166c58b859f162e551e29f05973e5c582c78f061c187061c187061c187061c187060c387060c3875555555555455551e3c78f1e8c78f1efc78f54b85c1e0f078f01e5c0dc1b36bc878f21f03c78f1e3c1e03c79b3e0f0179b0d86c1e3c1e3c079b01e3c2e6eb85c36172e0c3830e0c3830e0c1870e0c1870e070600c387060c0e0c03aaab5d1ea8f4505545055478b163c7a3162c58b1e3d52e0b0783c1e3c079700582c160b0162c058b0b9bae170b90b2e2f1703c5c42c783c058f165c1e02c78b1e172e2f2e0c3830e0c3830e0c1870e0c1870e07060300e0c181c061c3aaab5d1ea8f4510544555458b95163c580b162c580b2f1e162e1f43cb82c162c160b2e2cb8b162eb830e0c3830e0c3aaab2a8f1e3c7970b83c1e3f978b5e2dfca80a05c58f1e01b0d83c1e0003c580f160c3830e0c3830e070603061c383061c38300eaaaa3d1450544155 25 33554431 10 1023
def hc_67_5 : Nat → Nat := unpackHintV5 0xd9d5aad5c903c93326c42144bcadddb6718fb18d39ab4991a2d61d9cf57892869c8a1a1b86d0d27b26eb7994647539176ef192644aaa5e318659453b4ebaa348b980457ccf3cee24378d583019dd2971aa21460b1d5cfa0fe75e0bd1050002f4 0x52aad550f2879172f51309c4c687c7d7cac3e2d587c58fa1e5cb972f070703061c383061c383a0e0c3830e0c3830eaaaaaaaaaaaaab550f163c5c00000403c000000000838381d07060c383061c000155555540001555a1e3e878faa1e4c78f163c78f163c98f1e3c7d0f163c5d0f1e3c9932e5c984c9932645cbd45ebd0f1f513099326133f1f5f0fa1e3c78f163cd8f165cb972e0c1870e0c1870f070703a0e0c1870e0c1870e0c3830e0c3830ecb2ab5d5655551e9355555550554aaaaaa88264c098b0a222205e2c178b2200aa060c387060c387aa03830180755505455914415556aaaaa89970264c2228bd7a289c410b89905151540f809930267c8888008161b2060c387060c387aaaa03830a0f0320601d96556baac8a0aa8a0aad552aad4455554d0f1e4c263c995554ec3e2dd87c5972e5cbd55503061c383061c3830e0c3830e0c3b2aad755955555555555499b0264c222aaaaa8a09970264c22002101830e1c1830e1ea80e0caa0383196556b8a2ac8a2aab5555542cb8b058b1655530b162c58b162c5d50baa858b162c1830e1c1830e1eaaa8187061c187061d96556baacaaaa8b5555aa85c4eaa275555555555544cb930993265550faaa2f5c984c993099faaa375542ea8b972e5c1830e1c1830e1eaa075507aa061c187061c18765955aeaaaaab2aaaaaa0aa95543c7d0f1f05c264c098b01e40bc8178b05e2c81e01070703061c383061c383a0e07060300eaaa0a8aa2882aaad0f1f43c7d513265cb8132613082e0f1e545eb8f263c1603c58f260f0a058f1643c78f2809930267c5e440f000782c360b060c387060c387838381d0703830061c38306070601d96556baac8a0aaa3d26282aa8c58b467c58b3e7cf9f3e2c59f169b166c59f362cd8b162aa9f1e2e3f0b1e7c165cf97160b264c187061c187061c187061c187061c1830e1c1830e1d5555555555155556170f00058b0f802c16040b07900000000c3830e07064cad761456858ba163ea8597160b162c858b8fd2f162c36a2c162c59fa175c58ba1742c58b162d555458b055162c58b1f542c58b162c597162ea060c387060c387838381d07061c187060c383061c1830e1c1830e1d96556baacaaaaaaaa2d26aaa210f8782c0178000c3830e80cb0b878b0b80002caebc16002c160402c160f20000000187061c3870e01c1932b5d905058b1702c163e4742e00ab82eb87c8162c5835d4af5c5d0b058b01807838707070741c0e0c060c383061d4156bad755144555162c593040455162c5ab40b2163e858ba163e4742e0b82c160b2e02c5848c162c5e4140b0162c058b1642c5d0bae40b00060c0e030e1c1830e1c1830e1e0e1c1c1c1d07038301830061d169311556595555645105541552aa878fa162e058bcb82f2e03c805900b1602c590b058b00838381830e1c1830e1c1d0703830180755505455144155aa8162c582c58b8160f2000547d50b1e3cf80b3e1070703a0e070601c180c3830eaaaa2a8288aaaad0b1f43c7d50f263c1602c58f260f0a058b1642c58b265c059308160f201e3b0b83c2602c980b266c16542eb90b16506c05e0c1870e0c1870f070703a0e030e1c1830381c180c03b2caad755915547a4c45105569556aa2a2aa8597160b162caaaa160b162c162e9a858b162ea81830e1c1830e1ea8187061c187061d5555555655555556a8585c002161f00582c088880002000061c18703832656bb0a2b55550b87d50b2e2c162c5955542c162c582c5d550baf542c58b170baaa1713aaaaaaaaa8bd42e060c387060c387aaaa061c187061c187a83c0e996556baacaaaaaaaaaad502aa555544442f2e0bcb81115142eb80b1602c580555503061c383061c381c180c03b2aaaca82a0a20aaaa410b899044e2a2aaaaaaaa89970164c2202e442f880164c059b2221e5542eb8003061c383061c3d540c8a0f5407060300ecb2ab5d44555645105569556aa85942c858b8597160b162c1f43e162e160b85942e9162c58b838381830e1c1830e1c1d07061c187061c18755555555555555162d55585c2e162c5c2c58fae2c58b162cb8b162c58fa1f42c58b162c58b162c59f1748b162c5830e0c383061c1830e0e83830e0c3830e0c3a2d556bb2ab2aaaaaab0b87800b0580b1e0b0f802c16040b07900000000c3830e0303832656bb08a2b0b998b1742c58f1f542cb8b058b1642c5c3e878b161b162c582c58b3f0b170b17542eb8b162c58b162c58b162c78b162c98b162c7d0b462c58b162e858f162c58b165c58ba81830e1c1830e1e0e0e0741c187061c187061c1830e1c1830e1d96556baacaaaaaaaa2d26aaaa2e562e163c7970582cd9f058b0a162c58b162c58b0165cd8b061c187995aec8b549ab163c593263d18b168c9970164c0b82c2e170993367c1602c593261303702c58b2363c8dc0f058b0164c059b0582c362c1617175c2e0b0b97060c387060c387061c187061c18703830061c38306070601d26a4d55aeaa4d1415514155 24 16777215 10 1023
def hc_67_6 : Nat → Nat := unpackHintV5 0xc41a2cbd7da7b984feb40d5eac0a01a7592ca095b199bdb6950d2c8e11bf89513083d95e80f0ba78c20c7660986cbe696336625d916953de6d4ec9454901723eae9538c17b2ff6332ec44c2b94cc22225d1f3cb91aa1271056930bad2a0002eb 0x58b162c000000001600057162c58b162c58b163c58b164c58b0000000005802c07603b000011061c187061c1870000060c387060c387000e00c1545aaa4d000000000040154b85c2e1703e1f0f87c36170b9bae8c118f19b30786cd85cb830e0c3830e0c381c180c0380c3870e0c18303aa8970f821352621d06d5100000805c01e0400000000000041c1c0e8380001c06000aaaa008022000ab4aab515155515154d42c162c582c5d5550b162c583061c383061c3d555030e0c3830e0c3aaaaaacaaaaaaaaab55555555555543c7d0faaa1f5551178aabd43eaaa88fc5550f1e3c58f363c5972e5cbd5541e075540c1870e0c1870e0c3830e0c3830ead765655555555555541516aaaaaa82822220058b0162c8888001830e1c1830e1eaaa80e0c0601d5141565545105555aaaaaa88a08b843caaaf4545544143c8287944411f0a22000782c360baaa83c0eaa80e0c01870e0c181c180756bb2b2aa282aa282ab550b171fa3f48ba3742cd8b362d5458a7c7d50b1e7c165cf971655070703a0e0c3830e0c187060c383061c383061c3aaaaaaaaaaa2aaa82a2d555550b2e02c584444050511110003061c383061c3d55501c180c03aa282acaa8a20aaab5555554545544143c8285c45045c2201e3b0b83c8823615557285941b01dd5541e07554030e1c1830381c180c03ab5d95955155114415585d555542c58b17542eaaaaa175548b162c5830e0c3d503aa8187061c187061d555955555555a555a8a8aa165c582c58b2aaaa2a2aaaa458b162c1830e1c1830e1eaaa8187061c187061d5555565555555556a880205911110102c088000000838380607062d79911456aaaaaaaaa2171555510b8a85d555c58b162c5d5550baaaa163e85d550b162c58b2e2c5d55550781d55030e0c3830e0c383061c383061c3ab5d9595555555555555aa81640b2858b85c2c5c02cb9b1707072d79956aa270f95c3e059130165c0b9140b162ca89c0b0162cd9f20363ca81e0b160b20166c2261b81617175c2e0b0b978383a061c38307070741c0e0c01870e0c181c180756ba4d526aa8a0aa8a0aaab551385c2e1f02c8980b1605c805900b1610b20585c5d70582c858b05d100b162cb82c285c0fa2162c2e2c162e0e0e81870e0c1c1c1d07038301807060c0e030e1d5ae8b545aaa2882a22aab5502c2e42a028b1f542c580b162c9802c8816001402e838381d07038301830e1c1830e1c18075555145054415556aa270f99c3c858b05d100b165c16144e07d1171f02c8980b2e05c8058b05900b3611320585cd85c1617175e0e0e81870e0c1c1c1d07060c0e030e1c0e0c0601d5ae93549aaa934988aa8a20aa8b162e170b89d0ba05900b02e402c160b1642c816000c3830f070703a0e07060300eaaa8b5545105541516858ba163eaa805c102c2e400b1602c582c8816000c1870e0c1870f070703a0e07060300ea8a0aa2d5514415556aa270b85c3e059130162c0b900b20162c2163b8162c160b0b8baf42e058b162ca85c0b0162c5900b1e540b0d8b058b8383a061c38307070741c0e0c0601c061c5870e0c583060756ba2d516aa8a208aa8aaab551387cce1f234744c9932f13a91a3a264c99b89d41c1d030e1c1838383a0e0c3830e0c3830ead749aa4d5555555556a96a170faabd52aaad52ad550b2e2c58b162eaaaa17550b162c58b162c58baaaa85d542c58b162c1830e1c1830e1eaaaa075507061c187061c18765955aeab2aaaccaaaaaaa21544000000c3830e80b4c2c2e00110b00160b022220000000187061c0e0c995aec82942c7aaaaaad4ad5554b0b87d5555e2f550b2e2c58b162d5d55542eaa162c58b162c58b17542eaa162c58ba060eaa8387060c387060c387aaaa061c187061c187649aaaab2caad7559555555aaf5545102c0084884408800000000741c0607062aa88a23568c0000080401e040000000000000030e0c3830e0c38003000e0300055550040110005556858ba163ea858b2e5c058b058517ae2c591721544058b164c4058b162c79502ca0162c058b059102c00160b0582c1830e1c1830e1e0e1c1c1c1d0703830061c38306070601d96556baac8a0aaa2d26282aa042c5c2c7d502c22b815eb80000000000003061c1830f070703a0e0000aaab5d6baa80002a8b058aaaaaa2c58b56858ba163e858ba163eaaa162cb971628b1650b1745eb97a2e2c58b162c58b162c162c582c5c2c58b170ba162c58b160c1870e0c1870e0c1870e0c1870f070703a0e0c3830e0c3830e8b49aaaab2caad7559555555 24 16777215 10 1023
def hc_67_7 : Nat → Nat := unpackHintV5 0xe441c3ddc59fd1fef2c65ae9bf69bcb27b3caaa9f4a2e9f0977edb93490d8b59fc83b5e97e0d6a792d38701a456a297c62c1da5ae9f651725e494e0943a9693cb1be35b9be2f95892ae52c2541691e15cb171dbe10e98d0c392c061d87000187 0x5cb85cba3079766172e3cb85c2e1702e5c361b0d86c2e6c2e170b9bae0c3830e0c3830e0c181c061c381c180c03aa9726213512e1b043a0da016550b85d43ca08165017807900b20162c058b2058041c1c0c1870e0c1870e0e8381c180c03c8b55935564d47b225c1608741b0f1f0b1f5e170f858b81645c0b9701e402c805a3167c4610b07c0b1e1b0b85cdd7a4708c5a356548e1182346ac8078f2a0786cd85cbc1c1d030e1c1838383a0e07060300e030eac38706ac18303c8b626a8c9a8f644b82c109a8b2621d06c2c7d785c2e162e1e2e0583c8162c22e00b207c0b1610b0162c160b0b8baf40b162c858f163ca85c0b162c58f20a1702c0362c162e0e0e0741c18383c0c3870383018070187161c383160c181e45a2d9162d616a22c16082d458b10e83458b0162e282859542e0a08160f20058b0162c16440b00062c1830e1c1830e2c387838381d07038301807162d458b59168b644582c10e836162e168e170b858fae2c5972e10b05840b07900b08580b162cf82c81f02c582c1617175c58b164142e05850b8162c58b2163c58f2a1702c362c162c18b060e0f030e2c387838381d070383018070187161c383160c181c58b585ac8b45b222c16082d458b10e8361f0b858faf500b2858b081e3e0583c8a01f002c81f02c780b1602c586c2e17375c838381d07060c387060c3870383018079168f6579355e4d44b82c10e836aa45c2d87c0b07904c2602c81f02c782c161b0b85cdd7a118b4643c79503c993099326130d9b0b97838381d07061c18703830180701875e1c3835e0c181e1f0b858faf231f0b1702c1e443c0797005903e058f0162c2161b0b85cdd7a118b4643c79503e87c0f01e3d79006cd85cbc1c1c0e83c0c387060e0e07060300e030ebc38706bc18303c8b47b30f47a8f1e4d44b82c109a8b2621d068f1e3c78003c000000000008000061c187061c187000000076af47a3d0000000e83478b163cb82c1e0f058b162c0078b1e3cb8fae0b0583c790f8fd70366c58f2163cb970187061c187061c0e0c061c187039f067c168b47a3d12e0b45a22c0e834091d0ba470b85c3c000000000000000000160005700058002c1781000041c1d030e1c1838383a0e0000001c01842d162d85a8b16a2d90000010580741a050b1742c7c8e85c000000000000000000000c1870e0c1870f070703a0e00002c5a8b16b0b458b45b200001d06a3162d18000000000003c080000187061c187061c0000003870060c05a2d5eab40000042601d06802d58b162c58b1e2d58b162c580000000000000000002c000ae0b20580000bc05e00000c1870e0c1870e0c3830e0c3830e0000001c0180b16a2c5a8b168b168b45a0000020b00e8351af470b1f0f1f0b1702c80b80f20160b058b21640b00061c187838381d07038301807168b626a3268f644b82c10e83458b0858b085a3858b170b163eb8b16102caf02c1e402e160b162eb82c1640b00062e838b061c1870741c0e0c0601c58b6168b45a2d91160b043a0d017c2c78b978f462c5a32f00b2e05c058170b802cb80b2e0b3e0b3e0b058003061c383061c3830e0c3830e0c381c180c038b26a2c9a8b45abd44b82c10e83478b162c58f1e8c58b162c78f0000000000000000783c00001e0f0002b8bc05e0000f00079000030e0c3830e0c383061c383061c38000000700602d168f1e8f568f1ea3c9a8000008ec03a0d91c2e1723a170b800000000000000000f85c000787c000ae402f00783c1e0000001070703070781870e0e8380000007006122d564d626a3d7b2b40000047601d068123a1748e170b878000000000000000000041c3870f40c3870e1e0e1e83800042d162d85a8b16a2d900000e874016ac58b162c58f16ac58b162c000000000000000000003870e1c1830e1c3870e1c3870e1c3870000162d458b5162d162d168b400003a1d1e2c58b163c7a3162c58b1e3c0000000000000000000000e1c3870e1c3870e1c1830e1c3870e1c00005a2d1e3d1ead1e3d4793500000e876470b85c8e85c2e00000000000000000f85c000795c020e1e0e1e0f030e1c387a0e1c000245aac9ac4d47af65680000743aac58b5e000000001f0002b800000000070e1c3870e1c38000003062d16af55a00000200743a048e85d2385c2e1e0000000000000000000103060e0703060c1838183a0600010b458b616a2c5a8b6400001a0d005ab162c58b163c5ab162c58b0000000000000000000580003060c183060c183060c183060c1830600002c5a8b16a2c5a2c5a2d1680000341a3c58b162c78f462c58b163c780000000000000000000000c183060c183060c183060c183060c180000b45a3c7a3d5a3c7a8f26a00000d06c8e170b91d0b85c00000000000000001f0b8000f0f80040c1c0c1c0e060c18381c0c1800048b5593589a8f5ecad00000683558b16bc000000003e00057060c183060c18300000000000000181c5a2d5eab400001a0d010058b162c000000000058b162c58b162c58f162c593162c000000003870e1c3870e1c00015418355516aa9340000000550e8b162c5800000000003060c183060c180000b162c58b162c58b1e2c58b262c5800000000306aaaaa2d552680000020d540 24 16777215 10 1023
def hc_67_8 : Nat → Nat := unpackHintV5 0x826e1340054c9f2ab60f5250c76550fb9cf56dbbe4a6d2becd63f35b2f10ba569e3a8a97edd50f0f3a6dd66d28d38689caa83f95541cefb6cd94b8c616acf2e30a115c0560a0237849959f1f5b5c0d05aa059a3a221debd0daed004fa7741025ec000204 0x15c58d7226d500115c00aaaa00000000000202b800000015554000c1870e0c1870e013332004d49a800741b5400457002080800000202b800000055550000000002c780f000aaaa80000e03000060c387060c38799990001098000b1ea2c9a8741a2c5c00b1e002c1602c162c2f102c160f20000000187061c183038305a2d162d04582c78fa1650f1f43e879f2e2c165c8f8b167e1f43e28582cfc2cf8b8f8fa166c59b160c1870e0c1870f030e0c1c0e83830e0c3830e0c38b26a2c9ac8b47b29f45a2d0e83478f1e3c00f80f00200f803c080000000000000061c187061c1870006001c06000a3d1e801f004260001d068f1e3c79f3e3c78f1e6cf9b3e3c78f1e3c79bae6cf9b3e3d18f1e3c78f1e3c78f1e3c7971e3c7b31e0c3830e0c3830e0c3830e0c3830e0c1870e0c1870ea3d1ea7d3e9b478f51e4d43a0d878f918faf2387c8d5c1722e05cb80f228366d1951b83606d19b3e403c79503c566c36406d19b3e1b08d83e078f0b9bae170d85cbc1c1d030e1c1838383a0e070600c387060c0e0c03ca3626a8c9a8f644b8135364c4d821d06c8c7d787c3e563e1e3e0583c8163c22e140b162c878f2a078b163c79051b81600b160b207c0b1e11b0163c2e2eb85c16172f070703a0e0c1c1e061c381c18030e1c183038300f22d1ec8b1eb13512e04d4d9311608741b0f1f23472387c8c7d72e5c22e102c1e41b566cf9051b836140b162c878f2a0782c586c23602d59b3e0b207c0b1e17175c2e0b0b9706ac18383c0c3ab0e1e0e0e0741c0e0c01870e0c181c1807164d626b22d1ec897026a6c988b043a0daa9270f61f05c1e41309941b368c878f2a07932613264c262f361b207c0f1e130985cdd70b86c2e5e0e0e0741c187061c0e0c01870e0c181c180787c3e463ebc8c7c3c7c1707910f0780f1e5cb8506cda321e3ca81f43e0780f1e6cf900bcd86c81f03c780f3610f0b9bae170d85cbc1c1c0e83c0c387060e0e070600c387060c0e0c03ca347b30f47a8f1e4d44b8135364c4d821d06807e163c5c7c7a3162d1978059702e02c0b85c0166c05c02c0582c16000c1870e0c1870e0c3830e0c3830e07060300e2c9a8b26a2d16af512e0b043a0d1e3c78f2e170783c361b0790f80f9b1e3c78f001e3c797079b1e0c3830e0c3830e070601c180c3830ea3d1e89704d83d1e8741a5c2e170b86d186cd86cd8f0d9b660f0d86c361b361b0b9bae170d85cb830e0c3830e0c381c18030e1c183038300eaa25c09a9b2626c10e8361e3e163ebc2e1f0b1702c8b8172e03c805900b1610b20585cdd70b85c859711d100b2e2cb88c285c0fa2163c2e5c565e0e0e81870e0c1c1c1d07038301807060c0e030e1e45b135464d47b225c1608b2621350e836163ebc2e170b170f1702c1e40b161170059102c21602c585c5d70582c858b05d03e8858b05850b88058b163c2e2c162e0e0e0741c18383c0c387038301807060c0e030e1e45a2d9162d616a22c1608b1620b50e836162e168e170b858fae2c5972e10b05840b079010b0162c16440b0b8bae0b0582c285c402c58b2e42c582e81f442c585c582c583160c1c1e061c5870f070703a0e07060300e0c181c061c38b16b0b59168b644582c1162c416a1d06d548b85b0f8160f20984c059102c160b0b9bae170b90b2e23a07d10b1e13164c262c985cb8bcbc1c1c0e83830e0c381c180c0383060701870f0f85c2c7d7918f858b8160f221e03cb802c881602c78b3e0f08585cdd70b85c859711d03e8858f20163c59707850b82e5c5e5e0e0e0741e061c3830707038301807060c0e030e1e45a3d987a3d478f26a25c1608b2621350e8340b90003d18b168c00000000000000000000060007061c187061c1870000098008b45abd400003a0d562c5af000000000f80015c80007810000030e0c3830e0c3800000070e00c180b45abd5680000084c03a0d2e170b85c0f87c3e1f0b9bae170b88cb970b9707972e332e3c2e5c2e0c3830e0c3830e07060300e0c181c061c3aa8970f825c9884d43a0daa82e0f228b8141543c02e2cb9700d9103c2e0170a03741c1c0e8381c180c1870e0c1870e0c03ca347b225c4e4d539353608741b0f1f231f5e470f91b322e8c2f4405d1970b851781f45e21e3cb8f82e45c0b9701e405cb86c80d9b08d903c2e6c2e170b9baf070740c387060e0e0e8383060701870e07060300f28d89aa326a3d92e4c426a25c3608741b231f5e1f0f998f878f2162c1740fa21e3c16145e20162c78f8160f2058f08b802c582c881611b0163c2e6c2e0b0b8baf070703a0e0c1c1e061c383060701870e07060300f22d1ec8b1eb1352e4c426a25c1608741b23a91c0b079002c58b1701543c0162cb970059102c2e0b02e2eb8500ba0e0e0741c0e0c060c387060c3870601e45a3d912e3b26aec9a8b043a0d878f91a391c3e463eb85c28bc405d9972162c1740fa21e3cb9708b840b07900b1611b0166c16440b0b9b0b82c2e2eb83660c1c1e061d9870f070703a0e0c181c061c381c180c038b26b1359168f64b93109a89705821d06d5417079145c0a1e3e0078b02e2c78f00d9103c002807d070703a0e070603061c383061c38300f28d1ec897139354e4d4d821d06d549387b0f22e8c2f40fa2f10f1e3c784c99309932705c1e413098172e1b220784c261736170b85cdd7838381d07061c187060c0e030e1c0e0c0601e1f0f918faf231f0f1e45d185e81f45e21e3c78f201e3cb83c287d05c1e443c1e03c7972e0172e1b220780f1e6cf83c21e1736170b85cdd7838381d0781870e0c1c1c1830380c3870383018079468f661e8f51e3c9a9726213512e1b043a0d462c5a32e5c165c2e17004e3c5c9e163c05972e5c00580b0582c0005c02cd830e1c1870e0c3830e070603061c383061c38300e2d16af512e0b26a2c9a8b043a0d 25 33554431 10 1023
def hc_67_9 : Nat → Nat := unpackHintV5 0xa96a1b46ddfe71ddf4bc33c91c6e11ab46e1becc3fc9da78f350e8f479c3972b57f7a65aea8c2c44d661fbaa13584f0a8e8f7f4d0d18f1ec370386a8e680c64b27ed142f10239a6239d6b06119489e91d0dbf0a10bd60019ff000019 0x4400554000000001555000000c000f5554000c187060c382c0066664005a2d0e83420a00000aaaa8800aa8000000020800ae000115c000080000018001eaa075507aa00018004c0066626b4b3200001d069b366d983c366c7a346170d85c46001b361b366cda3375c361b00060c0e030e1c187061c187061c0e0c060c0187364c426a8d5443608741b54000045700002aaa80000080ae0000000055550003061c383061c3804ccc802f26abc9a800741b54000045720202000202b80000000015554000000141000555540000701800541e0753332000213000a589a8741b5440001040170078100000000000001070703a0e00007018004a35fb20002130000e836aa0587c822b85102c0003e3ea858f0165cf970aa0e0e0741c0e0c060c0187060c387060c387916af644f82c1164d459350e836aa467e3f51b3e8cda3375cdd1f367cd9f8d9b87c8e670f3f173e5e467d1c1c1c0e83830e0c3830e0c3c0c387060e0f28d653e9f4db135464d43a0d02858fa1e3e87d0f4e5c059708160f20059b0a0161102c001830e1c1830e1e0e0e0741c0e0c0601c5935164d645a3d91760b043a0d0000aaaaaa000000000000000000060c387060c387aaaa00004e4d53935999900000e836a88008000000000aaa08002aaa80018000c3830f333200002d168741a05555551010110010004015c808000000000200008ae00000055541e0755400701800004cd2c4d6640426000001d0680005550f1f42c5800000000000000000041c1c0c1870e0c1870e0e83800048b579355e4d47b200001d06d5000b0160000000000faa1607c0020e0e0741c0000187061e45a3d90000168b43a0d02858fa1e3ea82e0002c2e00400b0058410015c00000000002e00115c000000060c387060c387838381d0700380c000005935164d645a3d90109800000741a050b1742c7c3e85c00000000000000000000c1870e0c1870f070703a0e00002c5a8b16b22d16c80000741a3c78f1e000f0020001e040000000000000030e0c3830e0c380001c06000ed768f47a0002130000e83478f1e3c7a3078f078f1e3c0783c078170786c363c79bae0f1e3c1e6c360030e0c3830e0c380c387060c0e07060300ea3d1e83d4793110d821d06d50000555500000000000000000055550003061c383061c3804ccc800b16a2c5a800741b54457000020808000002b81000000555500000000141000555540000701800541e075333200020b000a585a8741b555455555445e2aaaa21f1547eaaa362cd8ba83c0eaaaa8187061c187061e9626b33329f45a2d0e836a800020803e00f0200000001e0000001070703a0e00007018004a3d90001098000741b551f87d0f8f9b878f375e363c79b3e6cfc8e6748e366cfc5cf97998f1e3e0e0e0741c187061c187061e061c3830707947b29f4fa6d89ab326a1d06d550155551111170a0082220a08d80555540eaa0e07060300f3333135a5105821d06d50000555510000000000000457000000aaaa060c387060c387000099995e4d5793500000e8340000585c002e010155555504410015c00000000000000022b8003061c383061c3d500c000f5400002c9a8b26b32130019900000e8340aaaaaa2000008002b80000000000003061c383061c3d55500000b16a2c5acccc80000741b5440001040003c0800000007800000041c1c0e8380001c060012bd1ec800084c0003a0d0dc1b91d546d9c0170d85c1e406c81e3c1f1b1e3cdd700838381830380c3870741c0e0c0601e5364c426a3d910d821d06d50000050b162c5d000000000000000000041c1c0e838003061c383061c38048b45b2002c5a8b16a001d06d5115c00001603c0800000202b800000050b162c5d0000002cb80000b1e02c002838381d070000380c0001830e1c1830e1e45a2d90001058000b16a2c5a8741b5dae93 23 8388607 9 511
def hc_67_10 : Nat → Nat := unpackHintV5 0xd291accd3557c605ccc1a917bd311eb681acb0518ca6fa569cee8394462a8fcd1e88f9b583a9547b9e036f371a662a436390a65e9140519f3d48de3040da013b216e3256332f44c42a414124c1601f515c16c6231175540cf1210501fc000140 0x2858fa1e3e87d0fa0165c201603c80167c059f0161102c001830e1c1830e1e0e0e0741c0e0c0601c5935164d645a3d912e0b043a0d1e2c58f000003e00003c00003e040400f000000187061c187061c0000060007168b47a3d0000098008741a3c78f1e5c2e0f1e0f1e3cbd71e8c1e3c1e3c78f198f00783c001e06c1e0c3830e0c3830e070600c387060c0e0c03a8f47a25c07a8f26208741b544000040170078100000000000001070703a0e000070180048b57b20002130000e836aaa80002a80000000000000000001830e1c1830e1eaaa8000058b5162d6666400003a0d22a80882aaa800078f01e000000000015c80822b800000000001540070185503061c383061c380004c8084c26478f51e4d400003a0d919baa0dc3e660f84605c0b86c8368cdd70dc6c366c83601070700c387060c0e0e8381c180c03ca3426a6c98b221b043a0daabd5555555542e2a2aaf0baaa8aaa2858b162c5d0ba163eaaaa82aaaa858f162c58b2e2c5d5555503aa83830e0c383061c1830e0c1870e0c1870f33330b5a5168b45a2d162d458b50e836aaaaaaaf178a8aaaaa0dd450b3f55785d550b162c5d0b1f554142c7d0ba163eaaa85ab162c597162eaa060eaa8387aaaa061c187060c383061c1830e1c1830e1e16b4b33322d168b45a2c5a8b16a1d06d5115c00001603c080002b8100000007c036000b1f542c580000b2e00002cb80b2e00141c3838383a0e0000701800c001830e1c1830e1e45a2d90001058000b16a2c5a8741b54000000015554000000000000015554000c1870e0c1870e013332009c9aa726a001d06d500115c0080808000ae04000000000555500000000b3e07c002aaaa0000380c006000c1870e0c1870f33320002130003e4d4f9350e836a80000000078faa1e3c0000000000000020e0e0741c001830e1c1830e1c0253a3d9004e4d53935000e836a800008ae400b00780015c080000003e01b00078faa1e3c000000059f03e00141c1c0e8380001c0600300060c387060c38795e8f640004260007c9a9f26a1d06d0b85d42c162e858b170b170fa1e3c78f07971e51bae2cdd0f85c2c58f058b8a362cd8b166cdd0b3f42c78b1f547cf8b3e7cf8b3f541c1c0e8383061c383061c3830e0c383061c1830e0c1870e0c1870f22d1ec8f1ea3c9a9f4fa2d168b3ea2d3a8741b551555555545e2a2aaaaf1ba8a885d542cd8b362e8dd0f1f55542cf9f3e2cf9f3e2cfd55503aa83d5030e0c383061c1830e0c1870e0c1870f33135a5993e9f45a2d167d45a750e836abd55100444440b022000000001d07038305b222c46ad1801f000803600f0200000000000000187061c187061c0000e0300046afd56800084c0003a0d162c58b162c58b3e7cf9f162c5d7162c58b162c58b162c58b551628b1e2e170b162c162c593160b911458b162d38b162d38b162cf8b162cf8b162c58b55061c187061c187061c187060c383061c1830e1c1830e1c1830e1c1830e1d545aaaaa8b5545a8b49aaaaaa3467cfa33e7cda3375cd9b3e8cd9f367cd9f367cd9b363cfb3667c79f3e5cf973e7d1a3061c187061c187061c187060c383061c1830e1c1830e1d1aaa7d3e9b4f93526a1d06c2eaa2285c3eaaf555410110b87d5505c160b22222161405142eaae44154410b00060c0e030e1eaaaa075507038301830061c58b105accccc2d6944582c10e83617505557aae02c0fd5cab9115055e8af5ca8162c0601eaf55eaa038301830e0c1871622d5dabb3222c168b43a0d20aa20a163ea85d5551142e1f555578b85005c160b15d10b2208282859450baab9100503075541c383060701870f540eaa038301830061e16b4a2c5882d6985b3222c1608741b55eaa8a205801111102c08800000000741c3807060b6504588d5a30000020001e040000000000000030e0c3830e0c38070000e0300046afd568200084c0003a0d02162e163eaf55e05845702bd7000000ae15c00001870e0c387838381d07000016a2d6ae8bae8b6400003a0d016000fabd5780002b8570001605702bd71742c00020e0e0741c001830e0c18700aba2eba2d900168b43a0d000585c00160002e858ba163c8001f23a17100170000800ae0000000b000022b800003061c383061c380c000f070703a0e000300162d458b505800c2d162d16c80000741b47c58f1755400000000000000000000001070703061c383061c383a0e00012bd564d559351ec80000741b550f163c5c00000403c000000000838381d07061c3830e1c000257a3d91ea3d400003a0d03e4000faa01e000003c7d0f163c5d000170000000ae404000045700000000018001e0e0e0741c1830e1c1830e1c0006001300195e8f6478f51e4d400003a0daaaaaa0000002000ae0000004000001100555503061c383061c38000c026665d935764d400003a0d 24 16777215 10 1023
def hc_67_11 : Nat → Nat := unpackHintV5 0xce85bdc701e1bee607b6a211af5dd1a9bd68a4854e9cddea96719b8d364f89010d7f267776fe0a6e223769d91265252d5f118556ce114fddbc47b60a3e6a533a0d1735b1172f9d852a315b2704cb21157c1959ef12c1a60badc507a1030001e8 0x2aa0585c82165102cf8170b942cd801f1f542c780b2e5cb855070703a0e0706030600c383061c383061c3c8b57b225c1608b26a2c9a8741b232f551787cce1e5d197ae5cbc5cb972e5e8bc7d1d172e5cdc5e8f972e5cbc1c1d030e1c1838383a0e0c3830e0c3830f28d89a9726ac974ba7d43a0daabd5555555e165110b20aa0a1742c7955150b1e4154405111105042c00160b0582e83d55503aa8381c18030e1c183038300f2cb330b5a511602d458b11608741b55555557a2e5c2882aaf0b288a163c82a88285d0b1e5544505042c888800160b0582e8183aaa0e1eaaa80e0c01870e0c181c180785ad2cccc88b016a2c588b043a0da170ba858b162e8022b80000000005c002002200000000000000020e0e0741c1830e1c1830e1c0000e030009168f6478f51e4d400047e0001d06d555555004570000000002081e400000000000000000005540eaa0f5400007018004cc4d696640004760001d06a3162d1800001f000000002e040400f000000187061c187061c0000060007168b57aed0000098008741a2c58b160b2b80002a8b16a2c78b85c2c5800002c1f80ec001100000000000000061c187061c18700060c387060c38700380c001545aaa000000080002aa3465d197ae5cb88cb85c2e5cb8f19b30788d18230000d81b0187061c187061c0e0c01870e0c181c180746aa25c09a931043a0d85d55550b87d55eaaaa170faa88aaaaaa17557aa85d15540b162c58b162c5d55545442c58b162c1830e1c1830e1eaaaa075507061c187061c187162d458b5999985ad28b45a2d168741a0555557aae4115c0af5c00000ae15c0000061c187aaaa000016a2d6666400003a0da163e82aa858faa175555550b87d5555e8b978aa2aa85d55eaa2a2162c58b162c58b17542eaa162c58ba060eaa8387060c387060c387aaaa061c187061c18785ad28b16a2c5acccc8b45a2d168741a8c58b465c16170b80b3e0b0582cf8170b8002c5c7c78b8fc2c780b8b970165cb830e0c3830e0c381c180c0383061c383061c38b45abd7689705822c9a8b26a1d06972e5d9971e5cb971e8d1972e5cb972e5cba32f5cb972e5cb9b2e5cb972e8cf9f3e7cb972e5c1830e1c1830e1c187061c187061c187061c187061cb9352e4d51aa974ba7d43a0daa22b800005c07810000000000001070703a0e000070180048b57b20002130000e836a80000008200000036040400f0000020e0e0741c000600030003c8b57b2001f00098008741b55171197465eb97222e5e1e239983c4623220003606c47070703a0e070600c387060c0e0c03ca35912e04d51931043a0d163c7d0b2878fa1f43cb97165445c58b2f0fa1e2c167c582cfc2c5c3e8597165c583061c383061c3c1c1c0e83830e0c3830e0c38b26a2c9ac8b47b25d2e8b45a1d068b162e058b0163e1f42ea017040b079002c580b160b1642c816000c1870e0c1870f070703a0e07060300e2c5a8b16b22d16c88b05821d068f162c7970583c1e02c160f160b1e05c2e0b859f162e1e3c5c0002e2e5c058f1e0c3830e0c3830e07060300e0c1870e0c1870e2d168f47a25c1608b26a2c9a8741a3c78f1e3d18f1e3c78f1e3c7972e5cb8f1e5eb8f1e3c78f1e5cf9f1e3c78f1e3c78f363c7972e5cb830e0c3830e0c383061c383061c3830e0c3830e0c3a8f47a3c7a8f26a5d2e9f50e8340aaaaaaaa08b841044047c28888802a0f03aaaaa038301807a589acccc89705821d06d5000000040000007c080801e0000041c1c0e83800000c000f22d1ec800004c0043a0daa82e0f1e5ebc5c1f2319c238b97078f0881e001b03633838381d0703830061c38306070601e51ec897026acc98821d06d55555155545eaa87c54555545447cb8b2e2e83d55503aa83830e0c3830e0c3cb2ccc4d694ba5d168b43a0d8365503e20b8003c8838380e0c0741c0e0c944d83d912e0741b0ba82a2a85970162c222208a0aa28595572200060c387060c387aaaa038301830061c58b5162d6985b3222c1608741b5502c1e410b3e503e8858f0b85c2e17a167c5d0050b1e02c7971e1541c1c0e8381c180c181c061c383061c383061c3c8b47b225c167c45164d459350e836175455550b2e2c162c5955555542eaaf542c58b160c1870e0c1870f55540c3830e0c187060c38b16a2c5ad30b6645a2d168b43a0daa858b87c8fa162c58ba16550b162c162c5931642c5c2e858b162c5ab070703a0e0c3830e0c1870e0c1870e0c3830eaa2d555545a8b556baad545cbc3e87c7e1f43cb8f2e5e0e0e0741c187061c187061e51ec974ba7d43a0d8bd1791d545d9c5cbc3c78f1e3e2e3c797af1f8b9737178b972e3e87972e5cbc1c1c0c1c1e061c383a0e0c3830e0c3830f29726b1351ec974ba7d43a0d 24 16777215 10 1023
def hc_67_12 : Nat → Nat := unpackHintV5 0x4a7917846c22ed16f1bc477b265495803329ea458fc50418b5b52822522eb8643988f8001cc 0x1544000104017007810000000000001070703a0e00007018004a347b20002130000e836aa162e1f43e858ba1f542cd9f166c59fa166c5943caa163cf82cb9f2e2caa0e0e0741c187061c1830e0c187060c387060c3879168f64fa7d167d168b26a2c9a8741b0f1f231f5e470f91b391a3a2e8d197918fa1f234746d1a337231f43e0e0e81870e0c1c1c1d07061c187061c187946c4d519351ecaa8741b540104004040404000000000000555500001c0600133320002130000e836aaaaaaaaaaa8d8b362e2aaaaa2a2a2f10faaaa8187061c187061ea0f03a99993e9f45a2da589a8741b231f5e1f0f998f878fa1f43c78fa2e3c7d0fa1e3c7d1b1e3e0e0e0741c18383c0c387061c187061c187947b23c7ac4d5543a0daa000020801e00f02000000000000020e0e0741c0000e03000947b208002130000e836aa162e1f43e167c5c3ea859b3e2cd8b3f02c78b1f43caa163cf82cb9f2e2caa0e0e0741c187061c187061c1830e1c1830e1e45a3d93e9f45a8b5164d459350e8361e3e468e470f918faeccbcce2ece87d0f666e671b6743e8783660c1c1e061d9870f070703a0e0c3830e0c3830ecc9ac4d651ecaa8741b544000f00200b803c080000000000000838381d070006001c0600128d1ec800084c0003a0daa858b87d0fa162e878fa163cd8b3e6cf8ba166c5943c7d40b1e7c165cf971655070703a0e0c3830e0c187060c383061c383061c3c8b47b27d3e8b45a2c9a8b26a1d06d549387b0f91a387d0f264c99391a387d0f264c993838381d07061c187061c187061c18787c3e463ebc8c7c3c7c8d1c3e87c3c78f2f0f91a387d0f878f1e6e1f070703a0f030e1c18383830e0c3830e0c3ca347b30f47a8f1e4d5543a0d 23 8388607 10 1023
def nh_67 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_67_12 (Nat.sub p 384)) (hc_67_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (hc_67_10 (Nat.sub p 320)) (hc_67_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (hc_67_8 (Nat.sub p 256)) (hc_67_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_67_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_67_5 (Nat.sub p 160)) (hc_67_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_67_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_67_2 (Nat.sub p 64)) (hc_67_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_67_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_67 : Nat → Nat × Nat := unpackForestF 0xc5359c525900c5fc3b49c3a4900c5bc2361c226100c57c0349c0249c004400c53bf25900b5fbbd6bbbd67bbb5fbbb57bba39bb83700b5bb945bba370b9457b926100b57b7b4eb7a3900b53b5c66b6266b5a4900b4fb4366b423900b4bb056ab025cb2266b0251b0a57b0827b025000b47aeb66aea3900b43acb59ad464acb4f00a5fa656ba6567a646baa244a645ba9244a6453a625fa6257a756ba624ea602700a5b9ec5ba4a709ec57a3d6b9eb61a2360a22709eb57a0c7ca0b709eb4f9f5709f2509eb4700a579da449c4539c24e9c23e00a53974669a4649a2689736f98c7c98a709736797b669734900a4f9624494c6b94a6694a4e00a4b91d6a9357091b679236691b5100a4790a448cc6b8f03f8f0378ea448cc638db638ca668ca4e00a4388d6f88d6b88d678a05488d6388b6688a5200a3f84d6f84d6b84d678605484d6384a6684a3e00a3b83c687fd6f7fd6b824707fd6780c58808547fd637fc6a00a377ea646f56f6f56b7d27c6f5677ba547b8546f5636f35e6f3526f26f792666f26a6f2677745d774556f2666f25f6f25773a6e73a6673a5e73a566f12a7116e711667115e711566f1266f9286f9246f02700a3364b596dc6464b4f6cb6464b4364a596b46464a4f69274692646924e64a436825264a3f64a3b66c6864a37652746526464a330085f4cc5b6337c62b714cc5761d6b4cb614cb5b603604cb575ec7c5eb704cb4f5db7c4cb4b5bd705ba5c5ba504cb475ab7c4cb434ca615924e4ca5b5837c57371572604ca5755c7c55a704ca4f5427c5424e4ca4b535704ca475127c512645124e4ca43502524ca3f4ca3b4ec704ca374d27c4d2644ca33008573e4664b4643e36f4a3543e36b4947c3e367483543e363473663e349464643e26f452543e26b4447c3e267432543e263422663e2493e23f3e23b3fd763fc583e2373ea543e2330084f2e56a3c6783c36c2e36b3b24f3ad702e36739b662e35138a6c2e26b37b4f375702e267362662e25134e7a34b762e23f33d70332762e23b30e7a30c7a3136b30c602e2372fd702ea762ea6c2e233008472d36423d6f23d6b2bb7c23d672ab5423d6323b662924423a6b2824423a6326a7626a4423a5b25b7c24a7624a4423a5323a390083f22c681856f1856b214701856720458185631ed691ed611846a1dc681826f1cc70182671bc581825f1a67a1a4601825718b5e18a661824100837172640dd6f0dd6b15a7c0dd6714a540dd6313a440dc6b12a440dc6311a440dc5b10a440dc530fb4b0da660e56b0e5630da4e0082f0c3680c2680156f0156b0ab700156709b580156308b680146f07b700146706b580145f053600526001457044570136a0325401d6301c6e01a6601342008270003f 9 11
def ch_67 : Nat → Bool := dagCheckNodeV5 fullMask g_67 ep_67 5 31 bds_67 396 (dagTraceF fullMask rootStock 11 f_67) cur_67 nh_67
set_option maxHeartbeats 0 in
theorem rc_67 : dagCheckRootsV5 fullMask g_67 ep_67 5 31 396 bds_67 (dagTraceF fullMask rootStock 11 f_67) (cur_67 0) (nh_67 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_0 : treeBlockF 0 32 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_1 : treeBlockF 32 64 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_2 : treeBlockF 64 96 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_3 : treeBlockF 96 128 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_4 : treeBlockF 128 160 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_5 : treeBlockF 160 192 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_6 : treeBlockF 192 224 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_7 : treeBlockF 224 256 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_8 : treeBlockF 256 288 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_9 : treeBlockF 288 320 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_10 : treeBlockF 320 352 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_11 : treeBlockF 352 384 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_12 : treeBlockF 384 396 ch_67 = true := by decide +kernel
theorem nj_67_1 : ∀ i, 0 ≤ i → i < 64 → ch_67 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_67_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_67_1 h1 h2)
theorem nj_67_2 : ∀ i, 0 ≤ i → i < 96 → ch_67 i = true := block_join nj_67_1 (fun _ h1 h2 => treeBlockF_at nb_67_2 h1 h2)
theorem nj_67_3 : ∀ i, 0 ≤ i → i < 128 → ch_67 i = true := block_join nj_67_2 (fun _ h1 h2 => treeBlockF_at nb_67_3 h1 h2)
theorem nj_67_4 : ∀ i, 0 ≤ i → i < 160 → ch_67 i = true := block_join nj_67_3 (fun _ h1 h2 => treeBlockF_at nb_67_4 h1 h2)
theorem nj_67_5 : ∀ i, 0 ≤ i → i < 192 → ch_67 i = true := block_join nj_67_4 (fun _ h1 h2 => treeBlockF_at nb_67_5 h1 h2)
theorem nj_67_6 : ∀ i, 0 ≤ i → i < 224 → ch_67 i = true := block_join nj_67_5 (fun _ h1 h2 => treeBlockF_at nb_67_6 h1 h2)
theorem nj_67_7 : ∀ i, 0 ≤ i → i < 256 → ch_67 i = true := block_join nj_67_6 (fun _ h1 h2 => treeBlockF_at nb_67_7 h1 h2)
theorem nj_67_8 : ∀ i, 0 ≤ i → i < 288 → ch_67 i = true := block_join nj_67_7 (fun _ h1 h2 => treeBlockF_at nb_67_8 h1 h2)
theorem nj_67_9 : ∀ i, 0 ≤ i → i < 320 → ch_67 i = true := block_join nj_67_8 (fun _ h1 h2 => treeBlockF_at nb_67_9 h1 h2)
theorem nj_67_10 : ∀ i, 0 ≤ i → i < 352 → ch_67 i = true := block_join nj_67_9 (fun _ h1 h2 => treeBlockF_at nb_67_10 h1 h2)
theorem nj_67_11 : ∀ i, 0 ≤ i → i < 384 → ch_67 i = true := block_join nj_67_10 (fun _ h1 h2 => treeBlockF_at nb_67_11 h1 h2)
theorem nj_67_12 : ∀ i, 0 ≤ i → i < 396 → ch_67 i = true := block_join nj_67_11 (fun _ h1 h2 => treeBlockF_at nb_67_12 h1 h2)
theorem nc_67 : ∀ i, 0 ≤ i → i < 396 → ch_67 i = true := nj_67_12
theorem lb_67 : LowerBin fullMask rootStock g_67 12 :=
  lowerDagV5 (kn_cons lb_50 (kn_cons lb_63 (kn_cons lb_54 (kn_cons lb_66 (kn_cons lb_65 (kn_cons lb_2 (kn_cons lb_60 (kn_cons lb_64 (kn_cons lb_62 (kn_cons lb_61 (kn_cons lb_41 (kn_cons lb_58 (kn_cons lb_25 (kn_cons lb_29 (kn_cons lb_10 (kn_cons lb_59 (kn_cons lb_52 (kn_cons lb_1 (kn_cons lb_3 (kn_cons lb_57 (kn_cons lb_48 (kn_cons lb_13 (kn_cons lb_16 (kn_cons lb_56 (kn_nil))))))))))))))))))))))))) rc_67 nc_67 (by decide +kernel)

def wg : List Gate := [⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.and, [11, 12]⟩, ⟨GateOp.or, [9, 15]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.and, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276677320 * 2 ^ 32 + 4206930048) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276677320 * 2 ^ 32 + 4206930048)) (13 - 1) := by
  rw [show canon fullMask (4276677320 * 2 ^ 32 + 4206930048) = g_67 by decide]
  exact lb_67

end PEqualNP.Outside.L_meta_48861

theorem PEqualNP.Outside.L_meta_48861 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677320 * 2 ^ 32 + 4206930048) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677320 * 2 ^ 32 + 4206930048) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_48861.table2_from_lowerBin (4276677320 * 2 ^ 32 + 4206930048) 13 PEqualNP.Outside.L_meta_48861.root_lb PEqualNP.Outside.L_meta_48861.wg 18 rfl PEqualNP.Outside.L_meta_48861.wfits PEqualNP.Outside.L_meta_48861.weval
