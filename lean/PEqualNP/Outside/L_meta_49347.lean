import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49347

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

def m_0 : Nat := 0x5050505000000000
def s_0 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_0 : Nat := 0x10105000000000
def ep_0 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
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

def m_1 : Nat := 0x3030303000000000
def s_1 : List Nat := [0x1010101000000000, 0x30003000000000, 0x303000000000]
def g_1 : Nat := 0x10103000000000
def ep_1 : Nat := 0x1020000000000010002000000000000000000000000000000000000000000010100000000000
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

def m_2 : Nat := 0xf000f000000000
def s_2 : List Nat := [0x50005000000000, 0x30003000000000, 0xf000000000]
def g_2 : Nat := 0x10007000000000
def ep_2 : Nat := 0x60000000000000000000000000000000000000000000100020000000000010004000000000
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

def m_3 : Nat := 0x5500550000000000
def s_3 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_3 : Nat := 0x100150000000000
def ep_3 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
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

def m_4 : Nat := 0x3300330000000000
def s_4 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_4 : Nat := 0x100130000000000
def ep_4 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
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

def m_5 : Nat := 0xf000f0000000000
def s_5 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_5 : Nat := 0x100070000000000
def ep_5 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
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

def m_6 : Nat := 0xcccc0000
def s_6 : List Nat := [0x44440000, 0xc0c0000, 0xcc0000]
def g_6 : Nat := 0x44c0000
def ep_6 : Nat := 0x480000000000000408000000000000000000000000000004400000
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

def m_7 : Nat := 0x2222222200000000
def s_7 : List Nat := [0x202020200000000, 0x22002200000000, 0x222200000000]
def g_7 : Nat := 0x2022200000000
def ep_7 : Nat := 0x220000000000002002000000000000202000000000000000000000000000000000000000000
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

def m_8 : Nat := 0x4444444400000000
def s_8 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_8 : Nat := 0x4044400000000
def ep_8 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_9 : Nat := 0x3333000000000000
def s_9 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_9 : Nat := 0x113000000000000
def ep_9 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
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

def m_10 : Nat := 0x5555000000000000
def s_10 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_10 : Nat := 0x115000000000000
def ep_10 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
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

def m_11 : Nat := 0xa0a00000a0a0
def s_11 : List Nat := [0x202000002020, 0xa0000000a0, 0xa0a0]
def g_11 : Nat := 0x20000020a0
def ep_11 : Nat := 0x208000000000000000000000002000000080000000000000000000000020000020000000000000000000
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

def m_12 : Nat := 0xff000000000000
def s_12 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_12 : Nat := 0x17000000000000
def ep_12 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_13 : Nat := 0xc000c000c000c0
def s_13 : List Nat := [0x40004000400040, 0xc0000000c0, 0xc000c0]
def g_13 : Nat := 0x40004000c0
def ep_13 : Nat := 0x40008000000040000000800000000000000000000000000000000000000000000000000000004000400000
def bds_13 : List (Nat × List Nat × Nat × Nat) := []
def cur_13 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_13 : Nat → Nat := fun _ => 0
def f_13 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_13 : Nat → Bool := dagCheckNodeV5 m_13 g_13 ep_13 1 1 bds_13 1 (dagTraceF m_13 s_13 3 f_13) cur_13 nh_13
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsV5 m_13 g_13 ep_13 1 1 1 bds_13 (dagTraceF m_13 s_13 3 f_13) (cur_13 0) (nh_13 0) s_13 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_13 : treeBlockF 0 1 ch_13 = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 1 → ch_13 i = true := fun _ h1 h2 => treeBlockF_at nb_13 h1 h2
theorem lb_13 : LowerBin m_13 s_13 g_13 4 :=
  lowerDagV5 (kn_nil) rc_13 nc_13 (by decide +kernel)

def m_14 : Nat := 0xf0f000000000000
def s_14 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_14 : Nat := 0x107000000000000
def ep_14 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
def bds_14 : List (Nat × List Nat × Nat × Nat) := []
def cur_14 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_14 : Nat → Nat := fun _ => 0
def f_14 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_14 : Nat → Bool := dagCheckNodeV5 m_14 g_14 ep_14 1 1 bds_14 1 (dagTraceF m_14 s_14 3 f_14) cur_14 nh_14
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsV5 m_14 g_14 ep_14 1 1 1 bds_14 (dagTraceF m_14 s_14 3 f_14) (cur_14 0) (nh_14 0) s_14 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14 : treeBlockF 0 1 ch_14 = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 1 → ch_14 i = true := fun _ h1 h2 => treeBlockF_at nb_14 h1 h2
theorem lb_14 : LowerBin m_14 s_14 g_14 4 :=
  lowerDagV5 (kn_nil) rc_14 nc_14 (by decide +kernel)

def m_15 : Nat := 0x2200220022002200
def s_15 : List Nat := [0x200020002000200, 0x220000002200, 0x22002200]
def g_15 : Nat := 0x20002002200
def ep_15 : Nat := 0x200200000000200000020000000000000000000000002000200000000000000000000000000000000000000
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
def cur_15 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_15 : Nat → Nat := fun _ => 0
def f_15 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_15 : Nat → Bool := dagCheckNodeV5 m_15 g_15 ep_15 1 1 bds_15 1 (dagTraceF m_15 s_15 3 f_15) cur_15 nh_15
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV5 m_15 g_15 ep_15 1 1 1 bds_15 (dagTraceF m_15 s_15 3 f_15) (cur_15 0) (nh_15 0) s_15 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15 : treeBlockF 0 1 ch_15 = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 1 → ch_15 i = true := fun _ h1 h2 => treeBlockF_at nb_15 h1 h2
theorem lb_15 : LowerBin m_15 s_15 g_15 4 :=
  lowerDagV5 (kn_nil) rc_15 nc_15 (by decide +kernel)

def m_16 : Nat := 0xf0000000f000000
def s_16 : List Nat := [0x500000005000000, 0x300000003000000, 0xf000000]
def g_16 : Nat := 0x100000007000000
def ep_16 : Nat := 0x600000000000000000000000000000000000000000000000000000001000000020000000100000004000000
def bds_16 : List (Nat × List Nat × Nat × Nat) := []
def cur_16 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_16 : Nat → Nat := fun _ => 0
def f_16 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_16 : Nat → Bool := dagCheckNodeV5 m_16 g_16 ep_16 1 1 bds_16 1 (dagTraceF m_16 s_16 3 f_16) cur_16 nh_16
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV5 m_16 g_16 ep_16 1 1 1 bds_16 (dagTraceF m_16 s_16 3 f_16) (cur_16 0) (nh_16 0) s_16 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16 : treeBlockF 0 1 ch_16 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 1 → ch_16 i = true := fun _ h1 h2 => treeBlockF_at nb_16 h1 h2
theorem lb_16 : LowerBin m_16 s_16 g_16 4 :=
  lowerDagV5 (kn_nil) rc_16 nc_16 (by decide +kernel)

def m_17 : Nat := 0xf0f000000000
def s_17 : List Nat := [0x505000000000, 0x303000000000, 0xf000000000]
def g_17 : Nat := 0x107000000000
def ep_17 : Nat := 0x6000000000000000000000000000001020000000000000104000000000
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
def cur_17 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_17 : Nat → Nat := fun _ => 0
def f_17 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_17 : Nat → Bool := dagCheckNodeV5 m_17 g_17 ep_17 1 1 bds_17 1 (dagTraceF m_17 s_17 3 f_17) cur_17 nh_17
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV5 m_17 g_17 ep_17 1 1 1 bds_17 (dagTraceF m_17 s_17 3 f_17) (cur_17 0) (nh_17 0) s_17 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17 : treeBlockF 0 1 ch_17 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 1 → ch_17 i = true := fun _ h1 h2 => treeBlockF_at nb_17 h1 h2
theorem lb_17 : LowerBin m_17 s_17 g_17 4 :=
  lowerDagV5 (kn_nil) rc_17 nc_17 (by decide +kernel)

def m_18 : Nat := 0xff0000000000
def s_18 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_18 : Nat := 0x170000000000
def ep_18 : Nat := 0x6000000000000001200000000000000140000000000
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
def cur_18 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_18 : Nat → Nat := fun _ => 0
def f_18 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_18 : Nat → Bool := dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 1 (dagTraceF m_18 s_18 3 f_18) cur_18 nh_18
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 1 bds_18 (dagTraceF m_18 s_18 3 f_18) (cur_18 0) (nh_18 0) s_18 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18 : treeBlockF 0 1 ch_18 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 1 → ch_18 i = true := fun _ h1 h2 => treeBlockF_at nb_18 h1 h2
theorem lb_18 : LowerBin m_18 s_18 g_18 4 :=
  lowerDagV5 (kn_nil) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0x4444000044440000
def s_19 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_19 : Nat := 0x4000004440000
def ep_19 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
def cur_19 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_19 : Nat → Nat := fun _ => 0
def f_19 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_19 : Nat → Bool := dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 1 (dagTraceF m_19 s_19 3 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 1 bds_19 (dagTraceF m_19 s_19 3 f_19) (cur_19 0) (nh_19 0) s_19 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19 : treeBlockF 0 1 ch_19 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 1 → ch_19 i = true := fun _ h1 h2 => treeBlockF_at nb_19 h1 h2
theorem lb_19 : LowerBin m_19 s_19 g_19 4 :=
  lowerDagV5 (kn_nil) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0xa0a00000a0a0000
def s_20 : List Nat := [0x202000002020000, 0xa0000000a0000, 0xa0a0000]
def g_20 : Nat := 0x20000020a0000
def ep_20 : Nat := 0x208000000000000000000000002000000080000000000000000000000020000020000000000000000000000
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
def cur_20 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_20 : Nat → Nat := fun _ => 0
def f_20 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_20 : Nat → Bool := dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 1 (dagTraceF m_20 s_20 3 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 1 bds_20 (dagTraceF m_20 s_20 3 f_20) (cur_20 0) (nh_20 0) s_20 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20 : treeBlockF 0 1 ch_20 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 1 → ch_20 i = true := fun _ h1 h2 => treeBlockF_at nb_20 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 4 :=
  lowerDagV5 (kn_nil) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xc0c00000c0c0000
def s_21 : List Nat := [0x404000004040000, 0xc0000000c0000, 0xc0c0000]
def g_21 : Nat := 0x40000040c0000
def ep_21 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000000
def bds_21 : List (Nat × List Nat × Nat × Nat) := []
def cur_21 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_21 : Nat → Nat := fun _ => 0
def f_21 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_21 : Nat → Bool := dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 1 (dagTraceF m_21 s_21 3 f_21) cur_21 nh_21
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 1 bds_21 (dagTraceF m_21 s_21 3 f_21) (cur_21 0) (nh_21 0) s_21 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21 : treeBlockF 0 1 ch_21 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 1 → ch_21 i = true := fun _ h1 h2 => treeBlockF_at nb_21 h1 h2
theorem lb_21 : LowerBin m_21 s_21 g_21 4 :=
  lowerDagV5 (kn_nil) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xcc000000cc0000
def s_22 : List Nat := [0x44000000440000, 0xc0000000c0000, 0xcc0000]
def g_22 : Nat := 0x40000004c0000
def ep_22 : Nat := 0x48000000000000000000000000000000000000000400000008000000000000000000000004000000400000
def bds_22 : List (Nat × List Nat × Nat × Nat) := []
def cur_22 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_22 : Nat → Nat := fun _ => 0
def f_22 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_22 : Nat → Bool := dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 1 (dagTraceF m_22 s_22 3 f_22) cur_22 nh_22
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 1 bds_22 (dagTraceF m_22 s_22 3 f_22) (cur_22 0) (nh_22 0) s_22 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22 : treeBlockF 0 1 ch_22 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 1 → ch_22 i = true := fun _ h1 h2 => treeBlockF_at nb_22 h1 h2
theorem lb_22 : LowerBin m_22 s_22 g_22 4 :=
  lowerDagV5 (kn_nil) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0xffff0000000000
def s_23 : List Nat := [0x55550000000000, 0x33330000000000, 0xf0f0000000000, 0xff0000000000]
def g_23 : Nat := 0x17170000000000
def ep_23 : Nat := 0x606000000000000121200000000000014140000000000
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_23 : Nat → List (Nat × Nat) := fun _ => []
def nh_23 : Nat → Nat := unpackHintV5 0x4 0x0 6 63 3 7
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 0 bds_23 (dagTraceF m_23 s_23 3 f_23) (cur_23 0) (nh_23 0) s_23 3 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 0 (dagTraceF m_23 s_23 3 f_23) cur_23 nh_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 4 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0xffff00
def s_24 : List Nat := [0x555500, 0x333300, 0xf0f00, 0xff00]
def g_24 : Nat := 0x5f3700
def ep_24 : Nat := 0xa040000000000000032000000000000500400
def bds_24 : List (Nat × List Nat × Nat × Nat) := []
def cc_24_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xe81c8790701ccb98311620c4178af05e0bc168a734e09c13827046488310220421786f01e03c06c6d801d001 0x98504828229c1e130e888702c36121609098385834240e130d09048643d301a970b4a84a501e220e8f5307288353c189a084d0405029381226071102c701230061c4d8fe64772e378d19c54fe22770d377699ba4bdca56e1276691ae0fd5876a0374e19a60bd285680293e139a08c80422c1f0c0d8205c0826000f 11 2047 5 31 10 1023 17 131071
def cc_24_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xf8f1f0cdc8c8c8c8c8c8c8aca8a8a8a88c88816b686853504941403938380e01 0x3e4d21489053c7e9a3d061e028dd4c6ca235061a028ca38631a304e17a689028469c2d0b16048aa4c5320220a10c7845304812234e9126c292a069321078883a523c 8 255 3 7 10 1023 17 131071
def cc_24_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x102040810204048810191420401 0x9528932490288e24853081247c188134 7 127 3 7 9 511 16 65535
def cur_24 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_24_2 (Nat.sub p 64)) (cc_24_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_24_0 p) (Nat.blt p 32)
def hc_24_0 : Nat → Nat := unpackHintV5 0x9624a0a4091c2883430a18108284042020850408203f11b24d046042e116089ca4c122211008423a41b10c886022840f280b8002 0x0 13 8191 5 31
def hc_24_1 : Nat → Nat := unpackHintV5 0xd426623209710aa74c4a1a50447c33d09d88d8a6823211808b084e523211047883821a10b1044a1c30b185802821210808194006 0x0 13 8191 5 31
def hc_24_2 : Nat → Nat := unpackHintV5 0x4f4a41cfd27a23a19c84dc46452758e2c4941860a1031000c 0x0 13 8191 5 31
def nh_24 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_24_2 (Nat.sub p 64)) (hc_24_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_24_0 p) (Nat.blt p 32)
def f_24 : Nat → Nat × Nat := unpackForestF 0xc7e063b031bc74a23a491c288e12018cc0a7e053b029bbc911e2790134789a3e4d1e030f0140299814bc0a56052768a634511a030d0140291af8e17c68bd385e9a010fd6058b024021da99314c8004370219810bc08569024429d214d9083c042902139b130d8886c2c36120108c887a44352216960d0884a441e241a12090883a042118a60c51062783134020f874e0389820280e220106c1c700e30061c0105c0826000f 7 10
def ch_24 : Nat → Bool := dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 78 (dagTraceF m_24 s_24 5 f_24) cur_24 nh_24
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 78 bds_24 (dagTraceF m_24 s_24 5 f_24) (cur_24 0) (nh_24 0) s_24 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24_0 : treeBlockF 0 32 ch_24 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24_1 : treeBlockF 32 64 ch_24 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24_2 : treeBlockF 64 78 ch_24 = true := by decide +kernel
theorem nj_24_1 : ∀ i, 0 ≤ i → i < 64 → ch_24 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_24_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_24_1 h1 h2)
theorem nj_24_2 : ∀ i, 0 ≤ i → i < 78 → ch_24 i = true := block_join nj_24_1 (fun _ h1 h2 => treeBlockF_at nb_24_2 h1 h2)
theorem nc_24 : ∀ i, 0 ≤ i → i < 78 → ch_24 i = true := nj_24_2
theorem lb_24 : LowerBin m_24 s_24 g_24 6 :=
  lowerDagV5 (kn_nil) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0xf0f00000f0f000
def s_25 : List Nat := [0x50500000505000, 0x30300000303000, 0xf0000000f000, 0xf0f000]
def g_25 : Nat := 0x10100000503000
def ep_25 : Nat := 0x40200000000000000000000000000000000000000000000000000000101000000030000010100000500000
def bds_25 : List (Nat × List Nat × Nat × Nat) := []
def cur_25 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x16588f 4 15 2 3 5 31 7 127
def nh_25 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_25 : Nat → Nat × Nat := unpackForestF 0x39c4f 1 5
def ch_25 : Nat → Bool := dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 3 (dagTraceF m_25 s_25 4 f_25) cur_25 nh_25
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 3 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) (nh_25 0) s_25 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25 : treeBlockF 0 3 ch_25 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 3 → ch_25 i = true := fun _ h1 h2 => treeBlockF_at nb_25 h1 h2
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV5 (kn_nil) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0xcccc0000cccc00
def s_26 : List Nat := [0x44440000444400, 0xc0c00000c0c00, 0xcc000000cc00, 0xcccc00]
def g_26 : Nat := 0x40400004c0400
def ep_26 : Nat := 0x48000000000000000000000000000000000000000404000008040000000000000000000004040000400400
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 4, g_22)]
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def nh_26 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) (nh_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 nh_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV5 (kn_cons lb_22 (kn_nil)) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0xaaaa0000aaaa00
def s_27 : List Nat := [0x22220000222200, 0xa0a00000a0a00, 0xaa000000aa00, 0xaaaa00]
def g_27 : Nat := 0x20200000a2200
def ep_27 : Nat := 0x820000000000000000000000000000000000000020200000a000000020200000022000000000000000000
def bds_27 : List (Nat × List Nat × Nat × Nat) := []
def cur_27 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x16588f 4 15 2 3 5 31 7 127
def nh_27 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_27 : Nat → Nat × Nat := unpackForestF 0x39c4f 1 5
def ch_27 : Nat → Bool := dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 3 (dagTraceF m_27 s_27 4 f_27) cur_27 nh_27
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 3 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) (nh_27 0) s_27 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27 : treeBlockF 0 3 ch_27 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 3 → ch_27 i = true := fun _ h1 h2 => treeBlockF_at nb_27 h1 h2
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV5 (kn_nil) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0xff00ff0000000000
def s_28 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_28 : Nat := 0x100170000000000
def ep_28 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_18, s_18, 4, g_18), (m_3, s_3, 4, g_3), (m_4, s_4, 4, g_4)]
def cc_28_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_28_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_28 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_28_1 (Nat.sub p 32)) (cc_28_0 p) (Nat.blt p 32)
def hc_28_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_28_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_28 : Nat → Nat := fun p => Bool.rec (hc_28_1 (Nat.sub p 32)) (hc_28_0 p) (Nat.blt p 32)
def f_28 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_28 : Nat → Bool := dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 43 (dagTraceF m_28 s_28 6 f_28) cur_28 nh_28
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 43 bds_28 (dagTraceF m_28 s_28 6 f_28) (cur_28 0) (nh_28 0) s_28 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_0 : treeBlockF 0 32 ch_28 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_1 : treeBlockF 32 43 ch_28 = true := by decide +kernel
theorem nj_28_1 : ∀ i, 0 ≤ i → i < 43 → ch_28 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_28_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_28_1 h1 h2)
theorem nc_28 : ∀ i, 0 ≤ i → i < 43 → ch_28 i = true := nj_28_1
theorem lb_28 : LowerBin m_28 s_28 g_28 7 :=
  lowerDagV5 (kn_cons lb_5 (kn_cons lb_18 (kn_cons lb_3 (kn_cons lb_4 (kn_nil))))) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0xffff000000000000
def s_29 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_29 : Nat := 0x117000000000000
def ep_29 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14), (m_12, s_12, 4, g_12), (m_10, s_10, 4, g_10), (m_9, s_9, 4, g_9)]
def cc_29_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_29_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_29 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_29_1 (Nat.sub p 32)) (cc_29_0 p) (Nat.blt p 32)
def hc_29_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_29_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_29 : Nat → Nat := fun p => Bool.rec (hc_29_1 (Nat.sub p 32)) (hc_29_0 p) (Nat.blt p 32)
def f_29 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_29 : Nat → Bool := dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 43 (dagTraceF m_29 s_29 6 f_29) cur_29 nh_29
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 43 bds_29 (dagTraceF m_29 s_29 6 f_29) (cur_29 0) (nh_29 0) s_29 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_0 : treeBlockF 0 32 ch_29 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_1 : treeBlockF 32 43 ch_29 = true := by decide +kernel
theorem nj_29_1 : ∀ i, 0 ≤ i → i < 43 → ch_29 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_29_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_29_1 h1 h2)
theorem nc_29 : ∀ i, 0 ≤ i → i < 43 → ch_29 i = true := nj_29_1
theorem lb_29 : LowerBin m_29 s_29 g_29 7 :=
  lowerDagV5 (kn_cons lb_14 (kn_cons lb_12 (kn_cons lb_10 (kn_cons lb_9 (kn_nil))))) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0xf0f0f0f000000000
def s_30 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_30 : Nat := 0x10107000000000
def ep_30 : Nat := 0x1060000000000010006000000000000000000000000000101020000000000010104000000000
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_17, s_17, 4, g_17), (m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1)]
def cc_30_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_30_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_30 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_30_1 (Nat.sub p 32)) (cc_30_0 p) (Nat.blt p 32)
def hc_30_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_30_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_30 : Nat → Nat := fun p => Bool.rec (hc_30_1 (Nat.sub p 32)) (hc_30_0 p) (Nat.blt p 32)
def f_30 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_30 : Nat → Bool := dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 43 (dagTraceF m_30 s_30 6 f_30) cur_30 nh_30
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 43 bds_30 (dagTraceF m_30 s_30 6 f_30) (cur_30 0) (nh_30 0) s_30 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_0 : treeBlockF 0 32 ch_30 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_1 : treeBlockF 32 43 ch_30 = true := by decide +kernel
theorem nj_30_1 : ∀ i, 0 ≤ i → i < 43 → ch_30 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_30_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_30_1 h1 h2)
theorem nc_30 : ∀ i, 0 ≤ i → i < 43 → ch_30 i = true := nj_30_1
theorem lb_30 : LowerBin m_30 s_30 g_30 7 :=
  lowerDagV5 (kn_cons lb_2 (kn_cons lb_17 (kn_cons lb_0 (kn_cons lb_1 (kn_nil))))) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0xf0f0f0f00000000
def s_31 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_31 : Nat := 0x107070700000000
def ep_31 : Nat := 0x600000000000006000000000000000000000000000001020202000000000104040400000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def nh_31 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) (nh_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 nh_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0x3333333300000000
def s_32 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_32 : Nat := 0x113133300000000
def ep_32 : Nat := 0x1220000000000012002000000000010202000000000000000000000000000110100000000000
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_9, s_9, 4, g_9), (m_1, s_1, 4, g_1), (m_7, s_7, 4, g_7)]
def cc_32_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_32_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_32 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_32_1 (Nat.sub p 32)) (cc_32_0 p) (Nat.blt p 32)
def hc_32_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_32_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_32 : Nat → Nat := fun p => Bool.rec (hc_32_1 (Nat.sub p 32)) (hc_32_0 p) (Nat.blt p 32)
def f_32 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_32 : Nat → Bool := dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 43 (dagTraceF m_32 s_32 6 f_32) cur_32 nh_32
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 43 bds_32 (dagTraceF m_32 s_32 6 f_32) (cur_32 0) (nh_32 0) s_32 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_0 : treeBlockF 0 32 ch_32 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_1 : treeBlockF 32 43 ch_32 = true := by decide +kernel
theorem nj_32_1 : ∀ i, 0 ≤ i → i < 43 → ch_32 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_32_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_32_1 h1 h2)
theorem nc_32 : ∀ i, 0 ≤ i → i < 43 → ch_32 i = true := nj_32_1
theorem lb_32 : LowerBin m_32 s_32 g_32 7 :=
  lowerDagV5 (kn_cons lb_4 (kn_cons lb_9 (kn_cons lb_1 (kn_cons lb_7 (kn_nil))))) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0xaaaaaaaa00000000
def s_33 : List Nat := [0x2222222200000000, 0xa0a0a0a00000000, 0xaa00aa00000000, 0xaaaa00000000]
def g_33 : Nat := 0x2022200000000
def ep_33 : Nat := 0x220000000000002002000000000000202000000000000020222000000000000000000000000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def nh_33 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) (nh_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 nh_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0x5555555500000000
def s_34 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_34 : Nat := 0x115155500000000
def ep_34 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_10, s_10, 4, g_10), (m_0, s_0, 4, g_0), (m_8, s_8, 4, g_8)]
def cc_34_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_34_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_34 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_34_1 (Nat.sub p 32)) (cc_34_0 p) (Nat.blt p 32)
def hc_34_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_34_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_34 : Nat → Nat := fun p => Bool.rec (hc_34_1 (Nat.sub p 32)) (hc_34_0 p) (Nat.blt p 32)
def f_34 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_34 : Nat → Bool := dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 43 (dagTraceF m_34 s_34 6 f_34) cur_34 nh_34
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 43 bds_34 (dagTraceF m_34 s_34 6 f_34) (cur_34 0) (nh_34 0) s_34 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_0 : treeBlockF 0 32 ch_34 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_1 : treeBlockF 32 43 ch_34 = true := by decide +kernel
theorem nj_34_1 : ∀ i, 0 ≤ i → i < 43 → ch_34 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_34_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_34_1 h1 h2)
theorem nc_34 : ∀ i, 0 ≤ i → i < 43 → ch_34 i = true := nj_34_1
theorem lb_34 : LowerBin m_34 s_34 g_34 7 :=
  lowerDagV5 (kn_cons lb_3 (kn_cons lb_10 (kn_cons lb_0 (kn_cons lb_8 (kn_nil))))) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0xaaaa0000aaaa0000
def s_35 : List Nat := [0x2222000022220000, 0xa0a00000a0a0000, 0xaa000000aa0000, 0xaaaa0000]
def g_35 : Nat := 0x20000020a0000
def ep_35 : Nat := 0x20800000000000000000000000200000008000000020000020a000000020000020000000000000000000000
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 4, g_20)]
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def nh_35 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) (nh_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 nh_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV5 (kn_cons lb_20 (kn_nil)) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0x5555000055550000
def s_36 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_36 : Nat := 0x115000005550000
def ep_36 : Nat := 0x440000000000000000000000014000000500000010400000500000001100000000000000000000000000000
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def nh_36 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) (nh_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 nh_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0xff000000ff00
def s_37 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_37 : Nat := 0x170000003700
def ep_37 : Nat := 0x200000000000000000000000000000000000000006000000040000001200000032000000140000000400
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def nh_37 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) (nh_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 nh_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV5 (kn_cons lb_18 (kn_nil)) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0xf0f00000f0f0
def s_38 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_38 : Nat := 0x1070000030f0
def ep_38 : Nat := 0x2080000000000000000000000060000000c0000000000000000000001020000030000000104000000000
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def nh_38 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0xcccc0000cccc0000
def s_39 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_39 : Nat := 0x40000044c0000
def ep_39 : Nat := 0x448000000000000000000000004000000480000000400000408000000000000000000000004000004400000
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 4, g_22), (m_6, s_6, 4, g_6), (m_19, s_19, 4, g_19), (m_21, s_21, 4, g_21)]
def cc_39_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_39_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_39 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_39_1 (Nat.sub p 32)) (cc_39_0 p) (Nat.blt p 32)
def hc_39_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_39_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_39 : Nat → Nat := fun p => Bool.rec (hc_39_1 (Nat.sub p 32)) (hc_39_0 p) (Nat.blt p 32)
def f_39 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_39 : Nat → Bool := dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 43 (dagTraceF m_39 s_39 6 f_39) cur_39 nh_39
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 43 bds_39 (dagTraceF m_39 s_39 6 f_39) (cur_39 0) (nh_39 0) s_39 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_0 : treeBlockF 0 32 ch_39 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_1 : treeBlockF 32 43 ch_39 = true := by decide +kernel
theorem nj_39_1 : ∀ i, 0 ≤ i → i < 43 → ch_39 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_39_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_39_1 h1 h2)
theorem nc_39 : ∀ i, 0 ≤ i → i < 43 → ch_39 i = true := nj_39_1
theorem lb_39 : LowerBin m_39 s_39 g_39 7 :=
  lowerDagV5 (kn_cons lb_22 (kn_cons lb_6 (kn_cons lb_19 (kn_cons lb_21 (kn_nil))))) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xaaaa0000aaaa
def s_40 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_40 : Nat := 0x222000022aa
def ep_40 : Nat := 0x208800000000000000000000002000000088000002000000000000000222000022000000000000000000
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def nh_40 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0xaa00aa00aa00aa00
def s_41 : List Nat := [0x2200220022002200, 0xa000a000a000a00, 0xaa000000aa00, 0xaa00aa00]
def g_41 : Nat := 0x20002002200
def ep_41 : Nat := 0x200200000000200000020000000000000000000000002000200000000000200020022000000000000000000
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0xf000f000f000f00
def s_42 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_42 : Nat := 0x100070007000700
def ep_42 : Nat := 0x600000000000600000000000000000000000000000000000000000001000200020002000100040004000400
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def nh_42 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) (nh_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 nh_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xcc00cc00cc00cc
def s_43 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_43 : Nat := 0x40044004c00cc
def ep_43 : Nat := 0x48008800000040000000800000000000000000000400000008000000000000000000000004004400400000
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def nh_43 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) (nh_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 nh_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xffff0000
def s_44 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_44 : Nat := 0x75f0000
def ep_44 : Nat := 0x58000000000000070a000000000000020000000000000004500000
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def nh_44 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) (nh_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 nh_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0xcccccccc
def s_45 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_45 : Nat := 0x44c04cc
def ep_45 : Nat := 0x8000000000004800c8000000000408040000000000000000000000000004400400
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def nh_45 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) (nh_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 nh_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xa0a0a0a0a0a0a0a0
def s_46 : List Nat := [0x2020202020202020, 0xa000a000a000a0, 0xa0a00000a0a0, 0xa0a0a0a0]
def g_46 : Nat := 0x20000020a0
def ep_46 : Nat := 0x208000000020000020a00000002000000080000000000000000000000020000020000000000000000000
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def nh_46 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) (nh_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 nh_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0xff000000ff000000
def s_47 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_47 : Nat := 0x100000007000000
def ep_47 : Nat := 0x600000000000000000000000000000000000000010000000700000001000000020000000100000004000000
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def nh_47 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) (nh_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 nh_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV5 (kn_cons lb_16 (kn_nil)) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0xff000000ff0000
def s_48 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_48 : Nat := 0x170000005f0000
def ep_48 : Nat := 0x4800000000000000000000000000000000000000060000000a000000120000000000000014000000500000
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def nh_48 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xf0f00000f0f0000
def s_49 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_49 : Nat := 0x1070000070f0000
def ep_49 : Nat := 0x608000000000000000000000006000000080000000000000000000001020000020000000104000004000000
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14), (m_16, s_16, 4, g_16), (m_21, s_21, 4, g_21), (m_20, s_20, 4, g_20)]
def cc_49_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_49_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_49 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_49_1 (Nat.sub p 32)) (cc_49_0 p) (Nat.blt p 32)
def hc_49_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_49_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_49 : Nat → Nat := fun p => Bool.rec (hc_49_1 (Nat.sub p 32)) (hc_49_0 p) (Nat.blt p 32)
def f_49 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_49 : Nat → Bool := dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 43 (dagTraceF m_49 s_49 6 f_49) cur_49 nh_49
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 43 bds_49 (dagTraceF m_49 s_49 6 f_49) (cur_49 0) (nh_49 0) s_49 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_0 : treeBlockF 0 32 ch_49 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_1 : treeBlockF 32 43 ch_49 = true := by decide +kernel
theorem nj_49_1 : ∀ i, 0 ≤ i → i < 43 → ch_49 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_49_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_49_1 h1 h2)
theorem nc_49 : ∀ i, 0 ≤ i → i < 43 → ch_49 i = true := nj_49_1
theorem lb_49 : LowerBin m_49 s_49 g_49 7 :=
  lowerDagV5 (kn_cons lb_14 (kn_cons lb_16 (kn_cons lb_21 (kn_cons lb_20 (kn_nil))))) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0x2222222222222222
def s_50 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_50 : Nat := 0x2022202022222
def ep_50 : Nat := 0x200200000000220000020200002002000000000000202000202000000000000000000000000000000000000
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def nh_50 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) (nh_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 nh_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0xa0a0a0a0a0a0a0a
def s_51 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_51 : Nat := 0x20202020a020a
def ep_51 : Nat := 0x208000800000200000000000002000000080008000000000000000000020202020002000000000000000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 4, g_20)]
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def nh_51 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 0 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) (nh_51 0) s_51 4 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 0 (dagTraceF m_51 s_51 4 f_51) cur_51 nh_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV5 (kn_cons lb_20 (kn_nil)) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0xaaaaaaaaaaaaaaaa
def s_52 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_52 : Nat := 0x20222020a22aa
def ep_52 : Nat := 0x208208800000220000020a0000200200008008800020200020a000000020222020022000000000000000000
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_33, s_33, 5, g_33), (m_40, s_40, 5, g_40), (m_35, s_35, 5, g_35), (m_41, s_41, 5, g_41), (m_50, s_50, 5, g_50), (m_46, s_46, 5, g_46), (m_51, s_51, 5, g_51), (m_7, s_7, 4, g_7), (m_15, s_15, 4, g_15)]
def cur_52 : Nat → List (Nat × Nat) := unpackCursorV5 0x119 0x339f 3 7 1 1 6 63 7 127
def nh_52 : Nat → Nat := unpackHintV5 0x815900810000 0x2673cd6f7ac670660e30600f39d7719c6b1bc6cccccd30e2c783084 16 65535 8 255
def f_52 : Nat → Nat × Nat := unpackForestF 0x339f 1 6
def ch_52 : Nat → Bool := dagCheckNodeV5 m_52 g_52 ep_52 3 7 bds_52 2 (dagTraceF m_52 s_52 7 f_52) cur_52 nh_52
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 3 7 2 bds_52 (dagTraceF m_52 s_52 7 f_52) (cur_52 0) (nh_52 0) s_52 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52 : treeBlockF 0 2 ch_52 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 2 → ch_52 i = true := fun _ h1 h2 => treeBlockF_at nb_52 h1 h2
theorem lb_52 : LowerBin m_52 s_52 g_52 8 :=
  lowerDagV5 (kn_cons lb_33 (kn_cons lb_40 (kn_cons lb_35 (kn_cons lb_41 (kn_cons lb_50 (kn_cons lb_46 (kn_cons lb_51 (kn_cons lb_7 (kn_cons lb_15 (kn_nil)))))))))) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0x3333333333333333
def s_53 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_53 : Nat := 0x113133303133333
def ep_53 : Nat := 0x200200000001220000030200012002000100000010202000302000000000000000000000110100000100000
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 7, g_32)]
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def nh_53 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 0 bds_53 (dagTraceF m_53 s_53 7 f_53) (cur_53 0) (nh_53 0) s_53 7 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 0 (dagTraceF m_53 s_53 7 f_53) cur_53 nh_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 8 :=
  lowerDagV5 (kn_cons lb_32 (kn_nil)) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0xff00ff00ff00ff
def s_54 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_54 : Nat := 0x170077005f00ff
def ep_54 : Nat := 0x48008800000060000000a0000000000000000000060000000a000000120022000000000014004400500000
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_43, s_43, 5, g_43)]
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def nh_54 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 0 bds_54 (dagTraceF m_54 s_54 5 f_54) (cur_54 0) (nh_54 0) s_54 5 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 0 (dagTraceF m_54 s_54 5 f_54) cur_54 nh_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 6 :=
  lowerDagV5 (kn_cons lb_43 (kn_nil)) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0xffff0000ffff00
def s_55 : List Nat := [0x55550000555500, 0x33330000333300, 0xf0f00000f0f00, 0xff000000ff00, 0xffff00]
def g_55 : Nat := 0x171700005f3700
def ep_55 : Nat := 0x4820000000000000000000000000000000000000060600000a040000121200000032000014140000500400
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_24, s_24, 6, g_24), (m_26, s_26, 5, g_26), (m_25, s_25, 5, g_25), (m_48, s_48, 5, g_48), (m_37, s_37, 5, g_37), (m_27, s_27, 5, g_27), (m_23, s_23, 4, g_23)]
def cur_55 : Nat → List (Nat × Nat) := unpackCursorV5 0x987c7871545050494841240b01 0x1697552ac245446a68d25aeab55868a48d8d221a4468b4b1591ab1256a68ee91c51b801f 8 255 3 7 11 2047 15 32767
def nh_55 : Nat → Nat := unpackHintV5 0x3511ea76d27f1e9d825c5b169c798c1b60031740c5a030b7b1016c80005 0x4e739ce6ab56ace96ccf398e733ce639ce739ce739ce739804c9939ce739b3a956b97554cf398e733ce639ce739ce739ce739804c9939ce7399e7318fa739d35735ad99596739ce733ce639ccf398e739ce739ce6013262d574c9e6399e639b31ccf3674c733ce98000001302613 18 262143 8 255
def f_55 : Nat → Nat × Nat := unpackForestF 0xb4ba2d1e1aec345148e5168a2b13563488495851b801f 4 11
def ch_55 : Nat → Bool := dagCheckNodeV5 m_55 g_55 ep_55 3 7 bds_55 12 (dagTraceF m_55 s_55 7 f_55) cur_55 nh_55
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 3 7 12 bds_55 (dagTraceF m_55 s_55 7 f_55) (cur_55 0) (nh_55 0) s_55 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55 : treeBlockF 0 12 ch_55 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 12 → ch_55 i = true := fun _ h1 h2 => treeBlockF_at nb_55 h1 h2
theorem lb_55 : LowerBin m_55 s_55 g_55 8 :=
  lowerDagV5 (kn_cons lb_24 (kn_cons lb_26 (kn_cons lb_25 (kn_cons lb_48 (kn_cons lb_37 (kn_cons lb_27 (kn_cons lb_23 (kn_nil)))))))) rc_55 nc_55 (by decide +kernel)

def g_56 : Nat := 0x1171777075f37ff
def ep_56 : Nat := 0x648208800001660000030a000160060005800c801060600070a040001121222020032000114144404500400
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_49, s_49, 7, g_49), (m_34, s_34, 7, g_34), (m_28, s_28, 7, g_28), (m_53, s_53, 8, g_53), (m_39, s_39, 7, g_39), (m_30, s_30, 7, g_30), (m_40, s_40, 5, g_40), (m_52, s_52, 8, g_52), (m_32, s_32, 7, g_32), (m_54, s_54, 6, g_54), (m_24, s_24, 6, g_24), (m_15, s_15, 4, g_15), (m_29, s_29, 7, g_29), (m_2, s_2, 4, g_2), (m_43, s_43, 5, g_43), (m_55, s_55, 8, g_55), (m_48, s_48, 5, g_48), (m_47, s_47, 5, g_47), (m_13, s_13, 4, g_13), (m_38, s_38, 5, g_38), (m_37, s_37, 5, g_37), (m_7, s_7, 4, g_7), (m_42, s_42, 5, g_42), (m_8, s_8, 4, g_8), (m_45, s_45, 5, g_45), (m_31, s_31, 5, g_31), (m_11, s_11, 4, g_11), (m_35, s_35, 5, g_35), (m_36, s_36, 5, g_36), (m_3, s_3, 4, g_3), (m_44, s_44, 5, g_44), (m_16, s_16, 4, g_16), (m_22, s_22, 4, g_22)]
def cc_56_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xba05b0ad81681b405a02c05600aa1d502a033089804c02505280920c9023851c08e04702285101880420a1010417a23d000f8001 0xfb540782a038d901a6a80c85405dae00c4d0150cc0a83708ab18411bc1d8be0d96f060af82c51c0726a0a0560482e0221500f2c80736f0349b014990090c803146018930081980406c0436f01d1b00a518030cd47c5fa362dd1115e788a739b5f9b9adcd8d5e676a73134f975a5cb6d1e5768724a5f8f92dc6495e284a70e24f84525c0491df3486f1a3f7611db8e8ddab466cc95f65cadb0c55d822a6b494f578a5aa451d452869d93f4bc9d9f24dced2666e12f3589596849cb12465305f2942d91215c880a64184f208258b611c5a0862083f1001d8760dc380661302f0941582609c100460601f02c0d80405c010260003f 13 8191 6 63 11 2047 21 2097151
def cc_56_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xd1d0d0bbb8b8aaa8a89a98988a88818079787170705b58511f1818180a080100 0x7e153eac7ea6ff12ff40b39049ba54d82a6899330c98a54bd325a952b4b94124a82e5051b5ac7946fc22fdc5bec2bf49479c92c8d5230a90b64 8 255 3 7 11 2047 17 131071
def cc_56_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xac2b0995bb6c1b06c192641905c97058560581244812040900400e2380c2300c0300c02100800000 0x3116dc04f6f927bc136e827fedbfda6ff0977ba4dea8df916fde5773137c649ee0662809acb54b0152b364aa1929b54a318e696fa053629259cd926a3596d5250549093621268cd222a4488512183caf58ea26fa497e7a35985be495f8e4d61127 10 1023 4 15 11 2047 18 262143
def cc_56_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x88620881d5741d068d91641725c17050d405011344101388e0380e0344c112040100220441000400 0x36937fd5a3d25cfa5976137f8193d26ef25175937c019bb460be1dba568e05739864e2917816ebc19b484cdb9e3404cd35a3416fdd183627fd69b7524dc849ae876ce130a826cad832146c24f3096c 10 1023 4 15 11 2047 18 262143
def cc_56_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x98251942148421078de0709c0701c0701846018060126481204086a1806018060144230802008002 0x184224f47c9d4f8c015270224d4705f0ad321325d2ac994e958f9289164cbe49044908e11e9f63926c59265d0ac0805231b845946a169f3e9b66d27cc237962db2253e349bc51275c08c0605a142643b6f864df088de06b440064 10 1023 4 15 11 2047 19 524287
def cc_56_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xd41a8340e80d01a02d3da0b415893c2604c088910201400801001e13c0780d11a01cc380700e01c020c40004 0x5e93ebbacf748c6e49ec5867640af6c0b41812db1464309da95bf4ab3e7c6bcb8c79116f1db5e3363c56b788d0f0d37e1267c14af8093efcb7df167bc2957051a9c37c5067630ae8413edc1fda83d0706b66532c8a258245ac48b54936a42657b4fae49f5a8deaca7d4137a724f491f28d22d10449d49d405563c9bb1046 11 2047 5 31 11 2047 19 524287
def cc_56_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xd0646311080c01e2f061b0162b0492412072381c0e043201004420100802210080400200 0x379be75d6fe8acfcd1af8e31f0c5bdf2dfba59f5c92eda64d94f9b4dbf61b3eb936d56d1a6dc2eca368b48d02899cd23352266144ca69192512e8aa5c954 9 511 4 15 11 2047 19 524287
def cc_56_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xc0170ad0da09ccac95028150090920202400784f01e0344414800e11c0380510a01022004004208008410001 0x7f5675c926340567e26f0ba4d7da455486e338561502e9656f8fd678e26f8ca6b8ba678a26388a5b82a577fa4d7ea3d5c1265406f46867330577d04d1482f0b027028157c164781447b1347a17c77934791347826a77a667bb6f7ab6b79b6778b6377136762647527c7497c73a4472b44722447124470364 11 2047 5 31 11 2047 20 1048575
def cc_56_8 : Nat → List (Nat × Nat) := unpackCursorV5 0x9425081600801e2781d1741d068da0681825c561545504c93044910404e229091240902409024009 0x8f4688124c8e865360577e04d8da5c8d1248c47080b5c8b25c8a92489a5c8912487b7885b6487c7c853608687c85b6c8483484b6485474840348836f8736b8636783b63834608256f81d678126e80a625506f47067350570b83d80035 10 1023 4 15 11 2047 20 1048575
def cc_56_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xa82a0a46188420180200789e0745d0741b26c1565415048d11404f13c0d2340c1300a21906018006 0x9e96ca256fa1d67a126fa0a6ba02679fa639f25b9e2579d1649c2349b9349a97c99a34991349cb6f9b36b9a36798b635e236981369746896a658224d95248932349534c92a309404c9323c92b449202495a3f94a3b93a3791a339147090a7d81a4d7f23d9017c5d926 10 1023 4 15 11 2047 20 1048575
def cc_56_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xcae432181c06030180b8dc2e16174381a2d0592c16083401c4e070290140000000000000 0x2cfb7d976bb1ecf60d8ebe9b57134aba4954492bbb5d6f63ad4df599aeb133d5a63aac7f538cea2b252144a7a694d9f298be51d34a5269489aa8f335436fa76d74bd9e93b1d1936 9 511 4 15 10 1023 19 524287
def cc_56_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xa02719c252942419024088a2084610751d0705c0701a2681a05185f14041100310c0210802000800 0xbf354be464b6045bd254bc47cbb97cbaa545606f4a067b985d0d055b8b54b7a54b7124b626fb5a4d0d245490662503e0c826bfb6bbeb63bda6fbca6bbb267ba263b9245b823fb6a335586f48867b50452483f1602f0c027b4164b3134b217cb1234b0934 10 1023 4 15 11 2047 20 1048575
def cc_56_12 : Nat → List (Nat × Nat) := unpackCursorV5 0xb82e0b0ac0a4dcd701b16c1b0649635815154141501404891144110404d3160501405008c2008002 0xcf264ce924cda5d0e25539846d434bd3255d224bd0a47cfa3fce2336f92f5f927cd055390472603f1702f0d827cc136cb37ccaa35c6a3ec5a326f12dc927cc8570c737cc6a7cc4924c4a6cc5b7cc527cc4124ca34bc9a6dc8a4bc7a47c623fc3a336e92f5f127c2936c2018c1814c0b54c0134 10 1023 4 15 11 2047 20 1048575
def cc_56_13 : Nat → List (Nat × Nat) := unpackCursorV5 0xa0e80a02358c2308c23088620882118420180200802005309b240901c87010c400c4300c01204001 0xe0254db124df854de567ce96ec4166b715eaa156db844c4a6cd9014dd45fdcc5bdc457db453da95fda15bd9957d8953d814fd794bd7147d6943e2d6fe1d6be0d67df563ce16fc3967b695fa9957de928dd925d6124d5364d49347012dd386d0e065d2a64d1d68d115cd0364 10 1023 4 15 11 2047 20 1048575
def cc_56_14 : Nat → List (Nat × Nat) := unpackCursorV5 0x982519425094223791e0745d0705c06c5b06c1b06c1745c1705c1705488d20062180421001304001 0xef27cee354eda54ed054f0d6fefd6beed67ecd63ebc68eac58e9c70e8c58e8254e7855e70544c8664285eeb56fea56be9567e6d63e626fe5a67e525fe4a575686f4c0674205f3a857e404de3264dd124e2254dc924e127cde125dc124db814 10 1023 4 15 11 2047 20 1048575
def cc_56_15 : Nat → List (Nat × Nat) := unpackCursorV5 0x9ca7094a508ca308c2308c2307d19664181601715c143501404892048120481204442f0801104001 0xffa447dc123fa9f1f6048fda447d4123f0d7df76b6fb3577d5a9c011bdfe8d6fe4677ea31bf20a1f4048f93647c1aa3dcdf0fe28af29357b1aa3d6151e5acef8d6f7beb5bdb59deaac6f4a6f7a133bce97de64aecf96f630b3ae057d552ae7e9457909a98049de24c8f0254 10 1023 4 15 11 2047 21 2097151
def cc_56_16 : Nat → List (Nat × Nat) := unpackCursorV5 0xdc361a3a809c67098660946509423288599641816018058960545505415048d20481020b82000800 0x13819a266df1236b889b3c40d8e1f4df0f26779d1fb948dcae0de4d8671dc2ac3a1145207e1e03786d32432912174f90ab448512222451a1a8df0c46b85a33c2718da42dec89674f8a7a2251e1224b08568839b641a4d60bae104b6c8211a40e4d5a22dc9e93e83db7c18dae0a6cf0336381537c0899de647ee4a37684b7b1e59e032ba9e13f4149b98249e014c8fc024 10 1023 4 15 11 2047 21 2097151
def cc_56_17 : Nat → List (Nat × Nat) := unpackCursorV5 0x6ad6a06816806806426406216206205e25833333203013002e12e02c12c02a122408d080061060041040021020001000 0x2478bf22c5b90e2bc8114d792beb295b564aba9c54d4129e9b14b464a39ea50e3f24b1ec7c8edbe4744d638ae11b37c8d51a2ee5394d2846c92a8f1a7c72d2e3768f1a34387927c0891de847ee5a378ccb6aec53d63296ac14752ca1a804fd342768b9373cc999b04acc224f18a548bd2245a9b22b488b115a55cab2665291528d1845f8ba2dc5915e2a8a6ba15f580adaac55d492a69f94f4c4a5a2851cf12871492589e3244ad52238f910b54 12 4095 5 31 11 2047 21 2097151
def cc_56_18 : Nat → List (Nat × Nat) := unpackCursorV5 0x9047ca7c07257207206a46056006005c25c05a15a05815805615604e44e04260fa0e00c10c00a10a0081080080042002 0x8e933cbe8f5a92dc6492694937c8a9ae394cf172639811ab505bd942cf2f1353849799049e504df21a6b8dd33c5898e5c4bb2d36b965b1c849aa354cd2726f90135c6899e2a4c72c23595a324aa116536c928d6893db21b64aa4d0ba050551f423c965740a2aa8e9371f0230aa0f80902d2a34f949a5ca0d1e4e6870fa4f81523bd28fdcc46f261555eca7ace52d5a28ea81435089fa724ed1c26e7b9333689598649e4a0aa4304f1ec238a80fc3d06e0701f0200bc90952464892226c909a2482911382948d146 12 4095 5 31 11 2047 21 2097151
def cc_56_19 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8390320640c81632664c0945282323ca780ec5d83745b4b4142a8046a8c0fa15a2a0450880c505408001000 0x9fc24a0a3fa063ba02379fa339f53f9f13b9ed379e9337ad2f7692b739276fd23a1a457aa3f7663b736376fa33a1448a0c459e44415c3f0f8370d42f088279dc5d084559d65d08655200460cc2e9da5589a4f86a4b83e47802439d05521c4f1fc470c82f080279c93d836579c23d6015e341268925f8625b832577fa539c6355fd5f575579bd353992f33d279b66d88a4f85a4b82a477f2438565a822569ad3d3952d3352581e579a63d57156331268825f84e5b81a577ea539aa355f55f56d579a13538d2f32d272c06f28c679984d07c459566f9924d07e4528866078269526f91e6b8f2678c263996452bc6f2846798c450c02f07427655679853d 11 2047 4 15 10 1023 20 1048575
def cc_56_20 : Nat → List (Nat × Nat) := unpackCursorV5 0x2c0a8aa0a45fa7c1a568182601532e8b01d0701c0070000000000 0xa4d5d4b537a465da4a557c63f7863b75a3771633a41555113f4b1373ad2f35127a3a457be3f77e3b7523770e33a316548537a2a65481363a52ea2e6d7b63f7763b74a3770633a256d50d3f47d373a12f349277723a74236a1c4d09045a124d0924573e371603e0fc360d82e08c26 10 1023 4 15 10 1023 20 1048575
def cur_56 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_56_20 (Nat.sub p 640)) (cc_56_19 (Nat.sub p 608)) (Nat.blt p 640)) (cc_56_18 (Nat.sub p 576)) (Nat.blt p 608)) (Bool.rec (Bool.rec (cc_56_17 (Nat.sub p 544)) (cc_56_16 (Nat.sub p 512)) (Nat.blt p 544)) (cc_56_15 (Nat.sub p 480)) (Nat.blt p 512)) (Nat.blt p 576)) (Bool.rec (Bool.rec (Bool.rec (cc_56_14 (Nat.sub p 448)) (cc_56_13 (Nat.sub p 416)) (Nat.blt p 448)) (cc_56_12 (Nat.sub p 384)) (Nat.blt p 416)) (Bool.rec (cc_56_11 (Nat.sub p 352)) (cc_56_10 (Nat.sub p 320)) (Nat.blt p 352)) (Nat.blt p 384)) (Nat.blt p 480)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_56_9 (Nat.sub p 288)) (cc_56_8 (Nat.sub p 256)) (Nat.blt p 288)) (cc_56_7 (Nat.sub p 224)) (Nat.blt p 256)) (Bool.rec (cc_56_6 (Nat.sub p 192)) (cc_56_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 224)) (Bool.rec (Bool.rec (Bool.rec (cc_56_4 (Nat.sub p 128)) (cc_56_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_56_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_56_1 (Nat.sub p 32)) (cc_56_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)) (Nat.blt p 320)
def hc_56_0 : Nat → Nat := unpackHintV5 0x8ee4f688e97f844d277d3dc478b1237411286c71e867ed2161dd845eb4ca59156854c11551f0b44f10b84a7d25466d0440398d3ba924379d0333a8fd2f09282941722002501af543171cf61251330e58fe098136036d850000db000000000000 0x350e7d4f8759800000255a0f5414000004b5547e8abd802a00000000000000d4384c0400e0000cf600044d56a0f503a000a080000025aa808800150000000000000000559a0680284001552b3ec014150b830e1cb830e1d54058b0162c4416078dcab5504a0a0881c0e004426d55553ea0aa8a00aa4c1870e4c1870e2202c580b160b03aaaac3e275513aaa0f503a858052ad55555412a27b5054381c00a0878442aaaaaaaa350596557d8a1b1eaa6c78350f415020b0162c058b0181e5a375541071280183080600442ac6e9981991806a1cfa9f16610580c0e0b05cab41eaa0f55542c2a5aaa3f555ee0950e2403201801441c8806a1c393550e1c010580c0e01c58070f0f55a83d40ea0f07aa83d550b00a96aaaaaa8254388033d830600c18300a0838442acd0369960f2c0d54acfb182ea1c0000d8f55363c3872e0cb830e1c00025aa802370000000000002acd1f40237523001750e02013001801c0000087aad41ea074100000500004b5510011002a000000001ec00080008559a4800402aa567d8042884c06030180c06070507540eaf647c0a0757ba8285000f6440d4183506aa35160c183060c183072ad03aaaa07555eeaa5a07555eeaaaa9546a1c183060c183060c5870f55545d5458b2e2e26ab507a81d42e22a5aaaa9554e5cba7169c5d45154ab34ccd54acfb9955550e1c38755aaaa550e1c3870e1c387aa55555555555555060c18355aaaa55060c183162c58baa555555559555555162c58b55aaaa552e5cb97162c58baa5555555567daaaaaaa1d541aa8b44565154e8aa8002a87061c387061c3800000000a802855000000000000002aaaaaaa802a8002caa1c1870e1c1870e00000000afb5656a800000000000000040401e1300098000700180000101000aaaaaaaa00aa0fb00043a870000364d55d930e1c3830e0c387000096aa000000000000000000156640296969a4003a870000583c1e000000000000980801c0060000040000aa1d0e804c83ec0013aa8882c0eab5504881c0e00442aaaaa0aa83ed4155550ea83545802b2b2a9d015555547830e1c7830e1c44058b0162c160755555aaa82441e3c7870380090aa8f55505545155554b872e1c44160b0581d5556aa0955478f01e3c98071e0c7830e2c580b17554883c780f0f9ec381c04e0f221559547830e1c7830e1c44058b0162c160757dab2b5504aaaa3c78f263c78f4e3c78f1e3c7930e1c7831e0c387162c0058baaaa441e3c078f00e0701383c88555555551eaaaa0aa800a0fb1ea1c4160b038f26aa3c9870e5c18f061c38b16002c5cb554149e1e20703809c2a8855998199d32303d4380000000003d47871e3c3800140000b172d54004010f9566400021f488f50e0000000000f583c5e0005800f51e1cb8f0e000280002c5c9d38f945a8745a0003ec026405555540013d800000000000aaaa1e2f0002c01001511e1c78f0e002000b878f95555511110581d55543c5e161282a0aaaa7f61cb831e0c38b017271f28227b440e07013840f152ea1c4160b03ac1e2f0b09393554e4c3872e0cb830e1c58b00162e93a74f49c40e0701384271554ea1d2e8b066400507daa80002ad500000000002aaa802a8003ec40400e003000002020004 24 16777215 10 1023
def hc_56_1 : Nat → Nat := unpackHintV5 0x9cdda0969d909039998c58f88a787887f8a08404fd7e895f78cd6f70edf86ced006938ed63b1625fa10459e1705541284e55bb4991314241d43db92239491c32f5952ec90b29755525291320812a1b3553157d6e0d7a01096d0303d9650000f6 0x20d55f6a0d50101001801c000e0b000381c000000000550f038387a0eae816004000000000000000000aaaaaaa875410007daa802caa4c1930e4c1930e0202000b058002c160030038000000000afb5656a880080000000000000000015555555410007daa800350e1c9aa870f500802c006007000382c000e0700000000025aaf703a81c4004000000000000000000ab4d34b4a10003ee6400ba80802c00600700000168bc0b0020000000000000055168b4058003ee640154000156a8000000000155540154015444160b55aa82552e5cb971602ea955550554155444160b55aa82442e17002215555401f6aa28aaaa87541aa2d65650554e800aaaaaab4aaaa1c1830e8c162d182c5aad352aad52a87060c3870e1c0e1c381c3870f54aaaaaaaa355555655555555554383061cf8b3e2d56aa3f7baaaa955560f503a83c1ea3f542e2295550e0c1870e1c3870e1c387aaa883c20d55f6a0d5550e0c1870e07161c0e1d56aaaaaaa955560f503a83c1eaa0f5542e2295550e0c1870e1c381c38703870e1eaaa20f0aaaaaaa8755555f6cacaaaaaaaa97068c397068c3800000002a828055000000000000002a80282a800a802aaa973e5cf8000002ac7ef65555002aa80141540e00054000000000000045500380c04f6000002a811055002aaa8005040107a81d00002a0000000000000000aa00a082a802bed9590006a1d18f55463c387aaa0000000096aa050000000000000000559900a0001a90006a1c2602007000067b00025aa808800226ab507a81d000504000000a80000000000000002acc80900033ee96a0050542e0c3872e0c387550162c058b110581e955556aa09414110381c00885555555541551401549830e1c9830e1c44058b0162c160755aaaaaa82555587c4eaa275541ea0750b00a544f6a0a870380111410f0555555554157db2b2288c7aaa31e0d43d054082c058b0162c060796a5a9aa820e2500306100c008855a5a599819a91806a1c393550e1c010580c0e01c58070f2d555555050f55a83d40ea0f07aa83d550b00a54388033d830600c1830088a08382accd2d2c0b3ee96a182ea1c000158f55563c3872e0cb830e1c00025aa8000014000000000001566402800064020ba873ea7c3972e1c0000025aaaaa3f7b0021eb5540ea0000800f62a00000000000047b0ba8701009800c00e000004b55100110043d56a0f503a080000282160000a8000000007b0080002015664200050067dd2d40103d4380000000003d47871e3c3800140000bf72d54004400080ab3217b000000a0647a8710582c0e3c9aa8f261c397063c1870e2c5800b172d55040b123c40e07013855444ab33034941324d05d5458b2e2e5aaaaa26ab507a81d42e229554e5cba7169c5d55450ab3332cfba5aa65555458b162d56aaa954b972e5c58b162ea95554baaacfb5555555543aa0d51688aca2a9d155555555a55550e0c187360b166c162d569a37552a87060c3870e1c0e1c381c3870f54aaaa0d4daaacaaaaaaaaaaaaa1c1830e7c59f16aaab07a81d41ea83d542e22956aa3f555eea95550e0c1870e1c3870e1c387a883c5520d55f6a0d5550e0c1870e07161c0e1d55560f503a83c1eaa0f5542e22956aaaaaaa95550e0c1870e1c381c38703870e1ea20f154aaaa0d55543aaaacb2abed55555554b83361cb83361c00000001563755000000000000002aa6d553e803228008aa00701809ec000005555000a08020f503a0000550220aa00540000000000000001540441551a00cb2abec001a87363d54d8f0e1eaa8000000025aaa37000000000000002accc6e009100 24 16777215 10 1023
def hc_56_2 : Nat → Nat := unpackHintV5 0xae2d0caa8ce8a4d56e9dd1c1994d21945d3c8dd9a1846a5c7fc9287a496071523e6c79366326555fecce5b452a56314551b91e4df8f045c20e410d2d3c054232965c2e211d28e94e24711e1fb1301af13015f1400d0a3a07d54d0468db00011a 0x2aaaaaaaaaaa2aa2222030182c16aaaa0e070f87c2c25115114060c180c1830080e2aa0c3aa0fdaa0fda88892c4406030180c060707e87067c21600007b0faaaaa830eaaa83f6aaa83f6aaaaaaa83060c183060c1aaaaa0e0703818385d2aaa83060c183060c183161c3c1cfc0c1aa83260d41aaa2c180c183018b060c183581d030740e060e174a1c18301830603060c18b0e1e0f2975060c38306a837d8b45b25e43a5d55550e0c18755aaaa550e0c1870e1c387aa555541bed55555555550ea2d1159595150e8aaaaaaaa8306aa2203038282aa8781cfcdd3f3742c2440e03038700e1c002038aaaa8aa02a00aa8a2aaaaa8880c0e1f3d870162d5554387060c1830e1c38700e1c00e1d5550f038fc7e1610b1742d7d22070181c0e00070e01c38407106aafb506a8880c0e01c58070eaaaa1c383060c1870e1c3870e1c38b161c38b0e1c38755543c0e0e1e83aba1610b1742d7d22070181c38070e0001c38070e101c555555543aa0fb050154515554b83561cb83561d54141444160b555a55aa82563c158f0447e1700221141555550554515554b9f2e7c443e7b1602c582c16aaa2c980b0162c58b062c18b555556aa0aaa910f87c7e1700058b058f221655260c987260c987110162c058b0582d555458f164c58b162c593162c58b162c38b062c18b0eaabed595aa82aaaa44264c09c307e1700058b0163c2215555526aaa83ec1405514463d5518f06a1c183aaa105828480c0f2d555555041c40e1c038700e03002215614169a60664601a870e4d54387a841603038071601c38b26aa2c5870e0c183061c3870e1c3870e2c5870e2c3870e1d596abdc0ea074155550710380c0e1c03870000e1c038708855a69a5a507d82813230931eaa6cb975e22930e0c187550645c2e951e0f098dc8da8aaa8f50e3c7aa8f1e1c38f063c1870e000000012d55400000000f00078000010ab32000a0112005d579b26aa4cd872e0cb835e1c4160b058284cb5542e858508bc2e37036cc002885599850581a691850002e0c3872e0c3875500000000866ea19ba550f17800000000000000001515540154000187061d547931e4dbe7266cd8f263c383061c0002a85c01ed1000154054055260c387260c387000000005555163c593162c58b164c58b162c5870e2c18b061c382aa4c9d135741e2f000b1742e80f620200000000002aaaaaaa81ec04055007e3d55f8f06a1c183000000000007eb3f374fcdd0781c00000000000000aa000a1c06804c800350e7d4f88000001ec0058b55161c380c387000038705fac1e071f8fc002c5c2d7c00000000000000d438726aa1c380000000002c7aa8b161c383060c1870e1c3870e1c38b161c38b0e1c38705fac1e07070f41d5d000b1742d7d0001ec06003000000001543a0d0e1d0ea1c38b503d808132003d4380000f1eaa3c7870e5c197061c380004b550043e000000000000055990000a091001ea1c793551e4c3872e0c7830e1c000000007ac1e2f47a1ece800000016000000aa1d168000004c800b0ba87000096aa003e3d54f8f0e1cb832e0c3870000a000000000000000559900980500002ea1cda9b0e5cb8700000036a6c3972e1c58b0000000000036001ec0008559901008ddeca6001ea1c7a8f0e3c78700000001ea3c38f1e1c58baaa80025aaa1f555ec0005599000087deda6992ea1c00005a8b0e2c58704fa9f0e5cb8705801ec162c00096aa00aa85dec10000000000059ec00002ea1c000058f55162c387160c5830e1c13e4d54f930e1cb832e0c3870000162c58b162cf8b163d98b162c5cb550055542ea000000000000160104007b559903d80811f969966400ba882c160b164d5458b161c583160c5875568bc2c2162e85d081700058b016102a8b45a0fb050264458aa0000ab540000000000aaaa0fb005500101003800c002020000011515554040400600700580070380000000b3d80aa1e071f8fc0b0020000000000000000 24 16777215 10 1023
def hc_56_3 : Nat → Nat := unpackHintV5 0xa1295b9ce5119565e08b328d85058b7ff54479fd7e74a55670651069f59c652d325e59b553cea34f093149a55942e9af3e25313d5c323b78793808dc32dd4b32dc003240272cc16024ba021fd13a1cdcbd133a690c9da708211f0319420000c6 0xaaaaaa0c1aaaaa83060c1a3058b460b16ab552b4ab54aa0c183068c787118f0e0b0e1ea95555555555565550554183063c18f060c1b706dc183060d4160b0182d12aa949870e03295541a0d5f6caaaaaa0c183060c193061d54183060c1833e0fdaaaa7c59f160c183060c583060c1aaaaac0ef755555552a9f0e7c3831e0c183060c183062c3ef0f54b2aaa83060c183260c183060c18f064d54183060c183060d555260b164c162c180c183018b060c18357dab2b03aaaaaaaaa9549930e130e031e0c060c180c183062c387aa55555549aa83506aafb55559555954183060c1a93557da0c1aaab2aaa4c593160c183066c59b16aa4c3930e0c183066c39b0e2c3ab0eaaaa937daaaaaaaaa0d418f1eaa3c7d03075420b0180c058b0162e5aaaa282083880c1900c38f0e01150ab334b4b0332300d41a326aa6c9d2cd235160c183066c162d182c5cb5540e81d548d4383060c19b661c461c161c3d52accd2d2ccd34cc835061d43d48d4583060c1870e1c3cb55540eaa0ea1c183060c3870e1c3870e1ea96581d07599f733353320d418000231eaa8c7828000004b5550055550000000000002cd36068c014001352000c1aa83260d41aa02013000180c0006000c0060000000004b5555555040017b000000000000000005960740d59f640020135200aa8aa00c1aaa8880c0602c580b16aa0e07233748cdd0b0910180c50500080e2aaaaaaaa0aa8a0aaaaa83060c183061c18755060c183060c383f6a8882c16030180c06aa7d1c7cfc0e07030f03070b0911101830fec060c060c0600407005555060c183064c183060c1831e0c9aa83060c3830e0c183060c1aa2202c580b1600c1803160301aa932744d1d034740c1d030f03070b084f6a0a83061c0183018030180101c55555549aa83506aafb4155468a0f1eaa3c783507415020b0162c058b0180e5a1f55410712801830806005107156829266066460055060c187060c1fb51eaafb418355545444160b0180c160b551f0f81c0e1f0f8584aaaaa8f7daaa8a82aa0d418f26aa3c9828341820b0180c058b0162c7ac0e070f6751e85841c40e0c060c180c1830080e29750683438700e1d05833207439701a830000a63d5698f05000000a6b0381c014cdd53374000000000000aa0d1000e1c0026400580c388ca6aef683063cd6130194c187f6ae577b77fb47a8f9610980c0602311806c36000ae818388d815000001eca6606881a8f50026a4c1ab8e0c183060c183366c183060c1830e1c015c0e37555000000047c1c0d9f66e3ed2d033f6cf7ee060d418f06a0d53eaa7c000060c1830fec060c183000000000581d03a061e060e3e7e3ebe000000000000000060d5418f06a0d5010098000c06000300060300181c000000000581d030740c3c0c1c00102c000000000000003d800a2d41830e0c1aa0df602c00140245c800b01a8310580c072d555047c7aa9f1e0c1acd0b16002c5d0450710180c0088a0a05599819a9a5a51806a3d4000000783067c0a005fbaaa02f7011f070367d8550306aa0c783506a882c01830062c06033e4d54f93060c7b3060c183060c183060cf83060c183060c18b16002c5cb555555541001c4061c0183006030038554047b593ec0e81ab3ee0696966a46155554183060c18355060c183060cd83f6aaa9b16ac583060c183060c1aaaab03aa81d55552a9b0ebc383060c183060c18b0efc3d52aaa83060d43aa8356a55362cd8b060c1830e1c387550e1c387060c1830e1c3870e1c387555506aa8355543fb43aad4aaaa0c183061c3870eb2aaaad503aa95554183060c3870e1c3870e1ea955061d507ed507ed44444426030180ca6030184d1017b0000 24 16777215 10 1023
def hc_56_4 : Nat → Nat := unpackHintV5 0xa73d54a089ad9b195c9282268e81008a84ff84a1797ff12c7ab94e75e1367274db6d61456849466089f05ba13a5820e054d4d34ef9774a353147d0994081d43c411037bd213131a327228422a91e1c1da314a9dd1005290c2cf607054a0001c1 0x2aaaaaaaad2aa3058b460b161c1830eab4aaad554aa1c38703870e07060c3870e1c3d52aaaaaaaaaaaaaaaaaa83061c3832e0fda87557da0c1aaab52a9b166c587060c3870e1c3aa870e1c387060c3870e1c3870e1c3aaaaaaa0d5550efb5555555543aaaaaa1c3aaaa7fdcaaaaaa87060c39f167c5aded55556a59aa55550e0c1870e1c3870e1c3870e1ea9541aaa1d5543aaaaa870ea1c9aaaad48a88b550e0c1870e07161c0e1d6555a55abdc0ea075521d15154383061c3870e070e1c0e1c387aa55555f6aa83555543aaaaaaaa1d5500000500961cb832e0e587000055aa00a5550000000000005155005000550055550eaa0002a9ff62a9f2e0cb833e000000000caaab552a0000000000000000aa0d550eaa00220020088084c0060070000000001955956a82000bd800000000000000002aaaafb55410005005500050542e0c3872e0c387550162c058b110581e1f2ad5412828220703801443c505455554155140554551e0c3872e0c387110162c058b0581d547b3a8f41e2f0b0915150e07138040f1554151550554551555555514044058b0162c060755966ea59ba0f038584880c1828203002038aaaaaaaa82aa2a1c54d9b55555c75506a1e204160b05cb0783c1c480641d557daaa0d0e2aaa0c1870e0c783f6aaa8306aaa80220b0580c0e0703aa8f87c1e070783c2c25545555543bed415555550eaaaaa870eaaa9ff62aa288b110181c160b57aaaa8781c7e3f0b0943fb14511018a0306004071541aaa1d5543aaaaa870eaaaa002822c44060700e2c038757aab2a8781c1c3d07a161287051044019ec1830060c180407155557daa8355550eaa0aa8a87154000014003872e0cb830e1c0001543c5e00966ea59ba00000000000054555968028002a8003ec55061c187110159ac0361b0181c001543c46c0a800000f64aabf4151506a1c01571d555366d54383061c018dab4a0000000aabed3eaa0aa0d550eaa00220020080800c00e0000000002aacaa1e2f00040b000000000000000f6002aaaafb5544004015400115444160755aa8255550e1cb832e0c387162c0058b5045440e070021281415555055555545478a0d43800000f51e05002fdcb017b80555f69f55506aa8755050458882c0ea3d9aaaaa9f55550e1cb831e0c387162c0058b655655aa82011e0a0881c0e0270aa808f6aaaabed54fa82aaaaaa2a3c5506aa875545445aa8b2e2d556558bc2e9454552e5d38b4e2e4f2aaaafb5555555555555162c58b55aaaa552e5cb97162c58baa5557daaaaaaaaaa87541aa2d1159595154e8a88aa0070182aaa800070e01cb802a27b000000000154085e01c3c0cbc1c3d072f4000000000000000000aa0220afb41aa0d00550059541830e1c1830e1d555438f0e4c3870e1c3930e5c3870e1d555260b164c162c383061c381c587038757dab2b555555554aa1c38703870e07060c3870e1c0e1c381c3870f54aaaaaaafb41aa0d55555506a1c3aa8754fa9f0e1c183060cbfb001830000000000025aaaaaaa680000000000000001a870e4d5438754040260030038001c2e00070380000000012d555555410005ec00000000000000001559f703581c10002804c800350e1c9aa870eaa8b0e0c1870e07161c0e1d60e1e065e0e1e8397a1741d4387060c3870e1c0e1c381c3870f070f2aa0df60c1a83060c5a2d990e8755554183060d56aaa954183060c587161ea955506fb555555955555541a8b44565654553a2aaaaaaa0a0000000000aa0e07233748cdd000000000000002aa8a800002a802aaaaa80306002a83060c180cf83f6a800001ec001802a9f471f3f03a0740d1c0c1c00000000000000022aaa800030060c0154006030544f6000000000c1600aa04230068e8183a068e060e00000000000000000055500504106a0d55f600aa8d00 24 16777215 10 1023
def hc_56_5 : Nat → Nat := unpackHintV5 0x95c9c59035658ba52488c0b98215ab7d393778a5256fee2e6c38ed66b56162551860248c5de4905a04f85758ab51997049720a43a174407cc9392dd43648b93245012c158c24d5d0206d1a1ba13317a10014c0b810990a0a758905b13100016c 0x835543aa8000000028f26aaaab4aaaaa3c9870e1c187061c3800029b66aab4aa1e0f000020801ec003800041001ed55555554015555540103870e1c000078f1e3c3870e1c3870001eddb8f0e1c387000007c6e0f078000f60003e3f0783c007e1f1f8fd541c3870e0000addab761c3870e000ae570783c00000000004009e4f0783c009d3c9d3d5400a83541fb0000105823c7aa3f981400ff66d602f6bc05551e1c78700001e3c7fb1fec78f0fec7bb1e3c3fb03d9ec07c3e0f1b80000162c58b0e2c58701600000b85c1e17000bf742fdd550b85c3c3af0e00002c58b161c58b0e02c78f1e3c39b1e1c000a0000f755540005ec002aaa802aaaaaa87870e0000000000f1e3c7877e3c3800140007b1f2b83cae0002f600003e83d00002b87d543d43882c16071e7d547bb0e1cb971e5c387162c0058b1e3d5478f0e1cb832e0c387162c0058b5596aa820016287881c0e027159550505011ed56663e0ccd0f99ac3e9a91a1e0f50e0000000000f51e1cb970e0000012d5400400080ab320000010f86a4ba8710582c0eac9aa9f261c397065c1870e2c5800b172d55040b129c40e0701385050442accc0d33a6a469381c38007664d66930e1c1b3061c3b316002e83d0400070380155011ee83d052ce6a89381c3870e00015554000000000155540154001c3870e000155540000000001155540154001c3870e00015554000000000047b0980801c00600000040155540154000240a0d43aaa4c7aaaa4c787a80002583c000000bed555555541aaa1c4040426002200070000000067b00015526aac1e070100000000000000000000afb555554044001540155541aaa1d4393555550e4d55554387a955151161c1830e1c0e2c381c3aab2ab55ee07503aa9550e8a81c1830e1c38703870e070e1c3d52bed5555555555555555555506aa870110109800880084c006007000000000155955aa82000bd800000000000000002bed555551001005500555478f555478f06a1e204160b05cb0783c1c480641d7daaaaaaaa835543aaaaa8726aaaaa1c380220a08b0181c038b00e1d551eaac1e07070f41e85848887050019ec1830060c18040715f6aaaaaaaaaa0aa8a28350e00aa8f1eaaa8f1e1c1830e00b2c0000000bed555555541aaa3d55f6028001cb970e000000000aaaac1e2f1f8fc000000000000000aaaa0d550e0202002200213001801c0000000005547aab078bc00102c000000000000003d800f15f6aaaaa82000a00aa008aaaa0d550e220a08b0581d55554793555551e4c3871e0c7830e1c58b00162d55955aaa08044478280703809c1e554047b57daaaaaa82aaaaaa28aaaa0d550eaa8a88b165c5aaa4d55a2f0ba5549a2a172e9c5a7172795f6aaaaaaaaaaaaaaa8b162c5aad5552a972e5cb8b162c5d52bed5554baaaaaaa9d550ea83545a22b2b2a2a9d150500555550e1c000000015659ba966e83c0e0000000000000051500055005500506a1d366d555572d543d400012c1e000000555f68355055550eaaa0002a8a7fd875540f6008000002bd55543c0e3f1f80000000000000001541aaa1d5440011001010038000020b00019ec00057aab2a8781c0400000000000000000002aaaafb550680282000aa000aaaaaa3c1870e3c1870e2202c580b160b03aaaa285541220f1e3c381c004a8555555554155145555552e0d7872e0cd8755360b16ac162d78b2e2d5555aaaa954db34e37362f2e5d38b4e2ea9555555555555555 24 16777215 10 1023
def hc_56_6 : Nat → Nat := unpackHintV5 0xdaf4ecd51d76d164eecd4109c66db5c298f5bcc575b8092fb3b515ad858ca2a2b99d7d499625d691fd0a8d452e8675b48199377bdd6f756d9c6b3e8c65fd505f01bf5472a44cf9de42b2923766d32dfe5a2462671c99f211bab8096216000258 0x80aa1c3870e0000002ab1faa8000f607b3d807b3d800010aaaaaa00aa00020d550eaa00000000b2aad2ad5002c4d555569626aaab07a81d00000020801ec00000f64042aaaaaaa802aaaaa80070e001eaaaa0a2733507a81d42c028000e070008f741555550555535251001d43870e1c380000000fb7dc1ecf6fb0aa3d81ec1e001f000008559999009900a83a870e0c3870e0c387000000005bdad2b54000000001300000008f6000f09808803c2600220007001800001002ad2d2cc804c80009020070e1c3aa80000005ec03d9edf68fbaa000f800807000021555554015401541aaa1d54000000016555aaa0010000000000008f600213001100109808801c00600000400aaaaaaaa00aa0002201c3870e00003c98f47a3c9870e1c187061c3800055550000000000041001eeaaa802a6a6a8003870e1c000283c1e00000000023d8004c0400e003000000013c9e0f07802a800044e00d41883c06031eb0381cbc20e1d54387060d41a0c18f16003c5d003283880c06004032801c0aa0d0697066479751e3d44380c383507ed41835441e00c58030603018f1eaa3c783060c183063c1831ecc183060c183060c183060c78b001e2c7ac0c1d033740e072f0800e2030600c380301801c1e554047b55060d4197506834b823cba8f1eb3221c55110180d541c0e5e12aaa83060c183060c1bb1600ec5a822a20301801ce650950282aaaa0aaaaaa8a2aa0d5541fb050458880c06a3d9aaaaabb5555060c183060c1831e2c01f8b4daab2a8381cbc2010e0a0880c060070aa808f6aaaaaaaa82aaaaaa28aa0000a81e57002800070eac1ab061c3800028000000000000002aaa802aaaaa802a800000071e3c38002afb547870e3c7870e000b4aaaa8795c003c7d30fbd80aaaa00aaaaaaaaa07b0100010ea83505555555930e1d5831e0c387000055556a3d9aaaa8795c00ac9b50000000000004020800f6aaaa00aaaaaaaaaa003d4380000f183c8e0000500e1c7831e0c3870000a000000000000000550e8b4026458b5162d4007a870000100e6cd87001e3d1e0f1e3c9871e0c7830e0002c5800000000000f000f642a8745a002d168b168b16800f50e0000001c78f0e0003c7a3d1e3c7fb0e3c18f061c00058ba162c5d0f583c8e001e3e85c3ef602a8745a002d168b168b16cc8f50e0207b0000387160c5830e1c11e3d47aa3c78f261c38f063c1870e00002c58b162c58f162c7b3162c58b1eb0791c002c5c2e858b3740000000000002c020800f6aa1d16800b16a2c5a8b16a2c5acc8003060c180002391c0e0600231ead56a31e0c1800000050000000000000000b85c0e0700550b1722c5c8003060c180000f1e3c7800000f1e3c78f1e0c18307ec183061c000183a060c1d0f87c0e07000f1f40e1f7b005c2e07038005c2e162e162eaa060c1830003d800c18f068341830001a326ad56a3260c183060c183060c1870e00000c183060c1ab060c7b3060c183472381c0e00060e819ba000000000000060104007b170b81c0e00060e418b9162e458b9aa005514478ac0ea3d9aaa870e3dd8f1e1c38f1e003dda3d543c6e36100aa1d506a8b00547a4d81151e281c0e03b07955011ed41815555055555555554507a871560f1e23038f1e3c9aa8f661c38f463c7870e3c7800f763c7a9b83c6e361003c78f0e1c7831e0c3871e2c0078b55501e50f1e23c0e0701d83caa808f7403e0550e9f4f823dda8f1eb323c7a8f3ea23c060c1831583c060c061c7a31eec7af1e8c1830e1c183060c1831ebc015bb1f1b818781838d840031e0d0683060c183062c00183061c187a0065070380c380c1801c7e554047ba00700f8bc0e071708b97a1e5eaa81839065e48383c3bf0e00003d58f763d58f761c3ab763d5870e02c58000f8dc1e3702c000163c5a2d162c387160c5830e1c0580000000000000104007b00005900b85c1e17000b1742c5d550b1722c5c80543d438f061c38f061c3883c078b01e2c46071e3d47aa3c78f263c78f263d055000e1c7831e0c3871e2c0078b5bdad2b550400f1078f0780f1e3d98070380ac1e554047b55a5a59981a5a599185506aa8755050458888c0ea3c9802aa82aaaa9b261c39b063c1870e3c5801b16b2aadeea8dd004028f660a20881c0e02b15955011ed5555555505555554501830683418f060c183a856230060c018b0180cd93369b4d93060c38700060c183060c0183060c183060c1830e1cd8b00362ea8dd03a07557b80200381c060c3b30060c0600c0600715955011eeaaa6a6aaa0aa6a6aa8a17875e1c000058f168b458b0e1c583160c38708d93369b4d930e1cd83360c38700000162c00000002aaa80f604000000000000000b198104007baaaa00a9a9a9a9aa00003a870e0c3870e0c387000000001e3d47aa3c78f263c78f263d955aa0e1c3830e0c38700001eb0f1f0fa1e3cdb3a0f07800003d88080000041001ed5478f51e7d43a1d001e9d478f59900 24 16777215 10 1023
def hc_56_7 : Nat → Nat := unpackHintV5 0x9be15b2e3cc64c481c71b378912930a2bfe00f9b3c8bca74da1edea589ac08a329576608e4eb59dc15ce72a9a4fc4cef2e8fe4fd0cf969df7d4379e28675bf0b61c514bb042406b840e39470e870ad7a311761c15de881b6828001b6 0xa83541fb0045cf5458b059b58812180002c0f62f551be1c380000b162c587162c380b6f3783cde0020000000058007b0005c2e0f0b8005c2eaa00163030e0c3aa8f1e3c79f3e3eddb1e3c787060c380002fb65aa00005551e9f500902ea1cd8f55363c3872e0cb830e1c000000025aaa37000000000000002acd2f40001900abd94c005d43db26aa7c9870e5c197061c3800000002c1e2f1fab7400000000000000aa2c3a2c5a00004c8b0000e1c040260030038000001c38004000000000007b00058b0e2c38002002c580140001d4387061c387061c3800000000ab00280783c00000000000000aa2c5a8b16a1d0e804c80541d4387061c387061c3800000002ded6950f0780000000000000f6000f0100784c00260001c006001006c0055162d458b50e87402640004160aa00008b540000a01c387061c1870e0001400000000007b0000001555401555554015400016f6ab5400aa1d506a0000c80000001ec00000040400e0030008808011001000055550055555500011050000e0c3870e0c3875500000000263c001443c1e00000000000000555555550055005506aa875500000000526aab7b0f0780000000000000f6002000880080801c0060011006c0015555555401540004403a870000954aa001e3c0003870e0c3830e1c000140000000000f60000002acc804cd2d2800750e00014ab7baa0089d07a81d00002a00000007b0000000780801c0060010101100100002acc804cd2d28000902a800028a870e1c3802aaa0d0005da00000007b0000015554015555401541aaaa800000028000aa29bf61c3870e0000000000007b00155555540154003870e1c0000d93769b5d930e1c3830e0c3870000371b83c1c3878000000000003d800000002e170783c002c5c8b17342e8580070e1c38000070e1c38000000001ec002602007001800400002c58b161c3870e002c58b1600020b00e1d56a50734b420f01e2c078b0180e5a82a2aa083880c18070e00c0600442ad2d2ccc0cc8c030e0d41fb5060d51078031600c180c072d555555050f55a81c0eaa075540ea0750b00a003880c18030e00c060011ee8283aad2d2ccc0ccd2d28c2aaa8307554aa08c582316220301aa282ad541070e0a0880c0600242aaaaaaaa0aa8a22830183550783c440603aa87ded55aa82a5555556a81d00402aaaaaa0aaaaaaaa0d5541fb050458880c06caacab5504b2aaaad2aaac0ea0750b00a0143828822030180047ba0a0eaaaaaaaa82aaaaaa28aa0000000a1c3a3068c1870e00002b5400a0000000000000010aaaa00aaaaaa00aa07b0100010ea8350556a801599555560f503a0000555a59540000000000003d9010aaaa00aaaaaaaaaa003d4380000807466c38043d2aa81c001238000000000855990099a69001ea1c000014003871e0c7830e1c00024aa80280000000000000021566402969664007a870103d80001c38b062c1870e0cb550055542ea87aad41ea07400010b85d542eaa0000000000000f64042acc8052d2ccd2d28003060c18000231e8d46a31e0014000154540140000000000000011555401535354000c183060007b001831e0d0683060003aaaa00aaaa89ccd40ea07400010381d540eaa0000000000000f640455550054d4d554d48020070e1c38750e0000011fa1e9554001ecf67b00f67b0f607b002265566402640000ea1c3830e1c3830e1c000000025aaaa1f5550043e26ab350f89aaccd541ea0740000001ec40403800001ec80855a5a5990099a5a500 23 8388607 9 511
def hc_56_8 : Nat → Nat := unpackHintV5 0xd7d291a0f3af072eb5cd504b1f1ef4b66227029ac7ed86871a30fc048dc3cd13429145faa2aa4a6ad48204a9040051c012a3800141217a82400504800a0900140403a74c2f439ac065886ca768e91c0cb1a524c2583c82768e80013b 0x7a870000000a0e1c7831e0c387000019a0f2b86e00a0000000000000003c550eeb40079f51e3d6640154187061c4403e1f0158ac06070005582800000f64a3d7789f01418047d43d438f061c38f061c380803c001e0003c260030038000000000b7b5a543cae036001437000000000000000f6003c551e3d47a875000402640078aa00000a001c3c7071c1870e0000a2b54000014000000000000aaaa00aaaaaa00aa09ec00000000045aa002200040e3c787000140001fee0015554000155555540440426003003800000b7b55aa2002200550ea835040000141160000c8000000007b00800010155544004015555540115400001400387460d1830e1c0001545bd8791c23001e3c00000000000000118aaaa00aaaaaa00aa0d550eaa00220020080800c00e00000000028f555bd8795c1b0021b8000000000000007b00562aaaaaaa8800802a8020f50e00000003c7870e3c18f061c380004a550000028000000000002acc8052d2cc8040f50e0003c2600c000000252a8000bd9000f0038f1e1c000a00007fb40055992000099a691ea1c04401e13001801c00000a55bdd50400144010fa0f503a080000282160000a8000000007b0080002015664800402669694020183060c000178f5eaf578f0060c000002aa28000028000000000002aaa802a6a6a800183060c00019ec0000000aa8a0022001e3c78f006000140000ff700155540001555540c183060201300180c00607000002aa077baa200220087ccd40e08000028216000150000000007b008000202aaa8800402aaa6a40207a8f0600c7aac8e43c787858c1c1703060c180000f51e14000000ae5703a286e001c380000000000000002b0bc5e061e060e002e5e4b979aa002e03060d06831e0c18307500804c000603000180030018000000000ae5703061c183a81dec3600437000000000000000f600ac2f1781979060e4187818382e0020154005c0e0d07ed06a003d4783060c19b360d7c7060c183060c1800f1e0e370000000034ba5d2eaa0d507ec015f1d555366d54183060c01366d5a500000005555a87a871e1c78700000001e3d54dfb014000e6cd870000000000000551e8f43aad00369b4007a87000014dfb51e3c39b5e1c021f5500051e000000000005599009999002ea1c0000f8f553e3c3872e0cb830e1c00025aa8000014000000000001566402370d480070e00011c99b63a6c9870e6c1af061c380001b8dc1e3700000000000000000141e800dcab9aa00 23 8388607 10 1023
def hc_56_9 : Nat → Nat := unpackHintV5 0xea5325bfa5433bf0de2b133bb8a7759577298868cf010492b2d5139475f78bebb28f26d7238c305f9580b825d94a4112a87253f4a2908942c09285800502024a040013742526e8004dd0009ba0012a4341d69f82a841430e90800187 0x60c183000001005800c00605540ef75440040050f99a81c10b000008580000554000007b0000000002aaa8008006aaa6a40078f1e3c183060e000001607b0000016003000018000f87c1c007102c0016002e170b85c0e070002c02a81830683418f060c183a800000000040160003018000c1600300180ae5703061c183a81dec16000b0020001800000007b0000005c2e062e41839061e060e0005800d500070e00000200b001801c00e1c16000b002000003d8000002c58b161c58b0e000b001162c58b00a0000ea1c3830e1c3830e1c000000005801403c1e00000000000000562aa73ea9cfa8743a01320150750e1c1870e1c1870e00000000b7b5a543c1e000000000003d80002b01e0200f098004c0003800c00200d800aa3c9a934ea1d0e804c80270044e0aa00008b5400081c3870e0010000080001000ec555500555550055000045aa0000500e1c3830e0c3870000a0000000000000000555500555555005500005bdaad5002a87541a800032000007b0000800010040400e0030008080440040001555401555554010044140003830e1c3830e1d540000000098f000510f0780000000000000118aaaaaaaa00aa00aa0d550eaa00000000a4d556f61e0f000000000001ec0001582000880080801c006001006c0055555555005500401100ea1c000252a8007801c3870e0008000f000006004003b1566402669a40203a87000094aa001e3c0003870e0c3830e1c0001400000000000000015664026696940203a870000a55bdd50044e83d40e800015000003d800040001000f01003800c00202022002000055990099a5a500801200e1c3870000364dda6d764c3870e0c3830e1c0000dc6e0f0780000000000000000004f2783c1e004e9e4da79aa000e1c38700000e1c38700000003d800001301003800c00200004e2d38b0e1c387004e2d38b004e0089c050600000001c3828000000f51e0c18306003cd8f878f1f0000000000002a8341a003cba8f1ea5d2e800f03a8766107806c360231180c060003c783060c19b08d800001ec1e5d2e97041e0c383507ed4183540401e0003000060300180c0060700000000007a8f060c1c0c1c0c1830600117c000000000000003d800f1541835065d41a0d0b80080174ba003c8dc6d01831b1e30f4383161b05aa8a00000a0000c18000002a83060c1801b8dc000000000000aaaa00aaaaaa00aa0e07008c4601b0d8880c06001b0582a83061b36051b0d83c00000f61b55415140060288220008000c001e7b0000000078f1e3d58f55060c18300221802aaaaaa800802aaaa0d5541fb0011001004040060030000105800000aab2a83060c1800400080000000000001ec005555555510010055004 23 8388607 10 1023
def hc_56_10 : Nat → Nat := unpackHintV5 0xc28d3fbbe9a9b4d9c4aa3ea79f76b298bdae9151db8c35478469f37a5a8474dd5f6e21af6695e361bd365a61d756c8e65141624da4e749ccf643a9893f45193985703668c7329cf32cb97927bd3f1fb60219599711f1da0c2174062180000188 0x183060c0000183060c0000067b0000000980800c0000200002e5cb97060c183002e5cb9700010b82aaaaa8007b010000000106875541a0d5506a83505541870703060e060c18300567ba8000c01801ec000000015555555401555554001835061c1a8300000000000183060c183061c383060c183060c3fb001ea3c187060c183060c183001e3c78f55061d060d06834005a2d168b418355061c1a8300040f6000000003061c383060c183060c183061c383061c383060c183060c1823d47830e0e060c1c0c18306002c58b85a3170000c01801ec00000160002a830ea0c1a8341a002c5a8b16a2d1680540c1aa830e0c183060c3830e0c183060c3830e0d4183060c183060c18020f01e2c078b0060c01870180d6f6b4a830f40c1d0381c8c20e2070e01c3803061c1830019ec02038aa3c7a8f2ea0c3a8306a0d06970664438aaaaaa0088030600c380c06b7b55aaaaaa825506875541a0d5506a83545802b2880c187060c0067b0088504382aaaaaaaa0aaaaaa8a2aa0c1aaaaa830eaaaa835541aa800a08b110060c01870180d47aaadec187a060e81c0e46121c141101830e0c1800cf60101c555555555555415514060d418706a0c01078030060301cb55555410f10e0c1d5540c1830703061fd8f01e94ab4d3330333320c1aa830e0d418020f0060c01870180e956f7555555050fa0707aa81c0eaa0707a81c0ea16014a87101830e0c1800cf6011144141c156969666066696946018306834187060c183000000000058f168b458b060c387060c183060c183060c387060c183060c183091c8e061e8183a070380f60400000c01801ec0000000005c2e061e41839070380058b9162e6a80018306834187060c1830000000002aaaaaaa880078f1e3c1830f55540c1830703061fd80005554d4d500555503060d06830e0c18306000000000555555551001ee1f3350383d540e075503a81d0400000c01801ec000000080aaa9a9aa00aaa9a900060c1a0d061c183060c000060c01870180c1870703060e060c18300e0701830e0c1800cf6001c0e172e5cb830e0d060c1a0c183065c0b972e5cb81c3940000d4383061c383061c3800000000ab00280781c00000000000000aa9cfaa73ea1d06804c80540d4383061c383061c3800000002ded6950f0380000000000067b00000784c04401e13000980007000008036002a8f26a4d3a8741a01320002270550000615aa0000500e1d55400028000000000000001555401555554015400016f6ab5400aa1d506a0000c800000cf600000000202007000008808011001000055550055555500011040060d060c3aa8000000f01443c0e001180080700000d8aaaaaa00aa00a000aaa1c3aa80000000131e000a21e07000000000000002aaaaaaa802a802a835543aa80000000293555bd8781c0020000000000cf600002000880084c04400e000011006c0015555555401540004401a870000a55bd954003c7800070f5540000a0000000033d800000000ab3201334b4a000d43800052adeea8022741ea0740000a800000cf6000000000f01003800004040440040000ab3201334b4a000240aa0000a2a1ea00550eaa000bb400000000001555401555540155543aa800000028000aa29bf61e061c004003d800000002aaaaaa802a80030e0c380001b26ed36bb261c3d0383870000371b838781c1c000000000000000004f2783c0e004e9e4da7993d27800187061c0000383061c000000067b00000980801c0000200004e5d3970e0c187004e5d3970001138030e0d41fb5060d500000000010058000c16000301800c00600f51e0c18381ab0703060c182c00160040000000007b000001541835062d41a0d00058008b45a00aa8355507ec0000416000000220020b0101001800c055aab2a83060c182c00160040000000007b000001555555540040055402a1ea1c7830e1c7830e1c0000000004016000b058002c1600300380b7b5a543cae058002c008000000000f6000002a8b16a2c5a8745a000b00199005500000101001801c05bdaad510010012a87541a822c000011600000ac800001ec0000000005555001001555555005506aa8755000000000011001058080800c00e028f555bd8795c0b00058010000000001ec000005555555500100155001ea1c000004016003003814ab7baa200200287d07a81d042c0000216000014a800001ec000000000559900200199a5a500 24 16777215 10 1023
def hc_56_11 : Nat → Nat := unpackHintV5 0xb79159ad3e95a70d8c9c7ea498690591cda78d192d881d3f80b5da7bc93b7431e66f59366875b963255459327d54b91e4f3d5f489da843fd283f25363885a831bdb22cf53225cdca2244e21cd55c18d8ff1319700f5cef0b74fa059d76000167 0xa000d038306000000000003d478f1e3e1e6c7c1c1830e00000000000c000055162d458b50e834005a2d0006a1c38f550e1c00103d800000001c3870e0c183062c1870e1c3870e1c38b161c38b0e1c387047a8f0e0c1870e1c3c1d58780058b170b5e2e0003d80c006000000002a8741a1c3a8716a002c5a8b16a2d16802d28781830060c380d4380f1603c5883c06070ed2d07583c0e5e1070600c180710380c0080e0f1ea3cfaaa8741afc19910e540d4383061c383061c3871eaa1c3871e1c9870e1c3871e1c3870e1c010780f1603c580c0e01c58070eb7b5a543c0e0e1e839ba5e1071038700e1c0067b060c0183060101c551e3d47d750e83438750eafc19910e2aaaaaa82a0883f160fc580c0eab5555550488a00c1820300221555555550554515555540110181c038b00e1d6f6ab55555504aa1d506a8743aaa1d5545802b288033d830600c1830088504382aaaaaaaa0aaaaaa8a2aaaaaaa28088231608c580c0eaa3c7d070f41e0723091018305040600407155555555055451141830e1c18f07ed55060d555555001e0f110181c0e071e079543c0e0e1e0e6e4612aaaaaaaa0aaaa835543aaa87555550e1d55540050458880c0e01c58070ea3d556f61e07070f41cdd2f094382882200cf60c1803060c02038aaaaaaaaaaaa82aa283c7aa870e0d43d054083c078b01e2c060796a5a9aa820e2500306100c18300221569696660664601a870e3d543870041e03038071601c3d2adeeaaaaaa0a1f41e0f50381d41e0f5507aaa16014a8710067b060c0183060111410705599a5a58199a5a5183e3d54f8f06a1e8387aa10580b1602c580c0f2d4b5355041c4a00e1c20180110ab1ba66066a460d938e9b6393061c187a007070562b0362c158b0181cdc6e0e1c3870f03839b08381c0e0c018300e030020e070e52b93721e072b0aa8838bc7af57abc7830e0c3830600000000000be5f00050701c0000000000000002e170b1722c5c8781c0154000c3830e1c98743a1c380000000002c78b45a2c5870e0c183061c3870e1c3870e2c5870e2c3870e1c25f2f83c0e0e1e839ba03d81000007b01800c000000000170b83c0e0e1e438b900162e458b9aa00463dfafd463c187061e800000000002aa8002880000000060000300002aaa6a6a802a800187061c38f0e8743870000000002aaaaaaa880078f1e3e060c7fb060c387aaa060c1d0000555554d4805555030e0c387261d0e870e000000000555555551001ee1f33507a81d41e0f5507aa8200000f6030018000000040555554d4805554d4803030e0c3aa8f1e3c7d3a63cf9f1e3c78a02c160b05afb65aa0e071018aaa3d3e8743afd6438350e6c7aa9b1e1c3acd082c06070162c058b96aa8dd041c480650070e00110ab334b4b034d2300d439f26ab4c9828343820b0181c058b0162d60f03a9d1fa1610710380c0e0c018300080e29750e1d06870e1c38b04bc97910e1c380c3830e1c98743a1c380003038071601c387060c3870e1e0e1e00e070067b060c018306001c0e172e1c1830e1c387438740b972e070e5000035060c183060c18306000000002c00a00e07000000000000002a972ea5cba8341a0132015035060c183060c1830600000000b7b5a541c0e00000000019ec0000001e0200f098004c000180000401b001547935265d41a0d009900010b82a800022d50000282a8306a00014000000000000000aaaa00aaaaaa00aa0000b7b55aa005506a83500006400067b0000000000101001800004040220020000aaaa00aaaaaa000220a0000c1aaaaa80000000131e000a20e070000000000c00000155555554015401541aaa0d540000000149aaadec1c0e00000000019ec000000400110010100180000401b0015555555401540004401a83000094aa001e0030703060c01001e00030000800762acc804ccc8040350600012954003c780055030740000a0000000000000000ab3201334b4a000d41800052adeea8022740ea0740000a8000cf60000000004003c04006000010101100100002acc804cd2d280009003060c180001b268d36a3260e060c183a0000371b81c0c183800000000000000002f1781c0e002e5e4b979aa00 24 16777215 10 1023
def hc_56_12 : Nat → Nat := unpackHintV5 0x91b629198cf2193cf40b33a7c3698edb55dcae843782ed6ace1ccfcae984cd6adf751579e28a31e1133298a2b5d841321c7aa3e0db2d119cacd2f5a1e59b280a1c8d1169681f19dc330d945e93c0a2ed20fd2461754281a8a10001a8 0xa0008c1870e8c1870e4d438000000050004955000000800080000014b4aab3201320000f50e3c1870e3c1870e000000012d55555440128ff6a3c7d4cab41c78f0e0000ab4b4b3201333201350e4c1870e4c1870e000000012d5555544007b87aad43e275513aaa0f503a08003d8808000000000402ad2d2cc804cd2d2802aaaaa97061c397061c38880b1602c582c0eab1baaa091140d8f00e0700211555555551a82aaa280aa8aa5c1870e5c1870e2202c580b160b03aacba3f41e2f0b09114140381c0083e2aaa4d5550554553801350e4c1870e4c1870e2130262c098b00e4d4993264e264e0e1c04f6a0a87038000aa4c9a9350ea0a8a7154000155543870e0c3830e1c00015543c1e0000000000000000155540155555401540001543870e1c004f600000000201c0060000040000aaaa00aa000220a000a80a0000000000ab0cda3a19b4703060c18008000000000002aaaaaaa802a80003506009b36aaaa346aa04006d6060c0183440f600aaaa028306aaa0c3aa80000001ec006a0d5555418355550001aad55954183060c00183070307082007b0000000000555555550055555500504555360c3875e0c387110562c0d8b1581d55550f1b8d84884c98372601c0e0041b662aaaaaaaa0aa8a2822aa8306aaa220bc582f160301aaaaad4d4122070e1400c0600442aaaaaaaa0aa8a00835541aa82822c44060365565581deeaa09655555a555581d0b00aa943a809ec180c0088a08382aaaaaaaa0aaaaaa8a2aa822ad2a8880c0618c586316aa0e60e1d555b84a220c06070e00c180040715555555505545005060d555541aaaaa0d5506ab502822c4401830062c06034daab2a83061c183a81dedb84a1d404f60c38030600c0600407155555555555550554514001561830e1e1830e1c000000015014003cde000000000000000555555550055004055361cd870000581ec005540500038b161c20000000000005555550055000106aa875500000000516aaaaa2c5aaaa870e2c18b061c384a6d5569543cde03d810020801ec000000000015555555401555554010154d87461c0000000556575504000000000040aaaaaa00aa00a000aa8c1870e8c1870e000000002a00a154002001300000000001555555540154010154d87461c000000542038f1e1c015555540154041aaa1d54000000016555bdaad510028f555a55547fb0e3c7870000555555550055550106aa87550000000059556956a8800f6b2aaaad2aaac1ea07410020801ec000000000805555555500555555000106aa875505045888075559543870526a027b0e070001555555550554503a870000264d549930e1c3830e0c3870000264d6261e0e1c3c000000000000000002a8743a008d3a9b4eb3200aa0000ab540000000000aaaa00aa001d438000135261c3870e00000000004d49870e1c380274e9d3800750e00004d49870e1c3800009ec0000002601c0060000040000aa1d0e802753a00008270000515500000000000557e6dfcfcdbf8383061c000000000000015555555401540155554000000000041831fec1830e1d55060d40154383061c3870e1d587001e3c78f5555555005555555555000f602000000021d506a8743aaa1d550554383061c3870f07561e005657a8001ec060030000004000555555550055555500 23 8388607 9 511
def hc_56_13 : Nat → Nat := unpackHintV5 0xad0deaaadc8ca6c905a1b5459c1d6697c5169339238fccdb8a09718471668019167ba91c783cdb7279716c418e66098e5fd18e59998e57908253e4eb4ea550480da63dfe84392d3432e1932e053726c9cf20619a1979ba0e56c909693b00025a 0xc1aa83f60c1835441603038071601c3cb5555555005ee1eab507a81d41e0f5507aaa17001c40e03038700e1c00222880f41c1566699a0f2c0ccd2d28c070e1c380005555000000000055550055002a0d507ec004172d08f1eaaa8f76aa0c18306000083c04404406030022215554507870e000155544003c98f47a3c9870eec18f061c380000000000000000010101155540155535204400c383507ed41835441600c5803060301cb5555555050f51e0c1831e0c783060c183062c05852ad2d2ccc0cccca83f6aaaa1d110181c1160aab54accb412aa1c1830eaa347a8b00e14aaaaaaaa82aaaaaa8355507ec4141458b110180d955956aa8251eaabb55060c1831602c29555555550555541ac0d65a10580c0e0b05cb55555050f51e1c1830e3c78f1e2c03850306aa0fd83060d510580c0e01c58070f2d5555554143d4787060c3870e1c7871e1c38b00e14ab334cd079606666478f1e3d478f063c38f063c3882c058b0162c160b96a8a0aaa0a51fed478f5478f1e3c580b0a55a5a59981999955110582d56aa82547fb551e3c78f1602c29543aa0d51600ac08a8f555550555555555541aaa1d5414116220b05ac0aa0ab55412a3d5547fb1e3c78f1602c29555555550555547a8f10582c172d554143d61e3c78f1602c287ac8d1a3462c05d52d0f51e20b0582e5aaa82878f551fec78f1e3c580b0a1e3c78f0e3c18f063c38b16002c5d0452aab330333334cd0f94187061c38f0e8743870e1c382c1603038071601c3d55554505050f1e3c783063fd83061c383060c58070aaaaaa9a982aaaa060c1830582c0603aaaaa0a1e3c78f060c7fb060c1831602c2818f06834183060c18316000c1d045030e0eaaaa0aaaaaa6a41830683418f060c183060c182c1600c1803160301d55054555050f1e3c783061c183060c1831fec580b0aaaa9a9aa82aaaa061c1870582c0607aaaaa0a1e3c78f0e1c183060c7fb1601c2838f0e8743870e1c38716001c3d04503060eaaaa0aaaaaa6a4160b0582eaaaa828580b0aaaaa82aaaa0582c160baaaaa00bdc4e66a0f503a85c00000445114155550555535250a0000000c183106000000008cda3919b47135260c18306000000000000002c5a8b16aaa0d06800b45a000035060c183060c180000000351fed478f060d06a830600003d478f1e3c7a31e0c18306003c78f1eaa2c5a2c5a0d06800b45a2d16800d4183060c183060c180000001ec0060c7aa83060c783260c183060c983060c1830001935264c99389a32703060c18003060e068c1c07b10100000000060002a8b16a2c5a8341a000c1a8316a2d16802aaa97061c397061c3aa80b1602c58882c0f4aaaab5504a0a0881c0e004426d55543aaa0aac8a2829311830e1cd830e1c9a870362c118b10988c0e4c993264d6261e371b091a0a04c40e070020db311a9b5550ea355833229c5058060c183060c18306a0c118b0462c4260301d5554b55414828420301801114b4aab330332300035060c183060c183062130262c098b0180e5aaaaa077baa8287aad43e275513aaa0742c02aa13da82a0c0600445041c15696966606669694601a83062a8030740e060c42603018231608c593581c0e0e1e8387a4610310180c500680040715418741834b9752e5d4b833221c0078f551fec18306a0d068306a0c183060c1838060c41e0f160f160f0780c063d61e3e1e6e0e0781c0e4612a8f1e8f2e8f47a0d069706640060d5418f060c183064c183060c1831e0c9835060c183060c183075084c098b0262c01830062c060326b132744cdd03061c183a81ded18427b50541830e00c180c0180c0080e2a9326a4cba832ea0c1a830e8306970664438a0008c1870e8c1870e4d4380000000000513183c8e000000000000000162d458b5550e8b4026400026a1c9830e1c9830e1c0000000058f55162c58f164c58b162c593162c58b161c38b062c1870e11358993a266e83c8e03d810007b1010000000000015458b5162d43a2d00162d458b59900 24 16777215 10 1023
def hc_56_14 : Nat → Nat := unpackHintV5 0xa49ce29ef9699bc4cd9818eb9448f48de19a8a80d885a9367e5dd37a84f67481817065076a957465e52c6165205d8cf658c532509a0b49b9b843858d3c31d53499e63009242ccccf2809312059ec1be51d1561a11111140a41b404ed5500013b 0xa0000c180028800000002aad2ad5000000000000002aaaaaaa802a802aa0d5541fb0000105800032ab2ad505ec004001100101001800c002000000000000000015555555401540440001a80d66a0000000078001c00460000000000000ab33320000000d4060c0014000000000025aaaaaa8800000000000001566696940264001a80d65a00000096aaaa0bd8003c0400e00301f807c0020000000000000001835507ec18306a800000004b5555541ea0bd8003c0400e00300381c000e0000400000000000000002accd3341e500990120000000aaaa0bd8004c0400e0030008000000000000aaaa00aa012000106830600000001c38280000013581c0e00162e8183a000000000000550683400b9752e5d6640018706a0fda8306a80803c00060000c0600300180000000004d6060e819ba07038058005ec00000000000000001541835065d41a0d0b800804c802280000280000070e0000aa1e07000b16aaa000000000000aaaa00aaaaaa00a0fdaaaa8740440426003003800800220000000002a8781cac9b50160017b0000000000000000055555555100100550054418000028000306000000aa0e070010b16aaa0000000000000aaaa00aaaaaa00aa8355507ec00440040101001800c0000000004daab2a8381c02c002f600000000000000000aaaaaaaa200200aa000d40000000060c001400009ac1e07000b1741c3d00000000000002a8741a00bcfaaf3eb32000d406a4d81870001e130003800070380000001b3d80000000000000aa1d069b4da000000aaaa222130181c03e1f02592c002a880bd800002a8741a1d13e0002804c8003501a935061c04401e13001801c03e04b000000009ac1e072f97c02c002f60000000000000000c1aa83f60c1835404401e13001801c000e0001c0e000000705800004d60f03838783d070e6e8058005ec00000000000000001543a0d0e1d0ec1c3a95c004026402a26a4c983261c983261c04401e130011000582c0060070000982c0000005bdad2b5410005ec00000000000000001569696648004026401541aaa1d540044004160220213001801c0000416000002caab7baa37040014000000000000000000aaaaaaaa200200aaa000c3830e1c98743a1c3d40201300180c00e07000180c000e07000000382c0000aaabdc0ea07040017b00000000000000000aaaaaa9a9200100aa00060c1a0d064c183060ea010098000c06000303800c060030380000000c16000551ba0740eaaf610005ec000000000000000002aaa6a6aa8800402aa800bad7564d54f93561cb832e0cf870000000096aaa5a90000000000000059666000026a4000040260030038000015402c002f6000000000000154000805500070eab52a839a5a10580b1600c180c072d415155044c4463c118f00603002215696966606646018706a0fda8306a882c018b0060c060396aaaaaaa00bdc3e26ab350381d540eaa81d40ea17004c4060c01c30060300222880f43c156969666066696946106aaaaaa1c3d550880c0e02c582aad5282a40a2070181c38070e00110aaaaaaaa82aa28a0fdaaaa87444060704582aad52b32d005ed55560f07a81c0e9556965585c02207018a08700088a203d0705555555541555555145555060eaa95414058b110180d514156aa0518f0463c110180c0088555555554155145541aaa83f620a0a2c58880c06caacab554017b59555569626aaab0383d40e0750b8061828220301801114407a0555555554155555514060d541fb818355a5aa910580c0e02c58070f2d5541514017b83881c06070e01c3800442accd2d2c0cc8c03581acb420b0181c160b96aaaaa00bdc3d56a0f503aa5d47ea17001c40e030381c0088a203d070 24 16777215 10 1023
def hc_56_15 : Nat → Nat := unpackHintV5 0xbc0197b878e2b2897cad215aa5cdd5a2fcb49f44ee9b50fd97d4df9305348fa4d88a7d4a844d8c796ab9748d376d19dd67f54960b9cf5a419e532dc547aee03e026b366de52bd2a72136a71de0d518017812a5570f08e708f9840570e200015c 0x2a89ec140607010ea83545aab5503bdc12b32aaaac1e85c2c02295569655a910380c0050438445041c1555505555555555951455550000e1d5400000000002956a000000000000001555555540154001018001d5400013d8010012ad540ef60010000052c4d55560f042c0002a0000000000000000100155550055555654001a870513dc030382ac070e0c183061c3a804cb5540ef74155550710380c000e1c0387088559981a5a5991806a1c144f60303801c383060c1870eacb5540ef70555550f55a83d0b00a85c2eaa1755541c40e0300038700e1c222820e0ab33034b4b334cb528c2aaa87060c3aad5552a87060c3870e1c3d52aaaaaaaaa82c06a1c00e03013d8000012c0441550012c044134013400000000000000aa27b050181c043aa0d516aad54c12b32aacac12b32caa20701800a08708888040600075500004f6004004ab550004004ab2a012a000000000000000d438289ec060700387060c1830e1d596aaa82aaaa969a82aaaa9a0e207018001c38070e111100c3830e1c1830f5555555555555541c3870e1c1830e1c3870f55540c3830e1c1830f555503bdd544e66a0f42e22aa0e1c3870e0c1870e1c387aaa883c5555555555354d5070eaa2c3835060d060d4183105850038060326b0328281c0e061131278f09e3c0180c0085e2a8b16a2c5a8341a2c199116030e0d41fb5060d51058031600c180c062c7aa8b160c183060c18b160c18b060c183060c183060c183a89ac0c1d033740e0705ec280262030600e18030180b0be0b1602c7842f1541835062d41a0d1608b16a2c5acc88b1555554387060c1830e1c4406070a05550f03914150910380c0e1c038700080e2aaaaaaaa0aa8a283f6aaaa1d110181c1160aaaaa1c383060c1870eaaa2c5a8b55a9543c0e564da85ec280440e031410e00700e070e01c3840715555555505555554515554183060c183060d5414284406030545550703922a78f09e3c110180c0584f2178aaaaaaaa82aa28aa8355507ec14116220301a8b55555162d5554183060c183060ea4daab2a8381c17b0a01860a0880c0602c0162c05842f15555555505555554501a87060d545835060c1830e882c06070a00f13583c0e0e505070083881c06070e01c3801c03901c550e83458b5162d45833221c06a1c1a8b5061c416030382c162c7aa8b161c383060c1870e2e58b162cf8b17513583c0e5f2f82f61400710380c0e0700e01c0e1c0387080e0306aa0fd83060d510580c0e01c38b160700e1c58f55162c387060c1830e1c3870e1c387162c387161c3870f513583c0e0e1e839ba0bd85001c40e03038700e1c00e01c0e1c0387080e2a8741a1c3a1d838716a2c1162d458b59910e544d4993064c393064c3882c058b162c2602c582c162c78b26aa2d162c01545a02c58b162c38b062c18b0f52ded695aa0bd85004c4264c09b705e230160dc162c058f082055a5a59981a5a599185506aa875510505162c44160b5055005162d45935555161c583160c587a96555bdd505ec2805b828222f1180b06e0b1602db8442aaaaaaaa0aaaaaa8a030e0c387261d0e870f502c1603038070e2c581c0387164c5a2d162c3870e1c183060c5830e1c00183060c38300e1c387aaaaaf703a81c17b0a00381c0e03038700e1c00e01c0e1c0387088aaaaaa9a982a9a9aa28060c1a0d064c183060ea0582c0600c1803062c580c062c98b45a2c5830600c18306000c1870e0c18b0e0c183060c1830755540e81d55ec2f6140231b80db8030600c0602c1b82c580b6e1115553535550553535450a83541fb00478f55547b755060c1830036b0020f0000580f555511e1c380000f263d1e8f261c3b7063c1870e00003e6f079bc00000000000000b001982e170785c002c5c8b17354002c0582c160b164c5a2d162c587160c583161eaaa0bd8500000b0058b016100b85c2e170b0858b9162e6a88581c38000a0c0140000000025aaaaaa8000000000000015696966402640018706a0fda8306a800000004b55555505ec001e02003018000c0001800c002000000000000000015696966402640480011401403870000000000055aa5a550000000000000055555555005500507ed55543a00000000ab54acca17b00101003800c044004000080000000000000000555555550055011000 24 16777215 10 1023
def hc_56_16 : Nat → Nat := unpackHintV5 0xbd821cb7518cb035c7ac5cf6a69d70a24d149c3d8498b4e293455c8ed51c89e93b8281da7cc96e783d23738d2c6bd1ef670d3162991d5b0de35734f65115884aad9a4296063d455431170c25dacf1d36291571f10e55c70a6cfa046183000118 0x5541835550e1d554183555550e1d43935555a915116aa1c1830e1c0e2c381c3acaab7babdc0ea075521d15154383061c3870e070e1c0e1c387aa555555555555555555506a1cf9355464e96691a8b0e0c187560b167c162e5aaaa696a83a870e0c1870e1c381c38703870e1ea96583b341e999a999061c1870e4c3a1d0e1ea0e0c1870e07161c0e1ea077b060e81830741c3870e1c1830e1c38703870e070e1c3c1c3d41c3c0e0e1e43cd550783c2c5aad03506000c18000000004b050045000000000000002ad2d2cc804c8002c06a0c00603013d8000012c044103bdd50043d568002820081c0001500000000000000002a80904c804cd2d2802a8880c06a80aaa0c1a8b16014ab3504b4aa880c06002f1e0bc78442aaaa0aaaaaa8a2a89ec1406030106a83545aab03bdd5412b32aaaac0e858052aad2cab5220301800a0c7088a09f82aaaa0aaaaaaaaaa8a2aaa8306000aa000000000014ab1400000000000000aaaaaaaa00aa00080c0006aa00009ec00800956077baa000800002955560700005400000000000000002002aaaa00aaaaaa000d418900c062c0c183060c1a143d6a0742c2a471310180c00461b28878ab3303334d2300d418900c060ab00c183060c18306a0132d5550555544c4060300118f0463c221566606969664601a830513d80c06003060c183060c1ab2d03bdd54155542ea87aad40e8580542e17550baaaa26203018002c580b8e111410f0559981a5a599a5a518060c1831f83c0603aaaa821e4c7a3d1e4c180c1830603c5803b1741141c0e030183060070a22aaaaaa0aaaa6a4a0183060c183060eaa077baaaa89ccd40e85c45541c383060c1870f555145555555554d4d5035060c1aa8b1614000000000004d6071070e00000000000000000aa0d06972ea5cba804c8002c060d5418f0000600c180035060030185427b00000000060b0026b0106c01830e0c1d40ef6000000000000000000aa02170065d41835065d060d0099005550455a551450180c01830162d541cc1c3aaa8b0910180c563c158f0008562aaaaaaaa0aa8a2ad0000031e3c183060c183071f383060c180030e0e077b371b84183c0006020ad5555455555419355a84f60a00c1803160301808355506835541aa0d516aa83061c183a81dec584ac9b544070c0183006030014108562aaaaaaaaa0aaaaaa8a2aaaaa850000027b00000055071070e00000000000000000aaaaaaaa00aa00080306000000d555406000355a800013d80000006c009541830e0c1d40ef60000000000000000002002aaaaaaaaa00aa000d41831540183a0703062030180c01a0a4d607038387a161e85844c40603118f0463c002118aa0c5a0c1a2c5a8b16a2c199116030683418f07ec1a83a840603060c060c58b0180c5260c183060c183161c183060c183066fda02c9880c780c180c06001b0d8aa0c5a0c1a0c5a0c1a2c1168b44580d47d0000031e3c183060c183071f183060c180030e0e077b371b898000c0600c0582316834383168b4160c1a835418f064c1a83a8144f6030060c0183162c060300183160c183060c183060c18b160c18b0e0c183060c18306a93581830e0c1d40ef62c2162e1742c59ba262031e00c1803018002c580b08462a8316a0c1a831683068b0458b5162d66445950306a0d5063c193060c1830683554187061c1a83060c193061c183060c183a89a932613164c262c180c183018b060c1835bdad2b03a07557baa26a1c9930e136e1c063c180c1830183060d587561ea956969696969a6669a66555060d5555418755555064d4183555061d56a45445aa8301830603160c18306b2aad40e81d55eea8dca34545506dc180c1830183060d587561ea8dcaaaaaaaaaaaaaaaaaaa3c98f47a3c983060c1d00381843078371603c580c063e6f070e01c3c0381cdc20e070383060c180c1830003c070ecc1f17879792e5e41c0e2e15501e0e5c060c1a0d064c183060ea0603060c062c183060e81830e0c1d40ef741c3830603060c060c1830e1e0f178bc0cbc830720cbc0c1c5e2f55078bc2c5aad0350e01c3800200000004b050054000000000000002ad2d2cc804c8002c06a1c00e03013d8000012c04415503bd8043e26ab34001410041e0000a80000000000000001540482640266996a500550410181d5014387555162c02956a609695510380c000e1c038708855554155555514 24 16777215 10 1023
def hc_56_17 : Nat → Nat := unpackHintV5 0xb20cc6ae34f6a8417da3553b9ff4d898c1cd94b5038ef5708a412d85ad257da203785d517560bf7164ff6b5d826699315f15e15b3cf654cd9c4f79554829d442b95c3f14e93a75283301dd2e4d2d26edd82350e71d31881691a80b3ed50002cf 0xaaaab7b55aaaa550ea83545a22b2ab54a8a2aaaaaaaaaaaaa82802aaaa870e00000000a24c78000781c00000000000000aaaaaaaa00aa00aa0d550eaa2000880080801c00001058000cf6000293555bd8781c041b00000000000000000005555555501100055005555550545110500e1c0680c1aa931f40c1d0381c2c244463c118f00603002118aaaaaaaa82aa28a0d418023c7aaaa3d1aa800023d5bd9b87c83c0040180301eaaaa2aa0d5506aa0a08b11019ec0183506aaaaa0c1aaaa800c383526aab7b070385840c1d03374a3050440603000183006108c5555555541555555145505005060d540000060000a8c0e07131e00000000000000000aaaaaaaa00aa00a800880080202835541aa8030000000000067b526aab7b0d8010381c000000000000000000aaaaaa2002aa00aa00aaaaaaa8a0220a00c180c55498fa0e1e83c0e16122070e01c38070180101c5555555541551455550eaa2a28bf62203155543875554dfb2061c180b438a2207018001c0e2aaaaaaa0aa8a2a835543aa882828b162200c180cf6a1d5555438750e4d55540060c1a93555bd8781c2c20e1e0f41c39ba438282207018001c38070e101c55555555415555551450541e0c387460c3875506e2c078b111181c7930464e1543c8e6e12a8a81c0e0040f662aaaaaaaa0aa8a2a835543aaa2a22d5549aaadeea945455a5555555555555506a1c98f0000e1eaa8000180000129540a0000000000000000ab334b4a0132000d4383c0400e0000cf600052adeea80880022741e0f50381d000504000000a80000000000000002acc8090004cd2d2800350620b0801931eaa0c1d405070e0152d55054b524c4060300118f0463c221566606969664601a8310580cf600c1831eaa0c1800c383a55bdd541555544e81d40ea170b008a81c0eaa07552a4c406030001830063c22282860ab33034b4b334b4a300004c7835060c1d55000000004a0002d5000000000000002ad2d2cc804c80008803c260d41803000000067ba55bd9001550044e0800002a0707a81c0e82160000a80000000000000002a9000cc804cd2d2800350e20b0060c067b898f550e1c2aa018300aa55bdd55054b521c40e0300038700e1c221566606969664601a8710580306033d871eaa1c3800c183a55bdd541555544e83d40ea160150783d541eaa543881c0600070e01c38445041c15666069696669694607a8710790c0f2d55043c9820f261c3bb063c1870e3c5803b16a1123c9884c381c00a22a95666066696949a09a9326a4e956f7555513a0f503a85c452a4d49d55450ab3333334b4b32a2c5a870e14000d438000000000030604d620700000000000000233ea8cfaaa8741a0132000b01a8700380c038f550e1c00038700e01509ec00000000026b0106c2077b060e818306000000000000000000aa025700e1d068d0e1d43a350099005405555a55110162c03870181d555418356070b091038700e1c0380c0080e2aaaaaaaa0aa8a2aaaaad427b050181c038b00e1c043aa0d50e875543aaa8b556077b060e8183062c2564daa2070181c38070e000a087080e2aaaaaaaaa0aaaaaa8a2aaaaa8005000000002a830600040e0000000000000055555555005500040600075500e000001c3aaaad400009ec00000036004ab03bd830740c18300000000000000000010015555555550055000550e0350e0c1d03061e103828074060726b0b0740c1d078183070b083881c38070e01c060040715458b5162d4387418b45833221c06a1c38f550e1ea0513d80c0e01c58070e0070e1c383060c18b061c3870e1c3870e2c5870e2c3870e1d526b40ef60c1d03060c5842c5d0b3741c40e03038700e1c00038700e1c2038aa1c3a0c5a1c3a8716a2c1162d458b59910e540d4383061c3870e0c983061c3871e1c9aa874387060c183550e8343870e1ea26a4c984c593098b0e0c1870e07161c0e1d6f6b4ad5ee07503aa83a870e1c381c3870383061c3870e070e1c0e1c387aa55a5a5a69a5a59996599 24 16777215 10 1023
def hc_56_18 : Nat → Nat := unpackHintV5 0xb279b1ab25d5a58967a08d3f9ca8f997714e8fe5e38805f8833d327f50fb7845c372158c676aab6291365b69ca5529904a22c24549363f198c3a553134a56c3001292c78e227095c22f5051c59a718d0e2132d690f84ea0b61090499b2000126 0x3060c180000f263d1e8f26000000003e38f060c183008e3e1ece3c0000030000060002c58b160c18306002c58b458b168b162c5800b0183060c160b019ec0183064c1a0d060c0061c183060c18b0160c183818380180c00060c01800b162c583060c18b0160c183418b068b162c582c588c99b51a6c983060c1830740c183800000000dc6e001c0c1838000000000000000bc5e2e5e4b9790703802a800040260c1830600c00000019ec002060c183000000000000002e2cb8b0b80083060c18017165c58026cdaa9030e0c05a87645824d1e6d54387162c387560ea8703881c0e1d555547931ea6cd9030e0c0593261e838b016a935366c387162c3870ea870e1e0e070381c0e1c5a2d168b458b061c1870582c0607364d36930a0707018300160cdc6e0e1e0707162c2161c3870e070380c000e1c038708381c382e170781c2c2162e458b985d0b88380c3830e0b0580306033d87261d0e870e003060c383061c580b0e1c3c1c3c1c0e07018001c38070e01c0e0b162c587060c38b0161c387438b0e8b162c581c3814000c1870e0c1870e0d438000000000280b0781c00000000000000bcfaaf3eaaa1d06804c803030e0c3aa8f263c9d3a64cf9f1e4c7875400017db2d500002aa934fa1d0060a81a87060c387060c3870780803c2600130000e00000000cf60002ded6950f03808360000000000000000000aa4c9a93aea1d068080013200b4a0e06030600c18350601c380b0e20b0180c1b4b40d6070385848c78231e04c406030021182c5a8b16aaa0d068b06644595035060c183060c1830620b0162c058b019ec0183063d54183063c193060c183064c183060c1800c3835bdad2a0e070b08183a066e89884c98138600c0600030600c7842315458b5162d41a0d1608306a0c5acc88b01a83000a060c183060c1830000000019a07039400000000000000001541a0d2e5d4b975009900a80401e00130001e1306a0c183060c183060c018000000000033daded6950d8010381c000000000000000000aa4c9a932ea17001068340264016943c0c1803061c06a1c01830160c41603038769683aac1e070b0838700e1c03881c0600407058b5162d5543a0d160cc8872a06a1c1830e1c1830e1c41602c580b1600c180cf61c78726aa1d0e1c38f0e4c3870e1c3930e1c3870e003060d6f6b4a8781c2c20e1e839ba0e2070e01c3807018001c38070e101c55162d458b50e8345821c3a8716b3221c5045552e0c3872e0c387110162c058b0581d555142aa091078f0500e0700121551eaaa0aa8a8f28107c3d43b7061c38f061c3883c078b06e2c86071eb3761403cde6e10f262131e4c9870380103d98aadd47a875860cc88f15555547830e1c7830e1c44058b0162c16075555a5aa82441e3c7870380108aaa0a8aa82aa2a8aaaaaa5c19f0e5c1ab0eaaac162cf82c5d7165c5aaaaaad5552aab3e1f4e572e5d38b4e2ea955526aaaaaaacaab5135264c1930e4c1930e4d4993098b261316b7b5a56a89a93264c984c994aa4c9a935559955500500e1d5540000000116a8280000000000000001555555540154015440400e0000cf60002ded56a8088001543aa0d4001410000006400000000000000015554044001555554015444406aaaaa80a1c3802aad54155552203018008c78231e110aaaa82aaaaaa28aa22033d80306aaaa0030e0d6f6ab55055554aa0d506a8b00541a0d5506aab2880c0600030600e38442830c15555055555555554501401541835550000000045000aaa00000000000000555555550055000110109aa803000000067b5bdaa900155002a0800002a0d506a0000c80000000000000002a8800aa802aaaaa802a8880c5554a8184aa1d55160adf510380c000e0714438aaaa82aaaaa28aa2203155550554060c015956aa0aaaa910380c000e1c03870885555415555551455110060c067b55550018306b7b55aa82aaa83d4aa1d506a8b00543a1d550eaab2881c0600070e01c38442821c15555055555555554515444860755aa8245500e1dd831e0c3871e2c01d8ba08a4540e07002889555554155555514 24 16777215 10 1023
def hc_56_19 : Nat → Nat := unpackHintV5 0xa011ef97aa1a91e57189a61083ad7e7f5d1477d1e373d4ff6ec1456a5d196605166284e05e4d0e59095154ad1750052a4c84e048550c4510d13fd94e391daf3409452e357528856c2469071f3d4b1b40ff163d4111cd1c0c6d580551c7000154 0x350e0d45a830e20b0181c058b0f9ec58f55162c387506870e00b162c9a930e0c1877e7cfbf1602c58b170b5e2e0e2070181c0e00070e070387161c0381c06a1c1a93541830e4c7aa931e1c3a834387a89a930e0c1877e7cfbf5e2f16bc5e2c9ac1e0747ef67cfd1f3e7d7cbe0ea1c383061c3870e1c3870e070e1c0e1c387838781ac0d65a26a4c383061cf9f3e7e5aaa3f7baaaa81aad4d40d63f42e22aa0ea1c383061c3870e1c3870e1eaaa20f00d438306aa4c1ad03061d06a4d5060c3d44d4987060c39f0f8b3e1f167cf9f3e4d60f038f9f5e7cfd47ef6be5f0750e1c1830e1c38703870e070e1c3870e1c3c1c3c0d606b2d135261c1830f2cf9f7f2d55551fbdd543d56a0f07599a97d0b88aa83a870e0c1870e1c3870e1c387aaa883c0350e0d49a830e4d4987060c3935261c1830e1d4387060c3870e1c3870e1c3870e1c38306aa0fd83060d526a4c383061c381c587038726a4c383061c3870f070f0750e1c1830e1c38703870e070e1c3870e1c3aa8741a1c3a1d0e1d5543a1d5555552e0cf872e0cf8700000000550500aa00000000000000554daaa002b2002c5aa93164d49a3066c39b068c3800000001326b1300dc6e0000000000000005546a6d57a8d0099005555552e0cd872e0cd8700000000558dd5400000000000000aa0a8002aa34019f62a802aaaaa97067c397072c3800000002acba3f55e2f000000000000002aa80aa8002aa0000b09a9300380c04f60000013526040000000000000002a8080a00a00aa0000000a1c38f063c1870e00002a1e3700280000000003c001e2aaa802aaaaa802a8882c16a80a6c3af066c1af0e2c5800b16aaa6e370b1610b551179dc006e06d9841b1555505555554515400000140387360cd830e1c00015143c6e001e3c780000000000002aaa802aaaaa802a80000000070f9c18f061c380002a878e1c0238f87b38f0020000002000aaaa00aaaaaa008aa27b050582c043aa0d516aa8b016acaa200028200aaaa82aaaaaa28aaaa6c1af0ebc19b0eaa0000000002aa9b8dc0000000000000000aaaaaaaa00aa00080c000eaa00009ec000025500000000000000100155550055001ea1c000014003871e0c7830e1c00007a41e37000b16000000f0000078003c550e8b40058b5162d664009a9310582c160aa4c361d183360d187500169326b13371b858b0858b162c988bc460023036cc20d8aa2d168b0458b5162d616c2d1160f50e00003c7800070e6c19b061c380000b078dc003c78f0000000000000550e8b40058b5162d664007a87000000000e1f1831e0c38700001ea3c3c70e011c7c3d9c7826000000002c001543a2d00162d458b5168b400584d498289ec160b00587160c583161d526a4c580b162c5c2c5c4c4000162c05802a8b45a2c1162d458b5168b44580d439f1eaa7c7870f554000000012d540a0000000000000000ab331b80006a4000187061cd939e9b67930e1e81c1c3800000001b8dc1c3c0e0e000000000000000050781cae4dc8055000350e6c7aa9b1e1c3acd000000004b5546e000000000000005599050000a290006a1cf9355a64c387506870e00000000b0781d4e8fd0000000000000028b50e1d06870000245c800030e0c384c0400e0000cf600007060c38100000000000000002c587060c38080002c58003060c180000f1e3d1e8f1e001400003e1f1038001830000001800003c001e0b85c0e07000b1722c5cd50003060c182c1603019b268d36a3260e0605070e002c39b8dc0e060c1c2c5842c183068c0180c004606d9841b05c2e070385842c5c8b1735442c060c18300001e3cda6d1e3c00183000001f1b81c4003c78f0000000000000170b81c0e00162e458b9aa00 24 16777215 10 1023
def hc_56_20 : Nat → Nat := unpackHintV5 0x7595b7db8be99c86a6fd8ee585dd5a423273454fe40aa0420185790abedaf5c99268e2d114f4a140488e2d0e22be95d59c22026a2667682629a800131 0xe1d5438706a0c183070307420f01e2c078b0180c7ac0c18030700e071b083881c787060c06030080e1c78aa3c7a8f2ea0d069706644381c3aa930e0d418341cb44d49a30d8b3623160c183064c9ac4c183060e060c1c6e371350e8c386d9870183060d5870f07372a972ea5cba8341a5d2ecc874ba3c782070e0d4183060c060c041e06c581b160301875878f1e0e071b083880c18030600c060041c0e1c552e5d4b97506834b833221c0e1c1038706a0c1a0c5010780f1610c580c063d47c71f0f671e060c1838610c39310383060c180c183000381c552e5d4797506834b825d2e81d0e5c061c1a83f6a0c1aa4d4983018b0603060c183064d4983060e060e060c18326a1c18306030603060c1870e1c3aa8306a0cba8341a5d2e974ba1d2eaaaaaa870f40e0e1d54383061d586c59b158b5550e1e070754dc6e550e0c1870e1c381c38703870e1e0e1e555555555555555507ed55543aaa1c1830e88b45550e0c187565554383061d510e81c3870e1c3870eaaaaaaaaaaaaaaaaaa0c1d03060e5501e2c078b110180d5141541c0e361071e1d10180c0040e1c78aaaaaaaa82aa28aaaa0c1d03060e553623168c362d54183060d55550703060e371b8db30e230e2a83060c1ab0e1e0e6e5555555555555555054060c0183062a81b1606c58880c063c78f5507038d84aa0a4220301801c56507f6070e4aaaaaaaa82aa28a0a80c1803060c550862c078b110180c7b38f471f2a83060c1c3086aa2a0301830600700e0703aaaaaaaaa0aa8a8aaa0d5541fb45445aa83060c1aaacaa0c18306a2a2a83060c1870e1c3aaaaaaaaaaaaaaaaaaaaad2aaa87060c39f058b3e0b16ab4d4aab54aa1c1830e1c38703870e070e1c3d52aaaa6d555595506a1c18355260d681c1d26a4c383061d186c59b118b264d6261c3c0e0e1c387371b83a870e0c1870e1c381c38703870e1e0e1c3879543a0d46a6d55aad990e8755554383061d56aaa954383061c3870e1ea95555555555555554387555550e0c187360b166c162d55aa37552a87060c3870e1c0e1c381c3870f54aaaa0d5550e8755567daaaaaaaaaaaaaaaaa1c1830f2c162cf82c5aa8781d2e8fd0ba550e0c1870e1c381c38703870e1e0e1e555543aa0d50eaaaaaaa1d50ea0d406a4d41870780801c04016000007cf6000135261c1830efcf9f96042f0000000000000000006a1c1a8b5061c416030387cf602c58b06aa0c1874183060d40162c5935261c1830e7cf9f3e2c058b162e16bc5c1c40e030381c000e1c038700e0701a8020030018083526a0c380b000000003e7b26a4c383061c5e0047cf9f3e00000000000000000d4383516a0c3882c06070581c7a8f0e0c18700e1c58071ea3c383061df9f3efc580b1e3c78f 23 8388607 10 1023
def nh_56 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_56_20 (Nat.sub p 640)) (hc_56_19 (Nat.sub p 608)) (Nat.blt p 640)) (hc_56_18 (Nat.sub p 576)) (Nat.blt p 608)) (Bool.rec (Bool.rec (hc_56_17 (Nat.sub p 544)) (hc_56_16 (Nat.sub p 512)) (Nat.blt p 544)) (hc_56_15 (Nat.sub p 480)) (Nat.blt p 512)) (Nat.blt p 576)) (Bool.rec (Bool.rec (Bool.rec (hc_56_14 (Nat.sub p 448)) (hc_56_13 (Nat.sub p 416)) (Nat.blt p 448)) (hc_56_12 (Nat.sub p 384)) (Nat.blt p 416)) (Bool.rec (hc_56_11 (Nat.sub p 352)) (hc_56_10 (Nat.sub p 320)) (Nat.blt p 352)) (Nat.blt p 384)) (Nat.blt p 480)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_56_9 (Nat.sub p 288)) (hc_56_8 (Nat.sub p 256)) (Nat.blt p 288)) (hc_56_7 (Nat.sub p 224)) (Nat.blt p 256)) (Bool.rec (hc_56_6 (Nat.sub p 192)) (hc_56_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 224)) (Bool.rec (Bool.rec (Bool.rec (hc_56_4 (Nat.sub p 128)) (hc_56_3 (Nat.sub p 96)) (Nat.blt p 128)) (hc_56_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (hc_56_1 (Nat.sub p 32)) (hc_56_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)) (Nat.blt p 320)
def f_56 : Nat → Nat × Nat := unpackForestF 0xa4caed20956914bb481550062fd1c914018b746165a2536d14996892da00c57a1c26cf2916790914224d9e422cf48fe7a4773d2379fc124f48ce7a27f3d13b9e89bcf44ce7908800c539dc2ece8956754bb3a055005afce44f66f46b3823d9bc9a802d6e6d4da00b579ac9ecd08d66947b34135005a9ccc1366348b3224d98c22802d3e6127b2f23597d1ecbc4d4016972e25d005a3cb2dae596c72c235005a1cab1925508b2534f94db2494d2e51ad12534793db2494d0e4d0bb2515592caec94154014bf242548fe2fc8c9123f8b72226c8fe2bc82d12414891fc538fc9280296e3d8f919b4f8e9be4744d6336971c5708cda3c6adf23546919b438ccb680295e314a914c5f8bd2245316e2d4d914c578ad2245314e2924a00a5389e3243adbe256a90eb6b88e3e43ad9e216a90eb6387537c3a99e1d08a00a4f86d324251be194890946b85d3e42519e146890a24484a31c24494014970856880db7c1adb20d26b01b6b82eb8406d9e076d903a3481c9ac06d8e034df01a6780cae80291e014c8fa46f7fd223e91adfd4f8fa4677ed223e918df4050fab5f7d5adbead5df56a6fa02400521be4d91e4adef8354792b5bdcdf1e4acef5b547ac2a3c958de44def22677912fbc895de5acef21350051fbc4991d9adef0254766b5bbc9f1d9aceed3547692a3b4151d9ac600a3b75e343915bdd58b0e456b74e3839159dce8b0e72547382ab9c151c8ac6e426f72133b9097dc84aee404d0051bb8c991acadee22546b2b5b849f1acacedfa546fc2a35958dac250de5676b092b5b17dad8b6d6c576dc2235b14dad2bed695b6b4abb64051ad2a6d694f6b4a5b5a51dad286d612400519b52d91a9268cd34b69c36b34955a54c8cd24b68ab43445719a48ed03646691fb3a9919d248cd23366d2eb34154012becc136004adb2adf19546ac3b4b61d36b249f187496c857061d23b1adf18d4f8c3a3f621be3109f1894d8c412461d1980255d8326cc181860c0a00254d806a8c01345a9b5afcd516a6c6be4645a937af49516a4d6bbc7c5dcbe2d499d754a8b52635cc2ead4915716a8b523f5b92a2dc4916a466b5a6f5ad26ad41140129eb416457db7acc4d15f6d6b217c57db3ac28d161268afb6357c9b00252d536d6ae13454db1aa69bd534d6a9a6755c922a698d5347eaa12454d1980251d512c8a336f53c9a28cdad4c4f8a617c519b3a944d1466c6a3a6a51d3328c4d8012869e56f4f2b3a789bd3c4d69e2674f131a7896d3d2d89e2570049fa74591306de9ba344dc9a260dad352f8983674c91a2644d1306c6981360049da5b1a12d4ca7d56f48d1fa54d31234769404c48d1ba4c8f1246889202448d19a411c1204fa9017c3eab3a3b1a11d0ca7d26f4692e234490fa4d68c4703e933a2a971152487d2634492e224490fa4b683b6f43e3e20edad0d0f883b6742db62111d1096c88403441db1a0d180fa4ae8056f402b3a009b9004c4800353e9269fd59cfa47a7da6f3ed229f41340126e7c1643b9b79ec4d0ee6d67a17c3b9b39e44d0ee6c677a6a3bd331dc4d80126676264376b79d29f0e92f86ed6739d221bb1ace468872244376319c4910dd8b670364374b79bcdf0dd2ce0092f36d321aedbcd94f86bb6735c9b0024acd56d05ad6f34db816b59cd0690681442d635998d20cc488661442d631992d20c92885ac5b2d5b596ad8cb56b65ab432d53796a99cb54ae5aa4f2d4b796a59cbd27c5a94a2e6b39728c4b927a5a9462d41f96c518b507a009272c8a6164510012465824529da794e93ca746e5624529ca7952934a90985393729c9380217c010b65147c289229441108a69e50155229369391f09c4f84e044229279331c0990984523725d2a9145b4928f849245248be1241108a29e474702393e91c9348a26e45b7022ca311449c010ae00853211b79089bc85098422370042780212c80ad040064171b78f95a07c2ca3e064171378f29b87928a2e25d171268ed1805c46e39d681cc320b85bc7048a3816e170ae8cf1806dcf033a7f19d368ce93469ad03416f19c260b84dc646c032146170938ba5b4612d82e93d174938ba1345d04e2e0660042380210c586a82c05410ab18aad90550c82126f14daa08497c508c62814d1091a89ad904d46a2116f129aa094150422be2424d1089a886d20434882194410c1e08449c0107e0083b0fc2a07958c3c4de1e25f0041b8720b039048008330d92a06c15027ac619a640cc3204f1bc314a813c5f0bd3204e5bc2d4a81395f0a92e0541702728e1414609c928020bc0105611b5408c2a02958c216c80a46f079aa03c150148be0e364050b7832d50190a80a15f05dae02851c1506e0a05600413822170110a80082303cb201adbc0d26c0081f0040d812990090c801b6f00d1b00c4980328c0203600c3300205c010260003f 10 11
def ch_56 : Nat → Bool := dagCheckNodeV5 fullMask g_56 ep_56 5 31 bds_56 660 (dagTraceF fullMask rootStock 11 f_56) cur_56 nh_56
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 fullMask g_56 ep_56 5 31 660 bds_56 (dagTraceF fullMask rootStock 11 f_56) (cur_56 0) (nh_56 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_0 : treeBlockF 0 32 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_1 : treeBlockF 32 64 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_2 : treeBlockF 64 96 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_3 : treeBlockF 96 128 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_4 : treeBlockF 128 160 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_5 : treeBlockF 160 192 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_6 : treeBlockF 192 224 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_7 : treeBlockF 224 256 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_8 : treeBlockF 256 288 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_9 : treeBlockF 288 320 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_10 : treeBlockF 320 352 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_11 : treeBlockF 352 384 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_12 : treeBlockF 384 416 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_13 : treeBlockF 416 448 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_14 : treeBlockF 448 480 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_15 : treeBlockF 480 512 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_16 : treeBlockF 512 544 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_17 : treeBlockF 544 576 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_18 : treeBlockF 576 608 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_19 : treeBlockF 608 640 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_20 : treeBlockF 640 660 ch_56 = true := by decide +kernel
theorem nj_56_1 : ∀ i, 0 ≤ i → i < 64 → ch_56 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_56_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_56_1 h1 h2)
theorem nj_56_2 : ∀ i, 0 ≤ i → i < 96 → ch_56 i = true := block_join nj_56_1 (fun _ h1 h2 => treeBlockF_at nb_56_2 h1 h2)
theorem nj_56_3 : ∀ i, 0 ≤ i → i < 128 → ch_56 i = true := block_join nj_56_2 (fun _ h1 h2 => treeBlockF_at nb_56_3 h1 h2)
theorem nj_56_4 : ∀ i, 0 ≤ i → i < 160 → ch_56 i = true := block_join nj_56_3 (fun _ h1 h2 => treeBlockF_at nb_56_4 h1 h2)
theorem nj_56_5 : ∀ i, 0 ≤ i → i < 192 → ch_56 i = true := block_join nj_56_4 (fun _ h1 h2 => treeBlockF_at nb_56_5 h1 h2)
theorem nj_56_6 : ∀ i, 0 ≤ i → i < 224 → ch_56 i = true := block_join nj_56_5 (fun _ h1 h2 => treeBlockF_at nb_56_6 h1 h2)
theorem nj_56_7 : ∀ i, 0 ≤ i → i < 256 → ch_56 i = true := block_join nj_56_6 (fun _ h1 h2 => treeBlockF_at nb_56_7 h1 h2)
theorem nj_56_8 : ∀ i, 0 ≤ i → i < 288 → ch_56 i = true := block_join nj_56_7 (fun _ h1 h2 => treeBlockF_at nb_56_8 h1 h2)
theorem nj_56_9 : ∀ i, 0 ≤ i → i < 320 → ch_56 i = true := block_join nj_56_8 (fun _ h1 h2 => treeBlockF_at nb_56_9 h1 h2)
theorem nj_56_10 : ∀ i, 0 ≤ i → i < 352 → ch_56 i = true := block_join nj_56_9 (fun _ h1 h2 => treeBlockF_at nb_56_10 h1 h2)
theorem nj_56_11 : ∀ i, 0 ≤ i → i < 384 → ch_56 i = true := block_join nj_56_10 (fun _ h1 h2 => treeBlockF_at nb_56_11 h1 h2)
theorem nj_56_12 : ∀ i, 0 ≤ i → i < 416 → ch_56 i = true := block_join nj_56_11 (fun _ h1 h2 => treeBlockF_at nb_56_12 h1 h2)
theorem nj_56_13 : ∀ i, 0 ≤ i → i < 448 → ch_56 i = true := block_join nj_56_12 (fun _ h1 h2 => treeBlockF_at nb_56_13 h1 h2)
theorem nj_56_14 : ∀ i, 0 ≤ i → i < 480 → ch_56 i = true := block_join nj_56_13 (fun _ h1 h2 => treeBlockF_at nb_56_14 h1 h2)
theorem nj_56_15 : ∀ i, 0 ≤ i → i < 512 → ch_56 i = true := block_join nj_56_14 (fun _ h1 h2 => treeBlockF_at nb_56_15 h1 h2)
theorem nj_56_16 : ∀ i, 0 ≤ i → i < 544 → ch_56 i = true := block_join nj_56_15 (fun _ h1 h2 => treeBlockF_at nb_56_16 h1 h2)
theorem nj_56_17 : ∀ i, 0 ≤ i → i < 576 → ch_56 i = true := block_join nj_56_16 (fun _ h1 h2 => treeBlockF_at nb_56_17 h1 h2)
theorem nj_56_18 : ∀ i, 0 ≤ i → i < 608 → ch_56 i = true := block_join nj_56_17 (fun _ h1 h2 => treeBlockF_at nb_56_18 h1 h2)
theorem nj_56_19 : ∀ i, 0 ≤ i → i < 640 → ch_56 i = true := block_join nj_56_18 (fun _ h1 h2 => treeBlockF_at nb_56_19 h1 h2)
theorem nj_56_20 : ∀ i, 0 ≤ i → i < 660 → ch_56 i = true := block_join nj_56_19 (fun _ h1 h2 => treeBlockF_at nb_56_20 h1 h2)
theorem nc_56 : ∀ i, 0 ≤ i → i < 660 → ch_56 i = true := nj_56_20
theorem lb_56 : LowerBin fullMask rootStock g_56 12 :=
  lowerDagV5 (kn_cons lb_49 (kn_cons lb_34 (kn_cons lb_28 (kn_cons lb_53 (kn_cons lb_39 (kn_cons lb_30 (kn_cons lb_40 (kn_cons lb_52 (kn_cons lb_32 (kn_cons lb_54 (kn_cons lb_24 (kn_cons lb_15 (kn_cons lb_29 (kn_cons lb_2 (kn_cons lb_43 (kn_cons lb_55 (kn_cons lb_48 (kn_cons lb_47 (kn_cons lb_13 (kn_cons lb_38 (kn_cons lb_37 (kn_cons lb_7 (kn_cons lb_42 (kn_cons lb_8 (kn_cons lb_45 (kn_cons lb_31 (kn_cons lb_11 (kn_cons lb_35 (kn_cons lb_36 (kn_cons lb_3 (kn_cons lb_44 (kn_cons lb_16 (kn_cons lb_22 (kn_nil)))))))))))))))))))))))))))))))))) rc_56 nc_56 (by decide +kernel)

def wg : List Gate := [⟨GateOp.and, [1, 3]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [2, 10]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [0, 12]⟩, ⟨GateOp.and, [5, 9]⟩, ⟨GateOp.or, [6, 12]⟩, ⟨GateOp.and, [8, 15]⟩, ⟨GateOp.and, [13, 14]⟩, ⟨GateOp.or, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 4171286528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676744 * 2 ^ 32 + 4171286528)) (13 - 1) := by
  rw [show canon fullMask (4276676744 * 2 ^ 32 + 4171286528) = g_56 by decide]
  exact lb_56

end PEqualNP.Outside.L_meta_49347

theorem PEqualNP.Outside.L_meta_49347 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676744 * 2 ^ 32 + 4171286528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 4171286528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_49347.table2_from_lowerBin (4276676744 * 2 ^ 32 + 4171286528) 13 PEqualNP.Outside.L_meta_49347.root_lb PEqualNP.Outside.L_meta_49347.wg 18 rfl PEqualNP.Outside.L_meta_49347.wfits PEqualNP.Outside.L_meta_49347.weval
