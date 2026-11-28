import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48160

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

def m_0 : Nat := 0xc0c0c0c00000000
def s_0 : List Nat := [0x404040400000000, 0xc000c00000000, 0xc0c00000000]
def g_0 : Nat := 0x4040c00000000
def ep_0 : Nat := 0x408000000000004000800000000000000000000000000000000000000000004040000000000
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

def m_1 : Nat := 0x4400440044004400
def s_1 : List Nat := [0x400040004000400, 0x440000004400, 0x44004400]
def g_1 : Nat := 0x40004004400
def ep_1 : Nat := 0x400400000000400000040000000000000000000000004000400000000000000000000000000000000000000
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

def m_2 : Nat := 0xf0f000000000000
def s_2 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_2 : Nat := 0x107000000000000
def ep_2 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_3 : Nat := 0xf000f0000000000
def s_3 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_3 : Nat := 0x100070000000000
def ep_3 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
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

def m_4 : Nat := 0xaaaa
def s_4 : List Nat := [0x2222, 0xa0a, 0xaa]
def g_4 : Nat := 0x22a
def ep_4 : Nat := 0x28000000000000020800000000000002200000000000000000
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

def m_5 : Nat := 0x4444444400000000
def s_5 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_5 : Nat := 0x4044400000000
def ep_5 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_6 : Nat := 0x4040404040404040
def s_6 : List Nat := [0x40004000400040, 0x404000004040, 0x40404040]
def g_6 : Nat := 0x4000404040
def ep_6 : Nat := 0x40400000000040000040000000004000400000000000000000000000000000000000000000000000000000
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

def m_7 : Nat := 0xff000000
def s_7 : List Nat := [0x55000000, 0x33000000, 0xf000000]
def g_7 : Nat := 0x17000000
def ep_7 : Nat := 0x600000000000000120000000000000014000000
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

def m_9 : Nat := 0xcc00cc00000000
def s_9 : List Nat := [0x44004400000000, 0xc000c00000000, 0xcc00000000]
def g_9 : Nat := 0x4004c00000000
def ep_9 : Nat := 0x48000000000000000000000000000400080000000000000000000000000004004000000000
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

def m_10 : Nat := 0xa0a0a0a00000000
def s_10 : List Nat := [0x202020200000000, 0xa000a00000000, 0xa0a00000000]
def g_10 : Nat := 0x2020a00000000
def ep_10 : Nat := 0x208000000000002000800000000000000000000000000020200000000000000000000000000
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

def m_11 : Nat := 0xf0000000f000000
def s_11 : List Nat := [0x500000005000000, 0x300000003000000, 0xf000000]
def g_11 : Nat := 0x100000007000000
def ep_11 : Nat := 0x600000000000000000000000000000000000000000000000000000001000000020000000100000004000000
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

def m_12 : Nat := 0xff0000000000
def s_12 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_12 : Nat := 0x170000000000
def ep_12 : Nat := 0x6000000000000001200000000000000140000000000
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

def m_13 : Nat := 0x4444000044440000
def s_13 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_13 : Nat := 0x4000004440000
def ep_13 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
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

def m_14 : Nat := 0xcccc00000000
def s_14 : List Nat := [0x444400000000, 0xc0c00000000, 0xcc00000000]
def g_14 : Nat := 0x44c00000000
def ep_14 : Nat := 0x4800000000000004080000000000000000000000000000044000000000
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

def m_15 : Nat := 0xaa00aa
def s_15 : List Nat := [0x220022, 0xa000a, 0xaa]
def g_15 : Nat := 0x2002a
def ep_15 : Nat := 0x280000000000000000000000000002000800000000000200200000000000000000
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

def m_16 : Nat := 0x330033003300330
def s_16 : List Nat := [0x110011001100110, 0x30003000300030, 0x33000000330, 0x3300330]
def g_16 : Nat := 0x110031003100330
def ep_16 : Nat := 0x200002000000200000000200000000000000000000000000000000000000000000000000110001000100000
def bds_16 : List (Nat × List Nat × Nat × Nat) := []
def cur_16 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x193430d19282090d28209263a88d9d3a54d903a10d800f 7 127 3 7 10 1023 14 16383
def nh_16 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_16 : Nat → Nat × Nat := unpackForestF 0xc7463629d64a0a6c43a494209086c00f 3 10
def ch_16 : Nat → Bool := dagCheckNodeV5 m_16 g_16 ep_16 1 1 bds_16 10 (dagTraceF m_16 s_16 4 f_16) cur_16 nh_16
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV5 m_16 g_16 ep_16 1 1 10 bds_16 (dagTraceF m_16 s_16 4 f_16) (cur_16 0) (nh_16 0) s_16 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16 : treeBlockF 0 10 ch_16 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 10 → ch_16 i = true := fun _ h1 h2 => treeBlockF_at nb_16 h1 h2
theorem lb_16 : LowerBin m_16 s_16 g_16 5 :=
  lowerDagV5 (kn_nil) rc_16 nc_16 (by decide +kernel)

def m_17 : Nat := 0xc300c300c300c300
def s_17 : List Nat := [0x4100410041004100, 0x300030003000300, 0xc3000000c300, 0xc300c300]
def g_17 : Nat := 0x100030003004300
def ep_17 : Nat := 0x200400000000200000040000000000000000000000000000000000000000000000000000100000000004000
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
def cc_17_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0x793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_17_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014 8 255 3 7 10 1023 16 65535
def cur_17 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_17_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_17_0 p) (Nat.blt p 32)
def hc_17_0 : Nat → Nat := unpackHintV5 0xfa27b13925c04dc2654aea160aa084d1a50d28090248023090c68604112080fc47833a11c08bd25a22b111246902a50d400b0002 0x0 13 8191 5 31
def hc_17_1 : Nat → Nat := unpackHintV5 0xa2351027893c09a24a1a501204900461218d0447e23649a08c845292140e145102230e187003041800a1038c1c00a20500188006 0x0 13 8191 5 31
def hc_17_2 : Nat → Nat := unpackHintV5 0x6 0x0 6 63 3 7
def nh_17 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_17_2 (Nat.sub p 64)) (hc_17_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_17_0 p) (Nat.blt p 32)
def f_17 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def ch_17 : Nat → Bool := dagCheckNodeV5 m_17 g_17 ep_17 1 1 bds_17 64 (dagTraceF m_17 s_17 5 f_17) cur_17 nh_17
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV5 m_17 g_17 ep_17 1 1 64 bds_17 (dagTraceF m_17 s_17 5 f_17) (cur_17 0) (nh_17 0) s_17 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_0 : treeBlockF 0 32 ch_17 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_1 : treeBlockF 32 64 ch_17 = true := by decide +kernel
theorem nj_17_1 : ∀ i, 0 ≤ i → i < 64 → ch_17 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_17_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_17_1 h1 h2)
theorem nc_17 : ∀ i, 0 ≤ i → i < 64 → ch_17 i = true := nj_17_1
theorem lb_17 : LowerBin m_17 s_17 g_17 6 :=
  lowerDagV5 (kn_nil) rc_17 nc_17 (by decide +kernel)

def m_18 : Nat := 0xc3c30000c3c30000
def s_18 : List Nat := [0x4141000041410000, 0x303000003030000, 0xc3000000c30000, 0xc3c30000]
def g_18 : Nat := 0x103000003430000
def ep_18 : Nat := 0x240000000000000000000000002000000400000000000000000000000000000000000000100000000400000
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
def cc_18_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0x793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_18_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014 8 255 3 7 10 1023 16 65535
def cur_18 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_18_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_18_0 p) (Nat.blt p 32)
def hc_18_0 : Nat → Nat := unpackHintV5 0xfa27b13925c04dc2654aea160aa084d1a50d28090248023090c68604112080fc47833a11c08bd25a22b111246902a50d400b0002 0x0 13 8191 5 31
def hc_18_1 : Nat → Nat := unpackHintV5 0xa2351027893c09a24a1a501204900461218d0447e23649a08c845292140e145102230e187003041800a1038c1c00a20500188006 0x0 13 8191 5 31
def hc_18_2 : Nat → Nat := unpackHintV5 0x6 0x0 6 63 3 7
def nh_18 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_18_2 (Nat.sub p 64)) (hc_18_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_18_0 p) (Nat.blt p 32)
def f_18 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def ch_18 : Nat → Bool := dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 64 (dagTraceF m_18 s_18 5 f_18) cur_18 nh_18
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 64 bds_18 (dagTraceF m_18 s_18 5 f_18) (cur_18 0) (nh_18 0) s_18 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18_0 : treeBlockF 0 32 ch_18 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18_1 : treeBlockF 32 64 ch_18 = true := by decide +kernel
theorem nj_18_1 : ∀ i, 0 ≤ i → i < 64 → ch_18 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_18_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_18_1 h1 h2)
theorem nc_18 : ∀ i, 0 ≤ i → i < 64 → ch_18 i = true := nj_18_1
theorem lb_18 : LowerBin m_18 s_18 g_18 6 :=
  lowerDagV5 (kn_nil) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0xa0aa0a00a0aa0a0
def s_19 : List Nat := [0x202202002022020, 0xa0a00000a0a0, 0xa00a0000a00a0, 0xa0aa0a0]
def g_19 : Nat := 0x2000002020020
def ep_19 : Nat := 0x200002000000000000000000002000000000020000000000000000000020000020200200000000000000000
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
def cur_19 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1d3c30c1d3020c0e3024f263e88c993e54c903e10c800f 7 127 3 7 10 1023 14 16383
def nh_19 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_19 : Nat → Nat × Nat := unpackForestF 0xc7c632e9814f8a6443e51824f086400f 3 10
def ch_19 : Nat → Bool := dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 10 (dagTraceF m_19 s_19 4 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 10 bds_19 (dagTraceF m_19 s_19 4 f_19) (cur_19 0) (nh_19 0) s_19 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19 : treeBlockF 0 10 ch_19 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 10 → ch_19 i = true := fun _ h1 h2 => treeBlockF_at nb_19 h1 h2
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagV5 (kn_nil) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0xffff00000000
def s_20 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_20 : Nat := 0x175f00000000
def ep_20 : Nat := 0x48000000000000060a0000000000001200000000000000145000000000
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_20 : Nat → List (Nat × Nat) := fun _ => []
def nh_20 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_20 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 0 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) (nh_20 0) s_20 4 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 0 (dagTraceF m_20 s_20 4 f_20) cur_20 nh_20 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xaa00aa00aa00aa
def s_21 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_21 : Nat := 0x2000a0002002a
def ep_21 : Nat := 0x20000000080000002800000000000000000002000a0002000800020000000200200000000000000000
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_21 : Nat → List (Nat × Nat) := fun _ => []
def nh_21 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_21 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 0 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) (nh_21 0) s_21 4 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 0 (dagTraceF m_21 s_21 4 f_21) cur_21 nh_21 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xffff000000000000
def s_22 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_22 : Nat := 0x1117000000000000
def ep_22 : Nat := 0x6000000000000000600000000000011120000000000001114000000000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_22 : Nat → List (Nat × Nat) := fun _ => []
def nh_22 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 0 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) (nh_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 0 (dagTraceF m_22 s_22 4 f_22) cur_22 nh_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0xff00ff0000000000
def s_23 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_23 : Nat := 0x1100170000000000
def ep_23 : Nat := 0x600000000000000000000000000000006000000000011001200000000001100140000000000
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_23 : Nat → List (Nat × Nat) := fun _ => []
def nh_23 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 0 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) (nh_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 0 (dagTraceF m_23 s_23 4 f_23) cur_23 nh_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0xff00ff00000000
def s_24 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_24 : Nat := 0x17005f00000000
def ep_24 : Nat := 0x480000000000000000000000000006000a0000000000120000000000000014005000000000
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def nh_24 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0xf0f0f0f00000000
def s_25 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_25 : Nat := 0x107070f00000000
def ep_25 : Nat := 0x608000000000006000800000000000000000000000001020200000000000104040000000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_3, s_3, 4, g_3), (m_0, s_0, 4, g_0), (m_10, s_10, 4, g_10)]
def cc_25_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_25_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_25 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_25_1 (Nat.sub p 32)) (cc_25_0 p) (Nat.blt p 32)
def hc_25_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_25_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_25 : Nat → Nat := fun p => Bool.rec (hc_25_1 (Nat.sub p 32)) (hc_25_0 p) (Nat.blt p 32)
def f_25 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_25 : Nat → Bool := dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 43 (dagTraceF m_25 s_25 6 f_25) cur_25 nh_25
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 43 bds_25 (dagTraceF m_25 s_25 6 f_25) (cur_25 0) (nh_25 0) s_25 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_0 : treeBlockF 0 32 ch_25 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_1 : treeBlockF 32 43 ch_25 = true := by decide +kernel
theorem nj_25_1 : ∀ i, 0 ≤ i → i < 43 → ch_25 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_25_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_25_1 h1 h2)
theorem nc_25 : ∀ i, 0 ≤ i → i < 43 → ch_25 i = true := nj_25_1
theorem lb_25 : LowerBin m_25 s_25 g_25 7 :=
  lowerDagV5 (kn_cons lb_2 (kn_cons lb_3 (kn_cons lb_0 (kn_cons lb_10 (kn_nil))))) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0xcccccccc00000000
def s_26 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_26 : Nat := 0x4044c00000000
def ep_26 : Nat := 0x448000000000004004800000000000404080000000000000000000000000004044000000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9), (m_14, s_14, 4, g_14), (m_5, s_5, 4, g_5), (m_0, s_0, 4, g_0)]
def cc_26_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_26_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_26 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_26_1 (Nat.sub p 32)) (cc_26_0 p) (Nat.blt p 32)
def hc_26_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_26_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_26 : Nat → Nat := fun p => Bool.rec (hc_26_1 (Nat.sub p 32)) (hc_26_0 p) (Nat.blt p 32)
def f_26 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_26 : Nat → Bool := dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 43 (dagTraceF m_26 s_26 6 f_26) cur_26 nh_26
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 43 bds_26 (dagTraceF m_26 s_26 6 f_26) (cur_26 0) (nh_26 0) s_26 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_0 : treeBlockF 0 32 ch_26 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_1 : treeBlockF 32 43 ch_26 = true := by decide +kernel
theorem nj_26_1 : ∀ i, 0 ≤ i → i < 43 → ch_26 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_26_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_26_1 h1 h2)
theorem nc_26 : ∀ i, 0 ≤ i → i < 43 → ch_26 i = true := nj_26_1
theorem lb_26 : LowerBin m_26 s_26 g_26 7 :=
  lowerDagV5 (kn_cons lb_9 (kn_cons lb_14 (kn_cons lb_5 (kn_cons lb_0 (kn_nil))))) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0xcc00cc00cc00cc
def s_27 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_27 : Nat := 0x4004c0044004c
def ep_27 : Nat := 0x40000000000048000000080000000000000000000400080000000800000000000000000004004000440040
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def nh_27 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) (nh_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 nh_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0x66666666
def s_28 : List Nat := [0x22222222, 0x6060606, 0x660066, 0x6666]
def g_28 : Nat := 0x6464666
def ep_28 : Nat := 0x40200000000000400020000000000602020000000000000000000000000000000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := []
def cur_28 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x1924309193c2050d3c205263d88d5d2a549902a109800f 7 127 3 7 10 1023 14 16383
def nh_28 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_28 : Nat → Nat × Nat := unpackForestF 0xc7a63529564f0a4c42a49e205084c00f 3 10
def ch_28 : Nat → Bool := dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 10 (dagTraceF m_28 s_28 4 f_28) cur_28 nh_28
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 10 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) (nh_28 0) s_28 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28 : treeBlockF 0 10 ch_28 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 10 → ch_28 i = true := fun _ h1 h2 => treeBlockF_at nb_28 h1 h2
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV5 (kn_nil) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0xaaaaaaaa00000000
def s_29 : List Nat := [0x2222222200000000, 0xa0a0a0a00000000, 0xaa00aa00000000, 0xaaaa00000000]
def g_29 : Nat := 0x2020a00000000
def ep_29 : Nat := 0x2080000000000020008000000000002020a0000000000020200000000000000000000000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_29 : Nat → List (Nat × Nat) := fun _ => []
def nh_29 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 0 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) (nh_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 0 (dagTraceF m_29 s_29 4 f_29) cur_29 nh_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0x666600006666
def s_30 : List Nat := [0x222200002222, 0x60600000606, 0x6600000066, 0x6666]
def g_30 : Nat := 0x64600004666
def ep_30 : Nat := 0x402000000000000000000000004000000020000006020000020000000000000000000000000000000000
def bds_30 : List (Nat × List Nat × Nat × Nat) := []
def cur_30 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x1924309193c2050d3c205263d88d5d2a549902a109800f 7 127 3 7 10 1023 14 16383
def nh_30 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_30 : Nat → Nat × Nat := unpackForestF 0xc7a63529564f0a4c42a49e205084c00f 3 10
def ch_30 : Nat → Bool := dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 10 (dagTraceF m_30 s_30 4 f_30) cur_30 nh_30
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 10 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) (nh_30 0) s_30 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30 : treeBlockF 0 10 ch_30 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 10 → ch_30 i = true := fun _ h1 h2 => treeBlockF_at nb_30 h1 h2
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV5 (kn_nil) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0xc0c0c0c0c0c0c0c0
def s_31 : List Nat := [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0]
def g_31 : Nat := 0x4000404040
def ep_31 : Nat := 0x40400000000040000040000000004000400000000000000000000000000000000000000000004000404040
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def nh_31 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) (nh_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 nh_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0x66006600660066
def s_32 : List Nat := [0x22002200220022, 0x6000600060006, 0x6600000066, 0x660066]
def g_32 : Nat := 0x6004600460066
def ep_32 : Nat := 0x40002000000040000000200000000000000000000600020002000000000000000000000000000000000000
def bds_32 : List (Nat × List Nat × Nat × Nat) := []
def cur_32 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x1924309193c2050d3c205263d88d5d2a549902a109800f 7 127 3 7 10 1023 14 16383
def nh_32 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_32 : Nat → Nat × Nat := unpackForestF 0xc7a63529564f0a4c42a49e205084c00f 3 10
def ch_32 : Nat → Bool := dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 10 (dagTraceF m_32 s_32 4 f_32) cur_32 nh_32
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 10 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) (nh_32 0) s_32 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32 : treeBlockF 0 10 ch_32 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 10 → ch_32 i = true := fun _ h1 h2 => treeBlockF_at nb_32 h1 h2
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV5 (kn_nil) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0xcccc0000cccc0000
def s_33 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_33 : Nat := 0x4000004440000
def ep_33 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000004000004440000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def nh_33 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) (nh_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 nh_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0x5555000055550000
def s_34 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_34 : Nat := 0x1115000015550000
def ep_34 : Nat := 0x440000000000000000000000004000000400000000400000400000011100000100000000000000000000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def nh_34 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) (nh_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 nh_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0xff000000ff00
def s_35 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_35 : Nat := 0x170000005700
def ep_35 : Nat := 0x400000000000000000000000000000000000000006000000020000001200000002000000140000005400
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def nh_35 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) (nh_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 nh_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0xf0f00000f0f0
def s_36 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_36 : Nat := 0x105000005070
def ep_36 : Nat := 0x402000000000000000000000004000000020000000000000000000001000000000200000105000005040
def bds_36 : List (Nat × List Nat × Nat × Nat) := []
def cc_36_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_36_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_36 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_36_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_36_0 p) (Nat.blt p 32)
def hc_36_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_36_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_36_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_36 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_36_2 (Nat.sub p 64)) (hc_36_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_36_0 p) (Nat.blt p 32)
def f_36 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_36 : Nat → Bool := dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 64 (dagTraceF m_36 s_36 5 f_36) cur_36 nh_36
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 64 bds_36 (dagTraceF m_36 s_36 5 f_36) (cur_36 0) (nh_36 0) s_36 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_0 : treeBlockF 0 32 ch_36 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_1 : treeBlockF 32 64 ch_36 = true := by decide +kernel
theorem nj_36_1 : ∀ i, 0 ≤ i → i < 64 → ch_36 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_36_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_36_1 h1 h2)
theorem nc_36 : ∀ i, 0 ≤ i → i < 64 → ch_36 i = true := nj_36_1
theorem lb_36 : LowerBin m_36 s_36 g_36 6 :=
  lowerDagV5 (kn_nil) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0xf0f00000f0f0000
def s_37 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_37 : Nat := 0x107000007070000
def ep_37 : Nat := 0x600000000000000000000000006000000000000000000000000000001020000020200000104000004040000
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def nh_37 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) (nh_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 nh_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0xcccc0000cccc
def s_38 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_38 : Nat := 0x44c0000444c
def ep_38 : Nat := 0x400000000000000000000000004800000008000004080000000800000000000000000000044000004440
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def nh_38 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0xaaaa0000aaaa
def s_39 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_39 : Nat := 0x20a0000022a
def ep_39 : Nat := 0x20000000000000000000000008000000280000020a0000020800000200000002200000000000000000
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def nh_39 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) (nh_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 nh_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xcc00cc00cc00cc00
def s_40 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_40 : Nat := 0x40004004400
def ep_40 : Nat := 0x400400000000400000040000000000000000000000004000400000000000000000000000000040004004400
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def nh_40 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0xf000f000f000f00
def s_41 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_41 : Nat := 0x100070007000700
def ep_41 : Nat := 0x600000000000600000000000000000000000000000000000000000001000200020002000100040004000400
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0xcccccccc
def s_42 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_42 : Nat := 0x444444c
def ep_42 : Nat := 0x40080000000000400008000000000400000800000000000000000000000004444440
def bds_42 : List (Nat × List Nat × Nat × Nat) := []
def cc_42_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_42_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_42 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_42_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_42_0 p) (Nat.blt p 32)
def hc_42_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_42_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_42_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_42 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_42_2 (Nat.sub p 64)) (hc_42_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_42_0 p) (Nat.blt p 32)
def f_42 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_42 : Nat → Bool := dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 64 (dagTraceF m_42 s_42 5 f_42) cur_42 nh_42
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 64 bds_42 (dagTraceF m_42 s_42 5 f_42) (cur_42 0) (nh_42 0) s_42 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_0 : treeBlockF 0 32 ch_42 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_1 : treeBlockF 32 64 ch_42 = true := by decide +kernel
theorem nj_42_1 : ∀ i, 0 ≤ i → i < 64 → ch_42 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_42_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_42_1 h1 h2)
theorem nc_42 : ∀ i, 0 ≤ i → i < 64 → ch_42 i = true := nj_42_1
theorem lb_42 : LowerBin m_42 s_42 g_42 6 :=
  lowerDagV5 (kn_nil) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xffff0000
def s_43 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_43 : Nat := 0x17570000
def ep_43 : Nat := 0x400000000000000602000000000000120200000000000014540000
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def nh_43 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) (nh_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 nh_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xffff
def s_44 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_44 : Nat := 0x577f
def ep_44 : Nat := 0x28000000000000020800000000000002200000000000005440
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def nh_44 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) (nh_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 nh_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0xff00ff00
def s_45 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_45 : Nat := 0x17005700
def ep_45 : Nat := 0x40000000000000000000000000000600020000000000120002000000000014005400
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def nh_45 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) (nh_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 nh_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xff00ff
def s_46 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_46 : Nat := 0x57007f
def ep_46 : Nat := 0x280000000000000000000000000002000800000000000200200000000000540040
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def nh_46 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) (nh_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 nh_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0xf0f0f0f0
def s_47 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_47 : Nat := 0x10505070
def ep_47 : Nat := 0x40200000000000400020000000000000000000000000100000200000000010505040
def bds_47 : List (Nat × List Nat × Nat × Nat) := []
def cc_47_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_47_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_47 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_47_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_47_0 p) (Nat.blt p 32)
def hc_47_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_47_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_47_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_47 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_47_2 (Nat.sub p 64)) (hc_47_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_47_0 p) (Nat.blt p 32)
def f_47 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_47 : Nat → Bool := dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 64 (dagTraceF m_47 s_47 5 f_47) cur_47 nh_47
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 64 bds_47 (dagTraceF m_47 s_47 5 f_47) (cur_47 0) (nh_47 0) s_47 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_0 : treeBlockF 0 32 ch_47 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_1 : treeBlockF 32 64 ch_47 = true := by decide +kernel
theorem nj_47_1 : ∀ i, 0 ≤ i → i < 64 → ch_47 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_47_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_47_1 h1 h2)
theorem nc_47 : ∀ i, 0 ≤ i → i < 64 → ch_47 i = true := nj_47_1
theorem lb_47 : LowerBin m_47 s_47 g_47 6 :=
  lowerDagV5 (kn_nil) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0xaaaaaaaa
def s_48 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_48 : Nat := 0x202022a
def ep_48 : Nat := 0x280000000000000028000000000202020800000000020202200000000000000000
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def nh_48 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xf000f000f000f0
def s_49 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_49 : Nat := 0x10005000500070
def ep_49 : Nat := 0x40002000000040000000200000000000000000000000000000000000100000000000200010005000500040
def bds_49 : List (Nat × List Nat × Nat × Nat) := []
def cc_49_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_49_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_49 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_49_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_49_0 p) (Nat.blt p 32)
def hc_49_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_49_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_49_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_49 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_49_2 (Nat.sub p 64)) (hc_49_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_49_0 p) (Nat.blt p 32)
def f_49 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_49 : Nat → Bool := dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 64 (dagTraceF m_49 s_49 5 f_49) cur_49 nh_49
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 64 bds_49 (dagTraceF m_49 s_49 5 f_49) (cur_49 0) (nh_49 0) s_49 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_0 : treeBlockF 0 32 ch_49 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_1 : treeBlockF 32 64 ch_49 = true := by decide +kernel
theorem nj_49_1 : ∀ i, 0 ≤ i → i < 64 → ch_49 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_49_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_49_1 h1 h2)
theorem nc_49 : ∀ i, 0 ≤ i → i < 64 → ch_49 i = true := nj_49_1
theorem lb_49 : LowerBin m_49 s_49 g_49 6 :=
  lowerDagV5 (kn_nil) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0xff000000ff000000
def s_50 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_50 : Nat := 0x1100000017000000
def ep_50 : Nat := 0x600000000000000000000000000000000000000000000000600000011000000120000001100000014000000
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def nh_50 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) (nh_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 nh_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0x5500550055005500
def s_51 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_51 : Nat := 0x1100150015005500
def ep_51 : Nat := 0x400400000000400000040000000000000000000000004000400000011001000100000000000000000000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def nh_51 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 0 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) (nh_51 0) s_51 4 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 0 (dagTraceF m_51 s_51 4 f_51) cur_51 nh_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0xff000000ff0000
def s_52 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_52 : Nat := 0x17000000570000
def ep_52 : Nat := 0x40000000000000000000000000000000000000000600000002000000120000000200000014000000540000
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def nh_52 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 0 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) (nh_52 0) s_52 4 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 0 (dagTraceF m_52 s_52 4 f_52) cur_52 nh_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0x4444444444444444
def s_53 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_53 : Nat := 0x4044404444444
def ep_53 : Nat := 0x440400000000440000040000004004000400000000404000400000000000000000000000000000000000000
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_13, s_13, 4, g_13), (m_1, s_1, 4, g_1), (m_6, s_6, 4, g_6)]
def cc_53_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_53_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_53 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_53_1 (Nat.sub p 32)) (cc_53_0 p) (Nat.blt p 32)
def hc_53_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_53_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_53 : Nat → Nat := fun p => Bool.rec (hc_53_1 (Nat.sub p 32)) (hc_53_0 p) (Nat.blt p 32)
def f_53 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_53 : Nat → Bool := dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 43 (dagTraceF m_53 s_53 6 f_53) cur_53 nh_53
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 43 bds_53 (dagTraceF m_53 s_53 6 f_53) (cur_53 0) (nh_53 0) s_53 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_0 : treeBlockF 0 32 ch_53 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_1 : treeBlockF 32 43 ch_53 = true := by decide +kernel
theorem nj_53_1 : ∀ i, 0 ≤ i → i < 43 → ch_53 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_53_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_53_1 h1 h2)
theorem nc_53 : ∀ i, 0 ≤ i → i < 43 → ch_53 i = true := nj_53_1
theorem lb_53 : LowerBin m_53 s_53 g_53 7 :=
  lowerDagV5 (kn_cons lb_5 (kn_cons lb_13 (kn_cons lb_1 (kn_cons lb_6 (kn_nil))))) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0x2222222222222222
def s_54 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_54 : Nat := 0x2020202020222
def ep_54 : Nat := 0x200002000000200000000200002000000000020000202020202020000000000000000000000000000000000
def bds_54 : List (Nat × List Nat × Nat × Nat) := []
def cc_54_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_54_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_54 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_54_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_54_0 p) (Nat.blt p 32)
def hc_54_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_54_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_54_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_54 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_54_2 (Nat.sub p 64)) (hc_54_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_54_0 p) (Nat.blt p 32)
def f_54 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
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

def m_55 : Nat := 0x5a005a005a005a00
def s_55 : List Nat := [0xa000a000a000a00, 0x1200120012001200, 0x5a0000005a00, 0x5a005a00]
def g_55 : Nat := 0x1000120012005200
def ep_55 : Nat := 0x200400000000200000040000000000000000000000000000000000010001200120002000000000000000000
def bds_55 : List (Nat × List Nat × Nat × Nat) := []
def cc_55_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a490320230c608c108a104207c4f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c50244438453c3d3c3930302c2c24253c2134183c143408100924ee3fda3bd637d233cd3fc93bb537a1339d2f952b89277d23783f743b60374c33482f402b342728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_55_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b09490909090747070707070707070545050505034292821202012101002 0xfd38f934f438f034e928e524e028dc24c64cc240bc4cb840b13cad34a818a41499389a3c903c8c3084188014 8 255 3 7 10 1023 16 65535
def cur_55 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_55_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_55_0 p) (Nat.blt p 32)
def hc_55_0 : Nat → Nat := unpackHintV5 0xb47533a905480a4050125952829404a024090ca8224009f08f807823919c80dc46833309904ace541290911c6902a50d400b0002 0x0 13 8191 5 31
def hc_55_1 : Nat → Nat := unpackHintV5 0xe41c83906c6d81b03606c0ccd81ad34ce7dcf09e03c0708ba9612c0580a10f51a4304510a010414c28032006 0x0 11 2047 4 15
def nh_55 : Nat → Nat := fun p => Bool.rec (Bool.rec (0) (hc_55_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_55_0 p) (Nat.blt p 32)
def f_55 : Nat → Nat × Nat := unpackForestF 0xf138f134f038f034063fdd28dd24dc28dc24063b06370633053f053bba4cba40b84cb8400537a53ca534a418a4140533052f9a3c052b8c3c8c300527801880140523043f043b664c6640654c65400437503c5034502c50240433042f453c042b393c393004272c2c2c240423213c2134041f143c1434041b041709240413000f 6 10
def ch_55 : Nat → Bool := dagCheckNodeV5 m_55 g_55 ep_55 1 1 bds_55 64 (dagTraceF m_55 s_55 5 f_55) cur_55 nh_55
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 1 1 64 bds_55 (dagTraceF m_55 s_55 5 f_55) (cur_55 0) (nh_55 0) s_55 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_0 : treeBlockF 0 32 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_1 : treeBlockF 32 64 ch_55 = true := by decide +kernel
theorem nj_55_1 : ∀ i, 0 ≤ i → i < 64 → ch_55 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_55_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_55_1 h1 h2)
theorem nc_55 : ∀ i, 0 ≤ i → i < 64 → ch_55 i = true := nj_55_1
theorem lb_55 : LowerBin m_55 s_55 g_55 6 :=
  lowerDagV5 (kn_nil) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0x5a5a00005a5a0000
def s_56 : List Nat := [0xa0a00000a0a0000, 0x1212000012120000, 0x5a0000005a0000, 0x5a5a0000]
def g_56 : Nat := 0x1012000012520000
def ep_56 : Nat := 0x240000000000000000000000002000000400000000000000000000010120000120200000000000000000000
def bds_56 : List (Nat × List Nat × Nat × Nat) := []
def cc_56_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a490320230c608c108a104207c4f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c50244438453c3d3c3930302c2c24253c2134183c143408100924ee3fda3bd637d233cd3fc93bb537a1339d2f952b89277d23783f743b60374c33482f402b342728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_56_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b09490909090747070707070707070545050505034292821202012101002 0xfd38f934f438f034e928e524e028dc24c64cc240bc4cb840b13cad34a818a41499389a3c903c8c3084188014 8 255 3 7 10 1023 16 65535
def cur_56 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_56_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_56_0 p) (Nat.blt p 32)
def hc_56_0 : Nat → Nat := unpackHintV5 0xb47533a905480a4050125952829404a024090ca8224009f08f807823919c80dc46833309904ace541290911c6902a50d400b0002 0x0 13 8191 5 31
def hc_56_1 : Nat → Nat := unpackHintV5 0xe41c83906c6d81b03606c0ccd81ad34ce7dcf09e03c0708ba9612c0580a10f51a4304510a010414c28032006 0x0 11 2047 4 15
def nh_56 : Nat → Nat := fun p => Bool.rec (Bool.rec (0) (hc_56_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_56_0 p) (Nat.blt p 32)
def f_56 : Nat → Nat × Nat := unpackForestF 0xf138f134f038f034063fdd28dd24dc28dc24063b06370633053f053bba4cba40b84cb8400537a53ca534a418a4140533052f9a3c052b8c3c8c300527801880140523043f043b664c6640654c65400437503c5034502c50240433042f453c042b393c393004272c2c2c240423213c2134041f143c1434041b041709240413000f 6 10
def ch_56 : Nat → Bool := dagCheckNodeV5 m_56 g_56 ep_56 1 1 bds_56 64 (dagTraceF m_56 s_56 5 f_56) cur_56 nh_56
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 1 1 64 bds_56 (dagTraceF m_56 s_56 5 f_56) (cur_56 0) (nh_56 0) s_56 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_0 : treeBlockF 0 32 ch_56 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_1 : treeBlockF 32 64 ch_56 = true := by decide +kernel
theorem nj_56_1 : ∀ i, 0 ≤ i → i < 64 → ch_56 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_56_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_56_1 h1 h2)
theorem nc_56 : ∀ i, 0 ≤ i → i < 64 → ch_56 i = true := nj_56_1
theorem lb_56 : LowerBin m_56 s_56 g_56 6 :=
  lowerDagV5 (kn_nil) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0x5050505050505050
def s_57 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_57 : Nat := 0x1010105010505050
def ep_57 : Nat := 0x40400000000040000040000000004000400000000000000000000010101000100000000000000000000000
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_57 : Nat → List (Nat × Nat) := fun _ => []
def nh_57 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_57 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 1 1 0 bds_57 (dagTraceF m_57 s_57 4 f_57) (cur_57 0) (nh_57 0) s_57 4 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_57 g_57 ep_57 1 1 bds_57 0 (dagTraceF m_57 s_57 4 f_57) cur_57 nh_57 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_57 : LowerBin m_57 s_57 g_57 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0xc0c0c0c0c0c0c0c
def s_58 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_58 : Nat := 0x4040c0404040c
def ep_58 : Nat := 0x400000000000408000000080004000800000008000000000000000000000000000000000004040004040400
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_58 : Nat → List (Nat × Nat) := fun _ => []
def nh_58 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_58 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 1 1 0 bds_58 (dagTraceF m_58 s_58 4 f_58) (cur_58 0) (nh_58 0) s_58 4 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_58 g_58 ep_58 1 1 bds_58 0 (dagTraceF m_58 s_58 4 f_58) cur_58 nh_58 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_58 : LowerBin m_58 s_58 g_58 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0xa0a0a0a0a0a0a0a
def s_59 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_59 : Nat := 0x2020a0202020a
def ep_59 : Nat := 0x200000000000208000000080002000800000008000000000000000000020200020202000000000000000000
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_59 : Nat → List (Nat × Nat) := fun _ => []
def nh_59 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_59 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 1 1 0 bds_59 (dagTraceF m_59 s_59 4 f_59) (cur_59 0) (nh_59 0) s_59 4 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_59 g_59 ep_59 1 1 bds_59 0 (dagTraceF m_59 s_59 4 f_59) cur_59 nh_59 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_59 : LowerBin m_59 s_59 g_59 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0x3333333333333333
def s_60 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_60 : Nat := 0x1113131313131333
def ep_60 : Nat := 0x200002000000200000000200002000000000020000202020202020000000000000000001110101010101000
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_54, s_54, 6, g_54)]
def cur_60 : Nat → List (Nat × Nat) := fun _ => []
def nh_60 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_60 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 1 1 0 bds_60 (dagTraceF m_60 s_60 6 f_60) (cur_60 0) (nh_60 0) s_60 6 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_60 g_60 ep_60 1 1 bds_60 0 (dagTraceF m_60 s_60 6 f_60) cur_60 nh_60 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_60 : LowerBin m_60 s_60 g_60 7 :=
  lowerDagV5 (kn_cons lb_54 (kn_nil)) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0xcccccccccccccccc
def s_61 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_61 : Nat := 0x4044c0444444c
def ep_61 : Nat := 0x440400000000448000040080004004800400008000404080400000800000000000000000004044004444440
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_26, s_26, 7, g_26), (m_53, s_53, 7, g_53), (m_33, s_33, 5, g_33), (m_58, s_58, 5, g_58), (m_38, s_38, 5, g_38), (m_31, s_31, 5, g_31), (m_27, s_27, 5, g_27), (m_40, s_40, 5, g_40), (m_42, s_42, 6, g_42)]
def cur_61 : Nat → List (Nat × Nat) := unpackCursorV5 0x13098486411188442030078bc1e0e1703443801 0x3230cd11d30791092028d3e3fe8ef637b8ce93f94ee13764cd52f44acd27148c01f 9 511 4 15 10 1023 14 16383
def nh_61 : Nat → Nat := unpackHintV5 0xab9f09c9f08e2e785f83762fd687db5d0b74fed24906e3cfc12f4db23db716bd20fd6e03cc10003c00000 0xaaaaaab5ad554637ec635ac631aaac635aceb9675cf7bde2000000000000aaaaa31bf6318c6aaaa318c6b1aa8c631cdef98c638671c2000000000000aaaaaa318d546358c6318c6f5519c70c6386318def7bc400000000000155554635ed546318d6b5ac40000016002aaaaaad6318c6f55555ad6318d55631ae6f7cd675cb3ae1000000000165c001555556a5558c6b39cf33bce7555876c63a18c678f08000000000002aaaa8c631aac3b75554aaab0ea753eaa1000000000000555555a9546f18c631cc6318d546338c750e3c784000000000001555546318d561dbaa10000000085555558c6b555aa87552aaac7a9d4faa84000000000008b82aaabe6f9aaaa9d6719c673d4aaa78f4fb673d1ce71000000000000555557bdef55aa9f6ea955565d43a8f542000000000000aaaaaa739c6719d6aaf7bdf52a9e3c739ce7a9f08000000000002aaaa9ce73aad547b62000000010aaaaaf9be6aab55553e55559750ea3d50800000000001170555555100000000 20 1048575 8 255
def f_61 : Nat → Nat × Nat := unpackForestF 0x18fc63b18df34418cc53f14ec537791053314bc52b149ca34148c01f 4 10
def ch_61 : Nat → Bool := dagCheckNodeV5 m_61 g_61 ep_61 3 7 bds_61 16 (dagTraceF m_61 s_61 8 f_61) cur_61 nh_61
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 3 7 16 bds_61 (dagTraceF m_61 s_61 8 f_61) (cur_61 0) (nh_61 0) s_61 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61 : treeBlockF 0 16 ch_61 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 16 → ch_61 i = true := fun _ h1 h2 => treeBlockF_at nb_61 h1 h2
theorem lb_61 : LowerBin m_61 s_61 g_61 9 :=
  lowerDagV5 (kn_cons lb_26 (kn_cons lb_53 (kn_cons lb_33 (kn_cons lb_58 (kn_cons lb_38 (kn_cons lb_31 (kn_cons lb_27 (kn_cons lb_40 (kn_cons lb_42 (kn_nil)))))))))) rc_61 nc_61 (by decide +kernel)

def m_62 : Nat := 0xff00ff00ff00ff00
def s_62 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_62 : Nat := 0x1100170017005700
def ep_62 : Nat := 0x600400000000600000040000000000000000000000006000600020011001200120002001100140014005400
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 5, g_23), (m_35, s_35, 5, g_35), (m_45, s_45, 5, g_45), (m_50, s_50, 5, g_50), (m_40, s_40, 5, g_40), (m_41, s_41, 5, g_41), (m_51, s_51, 5, g_51), (m_17, s_17, 6, g_17), (m_55, s_55, 6, g_55), (m_1, s_1, 4, g_1)]
def cur_62 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x1f 2 3 1 1 5 31 6 63
def nh_62 : Nat → Nat := unpackHintV5 0x860000 0x36779d6f5dcf359d1a3468d1a388888884 16 65535 8 255
def f_62 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
def ch_62 : Nat → Bool := dagCheckNodeV5 m_62 g_62 ep_62 3 7 bds_62 1 (dagTraceF m_62 s_62 7 f_62) cur_62 nh_62
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 m_62 g_62 ep_62 3 7 1 bds_62 (dagTraceF m_62 s_62 7 f_62) (cur_62 0) (nh_62 0) s_62 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62 : treeBlockF 0 1 ch_62 = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 1 → ch_62 i = true := fun _ h1 h2 => treeBlockF_at nb_62 h1 h2
theorem lb_62 : LowerBin m_62 s_62 g_62 8 :=
  lowerDagV5 (kn_cons lb_23 (kn_cons lb_35 (kn_cons lb_45 (kn_cons lb_50 (kn_cons lb_40 (kn_cons lb_41 (kn_cons lb_51 (kn_cons lb_17 (kn_cons lb_55 (kn_cons lb_1 (kn_nil))))))))))) rc_62 nc_62 (by decide +kernel)

def m_63 : Nat := 0xf0f0f0f0f0f0f0f
def s_63 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_63 : Nat := 0x107070f0707070f
def ep_63 : Nat := 0x600000000000608000000080006000800000008000000000000000001020200020202000104040004040400
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_25, s_25, 7, g_25)]
def cur_63 : Nat → List (Nat × Nat) := fun _ => []
def nh_63 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_63 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV5 m_63 g_63 ep_63 1 1 0 bds_63 (dagTraceF m_63 s_63 7 f_63) (cur_63 0) (nh_63 0) s_63 7 = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_63 g_63 ep_63 1 1 bds_63 0 (dagTraceF m_63 s_63 7 f_63) cur_63 nh_63 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_63 : LowerBin m_63 s_63 g_63 8 :=
  lowerDagV5 (kn_cons lb_25 (kn_nil)) rc_63 nc_63 (by decide +kernel)

def m_64 : Nat := 0x5555555555555555
def s_64 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_64 : Nat := 0x1115155515555555
def ep_64 : Nat := 0x440400000000440000040000004004000400000000404000400000011101000100000000000000000000000
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_53, s_53, 7, g_53)]
def cur_64 : Nat → List (Nat × Nat) := fun _ => []
def nh_64 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_64 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV5 m_64 g_64 ep_64 1 1 0 bds_64 (dagTraceF m_64 s_64 7 f_64) (cur_64 0) (nh_64 0) s_64 7 = true := by decide +kernel
theorem nc_64 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_64 g_64 ep_64 1 1 bds_64 0 (dagTraceF m_64 s_64 7 f_64) cur_64 nh_64 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_64 : LowerBin m_64 s_64 g_64 8 :=
  lowerDagV5 (kn_cons lb_53 (kn_nil)) rc_64 nc_64 (by decide +kernel)

def m_65 : Nat := 0xaaaaaaaaaaaaaaaa
def s_65 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_65 : Nat := 0x2020a0202022a
def ep_65 : Nat := 0x2000020000002080000002800020008000000280002020a0202020800020200020202200000000000000000
def bds_65 : List (Nat × List Nat × Nat × Nat) := [(m_54, s_54, 6, g_54), (m_39, s_39, 5, g_39), (m_48, s_48, 5, g_48), (m_21, s_21, 5, g_21), (m_29, s_29, 5, g_29), (m_19, s_19, 5, g_19), (m_59, s_59, 5, g_59), (m_15, s_15, 4, g_15), (m_10, s_10, 4, g_10)]
def cur_65 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x113184a4e3264f9342390894e78cd533148c01f 6 63 2 3 10 1023 14 16383
def nh_65 : Nat → Nat := unpackHintV5 0xdf00a378a30070666a8b621162003658006c0000 0x6f18f600318de35580cf5ce79d1c015aed00518d6ac13cb39d74776c3d8e01828d5007bd6a8c2a63c700001bc600bd46800478f0e3ca7 16 65535 7 127
def f_65 : Nat → Nat × Nat := unpackForestF 0x212918cd93e14ccb42290894e148c01f 4 10
def ch_65 : Nat → Bool := dagCheckNodeV5 m_65 g_65 ep_65 3 7 bds_65 9 (dagTraceF m_65 s_65 7 f_65) cur_65 nh_65
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV5 m_65 g_65 ep_65 3 7 9 bds_65 (dagTraceF m_65 s_65 7 f_65) (cur_65 0) (nh_65 0) s_65 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65 : treeBlockF 0 9 ch_65 = true := by decide +kernel
theorem nc_65 : ∀ i, 0 ≤ i → i < 9 → ch_65 i = true := fun _ h1 h2 => treeBlockF_at nb_65 h1 h2
theorem lb_65 : LowerBin m_65 s_65 g_65 8 :=
  lowerDagV5 (kn_cons lb_54 (kn_cons lb_39 (kn_cons lb_48 (kn_cons lb_21 (kn_cons lb_29 (kn_cons lb_19 (kn_cons lb_59 (kn_cons lb_15 (kn_cons lb_10 (kn_nil)))))))))) rc_65 nc_65 (by decide +kernel)

def m_66 : Nat := 0xff00ff00ff00ff
def s_66 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_66 : Nat := 0x17005f0057007f
def ep_66 : Nat := 0x400020000000480000002800000000000000000006000a0002000800120000000200200014005000540040
def bds_66 : List (Nat × List Nat × Nat × Nat) := [(m_49, s_49, 6, g_49), (m_52, s_52, 5, g_52), (m_24, s_24, 5, g_24), (m_27, s_27, 5, g_27), (m_46, s_46, 5, g_46), (m_21, s_21, 5, g_21), (m_32, s_32, 5, g_32), (m_8, s_8, 4, g_8), (m_15, s_15, 4, g_15)]
def cur_66 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x10574c9ab35d226c9168dab1156768ea51c49b801f 6 63 2 3 11 2047 15 32767
def nh_66 : Nat → Nat := unpackHintV5 0xdf00a378a300706670006a8b62113658006c0000 0x6358d6318f60000bd1bce78efa19c146f18002d5abb42e73c79d02776c3d8e5bd635000468d540f1ea0958c60000b51a801e3c38f00031d 16 65535 7 127
def f_66 : Nat → Nat × Nat := unpackForestF 0x415d168ecd744a3945a26ac455849b801f 4 11
def ch_66 : Nat → Bool := dagCheckNodeV5 m_66 g_66 ep_66 3 7 bds_66 9 (dagTraceF m_66 s_66 7 f_66) cur_66 nh_66
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV5 m_66 g_66 ep_66 3 7 9 bds_66 (dagTraceF m_66 s_66 7 f_66) (cur_66 0) (nh_66 0) s_66 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66 : treeBlockF 0 9 ch_66 = true := by decide +kernel
theorem nc_66 : ∀ i, 0 ≤ i → i < 9 → ch_66 i = true := fun _ h1 h2 => treeBlockF_at nb_66 h1 h2
theorem lb_66 : LowerBin m_66 s_66 g_66 8 :=
  lowerDagV5 (kn_cons lb_49 (kn_cons lb_52 (kn_cons lb_24 (kn_cons lb_27 (kn_cons lb_46 (kn_cons lb_21 (kn_cons lb_32 (kn_cons lb_8 (kn_cons lb_15 (kn_nil)))))))))) rc_66 nc_66 (by decide +kernel)

def m_67 : Nat := 0xffff0000ffff
def s_67 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_67 : Nat := 0x175f0000577f
def ep_67 : Nat := 0x4020000000000000000000000048000000280000060a0000020800001200000002200000145000005440
def bds_67 : List (Nat × List Nat × Nat × Nat) := [(m_36, s_36, 6, g_36), (m_35, s_35, 5, g_35), (m_20, s_20, 5, g_20), (m_38, s_38, 5, g_38), (m_44, s_44, 5, g_44), (m_39, s_39, 5, g_39), (m_30, s_30, 5, g_30), (m_12, s_12, 4, g_12), (m_4, s_4, 4, g_4)]
def cur_67 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x10574c9ab35d226c9168dab1156768ea51c49b801f 6 63 2 3 11 2047 15 32767
def nh_67 : Nat → Nat := unpackHintV5 0xdf00a378a300706670006a8b62113658006c0000 0x6358d6318f60000bd1bce78efa19c146f18002d5abb42e73c79d02776c3d8e5bd635000468d540f1ea0958c60000b51a801e3c38f00031d 16 65535 7 127
def f_67 : Nat → Nat × Nat := unpackForestF 0x415d168ecd744a3945a26ac455849b801f 4 11
def ch_67 : Nat → Bool := dagCheckNodeV5 m_67 g_67 ep_67 3 7 bds_67 9 (dagTraceF m_67 s_67 7 f_67) cur_67 nh_67
set_option maxHeartbeats 0 in
theorem rc_67 : dagCheckRootsV5 m_67 g_67 ep_67 3 7 9 bds_67 (dagTraceF m_67 s_67 7 f_67) (cur_67 0) (nh_67 0) s_67 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67 : treeBlockF 0 9 ch_67 = true := by decide +kernel
theorem nc_67 : ∀ i, 0 ≤ i → i < 9 → ch_67 i = true := fun _ h1 h2 => treeBlockF_at nb_67 h1 h2
theorem lb_67 : LowerBin m_67 s_67 g_67 8 :=
  lowerDagV5 (kn_cons lb_36 (kn_cons lb_35 (kn_cons lb_20 (kn_cons lb_38 (kn_cons lb_44 (kn_cons lb_39 (kn_cons lb_30 (kn_cons lb_12 (kn_cons lb_4 (kn_nil)))))))))) rc_67 nc_67 (by decide +kernel)

def m_68 : Nat := 0xffffffff00000000
def s_68 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_68 : Nat := 0x1117175f00000000
def ep_68 : Nat := 0x6480000000000060048000000000006060a0000000011121200000000001114145000000000
def bds_68 : List (Nat × List Nat × Nat × Nat) := [(m_25, s_25, 7, g_25)]
def cur_68 : Nat → List (Nat × Nat) := fun _ => []
def nh_68 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_68 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_68 : dagCheckRootsV5 m_68 g_68 ep_68 1 1 0 bds_68 (dagTraceF m_68 s_68 7 f_68) (cur_68 0) (nh_68 0) s_68 7 = true := by decide +kernel
theorem nc_68 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_68 g_68 ep_68 1 1 bds_68 0 (dagTraceF m_68 s_68 7 f_68) cur_68 nh_68 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_68 : LowerBin m_68 s_68 g_68 8 :=
  lowerDagV5 (kn_cons lb_25 (kn_nil)) rc_68 nc_68 (by decide +kernel)

def m_69 : Nat := 0xffff0000ffff0000
def s_69 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_69 : Nat := 0x1117000017570000
def ep_69 : Nat := 0x640000000000000000000000006000000400000000600000602000011120000120200001114000014540000
def bds_69 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 5, g_22), (m_52, s_52, 5, g_52), (m_43, s_43, 5, g_43), (m_50, s_50, 5, g_50), (m_33, s_33, 5, g_33), (m_37, s_37, 5, g_37), (m_34, s_34, 5, g_34), (m_18, s_18, 6, g_18), (m_56, s_56, 6, g_56), (m_13, s_13, 4, g_13)]
def cur_69 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x1f 2 3 1 1 5 31 6 63
def nh_69 : Nat → Nat := unpackHintV5 0x860000 0x36779d6f5dcf359d1a3468d1a388888884 16 65535 8 255
def f_69 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
def ch_69 : Nat → Bool := dagCheckNodeV5 m_69 g_69 ep_69 3 7 bds_69 1 (dagTraceF m_69 s_69 7 f_69) cur_69 nh_69
set_option maxHeartbeats 0 in
theorem rc_69 : dagCheckRootsV5 m_69 g_69 ep_69 3 7 1 bds_69 (dagTraceF m_69 s_69 7 f_69) (cur_69 0) (nh_69 0) s_69 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69 : treeBlockF 0 1 ch_69 = true := by decide +kernel
theorem nc_69 : ∀ i, 0 ≤ i → i < 1 → ch_69 i = true := fun _ h1 h2 => treeBlockF_at nb_69 h1 h2
theorem lb_69 : LowerBin m_69 s_69 g_69 8 :=
  lowerDagV5 (kn_cons lb_22 (kn_cons lb_52 (kn_cons lb_43 (kn_cons lb_50 (kn_cons lb_33 (kn_cons lb_37 (kn_cons lb_34 (kn_cons lb_18 (kn_cons lb_56 (kn_cons lb_13 (kn_nil))))))))))) rc_69 nc_69 (by decide +kernel)

def g_70 : Nat := 0x1117175f1757577f
def ep_70 : Nat := 0x6404020000006480000402800060048004000280006060a0602020811121200120202201114145014545440
def bds_70 : List (Nat × List Nat × Nat × Nat) := [(m_69, s_69, 8, g_69), (m_66, s_66, 8, g_66), (m_63, s_63, 8, g_63), (m_26, s_26, 7, g_26), (m_68, s_68, 8, g_68), (m_62, s_62, 8, g_62), (m_64, s_64, 8, g_64), (m_25, s_25, 7, g_25), (m_65, s_65, 8, g_65), (m_42, s_42, 6, g_42), (m_36, s_36, 6, g_36), (m_67, s_67, 8, g_67), (m_60, s_60, 7, g_60), (m_53, s_53, 7, g_53), (m_54, s_54, 6, g_54), (m_47, s_47, 6, g_47), (m_12, s_12, 4, g_12), (m_49, s_49, 6, g_49), (m_8, s_8, 4, g_8), (m_61, s_61, 9, g_61), (m_45, s_45, 5, g_45), (m_15, s_15, 4, g_15), (m_6, s_6, 4, g_6), (m_46, s_46, 5, g_46), (m_43, s_43, 5, g_43), (m_11, s_11, 4, g_11), (m_4, s_4, 4, g_4), (m_34, s_34, 5, g_34), (m_44, s_44, 5, g_44), (m_40, s_40, 5, g_40), (m_30, s_30, 5, g_30), (m_16, s_16, 5, g_16), (m_28, s_28, 5, g_28), (m_27, s_27, 5, g_27), (m_33, s_33, 5, g_33), (m_38, s_38, 5, g_38), (m_58, s_58, 5, g_58)]
def cc_70_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xa00d0028013829c04d066813019804c02505280920c9024032009004802400f0c7803b05d80ec07213901c02e006e0b3100e4001 0xfa70076b28389a01a4700c270059b302a8e01347008a60082b783d59c1b6de0cb6b05db3828d8c126b60835703d2d01c9080d09406046028320104d0070680287c00c1a012dbc066d602367009b1c9317e408af1f35f8f1adc76d5e386a71b34b8d5a3c6297e2e4b715a5789d29c4892e2148f0da3f8591dc1c8de00466fb95f7acadbca55dd32a6e414b708a3b6a4fda8276c91375dc99ace4bd57256a312748c91a2417d060b67d8573b8299d012ce208e6903f3101d9140dc7f0663582f1801589409c400461601f0840d81605c010260003f 13 8191 6 63 11 2047 21 2097151
def cc_70_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xe870781c0d16832390c0e030162b0546a141a050154a048a41028040188c060210100000 0x1f17cf2b2f65939269b97cd5b3684d32269816cfeb7fb59fa6dfc36bd9b3e6d8f16b77b57b8ab5a53ab0c948349cbe4c1f242691834a9b7d0dae56cf1363 9 511 4 15 11 2047 17 131071
def cc_70_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xf0747a1d0e874365b0d0e832390c85cae161b0546a1504e241028040188c051281040800 0xbcdc2d565b2da2b94caadc29966a4532814c9cd82fd6fbb59ee35ab6d0ac16fac5aea167a258e795b9a55e604a9611a48648e4923024881f21024909be2a6b8699e0a63 9 511 4 15 11 2047 18 262143
def cc_70_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xe874383c0e070381a2d06472181c0602c560a8d4282aa50245208140200c460301080800 0x3ea7cf3597c264ec4d3a27ce459b8934de4d36a6cfd5bfe567f695bd24eee5bfa96be659f8163dc56f6157d41934024cc5f3287cc64931024d29bf3a6bc899f0a63 9 511 4 15 11 2047 18 262143
def cc_70_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xd87b03606c0cc790710dc3b4360691d01a01402614c098128640be52aa50090920202400708e018230050805 0x50d6aa04cd3e97276b54e1669b2b92448244984cd6a986a12048238a64747096b012a63234ae49234928b52290239b846d6794cef275aa411a479668c2b9875befeb3df45abb4df729aedd33da263b24b76095eb4b7d596ba92cf4c58e90add11579e25f344ae5c93c59234b04c1805a241a43834850490609204124436b866c7089ae0931c0233 11 2047 5 31 11 2047 19 524287
def cc_70_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x8480807270696861606052504948414040323029282120201210090801000000 0xa125f3a4ae6493c9923bdacb791a2e92e5c470b64cd6a972cd2e58c60afacb5d1a2b0ae55470a82cd4e57294ae51c60 8 255 3 7 11 2047 19 524287
def cc_70_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x902408c6308c2308862088211841f256950541505415054150541505414150131178501405008c02 0xdd4cdb259b58c66ae77d42cdc35bf82b3efb5ade4d7b898f6d2ded16bd82c7ae56f4c91e3230c6689a2dbf41b5e7b67ce6c79a9bf3135e5a67ca4c7928ff211de3a37c5466984d8349361233c12672c48f02384a123 10 1023 4 15 11 2047 19 524287
def cc_70_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x8c46214e570381a4d06830980b254aa142923a1c0e069341848840200e47031068200200 0xfe8d1fabe4176181a5f014adfe93bf1237d268f90d1ee923d82479460f4131e2123c63479688f0091f11fbd63b79c6eef8cdd5183ab4476c7eec8edd71bba63372240e48d1bfacb9d2f73256e549dc691b5523 9 511 3 7 10 1023 19 524287
def cc_70_8 : Nat → List (Nat × Nat) := unpackCursorV5 0x8944221027cbe1c6d96c345a0bb4722102803c9c4c4602c960b0431208040190c0442002 0x905658fa648ed658e1648b1208d5658cb688a9208b2348b4558bd658aa348a1649145590b598f12f8d92b8c12789923888348782485920852308684c8583c8534484924840248823f8723b8623783a338227c8117c803707f120 9 511 3 7 11 2047 20 1048575
def cc_70_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xe47c8380f00d47a8350662cc190720602c0180300600b47682c0d80ac3581e6b82700d85a089600800000000 0xa0565962349f9649e944952349d97c9314c9cc669c1449b14494a349a16c98a609806c9786096c5595a609945f974579635f9535794b478a85f8505b7f057790537504b720476303b480376a03f47837934668486aa2d6fa0d679f46f9e46b9d4679bc639ac5b99c5794234939569294e8986f8386b7e067778637485b718576984f6284b4584740043920159012f8e92b8d1278b923 11 2047 5 31 11 2047 20 1048575
def cc_70_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x8608418408218018007e15f05c15a15815614e44c14c04634414024003c23c03c03a13a01911611221010e1026001000 0xaf17cae16c4e0377b862b356fb1567afc6faec67adc57ad156ac94e8d86f8706b808677a8637605b730576404b4d047ac01599120989309801097920aab7097120aa07ca987096920a8d65a83689612095930a737095120a636094920a4824ab56fa9567a7c6fa6c67a5c57a535aa4342941208c06f8606b7f867798637585b728576384b4b847a383d992346b03f4a8379812497a3497234a217ca187ca10706a84f4a04796a34 12 4095 5 31 11 2047 20 1048575
def cc_70_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xc01786f05e0bc1782743c9780f01e03c06c6d81b0322640c05802e1582b01508b0140280500a008610020002 0xbf256c145fc0457bfa5bbea53be24bbd85bbd053bc823c8d6fc7d67c6b6bc5363c435bc3956c2018c1815bc014baa7cba07cb9870b8d65b8264b727cb626c500377d062bb56fb9567b7c6fb6c67b5c57b5256b4a4e8f06f8806b818677c0637685b738576484b4f047b4025b297cb207cb1870b0d65b0164 11 2047 5 31 11 2047 20 1048575
def cc_70_12 : Nat → List (Nat × Nat) := unpackCursorV5 0x7c9f0785e0745d0741b26c1a168191424f13c0d2340a324490150500c8300c030048100401000400 0xd0565cfc68cea5ccdc70cca66cc25ccb25cca460d3d6fd1567d0c5acf26fce26bcd267cba63caa5bc9a57c1014c817cc0014c7134c3018bf814bf014c6366c5934c2818be814c4934be014c325bc2a53c0860 10 1023 4 15 11 2047 20 1048575
def cc_70_13 : Nat → List (Nat × Nat) := unpackCursorV5 0xd86c343a0d060b0171b841e010078bc1c2e070381a2d0683409240201004420010000000 0xdea44dda66dd244dc244e0d6fdfd67df356de26bdca63dba5bdb035d987cd8d65d6b66da56fd9567d836fd7b6bd7367d6363d5b5bd5357d4956d323fd2a33d2470d187c 9 511 4 15 11 2047 20 1048575
def cc_70_14 : Nat → List (Nat × Nat) := unpackCursorV5 0xd4341c1300c0300c02f19e2709857f5c1615816054550541324c13026890240902048005c1004001 0xec056eb966ef934ef038ee834ec024eda3fed23beca37eba336c83f540373902f298273183af1b4ff134bf0347ee343eb156ea94e6c04f6504b53047410433803f3083b2883720833ea015e9144e795ce6934e6034e8b4fe834be7347e5b43e514e6b84f520473703f27837e4815e2c60e3b51e323be2237e185d510373602f26827e037c 10 1023 4 15 11 2047 20 1048575
def cc_70_15 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc330c8720c8302c025b94241902408c6308c23080e007c51e44110441013c45a140320842000800 0xfed65fdd65fd468ffc55ff359fe23bfca37fc0556683b568373b82f3482b2c02724023fb144f995cf8934f8038f783423832fab4ffa34bf9347f7343f694e6d04f6604b55847420433a83f3383b2b03722833f6015f44703302af5361f4a3bf3a37f306d6583b548373982f3202b2a02721823ed966f2144ed166ec966f095c 10 1023 4 15 11 2047 20 1048575
def cc_70_16 : Nat → List (Nat × Nat) := unpackCursorV5 0xe87a0e8337cc330c8720a6690a42909ca7094a50725b16c192641725c1705c16158160580e816405 0x43edf220adf0f567875ab3ea5ade32c6e895b8701ac321f21aadf0c56785d2b3f85bdf42d6f4967788b1ba056dc62af0a13f84c99c251c2110f90ad6f842b3c1f169f92def916b79cb3bc058dce2b6e215781c124189f205048f815b778a9c0c582078bf02c57810adc0654def0b6ee85373025c0404e0dadf05d678292b3dc5addc2c6e595b8241441009601048fea3b7ed1b95e0dc7905e2d027 10 1023 4 15 11 2047 21 2097151
def cc_70_17 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8b903115e4ba3742d1da0ae74d272ce09c10ee1842169cd0198a9a4308410091f2204403d0700e001c00000 0x11fc555bc97abe4ad4f24e9f1234f091c7a0d56d25eae92b53493a7448d392471d3564dc91c720d5352466f83d8dc1aad64bd5b256a59274cc91b624eda026e5e8370f00f83a05e348ab19b596c09db3c4de320aa6883b2ec1b87407c2a0360d8170240981004a3049cde14f6bca5b3851d8d2866f04f3402597211c88087178250e00f85006c1902e0301309c0d45ad85ae276cd1378b03699e0ecb706e1b01f0940d82e05c04026dd93f6b49db324dd8c2666e83f2d81b86a07c1602e1201a8a92b452939b929ed614b65ca3b1450cdc09e6704b2d02390c10e2804a1981f0880d82805c020271324e6dca7b5652d9528ec414336c2796411e2504a1881f0480bc46d45aa276c99378882e9600dc2f03e08017 11 2047 4 15 11 2047 21 2097151
def cc_70_18 : Nat → List (Nat × Nat) := unpackCursorV5 0x154aa0540a81502a0540798d104b004 0x8823f86a3b85637836337053f6d13b69d37645335d92f5992b55927515233843f30c371f82f17c270fc1f080179195b915578652b845279105b90c576cc2b68c275d01f5901b5501750c135cd2f58d2b54d27509239236187a3f8623b8423782e336fd3f6c93b6893763d335c92f5892b549275052391c6d9086c904603803f2fc371f02f174270f41f078175c52f5852b5452750123 11 2047 5 31 10 1023 20 1048575
def cur_70 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_70_18 (Nat.sub p 576)) (cc_70_17 (Nat.sub p 544)) (Nat.blt p 576)) (cc_70_16 (Nat.sub p 512)) (Nat.blt p 544)) (Bool.rec (cc_70_15 (Nat.sub p 480)) (cc_70_14 (Nat.sub p 448)) (Nat.blt p 480)) (Nat.blt p 512)) (Bool.rec (Bool.rec (Bool.rec (cc_70_13 (Nat.sub p 416)) (cc_70_12 (Nat.sub p 384)) (Nat.blt p 416)) (cc_70_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (cc_70_10 (Nat.sub p 320)) (cc_70_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Nat.blt p 448)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_70_8 (Nat.sub p 256)) (cc_70_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_70_6 (Nat.sub p 192)) (Nat.blt p 224)) (Bool.rec (cc_70_5 (Nat.sub p 160)) (cc_70_4 (Nat.sub p 128)) (Nat.blt p 160)) (Nat.blt p 192)) (Bool.rec (Bool.rec (cc_70_3 (Nat.sub p 96)) (cc_70_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_70_1 (Nat.sub p 32)) (cc_70_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 128)) (Nat.blt p 288)
def hc_70_0 : Nat → Nat := unpackHintV5 0x925521a3be1ae8ab488a1352f07f90a89dd34227308889b3032468b08218dd29e5aed11156c29e4d2d10923a22242e4c08f4c2da37a4b18d2c17a3180660b2926e28e877892322e21846107502221704c784cc1ea0ea49182852480444ba00281d20000140000000 0x30303030f03030f03030303038b0f83c3c3e0f1f0f0f0f0f030303030f43c2c3d0f0b0f0f0f0f030303031f13131f0f0f1b1b0f0f0f0f0f0f0f0f0f0f1b0f0f0f0f0f0f0f0f03030303030303031b1b1384e1b4f1b0b1b46d1b0b0f1f00f0f00f03c0300c1f04c1f07c030303030f031b03030303030303030303030303030303030303031b03030303030000c0c00e2c0c2c0c0d45c0e1f87d543d51b1b1b271b271b1b1b271b3f170f0f17030303031ba3b551f07c03031b031b0303030303031b000c038b17030f03130f0f17031f13035555551703c0307c1f04c44170b0f0f0f0f0b0b03032f272f2703031f1f1384e1f1f5555003035017030f0303030303130313035500d015150b45c0c3c0d503544c3c3c5d51f65031f130343d8b555555545c5c3c3c3c3c5c5d5548d46c6d540c0c6cbc6c8c0c0c6c8c4e1387ced55545c0f1411f00307c1f04c4403030317030f03540d1b50303030313033f134b03550000c0c00e2c3c0c3c0c3c3c3c3c0c7c4c0d0b42d0b40d0b42c3c0f00c1f07c1302c40f0f50f43c3c0c0cac9cac9c0c0c7c7c4e1387c7c2c2d542c2c00c0c2c0c03c0c3c0c0c0c0c0c4c0cdc4d1c0c2d40c00c2c000c0c2c03030f030f030f0f0f0f031f130343d8b50b0b42c2d2b0342d0b540c0c2c2c2cac0c0c2c7c2e0b82c2c2c2c2c3c3c3c3c3c3c3c3c0c0c6cac6c8c0c0c6c8c4e1387cec2c2d542c2c2c2c2c2c2c2c8c2c2c6c6c2c2c2c2c3c0f00c1f07c1302c40b0b00b1f00303030f030f03030303031303371347030b5030b0b03030b1b03030000c0c00e2c3c0c3c0c3c3c3c3c0c7c4c0d5555543c0f00c1f07c131103c3c2c2c3c2c3c3c0c0cac9cac9c0c0c7c7c4e1387c7d555400c0d403c0c3c0c0c0c0c0c4c0c4c0d54034054550b4ad55030f030f0365547c3c3c3c3c0c7c4c0d55543d8b52b555546c6d555548c3c3c3c3c3c3c3c3c0c0c6cac6c8c0c0c6c8c4e1387ced555547c7c14403c0f00c1f07c131100c0c0d46c6d5540c0c3c0c3c0c0c0c0c0c4c0cfc4d2c0d540003030038b40c0d17030b0387e1f03130b0f42d030b03170f0f171b1b1b271b271b1b1b271b3f03030303031b23031ba3b0b50b1f07c031f0303030303030303031b000c038b17030f03130f0f17031f130342d0b42d0342d0b1703c0307c1f04c0b105d0f0f0f0f503032f272f2703031f1f1384e1f1f0b0b550b0b003030b03017030f03030303031303371347030b50300c2c003030b00c0c5c0c3c0c4c3c3c5c0c7c4c0d42c2d0f62d0b40d0b42d503030b0b0b03030b1f0b82e0b0b0b0b0b17170f0f0f0f171703031b2f1b2303031b231384e1f3b0b0b550b0b0b0b0b0b0b0b230b0b1b1b0b0b0b0b1703c0307c1f04c0b102c2c0b00b0b1f1f003030317030f03030303031303371347030b5030b0b030b03030b0b1b1b03030000c0c00e2c0c0c0c0c4c7c4c7c0c0c0c0d0b42d0340d0b42c7c1f00c0307c1302c42f172b0f2b0f2f17030350340c0c7c7c4e1387c7c0c0d540c0c00c0c0c0c00c0c0c0c0c0c0c0c0c0c0c0c6c0c0d40c0303000c0c0c030303030303131f131f0303030342c2d2b0b40d8b5030342d0b0b170b0b0b0f0b0b542c7c2e0b82c2c0c0c0c6c5c6c3c6c3c6c5c0c0c0c0c0c0c0c0c6c6c4e1386cec2c2d542c2c2c2c2c2c2c2c6c2c2c6c6c2c2c2c2c7c1f00c0307c1302c40b0b00b1f00303030303030303030303030303031b0303503030303030303030b031b03030000c0c00e2c0c0c0c0c4c7c4c7c0c0c0c0d5555547c1f00c0307c13110bc5cac3cac3cbc5c0c0c0c0c0c0c0c0c7c7c4e1387c7d555400c0d400c0c0c0c0c0c0c0c0c0c0c0d540340545543d51703030303503131f131f65547c0c0c0c0d4ad555550362d546c5c6c3c6c3c6c5d46c6d555546c0c0c0c0c0c0c0c0c6c6c4e1386ced55547c1f11f0500300c1f04c440303030303030340d550303030303030303031b03550000c0c00e2c0c0c0c0c4c7c4c7c0c0c0c0cbcacacbc0c0c0c0c7c4c4c7c7c1f00c0c031f07c1307c1f06c5c6c3c6c3c6c5c0c0c6c6c6c4e1386c7c6c2c6d1b46c2c00c0c0c0c00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0303000c0c0c03034f034f0384e1384e033b3b3b3b033b3b031384e131f1f07c0307c131f21307c1f07c5c7c3c7c3c7c5c0c0c7c7c7c9c0c0c4c4c6c7c2c7d1f47c2c00c0c4c0c04c0c4c0c0c0c0c0c4c4ea84e2c0c4c0c4c0c031302a131f00380c0c0c0eaaa8fcdcfcdc0c0c0c0ea86c7c6c7c0c0c0c0eaa86c7d1b47c7c1f00c032207c1f00c0c0eaaaaaaa87e0a01b031b03aaaaaaaaa92d1d2d1c0c6c6c0eaaa86c6c6c6c0c6c6c0e82a0aaa86e2c6c6d1b46c7c1f00c1b28220881f07c0303030303131f131f031f130303031f13131f1b17230f1b0f231703031b1b2303031b231384e1f1b0b2346d230b1f07c0307c1f04c1f07c0303031b031b0303030303130313031b031b030000c0c00e2c2c2c0000c0c0c0c0c0c0c0c0c0c0c0c4c3c3c4c4e13131384c4c0c0c0c0c43d5005055550000000000000303030350303550303030303030303550042d03030303540d035130f0f13544d940c0c0c0d0f62d555555500000000000003030303540d035030303030303030355000038b05c00f01100100003000c0130201010000300c0c0c0c3c3c3c3c0c0c0c0d10b40d0342d0b030340c0c0c0c0c4c4c4c4c2d40c00000000000003c00c000200b0006c000c0c0c0c3c3c3c3c0c0c0c0d10b40d0342d0b0050030303030303030313131384e13130b0b00000000000000003030303030303030303030303503030303030303030300030303030f0f0f0f0303030343d8b50b0b40c0d030342d0b540c0c0c0c0c0c0c0c2c4c2e0b82c2c2c2c2c0000000000000c0c0c0c0c0c0c0c0c0c0c0c0d40c0c0c0c0c0c0c0c2c0c0c0c0000e2c0f003c003000c01302002c0b011002c0b0002c00000302c2c0000c0c0c0c0c0c0c0c0c0c0c0c4e13131384c4c3c3c3c3c0c0c0c0d40014555540000000000015540c0c0c0c0c0c0c0c0c0c0c0c0c0d540000e2c50b40d55030303030365544c3c3c3c3c0c0c0c0d55543d8b5035554000000000001035540c0c0c0c0c0c0c0c0c0c0c0c0d540000e2c400110003c00f000c003004c08040b0110000300c0c0c0c4c3c3c4c0c0c0c0d0b0b43c40d0342d0b5000030303030303030313131384e13130b0b000000000000000030303030303030303030303035030303030303030303000038b00c0c0c0c4c3c3c4c0c0c0c0d42c2d0f62d0340d0b42d503030303030303030b130b82e0b0b0b0b0b000000000000030303030303030303030303035030303030303030303000038b05c00f000c003004c0800b01002c0b0002c00000300c0c0c0c4c4c4c4c0c0c0c0c0c0c0c0c4c4c4c4c000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0000e2c17003c003000c01302002c040000c43434343434343434343 26 67108863 11 2047
def hc_70_1 : Nat → Nat := unpackHintV5 0x9de89ba5d534a952446245f1d48d3089a233232829cc61fb61e27a4c919dd91747318899b4c2f468dc8a98b43065f2875169d25a5560a294362444d946892542224338c30f6d2c23571088c592062cd89189af30e222c9207342ae14491103bb2ae06111b8000308 0xc0c0000c0c0000c0c03138cc7c4e331f0f0f0f0f03030303374dc2cdd370b0f0f0f0f0303030333131333000000000000031b03030303030303030303030303030303030303030303030303000030303030f03030f03030303038b0f83c3c3e0f1f0f0f0f0f030303030f43c2c3d0f0b0f0f0f0f030303033313133300000000000003c0003c0f0003c00f000c003013c0800b010000c3c0c6c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c00e2c0000c0c2c0c0d45c0e1f87d543d500270dc02709c01703c0300c3b211000c0c0c0c038b000c2c2c0005c0c3c0cbc9c0c0cbc9c0c0c4c3c3c5c4e331f138cc7c0cbc4c0c54014155540000000000005c0c3c0d546c6d40c0c0c0c4c0c4c0d54010b45c0c3c0d503544c3c3c5d51f65032f130343d8b5555555400000000000017003c0440040000c02f00ec0804040017030f03540d1b50303030313031303550038b000230f030f030f0f0f0f032b1303442d0b0b4ac0d0b42c01400c0cac9cac9c0c0ccc7c4e138cc7c2c2c0000000000000003c0c3c0c0c0c0c0c4c0c4c0c2d40c2c2c0c0c6c6c0c0c003c0c3c0c3c3c3c3c0cac4c0d0f62d42c2d0b0b4ac0d0b42d503030b0b0b2b03030b1f0b82e0b0b0b0b0b00000000000003c00f000c02b00dc0800b01002c0b0002c00003c0c3c0c0c0c0c0c4c0c4c0c2d40c2c2c0c2c0c0c2c2c6c6c0c0c00e2c0008c2c2c000ac9c0c0cac9c0c0c3c0c3c0c4e331f138cc7c3c3c3c3c0cac4c0d4001454ad5550000000000001b1b5550f030f0303030303130313035500050b4ad55030f030f0365547c3c3c3c3c0cac4c0d55543d8b52b5554423000000000000100044000f003c00300ac03b0201010011b5540c3c0c3c0c0c0c0c0c4c0c4c0d5400e2c0008d030345c0c2c0e1f87c0c4c2c3d0b40c2c0c0005c0f09c37009c27000c0300c270dc80b1000c0c0c0c0c0c038b000c5c0c3c0c4c3c3c5c0cbc4c0d0b442d0342d0b500003032f272f270303331f1384e331f0b0b00000000000000017030f0303030303130313030b5030b0b03031b1b030300017030f03130f0f17032f130350b0b43d8b42d0342d0b540c0c2c2c2c0c0c2c7c2e0b82c2c2c2c2c000000000000b08c017003c00300bc03702002c0400b02c000b000017030f0303030303130313030b5030b0b03030b1b03030038b0002303030303132b132f0303030342d0b5140d0b42cbc5cac3cac3cbc5c0140cc7c4e138cc7c0c0c0000000000000000c0c0c0c0c0c0c0c0c0c0c0c0d40c0c0c0c0c0c0c0c0c0000c0c0c0c4cac4cbc0c0c0c0d0b0b4ac2d0362d40c0d0b42c2c5c2c2c2c3c2c2d50b1f0b82e0b0b03030300000000000005c00f000c00300dc0800b02c04400b02c000b00000303030303030303030303030350303030303030303030038b000032f172b0f2b0f2f17030303030303000132b132f138cc7c4e331f03030303555000515500000000000003030303030355503030303030303035500543d51703030303503132b132f65547c0c0c0c0d4ad555550362d5400000000000017003c0400110000c03000c2700ec08040b0110000c0c0c0d035540c0c0c0c0c0c0c0c0d5400e2c0000c6c5c6c3c6c3c6c5c0c0c0c0c0132b132f1386c7c4e1b1b030303032f2b2b2f1b46c2c6d1b0b0303030327033313133300000000000000303030303030303030303030303030303030303030303030303004f034f0384e1384e031f171f0f1f0f1f1703031f1f1f27030300ecdcecdc0cdcec0c4e84c7d1f0b1f47c2c00000000000004c0c4c0c0c0c0c0c4c4e84c0c4c4e84c4c0e1303130300030313331333033313030303331313330000000005c00f000c0000800b010006c0c6c0c0c0c0c0c4c0c4c0c6c0c6c0c00e2c0008c2c2c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c4c3c3c4c4e13131384c4c0c0c0c0d55555555545c0f1407c6c00c0304c131100c0c0c0d41500c0c0c0c0c0c0c0d5440c42d03030303540d035130f0f13544d940c0c0c0d0f62d55555551703c5047c00c0304c131100c0c0c0d50340d40c0c0c0c0c0c0c0c4c0d5400e2c0c0c00c5c0c0c0c3c0c0d5540c0d40d540c0c0c0c0c0c0c0c0c4c0e0380c0d40c2d55540c8c0c0030303030f0f0f0f0303030343c0d0b0b40c0d030342d0b030303540c0c0c0c0c0c0c0c0c0c4c4c4e1384c4c2c2d540c0c3c0f00c0304c1302c40b0b01f1b003030303030303030303030313030350303030030303000c0c00c0c0c0c3c3c3c3c0c0c0c0d0f62d42c2d030340c0d0b42d503030303030303030b130b82e0b0b0b0b0b0f03c0300c1304c0b102c2c02c7c00c0c0c0c0c0c0c0c0c0c0c0c4c0c0d40c0c0c0c0c0c0c0c0c00e2c0c0c00c3c0c0c0c3c0c0c0c0c0c0c0c0c0c0c0c4c0e0380c0c0c2d540c0c0c2c0c2c0c0c0c0c0c2c0c0c0c0c0c0c8c0c00b03030303030303030303031384c4e130f0f0f0f03030303555555551b0403c0f00c0304c131100c6c0c0c0c0c0c3c0c0c0c0c0c0c0c0c4c0c0c0c0d5540c6c0c2c2c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c4e13131384c4c3c3c3c3c0c0c0c0d5555550f50355547c6c1403c0f00c0304c1311151400c0c0c0c0c0c0c0c0c0c0c0d540340c0c50b40d55030303030365544c3c3c3c3c0c0c0c0d55543d8b50355551f0500f03c0300c1304c4450355503030303030303030303030303031303550038b03030503555550303030f0303030f0303030303030303030303130380e03035555032303000c0c0c0c4c3c3c4c0c0c0c0d0b40d0340d0b42d03030303030303131384e130b5031703c0300c1304c0b102c06c00c5c0c0c0c0c0c0c0c0c0c0c0c0e0380c0c2d40c0c0c6c0c0c6c0c0c0c0c0c4c3c3c4c0c0c0c0d0b40d0340d0b42d40c0c0c0c0d030303030303030313131384e13130b0b5503031703c0300c1304c0b102c2c07c6c00c0c0c0c0c0c0c0c0c0c0c0c4c0c0d40c0c0c00c0c0c00c0c0c0c03030303130f0f130303030350b0b43d8b40d0342d0b540c0c0c0c0c0c0c0c2c4c2e0b82c2c2c2c2c5c0f00c0304c1302c40b0b00b1f0030303030303030303030303130303503030303030303030b0303030038b0303003170303030f0303030303030303030303130380e0303030b030b550340c0c0c2c0c2c0c0c0c0c0c2c0c0c0c0c0c0c8c0c003030303131313130303030303030303131313131f07c0300c1304c1f07c0303030303030303030303031303030303030038b0303003170303030f0303030303030303030303130380e0303030b0340d0303032303000c0c0c0c0c0e2c0c3c0c0c0c3c0c4c3c3c5c4e171f1385c5c0c0c0c0c5c3c3c5c5d170b1745c2c0c0c0c0c7c4c4c7c5c5c3c3c3c3c5c5c5c5c5c5c5c5c6cac5c5c6c6c5c5c5c5c0c0c0c0c0c0c0c0c6c6c4e1386d3c6c2c6d1b46c2c5c0f05c5c05c7c00c0307c1307c1f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c6c0c0c0c0c0c0003030038b030303030f0f0f0f030303030f0f0f0f030303031f13131f0f03c0300c1f04c1f07c0f0f03030303030303030303030303031f1f1384e1f1f3f0b3f4fd3f0b00303030300303030303030303030303031b0303030303003030000c0c0c03030303 26 67108863 11 2047
def hc_70_2 : Nat → Nat := unpackHintV5 0x95609fa3ab35a89b89ea13527281fc5b1f6e22277d8bc1d021e86f78921acd22264bccf18851545e4c79166725855d479144725c4cd88891b230844d03f10a11263f40688e8129e3201008b851f629d08888eb3121e58aa858042c11709202e82e80664a78000332 0xc0d030f0f0f0f0303030355555550303555030355331f1384e331f55550f0f0f0f030303033313133355371f370dc7cdc0303030303030303030303031b03555030b03030303030303030303030303030303030f03030f03030303038b0f83c3c3e0f330f0f0f0f030303035543d0f5543d543d50f540d50356553d555555555550f230f03c3c3c0f0f0f0f030303033313133348d151540c3c0c6c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c6c0d40d5540e2c0c0c0c0c0c0c0c0c4cac4cbc0c0c0c0d55555546c5c6c3c6c3c6c5d51b1b1384e1b1f55552f2b2b2f0303030333131333551b1f1b06c6c6c0303030303030303030303030303550303030303030303030303034f034f0384e1384e0355555551f171f0f1f0f1f1703031f1f1f2703035555547c7c7c7c0c7c7c0c4e1384c7d547c7c7c1f1f1f04c0c4c0c0c0c0c0c4c4ea84e2c0d542c2ea131f0b0b0384c0c4c0c0c0305c0c5c0e1f87d52749d5274dd0f45d0340d91f5550303c0f0f031f1f106c0c6c0c0c0c0c0c0c6d03540e2c5c0c3c0c4c3c3c5c0c7c4c0d55555515400c0cbc9cbc9c0c0c7c7c4e1387c7d555503c0307c1f04c440f0f05017030f030303030313031303550b0b0303170b030300c6c005c0c3c0c5c5c0c0c5c0c0c4c3c3c5c4e17331385c5c0c7c4c0d50f545d55175551745d52f540d5951f5555555555540f22c3c3c03c3c3c0c1f07c1311f0504417030f0317170303171b030303030303130337134b0350b555038b00c6c0f030f030f0f0f0f032b130355555550f0f5503032b272b270303331f1384e331f05000000000000000f030f03030303031303371357035450b0b000000f030f030f0f0f0f032b1303543d50f54ad50356547d555555503c8b00002b0000000000f00300ac03302010004400404000f030f030303030313033f13570350b555038b00000c1b00f030f030f0f0f0f031f1303555555504503032b272b2703031f1f1384e1f1f55550f100c1f07c131105c5c1403c0c3c0c0c0c0c0c4c0c4c0d542c2c0c0c3c2c0c0c031b000f2b03030f0f03030f030f030f83c3c3e0f330f0f0f0f031f13035543d0f5543d543d50f54ad50356547d55550f42d55555550f0f170f0f003c8b030ac7c8c1f04c47c141103c3c6c6c0c0c3c3c0c3c0c0c3c0c3c0c0c0c0c0c4c0cdc4d7c0d42d5540e2c031b05c0c0c0c5c0c21f87c0c4d0f45d52749d5274dd503540d91f555503c000000c0c0c0c0c0c0c6d03540e2c5c0c3c0c4c3c3c5c0cbc4c0d5555555545c5c0c0cbc9cbc9c0c0ccc7c4e138cc7c14000000000000005c0c3c0c0c0c0c0c4c0cdc4d2c0d442c2c000005c0c3c0c4c3c3c5c0cbc4c0d50f545d52f540d5951f55555554000f22c000000000017003000330201000440040b0110005c0c3c0c0c0c0c0c4c0cfc4d2c0d42d5540e2c00000c0c06c6c00c0c0c0c4cac4cbc0c0c0c0d555554bc5cac3cac3cbc5d40c0d54cc7c4e138cc7c14000000000000000c0c0c0c0c0c0c0c0c0c0c0c6c0d440c0c000000c0c0c0c4cac4cbc0c0c0c0d50f545d503540d5951f5555555400ac00c8b000000000005c00f000c0cc08040011001010000c0c0c0c0c0c0c0c0c0c0c0c6c0d40d5540e2c00000c0c00c6c00c0c0c0c4c7c4c7c0c0c0c0d555554bc5cac3cac3cbc5d41147c7c4e1387c7d55547c1f00c41f04c44030305003030303030303030303030355030303030303030300c0c1f17230f1f0f231703030303004c7c4c7c4e1f231387ccc0c0c0c0d50f545d551f47d55235503540d5951f5555555555547c2b1f2300c0c0c0c0c00322c7c1311f0504403030303030303030303030303030303030303031b03503555038b00c0c03030303aaaa555555655555554dcfcdcfc0c0c0c0ea91f5555aaaaa96555aa1b031b03aaaaaaaaa9555555642d55662d555555642d5554b575f4b031b1b03aaaa47d55540c0c4ccc4ccc0ccc4c0d50f545d5540d595555555540c0ccc4c4ccd23454551b031b03030303031303130350b555038b1b031b030030303030300c0c0c0c0c0c0c0c0c0c0c0c4c3c3c4c4e13131384c4c0c0c0c0d0b42d42c2d42c2d0340d0b42c0c0f0f0f00c0c03c3c00c0304c1302c4030303030303503030340c0c0c0c0c0c0c0c0d40c030300030303030303030303030303130f0f131384c4c4e13130303030342d0b50b0b50b0b40d0342d0b03c8b0f0f00f0f0f0300c1304c0b100c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d540e2c030300c5c0c0c0c3c0c0c0c5c0c5c0c0c0c0c0c5c0c0c0c0c0c0c0c0c0c0c0c0c0c0c4c0e0380c0c0c2c0c00c0c0c7c15030303030f0f0f0f0303030342d0b40d0342d0b0000000003030f0303030303131313130b550000c0c0c0c3c0c0c0c0c0c0c0c0c0e0380c0c2c0c0000c6c0c0c0c0c0c3c3c3c3c0c0c0c0d0b42d0340d0b42c000000000c0c0c0c3c3c0c0c0c0c0c0c0c0c0c0c4c4c4e1384c4c2c2c00000000c0c0c0c0c0c0c0c0c0c0c0c0d4000500030303030f0f0f0f0303030342d0b40d0342d0b03c8b000003000000f003000c01302002c0400030303030303030303030303030355038b000003030030030f0303030f0303030303030303030303130380e0303030b030000032300000303003005400c0c0c03030303030303030303030303031384c4c4e13130f0f0f0f0303030350b0b50b0b42d0b40d0342d0b17170030300f00c0300c1304c0b100c0c0d03035030303030303030303030303030355038b0300c0c000c0c0c0c0c0c0c0c0c0c0c0c3e0f0f0f83c4c3c3c3c3c0c0c0c0d42c2d42c2d0b42d0340d0b42c3c3c5c3c3c00f22c0c03030304c1302c40303030303030303030303030303030303030303030355038b00c0c030f0303030303030f030f03030303030f0303030f0303030303030303030303130380e0303030b0300300c0c0c7c0c7c1503030303130f0f130303030342d0b40d0342d0b000f00000005c5c0c0c0c0c0c0c0c0c0c0c0c0c0c0c4c4c4e1384c4c2c2c00000000c0c0c0c0c0c0c0c0c0c0c0c0c0d540e2c00050003030303130f0f130303030342d0b40d0342d0b0003c8b00000005c00c003004c0800b010000c0c0c0c0c0c0c0c0c0c0c0c0c0d540e2c0000300c00c5c0c0c0c3c0c0c0c0c0c0c0c0c0c0c0c4c0e0380c0c0c2c0c00000000c0c00c01503030303131313130303030342d0b40d0342d0b03030303131313130b50b030303030303030303030303030355038b0303030303170303030f0303030303030303030303130380e0303030b030300c0c0c8c0c540c0c0c0c0c0e2c0c3c0c0c0c3c0c4c3c3c5c4e171f1385c5c0c0c0c0c5c3c3c5c5d170b1745c2c0c0c0c0ccc4c4ccc00000000000017003c01705c00170ac0003000c04f02002c04000303030303030303030303030303030303030303030303030038b00003 26 67108863 11 2047
def hc_70_3 : Nat → Nat := unpackHintV5 0xa34517a7552f894691da3a52ea8958a7a1821a880eca39e3e3fa74a08b1ba53066950a8983e42c5d7470964a226534cbb93be22a48ecc190f428e3b39130d9726e3218888b0330628147f08e124820686386f424c1590c804b515e0ef87b82922580684788000342 0x303030303038b030f0303030f03130f0f171385cac4e17170303030342d0b50b0b50b0b40d0342d0b0b170b0b0b0f0b0b0b170b170b0b0b0b0b170b2b0b0b0b0b03030303030303030b4f0b82e0b0b030303170f0f1717171705c8c5c03030303331313330b50b0b0b0b02c8c2c03030303030303030303030303030303030303035038b50303540c0c0c0c0c0c2c2c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c4e331f138cc7c3c3c3c3c0c0c0c0d40c0d40c0d0b42d0340d0b42cfc7cfc3f1f3f03c3c3c3c0c0c0c0ccc4c4ccc2d42d503030340c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d540c0c0c0c0c0c0c0c0c3c0c0c3c0c0c0c0c0e2c3e0f0f0f83ccc3c3c3c3c0c0c0c0d42c2d42c2d0b42d0340d0b42c2c3c2c2c2c2c2c2c3c2c3c2c2c2c2c2c3c2c2c2c3c2c2c0c0c0c0c0c0c0c0c2d3c2e0b82c2c0c0c0c3c8c3c0f0f0f03c3c3c3c0c0c0c0ccc4c4ccc2d42c2c2c2c0b230b00c3c0c6c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d40e2d40c0d5030303031b171b0f1b0f1b1703030303030b03132b132f1386c7c4e1b1b0303030342d0b503035030340c2d030342d0b2f2b2b2f1b1b1b06c7c6c030303032703331313330b50b030303030340c0d40c0c0c0c0c0c0c0c0c0c0c0c0d40c0c0c0c0d3c0d3c0e1384e1380c7c5c7c3c7c3c7c5c0c0c7c7c7c9c0c0c2c2c2d0b42d0b40d82d0b0b50b03503031f1f1f1f031f1f0313a131f1f1f07c7c7c0b50b13031303030303031313a13035a1340e0b503130313030300c1703170387e1f42d0b270b3f0b0b0b270b270b0b0b170b0f0b030303031fa0b03030303c0f0f031f0b07c0303030340e2d0350b0b00b0b0b0bc9c0c0cbc9c0c0c5c0c3c0c4e1f1f1387c7c4c3c3c5c0c7c4c0d40c0d42c0d0b42d0b40d0b42c2c2c03c3c02c0f00c1f07c1302c41740c0d40c0c5c0c3c0c0c0c0c0c4c0c4c0c2d40c031b0017030f0317170303170303130f0f171385ccc4e1717031f130342d0b50b0b50b0b42d0342d0b0b170b0b0b0f0b0b0b170b170b0b0b0b0b170b0b0b0b0b03030b0b0b2f03030b1f0b82e0b0b03030303c8b0f0f00f0f0f0307c1f04c0b102c2c02c7c05c0c3c0c5c5c0c0c5c6c0c0c0c0c0c0c4c0c4c0d40e2d40c0d500c6c0f030f030f0f0f0f032b13030b0b0b0b0f0f0b0b03032b272b270303331f1384e331f42d0b42d0342d0b003030000002b0000000003c0c3c0c0c0c0c0c4c0c4c0c0140503000f030f030f0f0f0f032b130342d0b42d0342d0b0b0f0b0b0b0f0b0b03030b0b0b2b03030b1f0b82e0b0b03030303c8b00002b0000000000f00300ac03302002c0400b02c000b00000f030f0303030303130313035038b503035400000c0c06c6c02c2c02c0b0b0f030f032b2703032b2703030f0f0f0f1387c7c4e1f1f031f130342d0b50b035030342d0342d0b0f02c171700b0b0030ac7c8c1f04c0b103c0c3c0d40c0c3d030303030303130313030b550300c6c003cac0c0c3c3c0c0c3c0c3c0c3e0f0f0f83ccc3c3c3c3c0c7c4c0d0f50b0b50b0b0b0b42d0b42d0342d0b0b0f0b0b0b0b0b0b0f0b0f0b0b0b0b0b0f0b0b0b0f0b0b03030b0b0b2b03030b1f0b82e0b0b0303030f0f170f0f003c8b030ac7c8c1f04c0b102c2c02c7c03c6c0c0c3c3c0c0c3c0c3c0c0c0c0c0c4c0c4c0d40e2d40c0d500c6c170303031703087e1f031342d0b5170b0f0b270b3f0b0b0b270b270b0b0b03030303030b27031fa0b030303c000000c0c0c0c0c0d038b40d45c0c3c0c4c3c3c5c0cbc4c0c5c5c2c2c2c2c2c2c0c0cbc9cbc9c0c0ccc7c4e138cc7d0b42d0b40d0b42c00c0c000000000000005c0c3c0c0c0c0c0c4c0c4c0c014055030017030f03130f0f17032f130342d0b42d0342d0b0b170b0b0b0f0b0b03030b0b0b2f03030b1f0b82e0b0b0303030003c8b000000000005c00c000cc0800b02c04400b02c000b000017030f0303030303130313035038b50303540000306c00c0c0c0c4cac4cbc0c0c0c0cbc5cac3cac3cbc5c0c0c0c0c0c0c0c0ccc7c4e138cc7d0b42d0340d0b42c00c0c0000000000000000c0c0c0c0c0c0c0c0c0c0c0c014055030003030303132b132f0303030342d0b40d0342d0b0b170b0b0b0f0b0b03030303030303030b1f0b82e0b0b030303002b00322c0000000000b08c017003c00303302002c0400b02c000b00000303030303030303030303035038b50303540000300c00c0c0c0cbc5cac3cac3cbc5c0c0c00c0303131f131f030303031387c7c4e1f1f42d0b40d03503035030342d0b1f07c0300c03030030301f04c0b100c0c0c0c0c0c0c0d40c0c0d0303030303030350300c0c1f17230f1f0f231703030303004c7c4c7c4e1f231387ccc0c0c0c0d0b42d42c2d42c2d0340d0b42c2c5c2c2c2c3c2c2c2c8c2c2c2c2c2c2c7c2c7c2c2c2c2c0c0c0c0c0c0c0c0c2c9c0c0c2c7c2e0b82c2c0c0c0c7c2b1f2300c0c0c0c0c00322c7c1302c40b0b02c02c2c7c7c00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d40e2d40c0d500c0c0303133313330333130342d0b42d0342d0b0b170b0b0b0f0b0b03030b0b0b03030b0b82e0b0b0303030303331313330b50b0b0b0b02c8c2c1b031b0303030303130313035038b50303546c0c6c0c15500c0c0c0c0c0c0c0c0c0c0c0c4c3c3c4c4e13131384c4c0c0c0c0d555555555503c500f0f00300c1304c4403030303030303030303030303030303030303035500c0c000c0c0c0c0c0c0c0c0c0c0c0c4c3c3c4c4e13131384c4c0c0c0c0d55555555540f22c3c3c03c3c3c0c0304c131100c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c4c0d40e2d540303117543d51745d551755503540d513565541151f47c10340c0c0c0c3c3c3c3c0c0c0c0d5555540f00000300001543c3d40c0c0c0c0c0c0c0c4c4c4e1384c4c014000000c0c0c0c0c0c0c0c0c0c0c0c4c0d4540000c0c000c0c0c0c3c3c3c3c0c0c0c0d5555540f22c00000c000003c00c003004c0804040003030303030303030303030313035038b5500000c03043d50f540d503544d595500000005040103403030303030303030303031384c4e130f0f0f0f030303035555555551700c0f100c0304c131111b5543d40d55135554547c05450303030303030303030303031384c4c4e13130f0f0f0f03030303555555555517170500f0f103c0c03030304c131100c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d035500c0c000c0c0c0c0c0c0c0c0c0c0c0c3e0f0f0f83c4c3c3c3c3c0c0c0c0d55555555543c3c5c3c3c00f22c0c03030304c131100c3c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c4c0d40e2d54030310f5550f43d550f543d503540d51356554151f040d03030303130f0f1303030303555555000000001703030303030303131384e135150045d55540d559540011b40c0c0c0c4c3c3c4c0c0c0c0d555554000000005c5d5540c0c0c0c0c0c0c0c4c4c4e1384c4c014000000c0c0c0c0c0c0c0c0c0c0c0c4c0d031500003030003030303130f0f13030303035555550003c8b00000005c00c003004c0804040003030303030303030303030313035038b5500000303003045d50f540d503544d5955000048c0001410040d03030303131313130303030355555503030303131313135503030303030303030303030313035038b550303030345d50f540d503544d59554548d10340c0c0c0c0c0e2c0c3c0c0c0c3c0c4c3c3c5c4e172b1385c5c0c0c0c0d50f545d55174ad551745d503540d5954f5555555555545c3c3c5c5c5c5c17231700c0c0c0ccc4c4ccd234545503030303030303030303030303030303030303031b03503555038b03030303 26 67108863 11 2047
def hc_70_4 : Nat → Nat := unpackHintV5 0xd9116f6a4848341e20d945194c258fa5f0045ad8c3e95bb216ac982855dc0e2a6011d49b12aa298484f1c46264429526d16a936800492c1122e23690602227d58b53968a89888858ae72ba4732011f388c0c9660c5272481d99740aec7c02965c0000296 0x12c0d7c0ea0fa85eaa80eaaaaa42d0b42d035a582d982c5c2c2c2c3c2c2c0c0c2c2c2c0c0e82eaaaa82c2eaaa801f07c0307ca1f1f0a2088122d4151303130303030303a13aaa038b0b55030b0b030b03030b0b131b030300c4c4c7c2703a170f0f17aaa550048b01703c0300c881b09c01b06c0400303030303030030300c6c170f0f17083e17a89e27a89e7b80e03aaa55555642c000000c0c0c0e03a80e2d412c0d2c0eaaa8dc5cdc3cdc3cdc5c0c0cdc9cdc9c0c0c2801555555555400000000004004c0c4c0c0c0c0c0e884c4c001554012c0d2c0ea0fa85eaa80eaaaaa55555555642d54000000000048b0005c00f000c002000880080804004c0c4c0c0c0c0c0e84eaa80e2d554000000c0c04c6c09c0e85c3c3c5eaa90f45d0340d9951b46d51b49d5407c1b10b44030303030303035034b034b03aaaa5555554b174b0f4b0f4b1703034b274b2703035a5550451f07c0307c8850440b0b0a01303130303030303aa680e2d5544c4d555500c4c4c7c4b034b03a83ea17aaa03aaaaa950f545d55b540d559955956565555555555007c1f00c1f21f0a08850b50104c0c4c0c0c0c0c0e84eaa80e2d13555540d5540313131f10b1f12c0c9c7700c0c6e6390b2306c0e2e2e0f90b42c7c2312c0f00c9c81b038b031b2703a170f0f17aaa42d0b00041703c0300c0309c881b09c01b06c00b000c0c0c0c0c0c030309c0e85c3c3c5eaa95400122c0c0c0c0c0c0d2c0d2c0eaaa92d2d2d2c0d2d2c0d940000000004c0c4c0c0c0c0c0ea8a038b135540012c0d2c0ea0fa85eaa80eaaaaa555555556554000000000048b1303130303030303a13aaa038b555000170f0f170327083e17a89e27a89e6b80e2780e03aaaa42d030b039660b0b0008230000c0c0c0c0c0e03a80e2d422d1c3c3d0b1f06c0d2c0c0eaaa91c5d1c3d1c3d1c5c0c0d1c9d1c9c0c0c28010b42d0b40d996942c2c0000000000004c0c4c0c0c0c0c0e884c4c0002d40c012c0c0ea0fa85eaa80eaaaaa42d0b42d0365a5a0b0b660000208c00000000405c00f000c002000880080800b001303130303030303a13aaa038b0b55030000003030131b00303a83ea17aaa03aaaaa80c0e6a60baa030388e2a2a84c0c4c0c0c0c0c0e84eaa80e2c4c0c4c4c0c4c0c4c4c0c0c0c0c0e0f83e0380d0342d030340c0d90b030303540c0c0c0c0c0c0c0c0c0c4c4ea82c2c2c2d540c0c3c3c3c3c0c0c0c0c4e84c2d42c7c7cdc1f1f3700c0c0c0c0c0c0c0c0ea80c0d40c0c0e80c0c0e030303030303030383e0f80e0343d8b50b0b40c0d0303642d503030303030303030b13aa0b0b0b0b0b0f0f0f0f0303030313a130b50b0b0b0b02c7c2c03030303030303030303aa038b03503030303030303030303030303030f0303030f03030303030303030303031303030b030b550340c0c0c2c0c2c0c0c0c0c0c2c0c0c0c0c0c0c03030323032a0303030383e1380e0342c2d0f0340d03642d40c0c0c0c0d03030303030303031313aa0b0b0b0b550303170f0f170303030313a130b50b1f1f3707c7cdc03030303030303030303aa038b03035030303a03030380c0c0c0c0c0c0c0e0f84e0380d42c2d0f62d0340d90b540c0c0c0c0c0c0c0c2c4ea82c2c2c2c2c5c3c3c5c0c0c0c0c4e84c2d42c2c2c2c0b1f0b00c0c0c0c0c0c0c0c0c0ea80e2c0d40c0c0c0c0c0c0c0c0c0c0c0c0c0c5c0c0c0c3c0c0c0c0c0c0c0c0c0c0c0c4c0c0c2d540c0c0c2c0c2c0c0c0c0c0c2c0c0c0c0c0c0c03030323032a0303030383e0f80e030f0f0f0f0303030313a13000003000000c0c0c0c3c3c0c0c0c0c0c0c0c0c0c0c4c4c000dc2ced3b4dc2c00000c0c0c0c0c0c0c0c0ea803030303000a000303030383e0f80e030f0f0f0f0303030313a1303c8b000003000000f003000c01302002c040003030303030303030303aa038b0303030300000c030030f0303030f03030303030303030303031303030b0340d0303000003230000030300300a80c0c0c0e0f84e0380c5c3c3c5c0c0c0c0c4e84c003c000000171703030303030303030303030303031313000370b3b4ed370b000003030303030303030303aa038b00c0c0c0c0028000c0c0c0e0f84e0380c5c3c3c5c0c0c0c0c4e84c000f22c00000017003000c01302002c040003030303030303030303aa038b0303030300000c03003170303030f03030303030303030303031303030b0340d03030000000030300300a80c0c0c0e1384e0380d0b42d0340d90b000000003717370f370f3717030303030303030313130000b0b5503030000030303030303030303aa00d40c0028000c0c0c0e1384e0380d0b42d0340d90b00000000107c17003c003000c01302002c000c0c0c0c0c0c0c0c0c0ea80e2c0d40c0000300c00c5c0c0c0c3c0c0c0c0c0c0c0c0c0c0c0c4c0c0c2c0c2d540d0303000003230000030300300a80c0c0c0e1384e0380cecec0c0c0c0c4e84c7c7c0c0c0c0c4e84c7cec7c0c0c0c0c0c0c0c0c0c0ea80e2c0c0c0c0c0c0c0c0c0c5c0c0c0c3c0c0c0c0c0c0c0c0c0c0c0c4c0c0c2c0d0340c0c0c03030323032a 25 33554431 11 2047
def hc_70_5 : Nat → Nat := unpackHintV5 0x893135433e56a0b33b0fc7a4879b92139b0cb1bd8400d5924c67b4c531a88c973966cb10232520d9d272e76126a4b48d298a4231191e0ac38e113d0670a602eb9331444c6096f2cc43e9e41d21350cac79051f4dc20323209cd93034e66010628400020c 0xc9c0c0c0c0eaaaa86c5c6c3c6c3c6c5eaaaaa2f2b2b2f03030303aa1b46c2c6d1b0b2f2b2b2f03030303aa1b1f1b06c6c6c03030303030303030303aa03030303030303030303030303030303030b030351703a89e27a89e7b83e1780e03aaa550f555590b1f07c23206c0c6c0c0c0c0c0e03a80e2d40c6c5c0c3c0eaaaaaa82c2c0c0cbc9cbc9c0c0d695555555555545c3c3c5c0cbcbc0ea92c7cfc4b1f3f1544c0c3c0c0c0c0c0e984c4d5555544c0c4c0d0b45c0c3c0d50356a0fa85d5565a55a8bea03aa5665aaa90f62d555555555642d545c3c3c5d511f4032f2f0388e2a2a9544c0c3c0d50344d40c0c0c0e84eaa80e2d5544c0c4c4d2c0c3c0c3c0eaaaa96680c0cac9cac9c0c0eaaa90f90b0b42c2d2b03665a50b0b0f0f0f0f032b2b03aa371f470dc7d1c0b50b0f030f0303030303aa131303030b0b03030b503130313030f030f03a83ea0fa8aea03aaaaa90f62d42c2d0b0b4ac0d6960b66540c0c2c2c2cac0c0e82eaaaa82c2eaaa82c2c2c3c3c3c3c0cacac0e238a8aa0b50b0b0b0b02c7c2c0f030f0303030303a13aaa038b0b55030b0b030b03030b0b131b03031303131347030f030f03aaaaa0b0baa03032b272b2703035a555543d4ad55555550f0f0f0f032b2b03aa4b1f3f12c7cfc550f030f0303030303a9a1313555555130313134b0350b4ad55030f030f035a55555aa0fa83ea2ba80d955aaaaaa55550f62d4ad555555547d1503c3c3c3c0cacac0e238a8aa5544d55030f030f0303030303a13aaa038b555130313134b0340c0d17030b0383e17a89e27a89e6ba80ea03aaaa0b0f42d030b039660b0b1f07c032723200c0c0c0c0c0e03a80e2d40c6c5c0c3c0eaaaa6a940c0cbc9cbc9c0c0eaaa90b642d03665a50b0b170f0f17032f2f03aa371f470dc7d1c0b50b13030f0303030303aa131303030b0b03030b50313031313470317030f03a83ea17a8bea03aaaaa942c2d0f62d0b40d969682c2d99503030b0b0b0303a0baaaaa0b0ba0b33aaaa0b0b0b170f0f17032f2f0388e2a2a82d42c2c2c2c0b1f0b04c0c3c0c0c0c0c0e84eaa80e2c2d540c2c2c0c2c0c0c2c2c4c6c0c0c4c0c4c4d1c0c0c0c0c0eaaa8bc5cac3cac3cbc5e966aaaa90b42d903665a503032f2b2b2f03030303aa371f470dc7d1c0b50b0303030303030303aa030303030303030303503030303031b0303030303a83ea17a80ea03aaaaa90b0b4ac2d0362d40c0d969682c2d982c5c2c2c2c3c2c2d5a0baaaaa0b0baaaa0303032f2b2b2f0303030388e2a2a82d42c2c2c2c0b1f0b00c0c0c0c0c0c0c0e80eaa80e2c0d540c0c0c0c0c0c0c0c2c0c6c0c0c0c0c0c0c6c0c0c0c0c0eaaa8bc5cac3cac3cbc5e80c0ea969555555555554bcacacbc0c0c0c0ea92c7cfc4b1f3f1540c0c0c0c0c0c0c0e980c0d5555540c0c0c0d50f545c0c0c0c0d40ea0fa85d6955556a80ea03aa6556aaa94ad555550362d555590b552f2b2b2f47d1500c0c0c0e238a8aa550303030340d550303030303a03aaa038b555030303031b030300c17031703a89e27a89e8383e1780e03aaa42d0b642c0c0f03c3c0c7e1f1f2806c0c6c0c0c0c0c0e03a80e2c0c6c0c6c5c0c3c0eaaaa2a800c0cbc9cbc9c0c0eaaa85c3c3c5c0cbcbc0ea92d370b4b4dc2e03c0307c880f0f0a01f07c13030f0303030303aa13130303131303031303130300c4c4c7c005c0c3c0c5c5c0c0c5c0c0ea0fa85eaa17aaa1785ea2fa80eaaaaaaaaa170f0f171745c2c5d170b032f2f039a982ea80f22c3c3c03c3c3c0c1f287c7c2882207c1f04c0c3c0c4c4c0c0c4c4c0c0c0c0c0c0e84eaa80e2c4c0c4c4d2c0c0313131f03c0c3c0eaaaa83c3ea80c0cac9cac9c0c0c28003c3c3c3c0cacac0ea8fd570b3f55c2c0f00002b0000000003c0c3c0c0c0c0c0e884c4c0004c0c4c0c003c0c3c0ea0fa83ea2ba80eaaaaa0f0f0f0f032b2b039a982ea80f22c0000ac0000000003c00c02b02000880080800b010003c0c3c0c0c0c0c0e84eaa80e2c4c0c4c4d5c0c000000c0c04c6c03c0c3c0eaaaa82280c0cac9cac9c0c0eaaa83c3c3c3c0cacac0ea92d370b4b4dc2c3c3c80f030ac7c7c8817170a01f07c0f030f0303030303aaa131303030f0f0303130313135f0300c4c4c7c003cac0c0c3c3c0c0c3c0c3c0eaa0f83eaa0faa0fa83ea2ba80eaaaaaaaaa0f43c2c3d0f0b0f0f0f0f032b2b039a982ea83c3c5c3c3c00f22c0c2b1f1f21f0a0881f07c0f1303030f0f03030f030f0303030303a13aaa038b130313135f0300c4c4c7c170303031703083e17a89e27a89e7fa80ea03aaaa42d0b0327642c0f0008230000c0c0c0c0c0e03a80e2c0c6c05c0c3c0eaaaaaa85c5c0c0cbc9cbc9c0c0c28005c3c3c5c0cbcbc0ea8fd4b0b3f52c2c0000000000004c0c3c0c0c0c0c0e884c4c0004c0c4c4d2c0c005c0c3c0ea0fa85ea2fa80eaaaaa170f0f17032f2f039a982ea8000f22c008230000000005c00c0020008800833022002c040013030f0303030303a13aaa038b130313134b030000003030131b003030303aaaa2f172b0f2b0f2f17a0303aa0a002f2b2b2f03030303aa3f55c2cfd570b0000000000000303030303030303a20303000030303031b030003030303a83ea17a80ea03aaaaa8bcacacbc0c0c0c0e6a60baa002b00322c008230000000005c00f000c2000880080800b010000c0c0c0c0c0c0c0e80eaa80e2c0c0c0c0c6c0c000000c0c00c6c00c0c0c0eaaa8bc5cac3cac3cbc5e822aaaa8bcacacbc0c0c0c0ea97d370b5f4dc2c7c1f00c88803030a01f07c0303030303030303aa03030303030303030303030300c0c0c6c1f171f0f1f0f1f170303030302a0fa85eaa1f87eaa1faa03a80eaaaaaaaaa2f2b2b2f1f47c2c7d1f0b030303039a982ea87c2b1f1f00c0c0c0c0c00322e87c7c2882207c1f00c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0e80eaa80e2c0c0c0c0c6c0c0303031b09c0e85c3c3c5eaa90b42c5c2c3c2c0c0c0c0ea86c2c9c2c2c2c6c2c6c2c2c2c07c1b122d140c0c0c0c0c0c0c0c0c0c2c0c6c0c5c3c3c5c2c0e0f85ea2789ea279ae0380eaa9102c0d90b44031f87c7ca00303030380ea038b5031b4b035f03aaaa3f173f0f3f0f3f1703033f273f270303aaaa42d0b42d036658501f07c0307c8850908101303130303030303aa131303030b0b03030b50300c4c4c7c 25 33554431 10 1023
def hc_70_6 : Nat → Nat := unpackHintV5 0x906506a3231ec8455071f0841a762cbe9caa1c26cbcbd99b22fa66780a195808c61f06e17272aa57c09b94cb24a4cc4cd120725441d4c90eed31036e49a0c293202be89789862e8221c7f876d2341b145405b2226138468832e3660c440e82f403a06c4a18000362 0xf030f0383e0f84e030f0f0f0f0f0f0f0f0303132b1313030303030343d8b50b0b42c2d2b03642d42c2d42c2d503030b0b0b2b03030b13aa0b0b0b130b1b0b0b0b0b0b130b130b0b0b0b0b0b0b0f0f0f0f032b1f0313a1313231304c4c4c0b50b0b0b0b02c7c2c0f030f0303030303a038ba0303a82d40c2c2c0c0c2c4c0c0c4c0c4c0d030345c0c2c0e1384e84c3c3c5c4c4c4c6c4c6c4c4c4c6c4c6c0c0c0c0c0c4c4c0c0c0c2c3d0b40c2c0d0b42c7c1f00c7c6c1300c0c0c0c0c0e038b80e85c0c3c0e0f84e1380c4c4c3c3c3c3c4c5c0c0c4cbc4c4c0c0c0c0c0d42c2d0f62d0b40d90b50b0b50b0b540c0c2c2c2c0c0c2c4c2c7ea82e0b0b0b130b1b0b0b0b0b0b130b130b0b0b0b0b0b0b170f0f17032f1f0313a1313231304c4c4c0b50b0b0b0b02c7c2c13030f0303030303a038ba0303a82d40c2c2c0c0c2c4c0c0c4c0c4c0c0c0c0c0e1384e0380c4c4c4c3c4c3c4c5c0c0c0c0c0c0c0c0c0c0c0d0b0b4ac2d0362d40c0d90b50b0b50b0b0b170b0b0b0f0b0b542c4ea82c2c2c4c2c6c2c2c2c2c2c4c2c4c2c2c2c2c0c0c0c7cac7cbc0c0c0c0c4e84c4c6c4c13131302d42c2c2c2c0b1f0b00c0c0c0c0c0c0c0e80e2e80c0ea035030303030303030303030303030f030f0383e0f84e030f0f0f0f0f0f0f0f0303131f131303030303030f0f0f0f032b2b0313a131344c2c4d130b03c8b00001f0000000000f00300ac01302004c1b0004c130002c04000f030f0303030303a038ba0303a84c0c4c0c0000304c05c0c0c0c5c0c21384e84c3c3c5c4c4c4c6c4c6c4c4c4c6c4c6c0c0c0c0c0c4c4c0c0c0d0b42c0c9d0b42c0f0000003030303030380e2e03a17030f0383e1384e0313130f0f0f0f13170303131f13130303030303170f0f17032f2f0313a131344c2c4d130b0003c8b000000000005c00c0004c1f022004c1b0004c130002c040013030f0303030303a038ba0303a84c0c4c0c0000304c00c0c0c0e1384e0380c4c4c4c3c4c3c4c5c0c0c0c0c0c0c0c0c0c0c0cbcacacbc0c0c0c0c4e84c4d130b1344c2c007c00c8b000000000005c00f000c04c0801306c001304c000b010000c0c0c0c0c0c0c0e80e2e80c0ea0303030300000c030131b131b8b8b130f0f1b42c7c1f03c03271b04c1b038b170f0f170327084e13a130f0f171313131b131b1313131b131b0303030303131303030342d030b0342d0b0000003030303030380e2e03a4b030384e1384e031313130f130f13170303131f1313030303030342d0b42d03642d42c2d42c2c00000000000041f05c00f000c0004c0801306c001304c000b001303130303030303a038ba0303a82d40c0000304c00c0e1384e1380c4c4c4c3c4c3c4c5c0c0c4c4c4c0c0c0c0c0cecec0cec0c4e84c4d130b1344c2c7c7c0c7c0c4e84c4c8c4c13131307cec7c4c0c4c0c0c0c0c0e80e2e80c0ea130313031303130342d03030303540d035aa5665aa43d8b555555545c3c3c5d511f403030303aa5503030303540d03503030303a038baa555030303033f0385ea0fa555a58cd5603a80eaa55558a88e20380c0c0c0eaaa90f62d42c2d030340c0d9950303030303030303aaaa0b0b0b0f0f0f0f03030303aa0b50b0b0b0b02c7c2c0303030303030303a038baa035503030303030303030b0333030303030303370383ea0fa80ea03aaa0b55a82e0baa82e33aa8a88e203942d035540c0c0c0c0d955aaaa955543d8b50355551f4540f0f0f0f03030303aa5540d55030303030303030303a038baa555030303033f0358cd55556a0fa83ea03a80eaa55558a88e20380c0c0c0eaaa942c2d0f62d0340d9950303030303030303aaaa0b0b0b170f0f1703030303aa0b50b0b0b0b02c7c2c0303030303030303a038baa035503030303030303030b0333030303030303370385ea0fa80ea03aaa0b55a82e0baa82e33aa8a88e20380030303030303030303030303aaaaaaaa170f0f171745c2c5d170b03030303aa03c8b0f0f00f0f0f0300c881f07c03030303030303030303030303030303a038baa03030303370300c0c0c7c85ea0fa85e17aa85e33aa80ea03aaa0b99a0a87c20380c0c0c0eaaa83c3c3c3c0c0c0c0ea80f22c00000c000003c00c0030202002c04000303030303030303a038baa030303033f0300000030300333083ea0fa80ea03aaa0b99a0000000a08cc020380030303030303030303030303aaaaaaaa0f43c2c3d0f0b0f0f0f0f03030303aa0f0f170f0f003c8b0300c0c0c881f07c03030303030303030303030303030303a038baa03030303370300c0c0c7c83e33aa83e0faa83ea0fa80ea03aaa0b99a0a87c20380c0c0c0eaaa85c3c3c5c0c0c0c0ea8000f22c00000017003000c080800b010000c0c0c0c0c0c0c0e80e2ea80c0c0c0cfc0c000000c0c00ccc217a83ea03a80eaa82e668000000282330080e03030303aaaa42d0b40d03660b170b0b0b0f0b0b0303030303030303aaaa007c1f00c0322048b50540c0c0c0c0c0c0c0e80e2ea80d540c0c0c0c0c0c0c0c2c0ccc0c0c0303031f217a83ea03a80eaa82d56a0b82eaa0b8cea82a1f080e03030303aaaa555555000000122c0017003c003000c080804000c0c0c0c0c0c0c0e80e2ea9554000000c0c00ccc217a83ea03a80eaa55550000000a08cc020380c0c0c0eaaa950f545d503540d5995933555555007c1f00c0322142d4040303030303030303a038baa40d55550355500c0c0c7c85ea0fa80ea03aa963355555a55550a87c20380c0c0c0eaaa9555555400000048b0303030303030303a038baa55500085ea0fa80ea03aa9555400020380c0c0c0eaaa90b42d0340d9800000000405c00f000c0030202002c000c0c0c0c0c0c0c0e80e2ea80d540c000000c0c00ccc217a83ea03a80eaa82d568000000282330080e03030303aaaa03030303aa03030303aa0303030303030303a038baa0303030303030303030385ea0fa80ea03aaa0b99a8a88e20380c0c0c0c0c0e2c0c3c0c0c0c3c0ea0fa85eaa178aeaa1785ea0389ea0380eaaaaaaaaa170f0f171745c2c5d170b030303039a982ea85c3c3c5c5c5c5c171f1700c0c0c0e238a8aa4b4b4b4b03030303030303030303030303030303a03aaa038b030303031b03030303031b030b4b031740c0c6c5f03171f03031b030f0380c0eaaaa80c0eaa80c0eaaaaa83c3c3c3c0c0c0c0ea92d770b4b42c3c3c3c3c0c0c0c0ea97c7ddc5f1f17d2d2c0c0c0c0c0c0c0c0eaa80c6c0c0c0c0c0c0c0c0c0c0c0c0c0c6c0c0c0c0c0c6c0c0c0c0c0c3c0c0c3c0c0c0c0c0e2eaa0f83eaa0faa0fa83ea03a80eaaaaaaaaa0f43c2c3d0f0b0f0f0f0f030303039a982ea83c7c3c0f0f0f03c3c3c3c0c0c0c0e238a8aa5f4b4b030f031b03030303030303030303030303030303a03aaa038b030303031b03030303031b03 26 67108863 11 2047
def hc_70_7 : Nat → Nat := unpackHintV5 0xafd481aaea216a594c2a7eb2f49b1093a57b2928d6511227a1be864474a0292d07c78859d8c3247214839bd41626ad48f993a2f65ef0bf159f43a50e4b312ba2fe46dc81902e3123ac0bf0c9343a2cb4b309ae2fe22b480872e2fe16d0bd038545e05291d8000294 0x303030f2b03030f0f03030f030f030f83c3c3e0f1f0f0f0f0f031f130355555555550000000000122c3c3c5c3c3c0c0c0c3c0e2c0c0cac0cac0c4c0c4c0d5400000c0c003c0c3c0cac9c0c0cac9c0c0c3c3c3c3c4e331f138cc7c0cac4c0d0b42d42c2d42c2d0b40d0b42c0000000000003c0c03171700003030303130313030b503000303030f2b03030f0f03030f030f030f83c3c3e0f1f0f0f0f0f032b130350b0b50b0b42d0b42d0342d0b000000000000100f0000f03c000f003c00300ac03302002c003c3c5c3c3c0c0c0c3c0e2c0c0cac0cac0c4c0c4c0c2d40c00000c0c06c6c00c0c0c3cac0c0c3c3c0c0c3c0c3c0c3e0f0f0f83c3c3c3c3c0cac4c0c3d0f0b0f43c2c3c3c3c3c0cacac0ccc4c4ccc3c8c3c0f0f0f03c3c3c3c0cacac0ccc4c4ccc3c3c5c3c3c0c0c0c3c0e2c0c0cac0cac0c4c0c4c0c6c0c6c0c6c0c6c0c0c0c0c0c4c3c3c4c0c0c0c0d0b42d0340d0b42c5c3c3c3c3c2c0c0c0c0c0c0c4c4c4c4c5031703c0300c1304c03100c4031703030303030303030380e03030b50303031b0300c0c0c7c03030303130f0f130303030342d0b40d0342d0b17170b0b0b0b0b0b030303030303030313131384e13130550305c0f00c0304c1300c540341400c0c0c0c0c0c0c0c0c0c0c0c0d40c0c0c0c0c0c0c0c0c030300c0c0c0c4c3c3c4c0c0c0c0d0b42d0340d0b42c2c5c2c2c2c3c2c2c0c0c0c0c0c0c0c0c2c4c2e0b82c2c01703c0300c1304c122d41503030303030f038b0303030303030303030303503030303030303030b03030300c0c031703030303030303030303130380e0303030b030b550340c0c0c2c0c2c0c0c0c0c0c2c0c0c0c0c0c00c0c0c7c00c0c0c0c0c0c0c4c3c3c4c0c0c0c0d555554000000005c3c3c3c3c030303030303131313135500031703030303030303030380e03555000031b0303030303130f0f13030303035555550000000001717000030303030303030313131384e13135555000003030300c0c0c0c0c0c0c0d540000c0c000c0c0c0c4c3c3c4c0c0c0c0d55555400000048b0005c00f000c003004c0804000c0c0c0c0c3c0e2c0c0c0c0c0c0c0c0c0c0d5400000c0c00c00c5c0c0c0c0c0c0c0c0c0c0c4c0e0380c0d555400000c8c00000c0c00c000c0c0c0c0c0c0c4c3c3c4c0c0c0c0d5545c5c0c0c0c0c0c0c0c0c4c4c4e1384c4d55555415145c0f00c0304c1302c2c00c0c1100c0c0d030303030303030355503035500c0c03030303130f0f1303030303543d517540d50356544d55555401703c0300c1304c50b50100c0c0c0c0c3c0e2c0c0c0c0c0c0c0c0c0c0d035540d54030300c5c0c0c0c0c0c0c0c0c0c0c4c0e0380c0d40d555540c0d40c2d555400c0303031f031f003030303030303130f0f1303030303555555000000122c0c0c0c0c0c3c0e2c0c0c0c0c0c0c0c0c0c0d54000c5c0c0c0c0c0c0c0c0c0c0c4c0e0380c0d555400000c00c0c0c0c0c0c0c4c3c3c4c0c0c0c0d5555545c00303030313131313555030303030f00c0c0c0c0c0c0c0c0c0d5403003030303130f0f130303030342d0b40d0342d0b00000000101717000030303030303030313131384e13130b0b5503030000030303030f00c0c0c0c0c0c0c0c0c0c0d40c0000c0c000c0c0c0c4c3c3c4c0c0c0c0d0b42d0340d0b42c00000000405c00f000c003004c0800b0003030303030f038b030303030303030303030350300000c030031703030303030303030303130380e0303030b550303000000003030030003030303030303130f0f1303030303170f0f170303030313131313170f0f17030303031313131303030303030f038b030303030303030303030303030303030303031703030303030303030303130380e0303030b0340d03030300c0c0c8c0c03030303030303131313130303030342d0b40d0342d0b0b170b0b0b0f0b0b03030303030303030b130b82e0b0b007c1f00c0304c13048b50540c0c0c0cac0c0c0c0e2c0c0c0c0c0c0c0c0c0d40c0c0c0c0c0c0c0c2c0c6c0c0c030300c5c0c0c0c3c0c0c0c0c0c0c4c0e0380c0c0c2d540c0c0c2c0c2c0c0c0c0c0c2c0c6c0c0c0c0c00c0c0c7c00c0c0c0c0c0c0c4c4c4c4c0c0c0c0d55555400000048b0005c00f000c003004c0804000c0c0c0cac0c0c0c0e2c0c0c0c0c0c0c0c0d5400000c0c00c6c00c5c0c0c0c3c0c0c0c0c0c0c4c0e0380c0d555400000000c0c00c6c000c0c0c0c0c0c0c4c4c4c4c0c0c0c0d50f545d503540d59513555555007c1f00c0304c13142d404030303032b030303038b030303030303030340d55035500c0c03170303030f030303030303130380e03035031b555550303555500303031f00303030303030313131313030303035555550000000122c0c0c0c0cac0c0c0c0e2c0c0c0c0c0c0c0c0d54000c5c0c0c0c3c0c0c0c0c0c0c4c0e0380c0d555400000c0c0c0c0c0c0c4c4c4c4c0c0c0c0d0b42d0340d0b42c00000000405c00f000c03000c27004c0800b00030303032b030303038b03030303030303030350300000c03003170303030f030303030303130380e0303030b550303000000003030031b000303030303030313131313030303032f2b2b2f03030303131313132f2b2b2f0303030313131313030303032b030303038b0303030303030303030303030303030303170303030f030303030303130380e0303030b0340d03030300c0c0c8c0c03030303170303030f030303030303030303131f131f0380c7c0e03030303030342d0b5030b5030340d0342d0b0b170b0b0b0f0b0b0303030303030b0b03030b1b0303030303030303030303030b330b82e0b0b007c1f00c0c00c7c00c0307c13048b50540c0c0c0cac0c0c0c0c0c0c0c0c0c0c0e2c0c0c0c0c0d40c0c0c0c0c0c0c0c2c0c6c0c0c030300c5c0c0c0c3c0c0c0c0c0c0c0c0c0c4cac4cbc0e031f0380c0c0c0c0c0d5555555554000000000048b0005c00f000c030000c1b0000c00300cc0804000c0c0c0cac0c0c0c0c0c0c0c0c0c0c0e2c0c0c0c0d5400000c0c00c6c00c5c0c0c0c3c0c0c0c0c0c0c0c0c0c4c7c4c7c0e031f0380c0c0c0c0c0d50f545d550346d550340d503540d595335555555555007c1f00c0c00c7c00c0307c13142d404030303032b03030303030303030303038b0303030340d55035500c0c03170303030f030303030303030303131f131f0380c7c0e03030303030355555555550000000000122c0c0c0c0cac0c0c0c0c0c0c0c0c0c0c0e2c0c0c0c0d54000c5c0c0c0c3c0c0c0c0c0c0c0c0c0c4cac4cbc0e031f0380c0c0c0c0c0d0b42d40c2d40c0d0340d0b42c000000000000405c00f000c030000c1b0000c00300cc0800b00030303032b03030303030303030303038b030303030350300000c03003170303030f030303030303030303132b132f0380c0e0303030303032f2b2b2f0340c2c0d030303030303331313332f2b2b2f03030300c8c0c0303030333131333030303032b03030303030303030303038b0303030303030303030303030303030303038b030f0303030f0383e13a1313a131380e0313130f0f0f0f1317131313131317131b13131313131713170303030303030303030303170f0f171745c2c5d170b0303030313a131344c2c4d130b170f0f1717171705c7c5c0303030313a13131b1304c4c4c1f3b1f4b03030303030303030303030303030303a038ba0303a80c0c0c0c0c0c0c0c0c0c0c0c3c0c0c3c0c0c0c0c0e2e83c3e83c4e0f83e0380c3c3c4c4c3c3c3c3c3c3c3c3c3c3c4c6c3c3c3c3c3c3c3c3c0c0c0c0c0c0c0c0c0c0c0c3d0f0b0f43c2c3c3c3c3c0c0c0c0c4e84c4d130b1344c2c3c7c3c0f0f0f03c3c3c3c0c0c0c0c4e84c4c6c4c13131307cec7c0c3c0c6c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0e80e2e80c0ea03030303030303030303030384e1380e031b171b0f1b0f1b170303130303032f2b2b2f0303030313a131b46c2c6d1b0b1f1f1f1f0303030313a131b1b1b06c7c6c1f1f1f1f030303030303030303a03031b030303030303030303 26 67108863 11 2047
def hc_70_8 : Nat → Nat := unpackHintV5 0x94f90aa48117a8e6873a23c2bc86105c20792167c08bb9e401847738391cd11fa6ed88d9a3f2ee6324bb17702b255690b14611f24bfcb111f021e41d4bd8fd21463b24848dc620632ec858b233302694bf08352e01b78ab84d54120f787b82862b005ec8580002f6 0xc0c0c5c0c3c0c5c5c0c0c5c0c0c4c3c3c5c4e171f1385c5c0c7c4c0d0b42d42c2d42c2d0b40d0b42c2c5c2c2c2c3c2c2c2c5c2c5c2c2c2c2c2c5c2c2c2c2c2c0c0c2c2c2cbc0c0c2ccc2e0b82c2c01703c17170171f00307c1f04c122d415030f038b0f0f03030f0f0f032b0303032b130313030b5030b0b030b03030b0b1b1b030300c6c030303031703170387e1b550048b01b06c01b09c01703c0300c3321006c0c3c0c0c0c0c0c3c0c0e2c0c0c00c0c031b000c0c00bc9c0c0cbc9c0c0c5c0c3c0c4e331f138cc7c4c3c3c5c0cbc4c0d5555555554000000000000003c3c0030f030303030313031303550003030317030f0317170303170303130f0f171385c7c4e1717032f130355555555550000000000122c0017003c01705c00170000300bc033020100030f038b0f0f03030f0f0f032b0303032b13031303550000030301b1b0030303031703170387e1b546d27546d1b43d1740d0364cd5406c1f10b441b030f03030303030f03038b03030350317030f03130f0f17031f1303555555555030303032f272f2703031f1f1384e1f1f50451703c0307c1f04c440b0b0170b040c3c0c0c0c0c0c4c0c4c0d543c3d554031b00c0c0c5c0c3c0c5c5c0c0c5c0c0c4c3c3c5c4e171f1385c5c0c7c4c0d50f545d55175551745d52f540d595335555555555005c0f05c5c05c7c00c1f07c13142d404030f038b0f0f03030f0f0f032b0303032b1303130346d55035500c6c030303031703170387e1b42d0b00041b06c01b09c01703c0300c0309c33202c01b030f03030303030f03038b030300c0c030303031703170387e1b5500048b1b030f03030303030f03038b030303030317030f0317170303170303130f0f171385c7c4e1717031f130355555555550000000000122c0c3c0e2c3c3c0c0c3c3c3c0cac0c0c0cac4c0c4c0d540000c0c00bc9c0c0cbc9c0c0c5c0c3c0c4e331f138cc7c4c3c3c5c0cbc4c0d42c2d42c2d0b42d0b40d0b42c000000000000003c3c0030f0f0f03032b0303032b130313030b5030003030317030f0317170303170303130f0f171385c7c4e1717032f130342d0b50b0b50b0b42d0342d0b0000000000001017003c01705c00170000300bc03302002c000c3c0e2c3c3c0c0c3c3c3c0cac0c0c0cac4c0c4c0c2d40c0000306c00c0c0c5c0c3c0c5c5c0c0c5c0c0c4c3c3c5c4e171385c5c0cbc4c0c5c3c3c5c5d170b1745c2c0cbcbc0ccc4c4ccc5c3c3c5c5c5c5c17231700cbcbc0ccc4c4ccc0c3c0e2c3c3c0c0c3c3c3c0cac0c0c0cac4c0c4c0c6c0c6c0c6c0c6c0c0c0c0c0c3c3c3c3c0c0c0c0d0b42d0340d0b42c2c2c2c2c3c3c2c2c0c0c0c0c0c0c0c0c4c4c4e1384c4c1540c0f03c0300c1304c030400d050030f030303030303030303030303030303503030303030303030300c0c030303030f0f0f0f0303030342d0b40d0342d0b0b0f0b0b0b0f0b0b03030303030303030b130b82e0b0b003c0f00c0304c13048b50540c3c0e2c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d40c0c0c0c0c0c0c0c0c030300c3c0c0c0c0c0c0c0c0c0c0c4c0e0380c0c0c2d540c0c0c2c0c2c0c0c0c0c0c2c0c0c0c0c0c00c0303031f031f0030303030303030f0f0f0f03030303555555000000100000f0f0030303030303030313131384e131355550000030f00c0c0c0c0c0c0c0c0c0c0c0c0d540000c0c000c0c0c0c3c3c3c3c0c0c0c0d55555400000048b0003c00f000c003004c0804000c3c0e2c0c0c0c0c0c0c0c0c0c0c0c0c0c0d540000300c00c3c0c0c0c0c0c0c0c0c0c0c4c0e0380c0d40c2d555400000000c0c00c000c0c0c0c0c0c0c3c3c3c3c0c0c0c0d43c3d540c0c0c0c0c0c0c0c4c4c4e1384c4d55555415143c0f00c0304c1302c2c00c0c141100d0303030303030303030355503035500c0c030303030f0f0f0f03030303543d50f540d50356544d55555400f03c0300c1304c50b50100c3c0e2c0c0c0c0c0c0c0c0c0c0c0c0c0c0d035540d54030300c3c0c0c0c0c0c0c0c0c0c0c4c0e0380c0d40d555540c0d555400c0c0c7c00c0c0c0c0c0c0c3c3c3c3c0c0c0c0d0f503030303131313130000000000300c0c0c0c0c0c0c0c0c0d503000030303030f0f0f0f03030303555555000000122c0c3c0e2c0c0c0c0c0c0c0c0c0c0c0c0c0c0d540000c3c0c0c0c0c0c0c0c0c0c0c4c0e0380c0d40d555400000c0c0c0c0c0c0c3c3c3c3c0c0c0c0d0b42d0340d0b42c000000003c3c0f0f0f030303030303131313130b50300030f03030303030303030380e03030b50303000031b03030303030f0f0f0f0303030342d0b40d0342d0b00000000000f0f0030303030303030313131384e13130b0b55030300000300c0c0c0c0c0c0c0c0c0c0d40c0000c0c000c0c0c0c3c3c3c3c0c0c0c0d0b42d0340d0b42c00000000403c00f000c003004c0800b00030f038b030303030303030303030303030303503000003030030030f03030303030303030303130380e0303030b030b550340c0c00000c8c00000c0c00c000c0c0c0c0c0c0c3c3c3c3c0c0c0c0c3c3c3c3c0c0c0c0c4c4c4c4c3c3c3c3c0c0c0c0c4c4c4c4c0c3c0e2c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c3c0c0c0c0c0c0c0c0c0c0c4c0e0380c0c0c2c0d0340c0c0c030303230300c0c0c3c0c3c0e0f0f83c3e1380e80c0c3c0c3e03031f1f1f2703030f0f0f0f0f0f0f032b2b0313a131f47c2c7d1f0b0f0f0f0f031f1f0313a131f1f1f07c7c7c1f1f1f1f0f030f03030303031313a13031313a13130384c0c4c0c4c0c4c0c2c2c0c0c2c0c2c2c3c0c3c0cac9c0c0cac9c0c0c3c3c3c3c4e1f1f1387c7c0c7c4c0d0b42d42c5042d0342d0b0f03c500f400c1f07c1302c40f0f030b030f171703030b0b030303032b032b03130313030b50300c6c0303030f2b03030f0f03030f030f030f83c3c3e0f1f0f0f0f0f031f130350b0b50b0b42d0b42d0342d0b0b0f0b0b0b0b0b0b0f0b0f0b0b0b0b0b0f0b0b0b0f0b0b03030b0b0b2b03030b330b82e0b0b003c7c03c3c03c0f00c1f07c13048b50543c3c5c3c3c0c0c0c3c0e2c0c0cac0cac0c4c0c4c0c2d40c2c2c0c0c2c6c0c0c031b000c0c003c0c3c0cac9c0c0cac9c0c0c3c3c3c3c4e331f138cc7c0cac4c0d55555555540000000000003c3c0c030f171700003032b032b031303130355000303030f2b03030f0f03030f030f030f83c3c3e0f1f0f0f0f0f032b130355555555550000000000122c000f0000f03c000f003c00300ac0330201000f0f170f0f0303030f038b03032b032b03130313035500000c1b00f030f030f0f0f0f031f1303555555503035503032b272b2703031f1f1384e1f1f50450f03c0307c1f04c440b0b00f0b00f0340c0c0c0c0c4c0c4c0d545c5d554031b00c0c0c3cac0c0c3c3c0c0c3c0c3c0c3e0f0f0f83c7c3c3c3c3c0c7c4c0d550f43d550f550f543d52b540d595335555555555003c7c03c3c03c0f00c1f07c13142d4040f0f170f0f0303030f038b03032b032b031303130346d55035500c6c 26 67108863 11 2047
def hc_70_9 : Nat → Nat := unpackHintV5 0xe6020ede41f0d302d0cc11bcc30a42bd6968b50a18aa62aaa26200975ac29041c687c2207ff9f27ae14676c10872910c6a4a1268208a6321405f190259a95c54615251c8a648525e41a9aa390a282f72662b29121ddb54121af00a39f800028e 0x21785c3c3c5ea03aa0fa2eaaaaa42d0b582d690b42d98000000000000405c17003c0f0220020000300bc080800b00130f0f13a80e13a13131313aa0b50b00000c1300f0f0f0fa283e1f87c0280ac0cac9cac9cac0c5c5c0010b42d0b42d90b50b0b50b0b0000000000000f0f0f0f2b132b1313a13331b1303331b13030b50b000f0f0f0f83e8ba0f0f87c7e2b1fa83c0c3c3c3cac3c0c3c5c3d0b42d0b42d90b50b0b50b0b000000000000107c0f003c00300ac01f07c08800f03c000f0000b000f0f0f0f2b132b1313a130f0f0f030f470f030b50b00000c3300f0f0002b272b032b272b030f0f0f0fa000a2aa5a50b0b42d0b42d0b6600000000000013131303131313030f0f0f0f13131313aa0b50b00a0f8aeaa030f0f0f0faaaa0fa2e8aea65a5a0b0b42d0b42d0b66208c0000000000004200088000f05c00f03c00300ac08022002c0213aa80c3c3c3c3c4c4c4c4ea82d42c0000304c2030385c5c5c5c3c3e0f83c7c7d0b42d4000107c5c0f09c4f009c27000c0309c2707c80b006c0c6c0cac9c031b05c3c3c5e83c3e0fa2c87e1fa0002b032f272f272b030f0f00042d0b42d0b642d42c2d42c2c00000000000041f05c3c3c4cac4cbc4c4e84ccc6c4c0ccc6c4c0c2d42c005c3c3c5e83c3e0fa2e1f87ea170317171717030f0f0f42d0b42d0b642d42c2d42c2c00000000000041f05c00f000c02f007c0801705c00170000b00170f0f132b132f1313a1317171303174713030b50b00000c3302703270387c7e2b1fa280cbc5cac3cac3cbc5c02800c0c0010b42d0b40d90b50b0b50b0b0000000000002f032b030303030313a03331b0303331b03030b503002703270387c7e2b1f80e8ba03031f171f0f1f0f1f17a80c0c0d0b42d0b40d90b50b0b50b0b000000000000107c17003c003009c01f02007c1f0007c0002c00bc0cac0c0c0c0c0c4e80c7c7c0c0c7d1c0c0c2d40c0000306c0bc5cac3cac3cbc5c9c0c9c0c7c7c0028aeaa000a242d0b5a50b0b42d036600000000000013031303131303031313030303030303aa0b50300a83ea1727032703a1fa2baaaaa80e8b42d0b5a582d0b40d98000000000000405c00f0200088000300c02709c080800b001303130384eaa0303030303aa0b50300000c130030303030f038b0f0f03030f0f0f170f0f171785c7c5e1717031f270355555555550000000000122c5c0c3c0c5c5c0c0c5cac0c0c0c0c0c0c7c0d2c0d54003c0c030f0f0f0f031f270340d51751f5b5b1f00000000000f030f03030303031f034b034b034b030003030f0f17031b030f0300c6c7ccc6c3c3c3c3c0c7c9c0d555555540000000048b030300c3c3c3c3c0c0c0c0d555554000000048b03030303030303030303030355000303030f0f170f0f0303030f038b0f83c3c3e0f1f0f0f0f0f031f2703555543d55555500000000000122c3c3d1c0c0c3c3c0c3c0c3c0c3c0c0c0c0c0c7c0d2c0d54000c5c0c5e85c5ea83ea5500048b1303130385e170f0f17a80ea83e8baaaaa955555555540000000000048b130f0f13a80e13a13131313aa55000f0f0f0fa2aa43d4acacacad94000000000003c3c3c3c4c4c4c4ea84c4c4c4c0283e2baa80c3c3c3c3eaaa83e8ba1fa955559555555000000000000122e13aa80c3c3c3c3c4c4c4c4ea95402a0fa85c9c0c9c0e87e87eaaaaa03a2d55555555540000000000048b1303130384eaa0303030303aa550043431f1f431f1f555555000000122d0d0c7c7d54009c5c9c3c9c3c9c5c9c0cbc9c9c0c02f2b2b2f2789c7c9e271f03432727270342d0b50b0b50b0b42c2d030b42d0b00000000000002f032b03271b0303271b030303032703034303030b50300a0faa0f0f0f0fa1f0f0f0f0f03c3c7e2c7c7c7c7c9c7da60b42d0b42d0b642c00000000002a83c3c3c3c4c4c4c4c4c4c4c4c2d42c013d0d3d0e1f1f87e1f87c7c5c7c3c7c3c7c5c7c0c7c7c7c9c7c0c042d0b42d0b60b42c2d42c2d42c2c0000000000000cc4ccc4ccc4ccc4c4e84c7c6c4c0c7c6c4c0c2d42c006c0c6c0c4ccc4ccc0c6c4c0d0b42d0b40d0b42c000000006c5c6c3c6c3c6c5c0c0c6c6c6c6c0c0c6c6c4e1386c7c2c2d542c2c00006c0c6c6c0c0c6c0c0c0c6c4c0ccc4c6c0c2c2d40c2c00004343434342d0b42d0b42d0b000000001017003c00300002002c010d0c2d42c00003000c0c0c0c0c0c0c0c0c5c0c0c5c0c0c0c0c4e1b1f1386c6c4c3c3c5c0c0c0c0c6d1b0b1b46c2c5c3c3c5c0c0c0c0ccc4c4ccc6c6c6c1b1f1b05c3c3c5c0c0c0c0ccc4c4ccc0c6c0c3c0c0c0c0c0c0c0c0c0c0c0c3c0c0c0c0e2c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c5c0c3c0e130f84c5e131f84c0c4c0c3ea030303031f1f1f270303131317170f0f17032f2f0313a131f47c2c7d1f0b170f0f17031f1f0313a131f1f1f07c7c7c1f1f1f1f13030f03030303031313a13030f0fa130f0384c0c4c0c4c0c4c0c0c0c0c0c5c0c5c0e1f86d0b42c6c2c6c2c2c2c6c2c9c2c2c2c5c2c3c2c0c0c0c0cce82c06c1f122d146c0c3c0c0c0c0c0c3c0c0e2c0c0c0c0c0c0c2c0c6c0c2c2c0c0c2c2c2c0cbc9c0c0cbc9c0c0c5c0c3c0c4e1f1f1387c7c4c3c3c5c0c7c4c0d4142c42d0b42d0342d0b1741405c0f00c1f07c1302c40b0b03030f0f03030b030f0303030303130313030b50300c6c 24 16777215 10 1023
def hc_70_10 : Nat → Nat := unpackHintV5 0xee6190e699f2e0698cd8d9e4d151e2ca09d2c1c212bd910cb1daeea9621ea291b49bc1b48feaf68ba91084b9bc7cd1fa75c1c46d920c66a1bc5e720c557a3e51490c482a483ef24e3a093a2e52ee263a061f69b41849c80bab280719240001c6 0xf0f0002b272b032b272b030f0f0f0fa000a2aa5555555555000000000010013131303131313030f0f0f0f13131313aa5500a0f8aeaa030f0f0f0faaaa0fa2e8aea5555642d555554000000000048b00200088000f003c00300ac0808040213aa80c3c3c3c3c4c4c4c4ea9540000304c0bc5cac3cac3cbc5c9c0c9c0c7c7c002aa80028955555555540000000000004c0c4c0c4c4c0c0c4c4c0c0c0c0c0c0ea95402a0fa85c9c0c9c0e87e8aeaaaaa03a2d5555555554000000000048b0005c00f02000880003009c080804004c0c4c0e13aa80c0c0c0c0ea9540000304c09c5c9c3c9c3c9c5c9c0c9c0c02f2b2b2f2789c7c9e271f032727035555555555500000000000002f032b03271b0303271b0303030303033b030355004f434f4387e1f87e1f1f171f0f1f0f1f171f031f1f1f271f0301555555555540000000000000cc4ccc4ccc4ccc4c4e84c7c6c4c0c7c6c4c0d54006c0c6c0c4ccc4ccc0c6c4c0d555554000000006c5c6c3c6c3c6c5c0c0c6c6c6c6c0c0c6c6c4e1386c7d555400006c6c0c6c0c0c0c6c0c6c0c4c0ccc4c6c0d554000043433b3b433b3b555555000000122c0017003c00300002010043433b3b5500000c0030303030f038b0f0f03030f0f0f170f0f171785c7c5e1717031f2703543d5175545d2b5545d17549d50356553d555555555401703c17170171f00307c1f07c50b50105c0c3c0c5c5c0c0c5cac0c0c0c0c0c0c7c0d2c0d1b5540d54031f03c0d030f0f0f0f031f2703555555503035551717551f1f5b96e1f1f50450f03c0307c1f07c50440b0b00f0b00f030f03030303031f034b03554b1b03034b1b030300c7c03030f0f17031b030f0340c6c7ccc6c3c3c3c3c0c7c9c0d54b546d50f543d527540d5953355555555006c1f03c0f00c1f07c1f142d404030340c3c3c3c3c0c0c0c0d50f543d503540d59513555555003c0f00c0304c13142d40403030303030303030303030340d55035500c0c0303030f0f170f0f0303030f038b0f83c3c3e0f1f0f0f0f0f031f27035543d0f5543d543d50f549d50356553d555555555400f1f00f0f00f03c0307c1f07c50b50103c3d2c0c0c3c3c0c3c0c3c0c3c0c0c0c0c0c7c0d2c0d1b5540d54031f00c5c0c5e85c5ea83ea549d27549d5b43d1749d03665501f07c42d104c0c4c0c4d40c5c3c3c5daaa95555555545c5cac0cbc9cbc9cac0d695541145c0f07c1f221102c2c2804c3c3c4c4c4c4c4ea9544c4c4c0c4c4c4c0c131321785c3c3c5ea03aa0fa2eaaaaa543d5175565559952f540d5959555555555401703ca087c07c1f22142d404130f0f13a80e13a13131313aa44d55035504c4c0f0f0f0fa6aa55555550f0f552b032b272b272b035a5550450f03c1f07c8850440b0b0a00f0f0f0f13131313aa55131313031313130304c4ca0f8aeaa030f0f0f0faaaa0fa2e87ea5566556550f543d52b540d59595555555554087c2803c0f07c1f22142d40484eaa030f0f0f0f13131313aa44d55035504c4c27032703aaa65555552f172b0f2b0f2f1751f1f555a5550451f07c0307c88440b0b0a01303130303030303aa55131303031313030300c4ca83ea1727032703a1fa1faaaaa80e8b543d51755665565527540d5959555555555401f07c87c2800c1f22142d4041303130384eaa0303030303aa44d55035500c4c270327032f1f2b1f031f270355555552717270f270f2717547c7c9e2787c7d41147c1f00c7c1f1f07c1f1102c2c07c2c0bc0cac0c0c0c0c0c7c0d6c0d549c6c0c0c9c6c0c0c031f06c6c6c6e1f87e1b86d5555546c6c6c6c6c6c6c6d86d5551f07c1b06c1f21106c1b13d0d3d0e1f87e1f87d55555547c5c7c3c7c3c7c5c7c0c7c7c7c9c7c0d550451f07c1f07c1f1f21f1102c2c07c2c0cc4ccc4ccc4ccc4c4e3384c7d547c6c4c7c0c0c7c7c6c4c0c131f06c0c6c0c4c7c4c7c0c6c4c0c6c5c6c3c6c3c6c5c0c0c6c6c6c6c0c0c6c7c4e1386c6d55555415147c1f00c1b07c1302c2c06c2c1106c0c6c0c0c0c0c0c4c6c0c4c0c7d555500c7c6c6c43431f1f431f1f543d51755503565555555401f07c1f07c1f07c50b50110d0c7c7d5540d541f1f00c0c0c0c3c0e2c3c3c0c0c3c3c3c5c3c3c5c5e171f1785c5c0c9c9c0d0b42d42c2d42c2d0b40d0b42c000000000000405c00f005c170005c2b0000c027013c0800b0017030f0317170303172b0303030303034b034b030b50300000c1b0030300017170000f0300d8e631f6398c7c3c3c3c3c0c9c9c0d42c2d42c2d0b42d0b40d0b42c0000000000018c6c0c0d8c6c0c0c3c0c3c0c0c0c0c0c0c0c2d40c000c0c3c3c5c0c6c0c3c0c031b33331b0f0f0f0f0327270342d0b42d0b42d0342d0b0000000000101b011c00f003c003009c03302002c000c0c030f0f0f0f0303030342d0b40d0342d0b00000000100f003c00300c00309c01302002c000c0c0c0c0c0c0c0c0c0c0c0c0d40c0000300c00c0c0c3c3c5c3c3c0c0c0c3c0e2c3e0f0f0f83c7c3c3c3c3c0c9c9c0d0f50b0b50b0b0b0b42d0b42d0342d0b03c23000000000000100f0000f03c000f003c00300c02709c04f02002c003c3d1c0c0c3c3c0c3c0c3c0c3c0c0c0c0c0c0c0c2d40c0000306c00c5c0c5e85c5ea83ea42d0b00042721c02709c01703c0300c2709c880b004c0c4c0c031305c5c0005c3c3c5cbc9cac0cbc9cac0c83ea00a0aa42d0b50b0b5a42d0b66000000000000130f0f13131313031313130313131313aa0b50b00 24 16777215 10 1023
def hc_70_11 : Nat → Nat := unpackHintV5 0x88c02f21381f080d0821f1224477c0911cf41f871e03e1bb118e66b10298632925ca09d95ed2764f5d0b131e17248887e10d02a43f487f0e702c435d07e0c192b62b689f89a92622148ab87571f6180caa051a1d2115c61839418608c8b101af10603a46300001d2 0x40c0d17170b0b87e1fa0b0f42d0b0b0b0001b1b1b1b1b1b170f0f1783e1787e1b50b0b43d8b42d0b642d50b030b0b0b0b030b1faa0b0b0b0b0b000000000000170f0f171b1b1b1b1ba1f0b50b0b0b0b3f0b1b0b0b001b031b0387e1f86e0342c2d2b0b40d8b50303642c2c5c2c2c2c3c2c2d50b1faa0b0b0303030000000000001b1b1b1b031b1b031ba1b0b50b0b0b0b1b0b1b0b0b000f0f0f0f83e0f86e1b0f0f0f0f1b1b1b1b1fa1f000000000f0f1b8b0f0f0f0f1b1b1b1b1b1b1ba1b1b1b1b1b000f0f0f0f030f0f0f1b0f030f1faa0f0f0f0b0f43d0f0b00000f170f170f0f1783e1786e1b170f0f171b1b1b1b1fa1f0000000017170f0f0f0f1b8b1b1b1b1b1b1b1ba1b1b1b1b1b0017171717031717171b1703171faa1717170b1745d170b00000f0f0f1b1b1b1b87e1f86e1b42d0b42d0b642c000000006c6c6c6c6c6c6c6c6e86c2c2d546c6c002c5c2c2c2c3c2c2c2c0c2c2c2c6c2c0c2c7ea82c2c2c2c2c000151b1b87e1f87e1b3b3b1b3b1b1fa1f000000001b1b1b1b1b1b1ba1f1b3b1b00434387e1f87e1f3b3b3b3b431fa1f000000222c0017003c0030002300b01000cc4ccc4ccc4ccc4c4e84ccc4ccc4c00000c000c0c0c0c3c0e2c3c3c0c0c3c3c3c5c3c3c5c5e171f1785c5c0c7c9c0d0b42d42c2d42c2d0b40d0b42c2c5c2c2c2c3c2c2c2c5c2c5c2c2c2c2c2c5c2cac2c2c2c2c0c0c2c2c2c9c0c0c2d3c2e0b82c2c01703c17170171f00307c1f07c122d41517030f0317170303172b0303030303031f034b030b5030b0b03030b1b030300c7c03030b0b0b030b0b171703030b0b03030f030b033f87c7cfe1f1f0f0f0f0f031f270350b1410b42d0b40d0b42d403d00f03c0307c1f07c0b040fc6c0c0cfc6c0c0c3c0c3c0c0c0c0c0c7c0cfc0c2d40c031f00c0c3c3c5c0c6c0c3c0c2c0c6c7ccc6c3c3c3c3c0c7c9c0d0b42d0b42d0b40d0b42c2c6c2c2c2d1c2c2c2c3c2c2c2c3c2c2c0c0c2c2c2c9c0c0c2ccc2e0b82c2c01b07c0f03c0307c1f07c122d415030303030f0f0f0f0303030342d0b40d0342d0b0b0f0b0b0b0f0b0b03030303030303030b130b82e0b0b003c0f00c0304c13048b50540c0c0c0c0c0c0c0c0c0c0c0c0d40c0c0c0c0c0c0c0c0c030300c0c0c3c3c5c3c3c0c0c0c3c0e2c3e0f0f0f83c7c3c3c3c3c0c7c9c0d42c2d42c2d0b42d0b40d0b42c2c3c2c2c2c2c2c2c3c2c3c2c2c2c2c2c3c2c2c2c3c2c2c0c0c2c2c2c9c0c0c2d3c2e0b82c2c00f0f1f1f00f0f03c03c0f00c1f07c1f048b50543c3d1c0c0c3c3c0c3c0c3c0c3c0c0c0c0c0c7c0d7c0c2d40c2c2c0c0c2c6c0c0c031f00c5c0c5e85c5ea83ea42d0b270b3f0b0b0b270b270b0b0b170b0f0b030b2703aa01f07c48b45130313030b03130317170b0b0b0b0b0b170f0f172f272b032f272b03aaaaaaaa42d0b505842d0b661703c90501f07c8884130f0f13131313031313130313131313aa0b50b04c4c85e170f0f17a80ea83e8baaaaa90b42d60b5a42d0b660b170b0b0b0f0b0baaa0b0ba0baa0b030b0b0b2f0b03aaaa005c0f2821f01f07c88122d415130f0f13a80e13a13131313aa0b50b0b0b0b030b130b0304c4c0f0f0b0b0b0b0b0b2b272b032b272b030f0f0f0faaaaaaaa585042d0b42d0b6650900f03c1f07c8881013131303131313030f0f0f0f13131313aa0b50b04c4ca0f8aeaa030f0f0f0faaaa0fa2e87ea5a582d0b42d0b42d9a82eaaaa82c2c2c3c2c2c2c3c2c2c2c0c2c2c2cac2c0eaaa80a1f1f0a200f03c1f07c88122d41584eaa030f0f0f0f13131313aa0b50b0b0b0b030b130b0304c4c2f172b0f2b0f2f17270327031f1f03030b0b0303aaaaaaaa42d0b585042d03661f07c50900307c888413031303131303031313030303030303aa0b50300c4ca83ea1727032703a1fa1faaaaa80e8b42d0b5a582d0b40d982c5c2c2c2c3c2c2e82eaaaa82c2c0c0c2c2c2c9c0c0eaaa801f07c87c2800c1f22048b50544c0c4c0e13aa80c0c0c0c0ea82d40c2c2c0c0c2c4c0c0c031309c5c9c3c9c3c9c5c9c0c9c0c2c2c2cbc7cac7c9e1f1f2787c7c0c7c9c0d0b42d4142c42c2d030b42d0b1f07c1f41400c7c1f1f07c1f02c42f032b03271b0303271b0303030303031f03030b50300c7c4f434f4387e1f87e1f1f171f0f1f0f1f171f031f1f1f271f030b0b0b42d0b42d0b60b42c2d42c501f07c1f07c1f1f21f1407d00b10cc4ccc4ccc4ccc4c4e84c7c6c4c0c7c6c4c0c2d42c131f06c0c6c0c4c7c4c7c0c6c4c0d0b42d0b40d0b42c6c5c6c3c6c3c6c5c0c0c6c6c6c6c0c0c6c6c4e1386c7c1542c1f07c0306c1f04c0b106d0501b1b031b0303031b031b03130333131b030b0b5030b0b0b0b00c7c6c6c43431f1f431f1f42d0b42d0b42d0b0b170b0b0b0f0b0b0b030b0b0b0b030b0b82e0b0b007c1f07c1f07c1f048b50550d0c7c7c2d42c2c2c2c0c2c2c0c1f1f00c0c0c0c3c0e2c3c3c0c0c3c3c3c5c3c3c5c5e171f1785c5c0c9c9c0d5555555554000000000048b0005c00f005c170005c2b0000c027013c0804005c0c3c0c5c5c0c0c5cac0c0c0c0c0c0cec0d2c0d540000306c00c0c0005c5c0003c0c03378dc7cde371f0f0f0f0f0327270355555555550000000000100371b0303371b03030f030f030303030337033703550003030f0f17031b030f0300c6ccccc6c3c3c3c3c0c9c9c0d555555540000000048b0006c04b003c00f000c02700cc0804000c0c030f0f0f0f03030303555555000000122c000f003c003000c0130201000303030303030303030303035500000c0300303030f0f170f0f0303030f038b0f83c3c3e0f1f0f0f0f0f03272703555543d0b5555550000000000122c000f0000f03c000f003c003009c04f0201000f0f4b03030f0f030f030f030f03030303033b034b035500000c1b003170317a1717aa0fa9540122c09c37009c27005c0f00c27221004c0c4c0c031305c5c0005c3c3c5cbc9cac0cbc9cac0ca80282a955555555540000000000004c3c3c4c4c4c4c0c4c4c4c0c4c4c4c4ea954021785c3c3c5ea03aa0fa2eaaaaa55555555550000000000122c0017003c0880080000c02f02020100130f0f13a80e13a13131313aa5500000c130 26 67108863 11 2047
def hc_70_12 : Nat → Nat := unpackHintV5 0x873d084192831f68584f3f1d475d10a39725d9bc33d8d282e66568f62fe4b41714378b01a225518bd2776c592a046c8743703fa1001cfcb50dc42e865c2182d855714c28008f35b83e225e1b01040b887e05302501eeaa60b0d1a04544c8104498000208 0x10b45c3c3c5d50356a0fa85d5565a55a8bea03aa5665aa010f62d555555555642d545c0f1411f01f07ca23a0222d104c3c3c4d50344d44c4c4c4e13aa80ea954131303c3c3c3eaaaa9668ac0cac9cac9cac0e82290f90b0b42c2d2b0b665a50b0b0f03c1f07c881f1f00b0b00b103c3c3c3c4c4c4c4ea84c4c4c0c4c4c4c0c2d42c131303c3c3c3ea0fa83ea2ba80eaaa8043d8b50b0b42c2d2b0b5a582d9950b030b0b0b2b0b03a0baaaaa0b0baaaa0b0b0b0f03c1f07ca23a0222c2c40b0b00b1f00f0f0f0f1313131384eaa03aa0b50b0b0b0b030b130b0304c4c0f0f0f0faaaaa0b0baa2b032b272b272b0350455543d4ad55555550f03c1f07ca121f1f050440f0f0f0f13131313aa13131303131313035504c4c50b4ad55030f0f0f0f5a55555aa0fa83ea2ba80d955aaaa8055550f62d4ad555555547c1403c0f07c1f288e8088b4444d55030f0f0f0f1313131384eaa03aa5504c4c40c0d17170b0b83e17a89e27a89e6ba89ea03aaa00b0f42d0b0b0b9660b0b1f07c1f1f88e222c4c0c4c0c4c4c4e80c5c3c3c5eaaaa6a94ac0cbc9cbc9cac0e82290b642d0b665a50b0b1703c1f07c881f1f00b0b00b104c3c3c4c4c4c4c4ea84c4c4c0c4c4c4c0c2d42c131305c3c3c5ea0fa85ea2fa80eaaa8050b0b43d8b42d0b65a5a0b0b66542c0c2c2c2c2c0e82eaaaa82c2e82c7eaaa82c2c2c5c0f07c1f288e8088b0b102c2c0b00b0b1f1f0130f0f131313131384eaa03aa0b50b0b0b0b030b130b0304c4c27032703aaaa2f172b0f2b0f2f17a59aa08a42d0b640d996940c0c7c1f00c1f2207c7c02c2c02c41303130303030303aa13130303131303030b50300c4c27032703a83ea17a89ea03aaaa010b0b4ac2d0362d40c0d969682c2d982c5c2c2c2c3c2c2d5a0baaaaa0b0baaaa0303031f07c0307ca23a0222c2c40b0b00b1f0130313030303030384eaa03aa0b5030b0b03030b13030300c4c27032703aaaa2f172b0f2b0f2f17a0b0baa504555555555551f07c0307c841f1f050441303130303030303aa13130303131303035500c4c543d5172703270350ba83ea175a55555aa27a80ea9955aa8052b5555540d8b5555642d547c1f11f0500307ca23a0222d104c0c4c0d135540c0c0c0c0e13aa80ea954031310d0ea0fa85eaa80eaaa8043439a982ea87c1f07c1f288e8088b1f07c131313131313131384eaa03aa1313131304c4c030303030f038b0f0f03030f0f0f83e17a171fa171787e03170f0f171745c2c5d170b032727031fa1f0000000000222c001705c00f03c01705c00170ac0003009c02300b010005c0c3c0c5c5c0c0c5cac0c0c0c0c0c0c4e80ccc0ccc0c00000c0c06c00c0c0005c5c0003c0c03a0f0fa1f1f83e0f87e033b53c2ced4f0b0f0f0f0f032727031fa1f000000000000334f1b1b0303331b034f03030f030f030303030313a0333033303000303030f0f170f0f0303030f038b83e83c3e83c3c7c7e0f83e1f80c3d0f0b0f43c2c3c3c3c3c0c9c9c0c7e87c0f07c000000000088b0003c0003c0f0003c17003c0f000c03009c27008c02c04000f0f333303030f0f030f03130f030f030303030313a03330333030000030301b00f0f0f0f83e0f87e1f5142d0b0b4ac2d90b00502b032b272b272b031f1faa0b0b0b0b0000000000000000f0f0f0f2b132b1313a130b50b331b1303331b1303000f0f0f0f83e0f87e1f43d8b50b0b42c2d2b0b642d50b030b0b0b2b0b030b1faa0b0b0b0b0b000000222c0000000f003c00300ac02300b02c04400b02c000b00000f0f0f0f2b132b1313a130b50b0b0b0b030b330b03000003047040c0d17170b0b87e1fa0b0f42d0b0b0b000088b1703c271ac02709c00300c2709c2302c401b031b032b270030306c170f0f1783e1787e1f50b0b43d8b10b42d90b50002b032f272f272b031f1faa0b0b0b0b000000000222c000000170f0f132b132f1313a130b50b331b1303331b130300170f0f1783e1787e1f50b0b43d8b42d0b642d50b030b0b0b0b030b1faa0b0b0b0b0b000000222c00000017003c00300bc02300b01002c0b0002c00005c3c3c4cac4cbc4c4e84c2d42c2c2c2c0c2ccc2c0c00000c11c09c0c9c0e1f87e1f80d0b0b4ac2d4503642cbc5cac3cac3cbc5c01407c7ea82c2c0c0c000000000000000bc0cac0c0c0c0c0c4e80c2d40ccc6c0c0ccc6c0c0c009c0c9c0e1f87e1f80d0b0b4ac2d0362d40c0d90b0b170b0b0b0f0b0b542c7ea82c2c0c0c0c00000088b00000005c00f000c027008c02c0b011002c0b0002c0000bc0cac0c0c0c0c0c4e80c2d40c2c2c0c0c2ccc0c0c00000c0c06c09c5c9c3c9c3c9c5c9c0cbc9c9c0c087e1fa1f1fa1f1f87c7e031f2f2b2b2f2749c2c9d270b033b272727031fa1f00000000000002f032b03271b0303271b03030303030313a0333033303000303030383e0f80e0343d8b50b0b40c0d0303642d503030303030303030b13aa0b0b0b0b0b000000000000030303030303030303a03035030303030303030303000303030383e1380e0350b0b43d8b40d03642d503030303030303030b13aa0b0b0b0b0b000000000000030303030303030303a03035030303030303030303000303030384e1380e033b3b0303030313a1300000000030303030303030303a0303030303001b031b0384e1384e033b473b47031b1b0313a13000000001b171b0f1b0f1b1703031b1b1b1b03031313aa13131b0b1b46d1b0b0000131b0313131b0313031b0313031b03131313aa0313131b0313131b03130000000c0c0c0c3c0e2c3c3c0c0c3c3c3e0f85e85c7e85c5e1b80c5c3c3c5c5d170b1745c2c0c6c6c0c7e87c0000000000005c3c3c5c5c5c5c6c5c6c5c5c0c6c6c0c6e86c6c6c6c6c003c0c0383e0f86e030f0f0f0f031b1b031fa1f000000000f030f0f03171b031fa1f3f3b3b3f000303030f0f170f0f0303030f038ba0f0fa0f1f83e0f86e030f43c2c3d0f0b0f0f0f0f031b1b031fa1f0000000000000f0f1b1b0f0f0f0f0f0f1b0f0f0f0f031b1b031ba1b1b1b1b1b000f0f0f0f83e0f87e1b43d8b50b0b42c2d2b0b642d50b030b0b0b2b0b030b1faa0b0b0b0b0b0000000000000f0f0f0f1b1b1b1b1ba1f0b50b0b0b0b3f0b1b0b0b00 25 33554431 10 1023
def hc_70_13 : Nat → Nat := unpackHintV5 0x83ed433fb6901df9788e849e06f9d223408f198e4480b813c456dd4b29308f9344550940986445d6a2128418fa73b473328235c0f6198a558b864fc522a82253cf610b47a87b8288319b0a18980d0c180d04f944c20d9bc0a618302e29380de24c0001bc 0x2717270f270f2717270327031f1f1f87e1fa0a1f21f1f80c7cbcacacbc9d270b2749c2c0c9c9c0c7e87c7c1f07e0a0031f07c7c1f207c1f0bc0cac0c9c6c0c0c9c6c0c0c0c0c0c0c4e80ccc0ccc0c031f03c3c3c3c3c3c3d50f0f2b032b272b272b0383e0f87e1fa0a0b10b42d0b42d42c2d42c2d90b0f03c1f07c0b82802c80b103c3c3c3cac4cac4ccc6c4c0ccc6c4c0c4e84c2d42c131f03c3c3c3e0f83e1f87c3c3c3c3c3c3c3c3c8c0c7c8c8cac7c0c043d8b50b0b42c2d2b0b642d42c2d42c2d50b030b0b0b2b0b030b1faa0b0b0b1f0b1f0b0b0b0b0b230b0b0b0b0b0b0b0b0f03c1f07c222e82a0b102c2c02c7c03c3c3c3cac4cac4c4e84c7c8c4c0c8cdc4c0c2d42c2c2c2c0c2ccc2c0c131f1030345c5c2c2e1f87e85c3c3c5c9c8d6c8c7c7c9c8c9c8c7c7c0c8c0c8c9c8c9c0c02c3d0b42c2c2d0b42c7c1f07c7e22e286c0c6c0cac9c6c0c6c0c5c3c3c5d43c3c3c3c5d2b032f272f272b0383e1787e1fa0a0b10b42d0b42d42c2d42c2d90b1703c1f07c0b82802ca80b105c3c3c4cac4cbc4ccc6c4c0ccc6c4c0c4e84c2d42c131f05c3c3c5e0f85e1f87c5c5c3c3c3c3c5c5c8c0c7c8c8cbc7c0c050b0b43d8b42d0b642d42c2d42c2d50b030b0b0b0b030b1f0b1faa0b82c2c2c7c2c7c2c2c2c2c2c8c2c2c2c2c2c2c2c2c5c0f07c1f088ba0a82c40b0b00b1f0170f0f132b132f1313a131f231303233713030b50b0b0b0b030b330b0304c7c270327032f172b0f2b0f2f17030323540c0e1f87e1f80e8282c42d0b42d035030350b03642c7c1f00c1f02e0a00b202c42f032b0303030303331b0303331b030313a030b50300c7c2703270387e1f87e0323171f0f230f1f1703031f2323270303010b0b4ac2d0362d40c0d90b50b0b50b0b0b170b0b0b0f0b0b542c7ea82c2c2c7c2c7c2c2c2c2c2c8c2c2c2c2c2c0c0c0c7c1f00c1f088ba0a82c40b0b00b1f02f032b030303030313a031f1b0303231b03030b5030b0b03030b33030300c7c1b031b0384e1384e031b171b0f1b0f1b1703031b1b1b1b03030aa130ecdcecdc0c6c6c0c4e84c6d1b0b1b46c2c7c1f00c1b04c81382807c1f04c0c4c0c0c0c0c0c4c4e80c4c4c6c4c4c0c4c4c6c0c0313131b10d0e1f87e1f87c8c5c7c3c8c3c7c5c8c0c7c8c8c7c0c03b3b3b3b431fa1f1f48c2c8d1f0b1f07c1f07c222e82a1f07c331333133313331313a131f2313032313033313331304c7c030303030f038b0f0f03030f0f0faaaaaaaa170f0f171745c2c5d170b03272703aa00000000222c000017003c01705c001707c0003009c0802c040013030f03131303031313030303030303aa1303130300000c13003030f0f170313030f0300eaaaaa86ccccc6c3c3c3c3c0c9c9c0ea800000088b000006c033003c00f000c0270200b010000c0c0c3c3c5c3c3c0c0c0c3c0e2eaaaa0f87eaaa83d0f0b0f43c2c3c3c3c3c0c9c9c0ea80000000088b000003c1f0003c0f0003c00f000c0270200b010003c3c4c0c0c3c3c0c3c0c4c3c0c3c0c0c0c0c0ea84c0c4c0c0000304c00c2c0c2d45c5ea9543d50088b02707c02707c01703c0309c84401303130300c4c42d170f0f17540d5aa5665aa43d8b555555540000000088b000005c00f01100107c000300bc081010004c3c3c4d50344d44c4c4c4ea9540000304c03c3c3c3eaaa90f62d42c2d0b0b4ac2d9950b030b0b0b2b0b03aaaa0b0b0b0000222c000000000f003c00300ac0802c0400b02c000b07c0000f0f0f0f13131313aa0b50b0b0b0b030b130b0300000c13050b4ad55030f0f0f0f6556aaaa55550f62d4ad55500000000222c000041f00110003c00f000c02b0204040044d55030f0f0f0f13131313aa5500000c13040c0d17170b0baaa0b0f42d0b0b0b00088b01703c2707c02707c00300c2709c80b1004c0c4c0c4c4c031305c3c3c5eaaa942c2d0f62d0b42d9950b030b0b0b0b03aaaa0b0b0b0000222c00000000b07c017003c00300bc0802c0400b02c000b07c000130f0f1313131313aa0b50b0b0b0b030b130b0300000c13027032703aaaa42c2d2b0b40d8b50303660b170b0b0b0f0b0b56aaa80c0c0c000088b0000000005c00f000c0270200b01002c0b0002c1f00004c0c4c0c0c0c0c0ea82d40c2c2c0c0c2c4c0c0c0000304c150f545c9c0c9c0d42ea9955aa94ad555550362d540000000088b000005c00f0107c00440003009c081010004c0c4c0d135540c0c0c0c0ea9540000304c07c5c7c3c7c3c7c5c9c0c9c0c0aaaaaaaaa2f2b2b2f1f47c2c7d1f0b03272703aa000000000000013031303131303031313030303030303aa13031303004343aaaa4343aa0000222c000017003c003000802c04001313131313131313aa1313131300000c130030303030f038b0f0f03030f0f0fa83ea17aa85e2baa85e17a89e27a80e03aaaaaaaa005c3c3c5c5d170b1745c2c0c9c9c0e6a60baa1703c17170171f00307ca23a0222c7c1f04c0c3c0c4c4c0c0c4c4c0c0c0c0c0c0e13aa80ea84c0c4c0c031302dbd8b0b6f031762c1f0f0f0380c3eaaaa80c0eaa85c5eaa82283c3c3c3c0c9c9c0ea96f0b6f42c3c0f00c1f282222c7c7c03c3c07c1f03c0c3c0c0c0c0c0ea84c4c0c0c4c4c0c0c4c0c4c0c031300c0c3c3c5c0c4c0c3c0e03a8cea1ba83ea0fa89ea03aaaaaa006ccccc6c3c3c3c3c0c9c9c0e6a60baa1b07c0f03c0307ca23a0222c7c1f00c0c0c3c3c5c3c3c0c0c0c3c0e2eaa0f83eaa0faa0fa83ea27a80eaaaaaaa800f43c2c3d0f0b0f0f0f0f032727039a982ea83c7c03c3c03c0f00c1f288e8088b1f07c0f0f1303030f0f030f03130f030f030303030384eaa03aa1303130300c4c27270327032faaaaa2717270f270f2717aa8228bcacacbc0c9c9c0ea89d270b2749c2c7c1f00c7c1f1f2207c7c07c7c07c1f04c0c4c0c0c0c0c0ea84c4c0c0c4c4c0c0c4c0c4c0c031300c2c0c2d45c5ea2789ea279ee0f85e2780ea81543d555642c7c1f223888b1303130313a03170f0f17aaaaaaa0b0b2b032f272f272b03504555555555551703c1f07c841f1f05044130f0f1313131313aa13131303131313035504c4c 25 33554431 10 1023
def hc_70_14 : Nat → Nat := unpackHintV5 0x87b861a12f17e7f54ad1f331447a44511df713476882a9cc11c26e1c9d1a4d27463f0a8983f17a5d846f1657214552487148318c4e287c928720646fc64104e2e23cb0910dd72aa34046b0baa2ae2914b289701aa20b0a206b72ea15b0a5836740a0878a4800043c 0xc0c0c0e0f84e0380d0b42d0340d90000f22c00000017003000c01302002c0400030303030303030303a40d600000c030170f0f1783e1787e1b42d0b42d0b64170f0f171b1b1b1b687e50b0003c8b0000000005c00c0007c0800b0100dc01b0005c3c3c5e0f85e1f87d0b42d0b42d6998b0b170b0b0b0f0b0b0b030b0b0b2f0b0356a0003c8b000000000005c00c0007c0800b01002c0b0002c00005c3c3c4cac4cbc4c4e84c2d42c2c2c2c2c0c2c2d2c2c0c000030cc05c0c0c5c5c5c21f87e85d0f49d5b549d27540d0349d2742d55598b5503c000006c0c6c0cac9d031b45c0c0c5c5c5c2aa90b42d662d85e0f89e3ba89e27a80e0389e27942e03c000004c0c4c0c4c4e031385c0c0c5c5c5c10f45d52749d5275fd527540eaa995555662c0f0004230004c0c4c0c4c4c4d40c5c0c0c5c5c5c21f87e90b42d46c6c6c6c6c6c0f000170303171717087e1fa42d0b5698b170b0f0b270b7f0b0b0b270b270b0b0b030b030b270b27035a03c000006c0c6c0cac9c2c2c0c0c2c6c0c5c5c0c0c3c0c5c5c5c5c0c3c0c5c0170f0f172789c7c9e271f032b27272703170f0f172749c2c9d270b032b27272703000f0000000000005c0c3c0c9c6c0c0c9c6c0c0c0cac0c0c9c0c0c0c0c0c005c3c3c5e170f85c5e1f1f8bc7c5c5c3ea17171f031f1f1f271f03005c3c3c5cacbcbcac7c7e8ec7c7d1f0b1f47c2c00000000000005c3c3c4cac4cbc4c4c7e8cc4c7c6c4c0c7c6c4c0ccc4ccc4c005c0c3c0c4c3c3c5c0c6c4c0c5c3c3c5c0c6c6c0ccc4c4ccc000000005c5c0c0c3c0c5c5c0c0c6c6c6c6c0c0c6c6c4e1386c7c6c2c6d1b46c2c00005c5c0c3c0c5c0c0c6c0c6c0c4c0ccc4c6c0c6c0c6c6c0c0000170f0f17170f0f172b2f2f2b170f0f172b2f2f2b0003c8b00000005c00c0000800b010005c3c3c5cacbcbcac00003009c0c9c0e1f87e1f80cbc5cac3cac3cbc5d547c7d42c2c0015554540140000000000000bc0cac0c0c0c0c0c4e80ccc6c0c0ccc6c0c0d54009c0c9c0e1f87e1f80d17543d503549d50b5555598b5554007c00c8b000000000005c00f007c07c0804400400101000bc0cac0c0c0c0c0c4e80d50346d554000030cc09c0c9c0eaaa90b42d0b40d98b5a85ea0fa80ea27a560b800ac00c8b000000000005c00f007c202002c040880083b00004c0c4c0c0c0c0c0ea82d40ea0384e80000304c09c0c9c0cbc5cac3cac3cbc5d47c7d56aaaa800155554001440000000000004c0c4c0c0c0c0c0c4c4c0c0c4c4c0c0ea954009c0c9c0d50f545d527540eaaa965555555598b002b00322c004230000000005c00f007c10004400808040400130313030303030344d5503aa5500000c1302703270387e1f87e0342d0b42d03642f172b0f2b0f2f1703030b0b1f1f03035000a000001f000000000000bc0cac0c0c0c0c0c4e80c2d40ccc6c0c0ccc6c0c0c006c0c6c0e1f87e1b80d0b42d0b40d906c6c6c6c0c6c6c0da1b942c007c00c8b0000000005c00f006c07c0800b01006c01b0009c0c9c0e1f87e1f80d0b42d0b40d6998b0b170b0b0b0f0b0b03030b0b0b27030356a001f00322c0000000000b08c017003c01f01f02002c0400b02c000b00002f032b030303030313a030b5030b0b030b03030b0b1b030300000c3302703270387e1f87c7e27031f171f0f1f0f1f17a1f1f1f2303802f2b2b2f032727031fa1f1f47c2c7d1f0b00000000000002f032b030303030313a031f1b03031f1b0303330333030003030303132b132f030303032f2b2b2f0303030333131333000000001b171b0f1b0f1b1703030303030303031b1b1384e1b1f1b0b1b46d1b0b0000031b03030303030303030303030303031b03030303031b03000009c0c9c0cbcacacbc0c9c9c0cbcacacbc0c9c9c0c00ac00c8b00000005c00f008c00800b01000bc0cac0c0c0c0c0c0c0c0c0c00003009c0c9c0e2f1f87c7e1f1f89c0c7c5c7c3c7c3c7c5e807c0387c7c7cbcacacbc0c9c9c0c7e87c7d1f0b1f47c2c7c1f00c1f07c7c87c030301f0301f07c2f032b030303030313a031f1b03031f1b03033303330300c7c1f171f0f1f0f1f172703270302aaaaaaa90b42d42c2d42c2d0b40d98b5a85ea0fa87e3baa87e1faa80ea27a560b87c2b1f1f00c0c0c0c0c00322e202c4a087c04c0c4c0c4c4c0c0c4c4c0c0c0c0c0c0ea82d40ea0384e8031309c0c9c0eaaa8bc5cac3cac3cbc5d4116aaa955555555547c1f00c4880303050441303130303030303aa13130303131303035500c4c1f171f0f1f0f1f17270327030150f545d551f47d551f5527540eaaaaaaa9655555555555598b1f0ac7c7c0303030303000c8b51f1f051088441303130313130303131303030303030344d5503aa5500c4c1b171b0f1b0f1b1703030303003030300c0c4c7c4c7c4e1b1f1386c6c0c0c0c0cbcacacbc6d1b0b1b46c2c0c0c0c0c7c4c4c7c7c1f00c0c00c0c00c0307c1307c1f00c6c0c0c0c0c0c6c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0303031b07c5c8c3c7c3c8c5c9c0c9c0c02f1f2b1f1f87c8c7e1f031f27032f2b2b2f2347c2c7d230b032727031f1f1f0ac7c8c0303030303000c8b1f07c1f07c2f032b032303031f230303030303031f0303030300c7c030303030f038b0f0f03030f0f0f83e17a171fa171787e0317170f0f0f0f17171717171717171f1f1717232b1717171703031f2323270303005c3c3c5c5d170b1745c2c0c9c9c0c7e87c7d230b2347c2c5c0f05c5c05c7c00c1f088ba0a87c1f05c0c3c0c5c5c0c0c5cac0c0c0c0c0c0c4e80c7c6c0c0c8c6c0c0ccc0ccc0c031f00c0c3c3c3c0c3c3c5c5c0c0c8c5c0c0c3c0c3c0e83ca083e0f87e033b53c2ced4f0b0f0f0f0f032727031fa1fa00f803c0f00c1f03c201f07c331b0303331b03030f030f030303030313a033303330300c7c0303030f0f170f0f0303030f038ba0f0fa0f1f83e0f87e030f0f230f0f0f0f0f0f0f0f0f0f1f1f0f0f0f0f0f0f0f0f03031f2323270303003d0f0b0f43c2c3c3c3c3c0c9c9c0c7e87c7d230b2347c2c3c3c7c7c03c3c0f00f03c0307c222e82a1f07c0f0f333303030f0f030f03130f030f030303030313a031f1b0303231b03033303330300c7c 26 67108863 11 2047
def hc_70_15 : Nat → Nat := unpackHintV5 0x82815740044f1ea9564f0693874e0d538009c1a8b5d4cac26661e8de2ee0851662438ac91a05280f2273a8192d532090699042816d1efc910e2d5446b398c3041571556b289c439c443a7a1c19810b8e9f84e73801efa100b4d0c041a63010f3f800021e 0x5c3c3c5e170f85c5e1f1f8bc7c5c0fa807c0c7c7c7c9c7c0c5c5c5c5c3c3c5cacbcbcac7e87c7d1f0b1f47c2c5c0f07c1f07c7c87c0f0f01f0f01f07c170f0f132b132f1313a131f1b13031f1b13033313331304c7c0300c17171717aa42d0b98b6278eea2789ea1783e0389e50b83c0f03c3c7c7e07c1303130380c4e005c3c3c5c5c5c5c0c5c5c0eaaaaaaa90b42d42c2d42c2d0b42d98b5a85ea0fa85e17aa85e3baa80ea2fa560b80f22c3c3c03c3c3c7c1f2202c4a087c04c3c3c4c4c4c4c0c4c4c4c0c4c4c4c4ea82d42ea0384e8131300c0305c5c5c5d52749d52760d0f45d2740ea99555662c3c0f03c3c7c7d1f1f1404c0c4c0c4d40c5c3c3c5eaaa91540ac0cbc9cbc9cac0eaaa9555555555503c1f07c880f0f05044130f0f1313131313aa13131303131313035504c4c005c3c3c5c5c5c5c0c5c5c0d50f545d55175551745d52f540eaaaaaaa9655555555555598b03c8b0f0f00f0f0f1f07c51f1f05108844130f0f1313131303131313031313131344d5503aa5504c4c003030f031705c0c3c0c6c6c0c0c6c6c0c0c4c3c3c5c4e1b1b1386c7c0c6c4c0c5c3c3c5c6d1b0b1b46c2c0c6c6c0c7c4c4c7c5c0f06c3c03c3c00c1b07c1307c1f05c5c0c3c0c5c5c5c5c0c0c6c0c6c0c4c0c4c0c6c0c6c0c031f1b1b00170f0f1717171703171703170f0f171785c5e17172b1f2f1f170f0f171745c2c5d170b2b2f2f2b1f1f03c8b0f0f00f0f0f1f07c1f07c1f07c170f0f17171717031717032b2f2f2b1f1f07c7c0f0f0f0f83e0f87e1f550f0f52b032b272b272b030b0b00055551500500000000000000f0f0f0f2b132b1313a13331b1303331b130355000f0f0f0f83e0f87e1f43d50f540d52b542d5555662d55503c8b00001f0000000000f00300ac01f02011001000404000f0f0f0f2b132b1313a13540d3f55500000c3300f0f0f0faaaa42d0b42d0b662d6a0fa83ea03a8ae9582e03c8b00002b0000000000f00300ac080800b010220020ec0000f0f0f0f13131313aa0b50ba80e13a00000c1300f0f0f0f50f0f552b032b272b272b03aaaaa000555550005103c0000ac000000000f0f0f0f131313131313130313131303aa55000f0f0f0f543d50f54ad503aaaa595555555662c0f22c0000ac0000000003c00c02b0100044008080404000f0f0f0f1313131344d5503aa5500000c1300f0f0f0f83e0f87e1f42d0b42d0b640b0b0b0b0f0f0b0b2b032b272b272b035000a000000001f0000000003c3c3c3cac4cac4c4e84c2d42ccc6c4c0ccc6c4c0c000c0c0c0e0f83e0380d0b42d0340d900f22c00000c000003c00c003004c0800b010000c0c0c0c0c0c0c0c0e903580000300c03c3c3c3e0f83e1f86d0b42d0b42d903c3c3c3c6c6c6c6da1f942c0f22c00007c00000003c00c02b007c0800b0100dc01b0003c3c3c3e0f83e1f87d0b42d0b42d6998b0b0f0b0b0b0f0b0b0b030b0b0b2b0b0356a03c8b00001f000000000b08c00f00300ac01f02002c0400b02c000b00000f0f0f0f2b132b1313a130b50b0b0b0b0b030b0b570b0300000c3300f0f0f0f83c3e0f0f87e1fa0f0f0f0f0f87c0c7c7c7c9c7c0c00f0f0f0f2b2b2b2b1fa1f1f47c2c7d1f0b00000000000000f0f0f0f2b132b1313a131f1b13031f1b130333133313000f030f030f0f0f0f031b13030f0f0f0f031b1b0333131333000000000f030f0f0f0f030303031b1b1b1b03031b1b1384e1b1f1b0b1b46d1b0b00000f030f0f0f03031b0303031b130333131b031b1b031b03000003c3c3c3c3c3c3c3cacacacac3c3c3c3cacacacac0f22c0000ac000003c00c02b000800b010003c3c3c3cacacacac00003003c3c3c3e0f0f83c3e2b1f87c7e803c0f87c0c7c7c7c9c7c0c3c3c3c3c3c3c3cacacacac7e87c7d1f0b1f47c2c3c0f07c1f07c7c87c171701f1701f07c0f0f0f0f2b132b1313a131f1b13031f1b13033313331304c7c003cac3c0c3c3c3c0c3c3c3c3eaaaaaaa942c2d42c2d0b42d0b42d98b5a83e3baa83e0faa83ea0fa80ea2ba560b83c3c5c3c3c00f22c7c2b1f1f2202c4a087c03c4c3c0c3c3c3c0c3c3c3c3c4c4c4c4ea82d42ea0384e8131303c3c3c3eaaa94114ac0cac9cac9cac0eaaa9555555955543c3c40f1f0ac7c7c881717050440f0f0f0f13131313aa13131303131313035504c4c003cac3c0c3c3c3c0c3c3c3c3d550f43d550f550f543d52b540eaaaaaaa9655555555555598b0f0f170f0f003c8b1f0ac7c7c47c14221103c4c3c0c3c3c3c0c3c3c3c3c4c4c4c4d135540ea9541313000c0c3c0f031b1b03031b1b03030f030f031386c7c4e1b1b0f0f0f0f031b13031b46c2c6d1b0b0f0f0f0f031b1b031f13131f171701b1700f03c0306c1f04c1f07c0f0f0f0f030f0f0f03031b0303031b131b0313031f1b031b1b0300c7c6c6c003cac3c0c3c3c3c0c3c3c3c3c3e0f0f0f83c3c3c3c3cac7cac7c3d0f0b0f43c2c3c3c3c3cacacacac7c7c3c3c5c3c3c00f22c7c2b1f2307c1f07c1f03c3c0c3c3c3c0c3c3c3c3cacacacac7c7c1f1f05c3c3c5e0f85e1f87c5c5d554ac0cbc9cbc9cac0c2c2c001555465401400000000000005c3c3c4cac4cbc4c4e84ccc6c4c0ccc6c4c0d54005c3c3c5e0f85e1f87d17543d50354bd50b5555598b5554000f22c0000000000170030001f07c088044004001010005c3c3c4cac4cbc4c4e84d5034fd554000030cc05c3c3c5eaaa90b42d0b42d98b5a85ea0fa80ea2fa560b8000f22c00000000001700300080800b02c0440880083b00004c3c3c4c4c4c4c4ea82d42ea0384e80000304c05c3c3c5d5545c5cac0cbc9cbc9cac0eaaaa800155554001440000000000004c3c3c4c4c4c4c4c4c4c4c0c4c4c4c0ea954005c3c3c5d50f545d52f540eaaa965555555598b0003c8b00108c0000000017003000400110020ec088040b0110004c3c3c4c4c4c4c4d135540ea9540000304c05c3c3c5e0f85e1f87d0b42d0b42d6998b05c5c2c2c2c2c2c2cac0cbc9cbc9cac0d40028000000f22c0000000000170f0f132b132f1313a130b50b331b1303331b130300 25 33554431 10 1023
def hc_70_16 : Nat → Nat := unpackHintV5 0x8780c8a0c123e7e68939ed518a7568bd9c7c1bc6bacc899cc23e643c5e97b12bc5e9006978a0345a6c7795d818651f0ae137f1fa4b745110bc4423d94ab8d0e4ae2eeca98b12152266cbb88602761ea45b866228e147ca183dc2860c6461828812205849380002c2 0xc0c0c3c3c5c3c3c0c0c0c3c0e2e83c3e83c7e0f83e1f80d0f5550f43d550f543d503549d50b555550f42d555598b55543c7c3c0f0f0f03c3c3c3c0c9c7c0c7e87d51234550f0f333303030f0f030f03130f030f030303030313a03540d1b55533031f032717270f270f271727032703561f87e82c2e87c2e1f1f80c7d555555555547cac7cbc7c7c9c1f1f2700c9c7c0c7e87d54bc0cac0c9c6c0c0c9c6c0c0c0c0c0c0c4e80d54cc0c7c0c6c0c6c0e1384e1380c6c5c6c3c6c3c6c5c0c0c6c6c6c6c0c0c2c2ea84c2d55555555547cfc7cfc0c6c6c0c4e84c6c7c6c1b1b1b1544c0c4c0c0c0c0c0c4c4e80c4d5555130313131b03434387e1f87e1f45d50f540d5542d5555662d5551f1f1f1f431fa1f5448d154cc4ccc4ccc4ccc4c4e84d5035554cc4c7c4c0c0c0c0c3c0e2c3c3c0c0c3c3c3eaaaaaaa90b42d42c2d42c2d0b40d98b5a85ea0fa85e17aa85e2baa80ea27a560b85c3c3c5c5c5c5c171f1700c9c9c0ea82d42ea223813030f03131303031313030303030303aa0b503a80e13a1303130303030f0f170313030f0380eaaaaa90b42d0b42d0b40d98b5a86ea33a83ea0fa80ea27a560b86ccccc6c3c3c3c3c0c9c9c0ea82d42ea22380303030f0f170f0f0303030f038baaaa83e3baaaa50b0b50b0b42d0b42d03662d6a0f8eeaa0f83eaa0fa83ea03a89e9582e0f1f0f03c3c3c0f0f0f0f03272703aa0b50ba888e03c3c4c0c0c3c3c0c3c0c4c3c0c3c0c0c0c0c0ea82d40ea0384e84c0c4c0c9c5c9c3c9c3c9c5c9c0c9c0eaaa9a5aaaa42d0b50b0b50b0b42c2d030b662f2b2b2f271f2709c7c9c03272703aa0b50b13031303131303031313030303030303aa0b503130313034343aaaa42d0b42d0b662d6a17a83ea03aa9582e4343aa0b50ba888e04c4c4c4c4c4c4c4ea82d42ea0384e84c4c4c4c0c0c0c0c3c0e2c3c3c0c0c3c3c3d50f545d55174ad551745d52749d50340eaaaaaaa9655555555555598b170f0f1717171705c7c5c0327270348d152a9544c0c3c0c4c4c0c0c4c4c0c0c0c0c0c0d135540ea9544c0c4c0c8b731f8b1cc0c5c7c2d0f0f0340c3eaaa940c0d5545c5d56aaa9555555662d55543c3c3c3c0c9c9c0ea87dcc731f1543c0c3c0c0c0c0c0ea84c4c0c0c4c4c0c0d544c0c4c0c0c0c3c3c5c0c4c0c3c0d0354cd51b543d50f549d503aaaaaa59555555555662c6ccccc6c3c3c3c3c0c9c9c0d23454aa550303030f0f170f0f0303030f038b5543d0f5543d543d50f549d503aaaaaaaa5955555555555662c3c7c3c0f0f0f03c3c3c3c0c9c9c0d23454aa550f0f1303030f0f030f03130f030f030303030344d5503aa551303130327270327032faaaaa2717270f270f271756aaa955555555554bcacacbc0c9c9c0ea89c7c9c271f271544c0c4c0c0c0c0c0ea84c4c0c0c4c4c0c0d544c0c4c0d0d0d50f545d5540eaaa965555555598b434348d152a9544c4c4c4c4c4c4c4d135540ea9544c4c4c4c0c0c0c0c3c0e2c3c3c0c0c3c3c3e0f85e85c7e85c5e1f80d0b42d42c2d42c2d0b40d6998b0b170b170b0b0b0f0b0f0b0b0b170b170b0b0b0b0b170b2b0b0b0b0b03030b0b0b27030356a170f0f1717171705c7c5c03271f031fa1f0b50b0b0b0b02c8c2c17030f0317170303172b03030303030313a030b5030b0b030b03030b0b1b030333031f0303030b0b0b030b0b171703030b0b03030f030b03a0f6960f83e1f80d42e5a42d0b42d03642c7c7d3c1f1f4f03c3c3c3c0c9c7c0c7e87c2d42ccd3c6c6c0c0ccc6c0d3c0c0c3c0c3c0c0c0c0c0c4e80c2d40ccc0c7c0c0c0c0c3c3c5c3c3c0c0c0c3c0e2e0fa0f0fa0f0f1f1f83e0f87e0343d42c2d42c2c2c2d0b42d0b40d6998b0b0f0b0b0b0b0b0b0f0b0f0b0b0b0b0b0f0b170b0b0b0f0b0f0b0b03030b030b0b0b270b27030356a0f1f0f03c3c3c0f0f0f0f03271f031fa1f0b50b0b0b0b02c8c2c0f0f333303030f0f030f03130f030f030303030313a030b5030b0b030b03030b0b1b030333031f032717270f270f271727032f2727030b0b0b87e1fa5a1f61f1f80c7d0b42d6942e42c2d030b642c7cac7cbc7c7c9c1f1f2700c7c9c7c7c0c7e87c2d42cbc0cac0c9c6c0c0c9c6c0c0c0c0c0c0c4e80c2d40ccc0c7c0c0c0c0c0e1384e0380d0b42d0340d90b1f1f0303030313a130b50b030303030303030303a40d6030303031b031b0384e1384e0342d0b42d03642c6c5c6c3c6c3c6c5c0c0c6c6c6c6c0c0d6a84da550b87d5c7d2c0c6c6c0c4e84c2d42c6c7c6c1b1b1b04c6c0c4c4c6c0c4c0c6c0c4c0c6c0c4c4c4ea80c4c2c2d540c2c2c2c2c4c6c0c4c4c6c0c4c0c0c0c0c3c0e2c3c3c0c0c3c3c3e0f85e85c7e85c5e1b80d0b42d42c2d42c2d0b40d90b170f0f171717171b171b1717031b1b03686e50b170f0f1717171705c7c5c031b1b031fa1f0b50b1b1b1b1b0f030b0383e0f86e0342d0b42d03642c3c0c3c3c0c5c6c0c7e87c2d42c3c3c3c3c0c6c6c0c7e87c2d42c7cdc7cdc0c0c0c3c3c5c3c3c0c0c0c3c0e2e83c3e83c7e0f83e1b80d42c2d42c2d0b42d0b40d90b0f0f1b1b0f0f0f0f0f0f1b0f0f0f0f031b1b03686e50b0f1f0f03c3c3c0f0f0f0f031b1b031fa1f0b50b1b1b1b1b0f0f0f0f83e0f86e1b42d0b42d0b642c3c3c6e2c3c3c3c3c6c6c6c6c6c6da1b942c3c3c3c3c0c3c3c3c6c3c0c3c7ea83c3c2c2d542c2c3c5c3c3c3c3c3c6c6c6c6c7e87c2d42c6c6c6c6c3c3c3c0f1f0f05c3c3c5e0f85e1b86d0b42d0b42d90b17170f0f0f0f1b8b1b1b1b1b1b1b686e50b17171717031717171b1703171faa17170b0b550b0b0f0f0f170f0f171b1b1b1b1fa1f0b50b1b1b1b1b17171705c7c5c1b1b1b1b87e1f86e1b42d0b42d0b641b1b1b1b1b1b1b1b686e50b000000000006c1b05c00f000c01b007c0800b01006c006c6e1f87e1f86d0b42d0b42d90b1b1b1b1b1b1b687e50b1f1f1b1f1b1fa1f0b50b1f1b1b434387e1f87e1f42d0b42d0b5a662c2c5c2c2c2c3c2c2c2c0c2c2c2c2c0d5a87c7c7c7d0c7e87c2d42c2c2c2c0b230b0cc4ccc4ccc4ccc4c4e84c2d42c2c2c2c2c0c2c2c2c0ccc4c7c4c0c0c03c0c5c1717171717030f03172787c7c9e1f1f170f0f17031f27032749c2c9d270b170f0f17032727031f1f1f0f00f0f01703c3c3c031f07c7c1f07c1f07c271b0303271b030317030f03030303031f0303030300c7c 26 67108863 11 2047
def hc_70_17 : Nat → Nat := unpackHintV5 0x9c7ce54b34c2a43b57d1a69dc871189407ec29eec54ceb3b0a70315b363c7719f04b8c632545e05452d6866956553c9f23024ad52f231695103a5447b21ac37dd6d1920b38b0f6044f624622754f0e30c285d94fc257a540da945051071010d5ec00021a 0x85e170f0f17a80ea83e8baaaaa85c3c3c5e60b9a2b2f2f2baa170f0f17a888e0acbcbcaea84c3c3c4ea0384e84c4c4c4ea84c4c4c4c4c4c4c4c3c0c3c0e0f83e1380c3c0c3ea030303031b1b1b1b03031313aa13130f0f0f0f031b1b0313a131b46c2c6d1b0b0f0f0f0f031b1b0313a131b1f1b06c6c6c1f3b1f470f030f0f0f03031b030303131313a03130f0f0f130313131b03130313131b030f0f0f0f83e8ba0f0f87cae2b1fa83c0c3c3c3cac3c0c3c5c3c3c3c3c3cacacacac7e87c3d0f0b0f43c2c3c3c3c3c7cac7cac7e87c3c3c3c0f230f07cec7c3c3c3c3cac4cac4c4e84c3c3c3c0c3c3c0ccc4ccc4ccc4c7c4e83e2baa80c3c3c3c3eaaa83e8ba2baa6a60b0f0f0f0f2b2b2b2baa88e2a03c3c3c3cacacacaeaa13aa80c3c3c3c3c4c4c4c4ea84c4c4c4c4c4c4c4e80c0c3c0c5e1717030f031717171783c3e0f17a0f0fa1f0f87c7e031f170f0f172749c2c9d270b032b272727031fa1f170f0f171f1f2707c7c9c031f271f1f031fa1f1f3b1f17030f03271b0303271b0303032b0303270313a033303330333031f0317030f0383e1384e03a03030f031380c0c6c6c6c6c0c0c3c3ea84c3c5c3c3c5c0c6c6c0c4e84c6d1b0b1b46c2c5c3c3c5c0c6c6c0c4e84c6c7c6c1b1b1b07cec7d1c4c5c0c3c0c4c0c0c4c0c6c0c4c4e80c4c4c5c4c4c0c4c4c6c0c4c0c4c4c6c0c5c3c3c5e83c3e0fa2e1f87ea170317171717030f0f0f170f0f172b2f2f2b1fa1f1745c2c5d170b170f0f171f2f1f2b1fa1f17171705c8c5c1f3b1f170f0f132b132f1313a13171713031713033313331333131f130303030384e1380e031b171b0f1b0f1b17030303a80c0c0c0ea80c0cbcacacbc0c0c0c0c4e84c6d1b0b1b46c2c7cac7cbc0c0c0c0c4e84c6c7c6c1b1b1b07cec7d1c0c6c0c0c0c0c0c0c0c0c0c0c0c4e80c0c0c6c0c0c0c0c0c6c0c0c0c0c0c6c0c9c0c9c0e1f2b8ac7e03a2e80c0cbc5c7c3cac3c7c5ea0303032f2b2b2f032727031fa1f1f4ec2ced1f0b1f2b1f2f03271f031fa1f1f231f07c8c7c1f3b1f2f032b030303030313a031f03033303033303330333031f03a83ea1727032703a43a2baaaaa80e8b2f2b2b2f9a982c0c9c9c0ea8bcacacbe238a803272703aa1303130384eaa0303030303aa130313031303130303030b0b0f03170b545c5c0c3c0c5c9e271f2789c7c5c3c3c5c0c9c9c0d555543d555555271f2709c7c9c170f0f17032727033b3b55271b0303271b030317030f03030303033b0303550303170f0f1785c3e171787c7e2f1f170b0fa82c2c7c0c7c7c7c9c7c0d555555555555170f0f171f1f1f1f1fa1f1f1f1f07c7c7c55170f0f132b132f1313a131f1b13031f1b1303551f131f130b0b03030f03170b17030f031b1b03031b1b0303130f0f171386c6c4e1b1f031b13035555555555170f0f171b1f1b06c6c6c031b1b0333131333551717030f0317540c0c6c0c6c0c4c0c4c0d5546c0c6c0d0b45c3c3c5d503545c3c3c5d5652b2f2f2b43d8b555555545c3c3c5d512342b2f2f2b3b3b55170f0f17540d52b2f2f2b3b3b550f0f0f0f83c3e0f0f87e1fa50f43e1f031f1f1f271f030b0b0b42d0b42d0b60b42c2d42c2d42c2c3c3c3c3c7c7c7c7c7e87c7c7c7c1f1f1f02d42c3c3c3c3cac4cac4c4e84c7c6c4c0c7c6c4c0c2d42c7c4c7c4c3c0c3c0c3c3c3c3c0c6c4c0d0b42d0b40d0b42c3c0c3d5030303031b1b1b1b03031b1b1384e1b1f0b0b550b0b0f0f0f0f031b1b03331313330b50b1b1f1b06c6c6c0f030f0f0f03031b0303031b130333131b030b0b5030b0b0b0b1b1b031b030f0f0f0f0f0f0f0f2b2b2b2b43d8b50b0b42c2d2b0b42d0b542c0c2c2c2cac2c0c2c2e0b82c2c2c2c2c3c3c3c3cacacacac2d42c2c2c2c0b230b03c3c3c3cacacacac2d42c2c2c2c0c2c2c0c3c3c3c3e0f0f83c3e2b1f87c7e82c2c3c2c3e1f031f1f1f271f0355555555555543c3c3c3c7c7c7c7c7e87c7c7c7c1f1f1f1543c3c3c3cac4cac4c4e84c7c6c4c0c7c6c4c0d547c4c7c4c2c2c0c0c3c2c3c0c6c6c0c0c6c6c0c0c3c0c3c0c4e1b1f1386c6c3c3c3c3c0c6c4c0d55555555546c6c6c1b1f1b03c3c3c3c0c6c6c0ccc4c4ccd5550f030f0f0f03031b0303031b131b031303335551b031b1b0350b4ad55030f0f0f0f65543c3c3c3cacacacad55543d8b52b5555234540f0f0f0f2b2b2b2b3b3b55555030f0f0f0f2b2b2b2b3b3b55503030f031745c5c0c3c0c5c2c2c2c5c3c3c5c9e271f2789c7c0cac9c9c9c0d0b0b43c2d42c2d42c2d0b0b40c2d0b42c5c3c3c5c9c7c9c271f2700cac9c9c9c0c2d42c5c0c3c0c9c6c0c0c9c6c0c0c0cac0c0c9c0c0c0c2d40c0c0c5c3c3c5e170f85c5e1f1f8bc7c5d0fa947c0c7c7c7c9c7c0c2c2c2d0b42d0b42d82d0b0b50b0b50b0b170f0f171f1f1f1f1f1fa1f1f1f1f1f07c7c7c0b50b170f0f132b132f13131fa33131f1b13031f1b13030b50b1f131f1317030f03130f0f17031b130342d0b42d0342d0b503030f031740c0c6c6c6c6c0c0c6c6c4e1386c7c2c2d542c2c5c3c3c5c0c6c6c0ccc4c4ccc2d42c6c7c6c1b1b1b05c5c0c3c0c5c0c0c6c0c6c0c4c0ccc4c6c0c2c2d40c2c2c2c2c6c0c6c6c0c5c3c3c5c5c3c3c5cacbcbcad42c2d0f62d0b42d0b42d50b030b0b0b0b030b0b82e0b0b0b0b0b170f0f172b2f2f2b0b50b0b0b0b02c8c2c170f0f172b2f2f2b0b50b0b0b0b030b0b032703270387e1f87c7e27031f171f0f1f0f1f17a51f40e0b0b0b42d0b42d0360b42c2d42c0d40c0c7c7c7c7c0c7c7c0c7e87c7c7c7c1f1f1f02d42cbc0cac0c0c0c0c0c4e80c7c6c0c0c7c6c0c0c2d40c7c0c7c0c0c0c0c0c4cac4cbc0c0c0c0d0b42d0340d0b42c6c5c6c3c6c3c6c5c0c0c0d503031b1b1384e1b1f03035503032f2b2b2f03030303331313330b50b1b1f1b06c6c6c031b03030303030303030303030303031b03030b50303030b03030303031b03270327032f2b2b2f0327270342c2d2b0b40d8b5030342d0b0b170b0b0b0f0b0b542c2e0b82c2c0c0c0cbcacacbc0c9c9c0c2d42c2c2c2c0b230b0bc0cac0c0c0c0c0c0c0c2d40c2c2c0c0c2c0c0c0c0c9c0c9c0e2f1f87c7e1f1f89c0c7c5c7c3c7c3c7c5e82c2c7c2c0e55555555555547c7c7c7c0c7c7c0c7e87c7c7c7c1f1f1f154bc0cac0c0c0c0c0c4e80c7c6c0c0c7c6c0c0d547c0c7c0c6c5c6c3c6c3c6c5c0c0c0c0c0c0c0c0c0c0c0c0c4cac4cbc4e1b1f1386c6c0c0c0c0d5555555554bcacacbc6c6c6c1b1f1b00c0c0c0ccc4c4ccd540c6c0c0c0c0d50303030303030303030355503030303543d5172703270350b2f2b2b2f65540c9c9c0d4ad555550362d54bcacacbd23454032727033b3b552f032b0355503030303033b0303550303030303030f038b0f0f03030f0f0f83e17a171fa171787e0345d50f545d175545d2b5540d527542d55555555662d555170f0f1717171705c7c5c03271f031fa1f5448d1545c0c3c0c5c5c0c0c5cac0c0c0c0c0c0c4e80d50346d554cc0c7c0c0c0d5545c5d5543c0d03a0f0ba0b0b83e0f87e03555555555551f1f4f07c7d3c0f0f0f0f03271f031fa1f55331b0303331b03030f030f030303030313a035533031f03 25 33554431 10 1023
def hc_70_18 : Nat → Nat := unpackHintV5 0x18489f2a91804653b476b57ccda7f15dcf62082ce3503004e07004c93e000264 0x30303030f038b0f0f03030f0f0f170f0f171785cac5e171703272703170f0f171745c2c5d170b03272703170f0f1717171705c8c5c0327270317030f0317170303172b0303030303030303030303030f030f0383c3e0f0f87c7e2703a03030f030fa85c5c7c5c0e0f0f0f0f0f0f0f032727031f8ee1f1f1f47c2c7d1f0b0f0f0f0f031f1f031f87e1f1f1f1f1f07c7c7c1f1f1f1f0f030f030303030313a031f1b03031f1b0303330333031f031f0303030303030303030303030303030303030303031386c7c4e1b1b0f0f0f0f030303031b46c2c6d1b0b0f0f0f0f03030303331313331b1b1b06c7c6c0f0f0f0f0303030333131333474b4b47030f03030f0303030f03030303030303030303031b0303031b0303031b0303031b0303031b0303031b030303030f0f17031b030f030b031b1b1b1b0f0f0f0f031b1b0346d1b50b0b42d0b42d0342d0b542c0c2c2c2c3c0c0c0c0c2c2c2c6c0c0c2ccc2e0b82c2c2c2c2c6c6c6c6c3c3c3c3c0c6c6c0ccccccccc2d42c2c2c2c0b230b142d0f5540c0c0c3c3d1b5540c5c0c6c0c3c0d036554cc6c6c6c6ccc6c3c3c3c3c0c6c6c0d55546d8b55555548d1506c6c6c6c3c3c3c3c0c6c6c0ccccccccd540c0c3c3c5c0c6c0c3c0c031b1b1b1b0f0f0f0f031b1b031b1b1b1b0f0f0f0f031b1b033333333306c1b000000000006c00c00f000c01b00cc0800b0100000f0f03030f0f0f0303030f0f1b1b03031b1b030317031b030f030f031f87c8c7e1f331b1b1b1b331b0f0f0f0f031b1b032347c2c7d230b1b1b1b1b0f0f0f0f031b1b031f33331f1b1b1b1b1b006c8b0f03c0306c1f07c1f07c03030f0f17031b030f030f031b33331b0f0f0f0f032727031b1b0f0f0f0f0327270333331b1b0f0f0f0f032727033333030303030f0f0f0f030303030f0f0f0f03030303131313130f0f0f0f030303031313131303030303030303030303030303030303030303030303030f0f170f0f0303030f038b0f83c3c3e0f0f0f0f0f032727030f43c2c3d0f0b0f0f0f0f032727030f230f03c3c3c0f0f0f0f032727030f0f03030f0f030f030f030f0303030303030303030303030317170f031717a85c5c0c3c0c5eaaaa83eaaaa2749c2c9d270b170f0f1703272703aa271f2709c7c9c170f0f1703272703aa131303031313030313030f0303030303aa1303130313031303 23 8388607 10 1023
def nh_70 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_70_18 (Nat.sub p 576)) (hc_70_17 (Nat.sub p 544)) (Nat.blt p 576)) (hc_70_16 (Nat.sub p 512)) (Nat.blt p 544)) (Bool.rec (hc_70_15 (Nat.sub p 480)) (hc_70_14 (Nat.sub p 448)) (Nat.blt p 480)) (Nat.blt p 512)) (Bool.rec (Bool.rec (Bool.rec (hc_70_13 (Nat.sub p 416)) (hc_70_12 (Nat.sub p 384)) (Nat.blt p 416)) (hc_70_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (hc_70_10 (Nat.sub p 320)) (hc_70_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Nat.blt p 448)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_70_8 (Nat.sub p 256)) (hc_70_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_70_6 (Nat.sub p 192)) (Nat.blt p 224)) (Bool.rec (hc_70_5 (Nat.sub p 160)) (hc_70_4 (Nat.sub p 128)) (Nat.blt p 160)) (Nat.blt p 192)) (Bool.rec (Bool.rec (hc_70_3 (Nat.sub p 96)) (hc_70_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (hc_70_1 (Nat.sub p 32)) (hc_70_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 128)) (Nat.blt p 288)
def f_70 : Nat → Nat × Nat := unpackForestF 0x18bf20b6190436c8656e432af2185b90c2bc821b2410c000c578fe2a802d7e3d06a00b5b005abc72d5a3906a00b538dc1a802d2c0168f194558c9acc64154014bf17a4e8bc1280296e2c6c31606d0052bc5095a2849d1402500529c4a93a2504a00a4b889a8c441740148f0e56f87dbe43959e1c6ad0e0350051fc2f5be190f90bd6785d2b0028ee0fadf0993f84c99c231c2110f907d6783e2d0028de01adf0627c806b3c0295a010510082580a2fc0c582028af0115b808a9c0404e0104800a337e22abf0d65fdacafc23b7eab2bf51a1f846efc055004afbec511ec69ef634b7ccae3d8d1def268f78387bc1a3d8d0dec29cf6015004adbccd85e6476f44707991bbcc1b4012aef2144751a7ba8d2de12b8ea3477749a3ba0e1dd068ea34375d1fbae8edd746eec02475d19ba8559d429cea015004a9ba4511c969ee4b4b73cae392d1dcc268e6034725a1b92539c902a0094b70da8b868edc58c0e1a3770c2e80251db6adee037c6dab3b6cd59bd488db26b6e933374911b64c6dc2446d92db6c0d40127ed4d6f6cc3e35359db1acad4b6f6a5b5b52d9dad6ccd4b636a5adb52d5da92ac0093b64eb7b4a8fda5466d1c7068c3e32759d938b4cfd6567e343269bd9d4b8c9a6b66e3832699d984cccc25c64d31b2c971934b6ca46064d2b8024dd78adec817c5e2b3b1c4d1786d6c5b6662c9a2f0d8d89268bc35b5e0ab30a96d854a6bc0185e00aaf317d810c0bcc575e52dafc959794a6bca4b5e42daf214d79046bc01400499ad15bd734f8b987c5cc382d159d70acab82645a237adc9f1688ceb626c5a22bad09596849cb402500497ab15bd632f8b187c58c382b159d60acab016456237abc5f1588ceae16c5622bab05595829cac01500495a8f5bd536e0a987c54c3828f59d50acaa836851e37a9cdc1478cea636051e2ba8ed6949048a3b4251c1e80249d24adea117c5083e2841c124ace9fd654fcb22491bd3d2889246b4ecbe24919d388cc9c14449231a6c511248b69a16c4922ba5317d2f4c09786c4bc3025315d2d8aa94b5f4ad30252d5d2968e92234490ab24d1992429c9201500491a27155136b28fd6547d322264bd1caca8e16444c95a33595196d089927452b2a2d155144688a16444c9180217d1106883a3f43c1220e8ed0d09883a3742c1e210d11082488402441d1980216cfc6c28227c3f097a045f0fc256803703f0939fa8d0fd2f87e1230042b9f24d0f906877a3f3d8921ec090ef4767a04c3bd1b9e0d10f1468780243bd1980214ce947e74a3b3a51b9d4d10e94660084b38c979c64ace324e7223438c9180211cd3ade69d6734dad1a69acdd4cc69a6334d2d9a65acd92cc6996334cad9ac630d4cee6a16634c918020fcc56de62b6b315b398ad8cc54de62a6b3153398a98cc547e62a3b3151b98cd10c54660083b22eb79828ccc12666047022eb3917168bcaca5e46822d379749708b4d65c47022d3396a998b54b845a632cd2e11696cb18c045a572bab295d1a08b2de5615c22cb59551c08b2ce5396629cae11658ca52b84595b28e3011655c9fad44fa6627d2e1164bc9bad44d96626cae1164ac98ad44c35022c9392b6009531846677232b51231689148046234230b311cdc08dace4615c22c918020dc890684036b21c1a100d8c850484026b20c1210098c8104840233004198d95bc7d4f8365671b12b0d893878aca3c2641b0b78ec4d06c2d63a27c1b0b38e259871268361631bc9a0d856c6d4d836157004178d4190614de34024185358ca5f0650f830a67188920c4090614c60082b12eb78bcdc04bace25b5a12da10b3594596d02596f15ca60965ac556e025967148b30a45304b2c62814c12cad89cd804b2ae2584a12c2300209c490c820a6f1189208c090414d62207c10533884090414c6008230b6b787c5f02dace1dd650ecb205adbc3926816b6b0dcbe05ad9c346cc1a1340b5b18644d02d6b61816c0b5ab85a5582d29c0081f0ac32044dbc290681136b098be04c1f0226ce1193408c1a044d8c010360656f07d3801959c1caca0e268031b78348e00c6d60c270031b382ad98154700636304d1c018d6c114c0063570312d0189080c094060460040b814190026de0393401c1a004dac050f80136700c1a004d8c010260003f 10 11
def ch_70 : Nat → Bool := dagCheckNodeV5 fullMask g_70 ep_70 6 63 bds_70 586 (dagTraceF fullMask rootStock 11 f_70) cur_70 nh_70
set_option maxHeartbeats 0 in
theorem rc_70 : dagCheckRootsV5 fullMask g_70 ep_70 6 63 586 bds_70 (dagTraceF fullMask rootStock 11 f_70) (cur_70 0) (nh_70 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_0 : treeBlockF 0 32 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_1 : treeBlockF 32 64 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_2 : treeBlockF 64 96 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_3 : treeBlockF 96 128 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_4 : treeBlockF 128 160 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_5 : treeBlockF 160 192 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_6 : treeBlockF 192 224 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_7 : treeBlockF 224 256 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_8 : treeBlockF 256 288 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_9 : treeBlockF 288 320 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_10 : treeBlockF 320 352 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_11 : treeBlockF 352 384 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_12 : treeBlockF 384 416 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_13 : treeBlockF 416 448 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_14 : treeBlockF 448 480 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_15 : treeBlockF 480 512 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_16 : treeBlockF 512 544 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_17 : treeBlockF 544 576 ch_70 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_18 : treeBlockF 576 586 ch_70 = true := by decide +kernel
theorem nj_70_1 : ∀ i, 0 ≤ i → i < 64 → ch_70 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_70_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_70_1 h1 h2)
theorem nj_70_2 : ∀ i, 0 ≤ i → i < 96 → ch_70 i = true := block_join nj_70_1 (fun _ h1 h2 => treeBlockF_at nb_70_2 h1 h2)
theorem nj_70_3 : ∀ i, 0 ≤ i → i < 128 → ch_70 i = true := block_join nj_70_2 (fun _ h1 h2 => treeBlockF_at nb_70_3 h1 h2)
theorem nj_70_4 : ∀ i, 0 ≤ i → i < 160 → ch_70 i = true := block_join nj_70_3 (fun _ h1 h2 => treeBlockF_at nb_70_4 h1 h2)
theorem nj_70_5 : ∀ i, 0 ≤ i → i < 192 → ch_70 i = true := block_join nj_70_4 (fun _ h1 h2 => treeBlockF_at nb_70_5 h1 h2)
theorem nj_70_6 : ∀ i, 0 ≤ i → i < 224 → ch_70 i = true := block_join nj_70_5 (fun _ h1 h2 => treeBlockF_at nb_70_6 h1 h2)
theorem nj_70_7 : ∀ i, 0 ≤ i → i < 256 → ch_70 i = true := block_join nj_70_6 (fun _ h1 h2 => treeBlockF_at nb_70_7 h1 h2)
theorem nj_70_8 : ∀ i, 0 ≤ i → i < 288 → ch_70 i = true := block_join nj_70_7 (fun _ h1 h2 => treeBlockF_at nb_70_8 h1 h2)
theorem nj_70_9 : ∀ i, 0 ≤ i → i < 320 → ch_70 i = true := block_join nj_70_8 (fun _ h1 h2 => treeBlockF_at nb_70_9 h1 h2)
theorem nj_70_10 : ∀ i, 0 ≤ i → i < 352 → ch_70 i = true := block_join nj_70_9 (fun _ h1 h2 => treeBlockF_at nb_70_10 h1 h2)
theorem nj_70_11 : ∀ i, 0 ≤ i → i < 384 → ch_70 i = true := block_join nj_70_10 (fun _ h1 h2 => treeBlockF_at nb_70_11 h1 h2)
theorem nj_70_12 : ∀ i, 0 ≤ i → i < 416 → ch_70 i = true := block_join nj_70_11 (fun _ h1 h2 => treeBlockF_at nb_70_12 h1 h2)
theorem nj_70_13 : ∀ i, 0 ≤ i → i < 448 → ch_70 i = true := block_join nj_70_12 (fun _ h1 h2 => treeBlockF_at nb_70_13 h1 h2)
theorem nj_70_14 : ∀ i, 0 ≤ i → i < 480 → ch_70 i = true := block_join nj_70_13 (fun _ h1 h2 => treeBlockF_at nb_70_14 h1 h2)
theorem nj_70_15 : ∀ i, 0 ≤ i → i < 512 → ch_70 i = true := block_join nj_70_14 (fun _ h1 h2 => treeBlockF_at nb_70_15 h1 h2)
theorem nj_70_16 : ∀ i, 0 ≤ i → i < 544 → ch_70 i = true := block_join nj_70_15 (fun _ h1 h2 => treeBlockF_at nb_70_16 h1 h2)
theorem nj_70_17 : ∀ i, 0 ≤ i → i < 576 → ch_70 i = true := block_join nj_70_16 (fun _ h1 h2 => treeBlockF_at nb_70_17 h1 h2)
theorem nj_70_18 : ∀ i, 0 ≤ i → i < 586 → ch_70 i = true := block_join nj_70_17 (fun _ h1 h2 => treeBlockF_at nb_70_18 h1 h2)
theorem nc_70 : ∀ i, 0 ≤ i → i < 586 → ch_70 i = true := nj_70_18
theorem lb_70 : LowerBin fullMask rootStock g_70 12 :=
  lowerDagV5 (kn_cons lb_69 (kn_cons lb_66 (kn_cons lb_63 (kn_cons lb_26 (kn_cons lb_68 (kn_cons lb_62 (kn_cons lb_64 (kn_cons lb_25 (kn_cons lb_65 (kn_cons lb_42 (kn_cons lb_36 (kn_cons lb_67 (kn_cons lb_60 (kn_cons lb_53 (kn_cons lb_54 (kn_cons lb_47 (kn_cons lb_12 (kn_cons lb_49 (kn_cons lb_8 (kn_cons lb_61 (kn_cons lb_45 (kn_cons lb_15 (kn_cons lb_6 (kn_cons lb_46 (kn_cons lb_43 (kn_cons lb_11 (kn_cons lb_4 (kn_cons lb_34 (kn_cons lb_44 (kn_cons lb_40 (kn_cons lb_30 (kn_cons lb_16 (kn_cons lb_28 (kn_cons lb_27 (kn_cons lb_33 (kn_cons lb_38 (kn_cons lb_58 (kn_nil)))))))))))))))))))))))))))))))))))))) rc_70 nc_70 (by decide +kernel)

def wg : List Gate := [⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [2, 11]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [8, 13]⟩, ⟨GateOp.and, [12, 14]⟩, ⟨GateOp.or, [10, 16]⟩, ⟨GateOp.and, [15, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4008241312 * 2 ^ 32 + 3903367296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4008241312 * 2 ^ 32 + 3903367296)) (13 - 1) := by
  rw [show canon fullMask (4008241312 * 2 ^ 32 + 3903367296) = g_70 by decide]
  exact lb_70

end PEqualNP.Outside.L_meta_48160

theorem PEqualNP.Outside.L_meta_48160 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241312 * 2 ^ 32 + 3903367296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241312 * 2 ^ 32 + 3903367296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_48160.table2_from_lowerBin (4008241312 * 2 ^ 32 + 3903367296) 13 PEqualNP.Outside.L_meta_48160.root_lb PEqualNP.Outside.L_meta_48160.wg 18 rfl PEqualNP.Outside.L_meta_48160.wfits PEqualNP.Outside.L_meta_48160.weval
