import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39155

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4277071594 * 2 ^ 32 + 4207462592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x000848455838e3c0#64 ++ 0x2000848455838e3c#64 ++ 0xc058d8cfd8f9e7cf#64 ++ 0xdc058d8cfd8f9e7c#64 : BitVec 256),
   (0x0083031320834d52#64 ++ 0x40083031320834d5#64 ++ 0xf1a72733208fffff#64 ++ 0xbf1a72733208ffff#64 : BitVec 256),
   (0x0638382c1b0c30a4#64 ++ 0x80638382c1b0c30a#64 ++ 0x6e38383c3f0e38fd#64 ++ 0x76e38383c3f0e38f#64 : BitVec 256),
   (0x2bc03dc02dd03e07#64 ++ 0x02bc03dc02dd03e0#64 ++ 0xafc03fc03ff03f0c#64 ++ 0xfafc03fc03ff03f0#64 : BitVec 256),
   (0x1dfdc00036ef8008#64 ++ 0x01dfdc00036ef800#64 ++ 0x3fffc0003fffc00b#64 ++ 0xf3fffc0003fffc00#64 : BitVec 256),
   (0x4f76b6ba80000000#64 ++ 0x04f76b6ba8000000#64 ++ 0xdfffffffc0000007#64 ++ 0xfdfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [10, 8]⟩, ⟨.and, [11, 5]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0xc058d8cfd8f9e7cf 0xdc058d8cfd8f9e7c

def z1 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xf1a72733208fffff 0xbf1a72733208ffff

def z2 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x6e38383c3f0e38fd 0x76e38383c3f0e38f

def z3 : W := mkw 0x143fc213122fc158 0x4143fc213122fc15 0x503fc033000fc0f3 0x0503fc033000fc0f

def z4 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x3fffc0003fffc00b 0xf3fffc0003fffc00

def z5 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xafc03fc03ff03f0c 0xfafc03fc03ff03f0

def z6 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0xdfffffffc0000007 0xfdfffffffc000000

def z7 : W := mkw 0x1dfdc10036ef8c0a 0x01dfdc10036ef8c0 0xbfffe7003fffff0f 0xfbfffe7003fffff0

def z8 : W := mkw 0x09c1000024c30000 0x009c1000024c3000 0x3fe700003fffc00b 0xf3fe700003fffc00

def z9 : W := mkw 0x0002021200000000 0x0000202120000000 0xd1a7273300000007 0xbd1a727330000000

def z10 : W := mkw 0x4f74b4a880000000 0x04f74b4a88000000 0x0e58d8ccc0000000 0x40e58d8ccc000000

def z11 : W := mkw 0x3f7cfcc01f7cb20d 0x03f7cfcc01f7cb20 0x0e58d8c01f700000 0x40e58d8c01f70000

def z12 : W := mkw 0x7ffffffabfffbe0f 0x07ffffffabfffbe0 0xffffffffffffff0f 0xfffffffffffffff0

def z13 : W := mkw 0x208009402dd03e07 0x0208009402dd03e0 0x200000003ff03f08 0x0200000003ff03f0

def z14 : W := mkw 0x4436823a80000000 0x04436823a8000000 0x503fc03fc0000003 0x0503fc03fc000000

def z15 : W := mkw 0x0200380009003004 0x0020038000900300 0x6e2038303f0e38fd 0x76e2038303f0e38f

def z16 : W := mkw 0x02833b3f29837df6 0xc02833b3f29837df 0xf1a73f3f208fffff 0xbf1a73f3f208ffff

def z17 : W := mkw 0x2bc33fd32dd37f57 0x42bc33fd32dd37f5 0xffe73ff33fffffff 0xfffe73ff33ffffff

def z18 : W := mkw 0x0d74800000000000 0x00d7480000000000 0x1fffc00000000003 0xf1fffc0000000000

def z19 : W := mkw 0x1089400036ef8008 0x01089400036ef800 0x200000003fffc008 0x0200000003fffc00

def z20 : W := mkw 0x0438082c1a0c20a0 0x80438082c1a0c20a 0x4038183c180e20fd 0x54038183c180e20f

def z21 : W := mkw 0x0638786d5b3cf3e4 0xa0638786d5b3cf3e 0x6e38383c3ffffffd 0x76e38383c3ffffff

def z22 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0x9fdfdfcfc0000002 0xc9fdfdfcfc000000

def z23 : W := mkw 0x0080010020800c02 0x00080010020800c0 0xa180270020803f0c 0xba180270020803f0

def z24 : W := mkw 0x2b403cc00d503205 0x02b403cc00d50320 0x0e4018c01f700000 0x40e4018c01f70000

def z25 : W := mkw 0x000040414030c340 0x2000040414030c34 0xc058d8cfc0f1c707 0xdc058d8cfc0f1c70

def z26 : W := mkw 0x000808041b0c30a4 0x8000808041b0c30a 0x200000003f0e38f8 0x0200000003f0e38f

def z27 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0xc018d8cfc009e7c7 0x0c018d8cfc009e7c

def z28 : W := mkw 0x308949403fffbe0f 0x0308949403fffbe0 0x200000003fffff08 0x0200000003fffff0

def z29 : W := mkw 0x0000000000000000 0x0000000000000000 0x60202030200e38fd 0x360202030200e38f

def z30 : W := mkw 0x0638786d5b3cf3e4 0xa0638786d5b3cf3e 0xee78f8ffffffffff 0xfee78f8fffffffff

def z31 : W := mkw 0x0200384009103204 0x0020038400910320 0xae4038c03ff03f0c 0xfae4038c03ff03f0

def z32 : W := mkw 0x0083031320834d52 0x40083031320834d5 0x918707030081c702 0x8918707030081c70

def z33 : W := mkw 0x3ffcfdc03ffcbe0f 0x03ffcfdc03ffcbe0 0xafd8ffc03ff03f0c 0xfafd8ffc03ff03f0

def z34 : W := mkw 0x0003021300034150 0x4000302130003415 0x50270033000fc0f3 0x050270033000fc0f

def z35 : W := mkw 0x09c0000024c00000 0x009c0000024c0000 0x2fc000003ff00008 0xf2fc000003ff0000

def z36 : W := mkw 0x4946869280000000 0x0494686928000000 0x91c7c7c3c0000002 0x891c7c7c3c000000

def z37 : W := mkw 0x463eba3e9b0c30a4 0x8463eba3e9b0c30a 0x7e3ff83fff0e38ff 0x77e3ff83fff0e38f

def z38 : W := mkw 0x2080010025c01c07 0x02080010025c01c0 0x2000000027001800 0x0200000002700180

def z39 : W := mkw 0x1dffc31336efcd5a 0x41dffc31336efcd5 0xffffe7333fffffff 0xfffffe7333ffffff

def z40 : W := mkw 0x1ffdf82c3fefb0ac 0x81ffdf82c3fefb0a 0x7ffff83c3ffff8ff 0xf7ffff83c3ffff8f

def z41 : W := mkw 0x0630302800000000 0x0063030280000000 0x0e20203000000000 0x20e2020300000000

def z42 : W := mkw 0x0200382c090030a4 0x80200382c090030a 0x4000383c000038f4 0x04000383c000038f

def z43 : W := mkw 0x2b403dc009103e07 0x02b403dc009103e0 0x8fc03fc000003f04 0xf8fc03fc000003f0

def z44 : W := mkw 0x0b40348000000000 0x00b4034800000000 0x8fc03fc000000004 0xf8fc03fc00000000

def z45 : W := mkw 0x19c5c00024e38008 0x019c5c00024e3800 0x11c7c00000f1c002 0x811c7c00000f1c00

def z46 : W := mkw 0x0638302c130c10a4 0x80638302c130c10a 0x6e38203c270e18f1 0x26e38203c270e18f

def z47 : W := mkw 0x0200380009003004 0x0020038000900300 0x0e0018001f000000 0x40e0018001f00000

def z48 : W := mkw 0x0bc0358020800c02 0x00bc0358020800c0 0xafc03fc020803f0c 0xfafc03fc020803f0

def z49 : W := mkw 0x020838041b0c30a4 0x8020838041b0c30a 0x2e0038003f0e38fc 0x72e0038003f0e38f

def z50 : W := mkw 0x0081000020830000 0x0008100002083000 0x31a7000020060000 0x231a700002006000

def z51 : W := mkw 0x000840055028c1c0 0x2000840055028c1c 0x4018c00fc009c0c3 0x04018c00fc009c0c

def z52 : W := mkw 0x420236ba80000000 0x0420236ba8000000 0xc0003fffc0000004 0x0c0003fffc000000

def z53 : W := mkw 0x4f7ebebe9b0c30a4 0x84f7ebebe9b0c30a 0xdfffffffdf000007 0xfdfffffffdf00000

def z54 : W := mkw 0x6ffebffebfdc3ea7 0x86ffebffebfdc3ea 0xfffffffffffe3fff 0xffffffffffffe3ff

def z55 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xaf803fc027003f04 0x2af803fc027003f0

def z56 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0x8fc01fc01ff00700 0xc8fc01fc01ff0070

def z57 : W := mkw 0x000a4a575838e3c0 0x2000a4a575838e3c 0xd1ffffffd8f9e7cf 0xfd1ffffffd8f9e7c

def z58 : W := mkw 0x29c005c024d00e03 0x029c005c024d00e0 0xafc007c03ff00708 0xfafc007c03ff0070

def z59 : W := mkw 0x000848445838a280 0x2000848445838a28 0x0000000018700000 0x0000000001870000

def z60 : W := mkw 0x3ffdf58037ef9c0f 0x03ffdf58037ef9c0 0x3fffe7003fffd80b 0xf3fffe7003fffd80

def z61 : W := mkw 0x0630302803041024 0x8063030280304102 0x2e20203027061830 0x22e2020302706183

def z62 : W := mkw 0x000840055028c1c0 0x2000840055028c1c 0x000000000009c0c0 0x0000000000009c0c

def z63 : W := mkw 0x42023effc81063c0 0x242023effc81063c 0xc0003fffc00027c4 0x0c0003fffc00027c

def z64 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0x0000000018f9e7c8 0x00000000018f9e7c

def z65 : W := mkw 0x0002021300004150 0x4000202130000415 0x40000033000000f0 0x040000033000000f

def z66 : W := mkw 0x1d7cc000166c8008 0x01d7cc000166c800 0x0e58c0001f700000 0x40e58c0001f70000

def z67 : W := mkw 0x2f783cec1f5c32a5 0x82f783cec1f5c32a 0x6e7838fc3f7e38fd 0x76e7838fc3f7e38f

def z68 : W := mkw 0x000848445838a280 0x2000848445838a28 0xc058d8cfd8700007 0xdc058d8cfd870000

def z69 : W := mkw 0x0bc038002dc03004 0x00bc038002dc0300 0x2fc038003ff0380c 0xf2fc038003ff0380

def z70 : W := mkw 0x0438486d5a3ce3e0 0xa0438486d5a3ce3e 0xc078d8ffd8ffe7ff 0xdc078d8ffd8ffe7f

def z71 : W := mkw 0x5ffff6bab6ef8008 0x05ffff6bab6ef800 0xffffffffffffc00f 0xfffffffffffffc00

def z72 : W := mkw 0x0082031220800c02 0x00082031220800c0 0xf1a7273320803f0f 0xbf1a7273320803f0

def z73 : W := mkw 0x0000000000000000 0x0000000000000000 0xc058d8cfc0000007 0xdc058d8cfc000000

def z74 : W := mkw 0x000040414030c340 0x2000040414030c34 0x8040c0c3c0f1c702 0x88040c0c3c0f1c70

def z75 : W := mkw 0x4946869280000000 0x0494686928000000 0xd1dfdfcfc0000007 0xdd1dfdfcfc000000

def z76 : W := mkw 0x0001000000030000 0x0000100000003000 0x10270000000fc003 0x010270000000fc00

def z77 : W := mkw 0x2b403dc00d503e07 0x02b403dc00d503e0 0x8e403fc01f703f04 0x48e403fc01f703f0

def z78 : W := mkw 0x1ffdf8003fefb00c 0x01ffdf8003fefb00 0x3ffff8003ffff80f 0xf3ffff8003ffff80

def z79 : W := mkw 0x3ffdfdc03fffbe0f 0x03ffdfdc03fffbe0 0xbfffffc03fffff0f 0xfbfffffc03fffff0

def z80 : W := mkw 0x000840055028c1c0 0x2000840055028c1c 0xc058d8cfc009c0c7 0xdc058d8cfc009c0c

def z81 : W := mkw 0x2bc87dc03df8be07 0x02bc87dc03df8be0 0xafd8ffc03ff9ff0f 0xfafd8ffc03ff9ff0

def z82 : W := mkw 0x2bc0358025c01c07 0x02bc0358025c01c0 0x2f80270027001800 0x22f8027002700180

def z83 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xf1ffffffe08fffff 0xff1ffffffe08ffff

def z84 : W := mkw 0x2f783cec1f5c32a5 0x82f783cec1f5c32a 0x0e5818cc1f700000 0x40e5818cc1f70000

def z85 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0xc00018cfd8f9e7cc 0x0c00018cfd8f9e7c

def z86 : W := mkw 0x04380000120c0000 0x004380000120c000 0x6e3820303f0e38fd 0x76e3820303f0e38f

def z87 : W := mkw 0x4f7cfcedd838e3c0 0x24f7cfcedd838e3c 0xce58d8cfd8f9e7cf 0xdce58d8cfd8f9e7c

def z88 : W := mkw 0x000040014020c140 0x2000040014020c14 0x0000c003c001c002 0x00000c003c001c00

def z89 : W := mkw 0x4f74b4a880000000 0x04f74b4a88000000 0x1fffd8ccc0000003 0xf1fffd8ccc000000

def z90 : W := mkw 0x2bc87dc57df8ffc7 0x22bc87dc57df8ffc 0xefd8ffcffff9ffcf 0xfefd8ffcffff9ffc

def z91 : W := mkw 0x6ff6bffaadd03e07 0x06ff6bffaadd03e0 0xfffffffffff03f0f 0xffffffffffff03f0

def z92 : W := mkw 0x2ff83dec3fdc3ea7 0x82ff83dec3fdc3ea 0xafd83fcc3ff03f0c 0xfafd83fcc3ff03f0

def z93 : W := mkw 0x29c84dc57cf8efc3 0x229c84dc57cf8efc 0xc1d8dfcfd8f9e7cf 0xdc1d8dfcfd8f9e7c

def z94 : W := mkw 0x0089494578bbefd2 0x60089494578bbefd 0x2000000038fffff8 0x02000000038fffff

def z95 : W := mkw 0x008b4b5778bbefd2 0x6008b4b5778bbefd 0xf1fffffff8ffffff 0xff1fffffff8fffff

def z96 : W := mkw 0x6ffefffffdf8ffc7 0x26ffefffffdf8ffc 0xfffffffffff9ffcf 0xffffffffffff9ffc

def z97 : W := mkw 0x29c005c024d00e03 0x029c005c024d00e0 0xa1c027c020f03f0c 0xba1c027c020f03f0

def z98 : W := mkw 0x3dfdc5c036ff8e0b 0x03dfdc5c036ff8e0 0xbfffc7c03fffc70b 0xfbfffc7c03fffc70

def z99 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xd18707030089e7cf 0x9d18707030089e7c

def z100 : W := mkw 0x2ff03de82fd43e27 0x82ff03de82fd43e2 0xafe03ff03ff63f3c 0xfafe03ff03ff63f3

def z101 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x1fdfc0001ff1c002 0xc1fdfc0001ff1c00

def z102 : W := mkw 0x29c005c024d00e03 0x029c005c024d00e0 0x81c007c000f00700 0x881c007c000f0070

def z103 : W := mkw 0x0089484578bbe3c0 0x20089484578bbe3c 0xf1ffd8cff8ffe7cf 0xff1ffd8cff8ffe7c

def z104 : W := mkw 0x4f7ebebe9b0c30a4 0x84f7ebebe9b0c30a 0xffffffffff0e38ff 0xfffffffffff0e38f

def z105 : W := mkw 0x0200386d491073e4 0xa0200386d491073e 0xc00038ffc0003ff4 0x0c00038ffc0003ff

def z106 : W := mkw 0x0d76821200000000 0x00d7682120000000 0xdfffe73300000007 0xfdfffe7330000000

def z107 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0x4018180c18f9e7cd 0x54018180c18f9e7c

def z108 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0x81c03fc000f03f04 0x881c03fc000f03f0

def z109 : W := mkw 0x000848445838a280 0x2000848445838a28 0x0058d8ccd8700000 0x40058d8ccd870000

def z110 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0x1fa7273000000000 0x21fa727300000000

def z111 : W := mkw 0x2ff83dec3fdc3ea7 0x82ff83dec3fdc3ea 0xeff83ffc3ffe3ffd 0xfeff83ffc3ffe3ff

def z112 : W := mkw 0x000848445838a280 0x2000848445838a28 0x4058d8ccd87820cd 0x54058d8ccd87820c

def z113 : W := mkw 0x000808041b0c30a4 0x8000808041b0c30a 0x000000001f000000 0x0000000001f00000

def z114 : W := mkw 0x0df8000036cc0000 0x00df8000036cc000 0x2ff800003ffe0009 0xf2ff800003ffe000

def z115 : W := mkw 0x16b9782c3fefb0ac 0x816b9782c3fefb0a 0x6e38383c3ffff8fd 0x76e38383c3ffff8f

def z116 : W := mkw 0x1dfdc8403effa208 0x01dfdc8403effa20 0xbfffd8c03fffe70f 0xfbfffd8c03fffe70

def z117 : W := mkw 0x4436823a80000000 0x04436823a8000000 0x1027003000000000 0x0102700300000000

def z118 : W := mkw 0x06bb3b3f3b8f7df6 0xc06bb3b3f3b8f7df 0xffbf3f3f3f8fffff 0xfffbf3f3f3f8ffff

def z119 : W := mkw 0x22023fd309107f57 0x422023fd309107f5 0xc0003ff300003ff4 0x0c0003ff300003ff

def z120 : W := mkw 0x1dffcb577effefda 0x61dffcb577effefd 0xffffffffffffffff 0xffffffffffffffff

def z121 : W := mkw 0x1081000026c70008 0x01081000026c7000 0x2000000027060000 0x0200000002706000

def z122 : W := mkw 0x2bc0358025c01c07 0x02bc0358025c01c0 0xafc03fc027001804 0xfafc03fc02700180

def z123 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x4e18383c1f0038f4 0x44e18383c1f0038f

def z124 : W := mkw 0x0630302803041024 0x8063030280304102 0x6e202030270e38fd 0x36e202030270e38f

def z125 : W := mkw 0x1dfdc8447effa288 0x21dfdc8447effa28 0x3fffd8ccffffc00b 0xf3fffd8ccffffc00

def z126 : W := mkw 0x19c7c31324e3cd5a 0x419c7c31324e3cd5 0x91c7c70300f1c702 0x891c7c70300f1c70

def z127 : W := mkw 0x0bc3379320834d52 0x40bc3379320834d5 0xffe73ff3208fffff 0xfffe73ff3208ffff

def z128 : W := mkw 0x0003021200030010 0x4000302120003001 0x1027003000060030 0x0102700300006003

def z129 : W := mkw 0x19c5800024c30008 0x019c5800024c3000 0x1187000000000000 0x0118700000000000

def z130 : W := mkw 0x1dfdc04176ffc348 0x21dfdc04176ffc34 0xbfffc0c3ffffc70b 0xfbfffc0c3ffffc70

def z131 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0xe078f8fff8ffffff 0xfe078f8fff8fffff

def z132 : W := mkw 0x420237bb80004d52 0x4420237bb80004d5 0xc0003fffc0003ff4 0x0c0003fffc0003ff

def z133 : W := mkw 0x0008080418082080 0x0000808041808208 0x4018180c180820cd 0x54018180c180820c

def z134 : W := mkw 0x1ffdf86d7ffff3ec 0xa1ffdf86d7ffff3e 0xfffff8ffffffffff 0xffffff8fffffffff

def z135 : W := mkw 0x108948043fefb0ac 0x8108948043fefb0a 0x200000003ffff8f8 0x0200000003ffff8f

def z136 : W := mkw 0x1ffdf02837ef902c 0x81ffdf02837ef902 0x3fffe0303fffd83b 0xf3fffe0303fffd83

def z137 : W := mkw 0x04b90000328f0000 0x004b90000328f000 0x3fbf00003f8fc00b 0xf3fbf00003f8fc00

def z138 : W := mkw 0x1d7cc000166c8008 0x01d7cc000166c800 0x2e78c0003f7e0009 0x72e78c0003f7e000

def z139 : W := mkw 0x0d74800000000000 0x00d7480000000000 0x1fa7000000000000 0x21fa700000000000

def z140 : W := mkw 0x0200380009003004 0x0020038000900300 0x2e0038003f00380c 0x72e0038003f00380

def z141 : W := mkw 0x09c3031324c34d52 0x409c3031324c34d5 0xffe727333fffffff 0xfffe727333ffffff

def z142 : W := mkw 0x1df5800026c70008 0x01df5800026c7000 0x3fa7000027060000 0x23fa700002706000

def z143 : W := mkw 0x1df5800026c70008 0x01df5800026c7000 0x3fffc00027060003 0xf3fffc0002706000

def z144 : W := mkw 0x0089494578bbefd2 0x60089494578bbefd 0xe058d8cff8ffffff 0xde058d8cff8fffff

def z145 : W := mkw 0x108b431336efcd5a 0x4108b431336efcd5 0xf1a727333fffffff 0xbf1a727333ffffff

def z146 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0x1ffffffcc0000000 0x61ffffffcc000000

def z147 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x0e18180c1f000000 0x40e18180c1f00000

def z148 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0x2e4018c03ff03f08 0x42e4018c03ff03f0

def z149 : W := mkw 0x4ff6b6baa4c00000 0x04ff6b6baa4c0000 0xfffffffffff0000f 0xffffffffffff0000

def z150 : W := mkw 0x0630302800000000 0x0063030280000000 0x4e38383c00000005 0x74e38383c0000000

def z151 : W := mkw 0x0000000000000000 0x0000000000000000 0x800000000080270c 0x9800000000080270

def z152 : W := mkw 0x04384000122c8000 0x004384000122c800 0x2e78c0003fffc00b 0xf2e78c0003fffc00

def z153 : W := mkw 0x000040414030c340 0x2000040414030c34 0x0000000000f1c700 0x00000000000f1c70

def z154 : W := mkw 0x0002031300004d52 0x40002031300004d5 0xc00027330089ffff 0x9c00027330089fff

def z155 : W := mkw 0x0003021300034150 0x4000302130003415 0x100700030001c002 0x0100700030001c00

def z156 : W := mkw 0x0b40348000000000 0x00b4034800000000 0x0e4018c000000000 0x40e4018c00000000

def z157 : W := mkw 0x443e823e920c00a0 0x8443e823e920c00a 0x503fc03fc00e00f3 0x0503fc03fc00e00f

def z158 : W := mkw 0x3ff5b58027c71c0f 0x03ff5b58027c71c0 0x3fa7270027061800 0x23fa727002706180

def z159 : W := mkw 0x4f7ebebe98082080 0x04f7ebebe9808208 0xdfffffffd80820cf 0xfdfffffffd80820c

def z160 : W := mkw 0x4f7efeffd838e3c0 0x24f7efeffd838e3c 0xdfffffffd8f9e7cf 0xfdfffffffd8f9e7c

def z161 : W := mkw 0x4ff6b7baa0800c02 0x04ff6b7baa0800c0 0xffffffffe0803f0f 0xfffffffffe0803f0

def z162 : W := mkw 0x0b403c8009003004 0x00b403c800900300 0xafc03fc03f00380c 0xfafc03fc03f00380

def z163 : W := mkw 0x0000404040308200 0x2000040404030820 0x0040c0c0c0700000 0x00040c0c0c070000

def z164 : W := mkw 0x4f76f6fbc030c340 0x24f76f6fbc030c34 0xdfffffffc0f1c707 0xfdfffffffc0f1c70

def z165 : W := mkw 0x5ff7b6baa6c70008 0x05ff7b6baa6c7000 0xffffffffe7060007 0xfffffffffe706000

def z166 : W := mkw 0x1ffdf82c3fefb0ac 0x81ffdf82c3fefb0a 0x3fffd80c3fffc00b 0xf3fffd80c3fffc00

def z167 : W := mkw 0x0630302803041024 0x8063030280304102 0x0e00000007000000 0x00e0000000700000

def z168 : W := mkw 0x2ff83dac3fcc3ca7 0x82ff83dac3fcc3ca 0x6fb83f3c3f0e38fd 0x76fb83f3c3f0e38f

def z169 : W := mkw 0x0081010120834d52 0x40081010120834d5 0xe0000003208fffff 0x9e0000003208ffff

def z170 : W := mkw 0x2bc23fd22dd03e07 0x02bc23fd22dd03e0 0xffe73ff33ff03f0f 0xfffe73ff33ff03f0

def z171 : W := mkw 0x0000084008102200 0x0000008400810220 0x804018c018f0270c 0xd804018c018f0270

def z172 : W := mkw 0x0438002c120c00a0 0x80438002c120c00a 0x6038203c200e38fd 0x36038203c200e38f

def z173 : W := mkw 0x0430000000000000 0x0043000000000000 0x0e38000000000001 0x70e3800000000000

def z174 : W := mkw 0x0430002800000000 0x0043000280000000 0x4038003c00000001 0x04038003c0000000

def z175 : W := mkw 0x6bc6bfd2add03e07 0x06bc6bfd2add03e0 0xbfc7ffc3fff03f0e 0xfbfc7ffc3fff03f0

def z176 : W := mkw 0x1d7cc8445e7ca288 0x21d7cc8445e7ca28 0x0e58d8ccdf700000 0x40e58d8ccdf70000

def z177 : W := mkw 0x5ffffebebfefb0ac 0x85ffffebebfefb0a 0xfffffffffffff8ff 0xffffffffffffff8f

def z178 : W := mkw 0x06bb3b3e3b8f3cb6 0xc06bb3b3e3b8f3cb 0x7fbf3f3c3f0e38fd 0x77fbf3f3c3f0e38f

def z179 : W := mkw 0x0008000010080000 0x0000800001008000 0x0018000018080009 0x5001800001808000

def z180 : W := mkw 0x1d7dc000166f8008 0x01d7dc000166f800 0x1e7fc0001f7fc003 0x41e7fc0001f7fc00

def z181 : W := mkw 0x04380000120c0000 0x004380000120c000 0x2e3800003f0e0009 0x72e3800003f0e000

def z182 : W := mkw 0x063a3b3f1b0c7df6 0xc063a3b3f1b0c7df 0xee383f3f3f0e3ffd 0x7ee383f3f3f0e3ff

def z183 : W := mkw 0x000848041828a080 0x0000848041828a08 0x4058d80c18f9e0cf 0xd4058d80c18f9e0c

def z184 : W := mkw 0x043b023f120f41f0 0xc043b023f120f41f 0x503f003f000fc0f3 0x0503f003f000fc0f

def z185 : W := mkw 0x0081000020830000 0x0008100002083000 0x31a70000208fc00b 0xb31a70000208fc00

def z186 : W := mkw 0x0438002c120c00a0 0x80438002c120c00a 0x0018000c00000000 0x00018000c0000000

def z187 : W := mkw 0x543fc23a922f8008 0x0543fc23a922f800 0x503fc03fc00fc003 0x0503fc03fc00fc00

def z188 : W := mkw 0x0081010120834d52 0x40081010120834d5 0x20000000208ffff8 0x020000000208ffff

def z189 : W := mkw 0x0083031220830c12 0x40083031220830c1 0x31a7273020061830 0x231a727302006183

def z190 : W := mkw 0x00830b5768936fd2 0x600830b5768936fd 0xf1a73fffe08fffff 0xbf1a73fffe08ffff

def z191 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x3fa700003fffc008 0x23fa700003fffc00

def z192 : W := mkw 0x06b9392d3b8f7df6 0xc06b9392d3b8f7df 0x6e38383c3f8ffffd 0x76e38383c3f8ffff

def z193 : W := mkw 0x0f74b02800000000 0x00f74b0280000000 0x5ffff83c00000007 0xf5ffff83c0000000

def z194 : W := mkw 0x0002031300004d52 0x40002031300004d5 0xe0202733200e3ffd 0x3e0202733200e3ff

def z195 : W := mkw 0x02833b1329837d56 0x402833b1329837d5 0xffa73f333f8fffff 0xfffa73f333f8ffff

def z196 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x4038383c000e38f5 0x04038383c000e38f

def z197 : W := mkw 0x0630302800000000 0x0063030280000000 0xce78f8ffc0000007 0xfce78f8ffc000000

def z198 : W := mkw 0x0638782c1b2cb0a4 0x80638782c1b2cb0a 0x6e78f83c3ffff8ff 0xf6e78f83c3ffff8f

def z199 : W := mkw 0x0000000100004140 0x0000000010000414 0xc00000030089e7cf 0x9c00000030089e7c

def z200 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0x2f8027003ff03f08 0x22f8027003ff03f0

def z201 : W := mkw 0x4946869280000000 0x0494686928000000 0xd1e7e7f3c0000007 0xbd1e7e7f3c000000

def z202 : W := mkw 0x0002021200000000 0x0000202120000000 0x5027003300000003 0x0502700330000000

def z203 : W := mkw 0x0002031200000c12 0x40002031200000c1 0x0000273000001830 0x0000027300000183

def z204 : W := mkw 0x0008400010288000 0x0000840001028800 0x0058c00018f9c00b 0xd0058c00018f9c00

def z205 : W := mkw 0x5ffff7bbb6efcd5a 0x45ffff7bbb6efcd5 0xffffffffffffffff 0xffffffffffffffff

def z206 : W := mkw 0x0000084108106340 0x0000008410810634 0xc04018c318f9e7cf 0xdc04018c318f9e7c

def z207 : W := mkw 0x143dc000122f8008 0x0143dc000122f800 0x103fc000000fc003 0x0103fc000000fc00

def z208 : W := mkw 0x0208382c190830a4 0x80208382c190830a 0x4018383c180838fd 0x54018383c180838f

def z209 : W := mkw 0x2bc03dec2dd03ea7 0x82bc03dec2dd03ea 0xefc03ffc3ff03ffc 0xfefc03ffc3ff03ff

def z210 : W := mkw 0x0944800000000000 0x0094480000000000 0x11c7c00000000002 0x811c7c0000000000

def z211 : W := mkw 0x0438402d522cc1e0 0xa0438402d522cc1e 0x4038c03fc00fc0f3 0x04038c03fc00fc0f

def z212 : W := mkw 0x0002031300004d52 0x40002031300004d5 0xc000273300003ff4 0x0c000273300003ff

def z213 : W := mkw 0x063b3a3f1b0f71f4 0xc063b3a3f1b0f71f 0x7e3f383f3f0ff8ff 0x77e3f383f3f0ff8f

def z214 : W := mkw 0x06383028120c0000 0x006383028120c000 0x6e38383c3f0e000d 0x76e38383c3f0e000

def z215 : W := mkw 0x0bc0348024c00000 0x00bc0348024c0000 0xafc03fc03ff0000c 0xfafc03fc03ff0000

def z216 : W := mkw 0x2bc0358025c01c07 0x02bc0358025c01c0 0xaf80270027803f0c 0xbaf80270027803f0

def z217 : W := mkw 0x0000010100004d52 0x40000010100004d5 0x0000000000003ff0 0x00000000000003ff

def z218 : W := mkw 0x1ff5b02827c7102c 0x81ff5b02827c7102 0x3fa7203027061830 0x23fa720302706183

def z219 : W := mkw 0x008b0b17388b6dd2 0x4008b0b17388b6dd 0xf1bf3f3f388fffff 0xff1bf3f3f388ffff

def z220 : W := mkw 0x0008400010288000 0x0000840001028800 0x0000000018f9c008 0x00000000018f9c00

def z221 : W := mkw 0x09c008402cd02200 0x009c008402cd0220 0xafc018c03ff0270c 0xfafc018c03ff0270

def z222 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x2e38180c3f0e0009 0x72e38180c3f0e000

def z223 : W := mkw 0x0b487cc55838e3c0 0x20b487cc55838e3c 0xcfd8ffcfd8f9e7cf 0xfcfd8ffcfd8f9e7c

def z224 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000000300000007 0x9c00000030000000

def z225 : W := mkw 0x2bc13dc02dd33e07 0x02bc13dc02dd33e0 0xbfe73fc03fffff0f 0xfbfe73fc03fffff0

def z226 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xb18727032081ff0e 0xbb18727032081ff0

def z227 : W := mkw 0x0002031300004d52 0x40002031300004d5 0xd1a7273300003ff7 0xbd1a7273300003ff

def z228 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0x4018c00fd8f9e7cb 0x04018c00fd8f9e7c

def z229 : W := mkw 0x2bc03dc12dd07f47 0x02bc03dc12dd07f4 0xefc03fc33ff9ffcf 0xfefc03fc33ff9ffc

def z230 : W := mkw 0x1089410136efcd5a 0x41089410136efcd5 0x200000003ffffff8 0x0200000003ffffff

def z231 : W := mkw 0x5dffc692b6ef8008 0x05dffc692b6ef800 0xbfffc7c3ffffc00b 0xfbfffc7c3ffffc00

def z232 : W := mkw 0x0083435360b3cf52 0x60083435360b3cf5 0xf1e7e7f3e0ffffff 0xbf1e7e7f3e0fffff

def z233 : W := mkw 0x3ff5bdc02fd73e0f 0x03ff5bdc02fd73e0 0xbfe73fc03ff63f0c 0xfbfe73fc03ff63f0

def z234 : W := mkw 0x000848445838a280 0x2000848445838a28 0x0058d8ccd8f9c00b 0xd0058d8ccd8f9c00

def z235 : W := mkw 0x4f74b4a880000000 0x04f74b4a88000000 0x8fd8ffccc0000004 0xf8fd8ffccc000000

def z236 : W := mkw 0x1089400036ef8008 0x01089400036ef800 0x31a700003fffc00b 0xb31a700003fffc00

def z237 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x11ffc00000ffc003 0x811ffc00000ffc00

def z238 : W := mkw 0x0000000000000000 0x0000000000000000 0x0058d8ccc0000000 0x40058d8ccc000000

def z239 : W := mkw 0x0000080408002080 0x0000008040800208 0x4000180c000020c4 0x04000180c000020c

def z240 : W := mkw 0x00000845481063c0 0x200000845481063c 0xc00018cfc089e7cf 0x9c00018cfc089e7c

def z241 : W := mkw 0x0df4800024c00000 0x00df4800024c0000 0x3fffc0003ff0000b 0xf3fffc0003ff0000

def z242 : W := mkw 0x09c0000024c00000 0x009c0000024c0000 0x2f80000027000000 0x22f8000002700000

def z243 : W := mkw 0x1435800002070008 0x0143580000207000 0x1027000000060000 0x0102700000006000

def z244 : W := mkw 0x4437823b80034150 0x44437823b8003415 0x503fc03fc00fc0f3 0x0503fc03fc00fc0f

def z245 : W := mkw 0x0208786d5938f3e4 0xa0208786d5938f3e 0xc058f8ffd8f9ffff 0xdc058f8ffd8f9fff

def z246 : W := mkw 0x0438002c120c00a0 0x80438002c120c00a 0x4038003c000e00f1 0x04038003c000e00f

def z247 : W := mkw 0x19c5c00024e38008 0x019c5c00024e3800 0x3fc7c0003ff1c00a 0xf3fc7c0003ff1c00

def z248 : W := mkw 0x4fffbfbfbb8f7df6 0xc4fffbfbfbb8f7df 0xffffffffff8fffff 0xfffffffffff8ffff

def z249 : W := mkw 0x143dc02c122f80a8 0x8143dc02c122f80a 0x503fc03c000fc0f3 0x0503fc03c000fc0f

def z250 : W := mkw 0x2bc0358025c01c07 0x02bc0358025c01c0 0x2fc027003ff01808 0xf2fc027003ff0180

def z251 : W := mkw 0x06b3333a23871c36 0xc06b3333a23871c3 0x3fa7273027061830 0x23fa727302706183

def z252 : W := mkw 0x4ff7b7bba0834d52 0x44ff7b7bba0834d5 0xffffffffe08fffff 0xfffffffffe08ffff

def z253 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xb1a70703208fc70b 0xbb1a70703208fc70

def z254 : W := mkw 0x5ff7b6baa6c70008 0x05ff7b6baa6c7000 0x3fa7273027060000 0x23fa727302706000

def z255 : W := mkw 0x0083435360b3cf52 0x60083435360b3cf5 0x91c7c7c3c0f1c702 0x891c7c7c3c0f1c70

def z256 : W := mkw 0x42023ebe890030a4 0x842023ebe890030a 0xc0003fffc00038f4 0x0c0003fffc00038f

def z257 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xe0002733208ffffc 0x0e0002733208ffff

def z258 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0x804018c018f9e7cc 0xd804018c018f9e7c

def z259 : W := mkw 0x0000084008102200 0x0000008400810220 0x004018c018700000 0x4004018c01870000

def z260 : W := mkw 0x22003dc009103e07 0x022003dc009103e0 0x80003fc000003f04 0x080003fc000003f0

def z261 : W := mkw 0x143dc000122f8008 0x0143dc000122f800 0x3e3fc0003f0fc00b 0x73e3fc0003f0fc00

def z262 : W := mkw 0x44b7833ba0834d52 0x444b7833ba0834d5 0xf1bfe73fe08fffff 0xbf1bfe73fe08ffff

def z263 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000000000820cd 0x140000000000820c

def z264 : W := mkw 0x4f76b6ba83041024 0x84f76b6ba8304102 0xffffffffe7061837 0xfffffffffe706183

def z265 : W := mkw 0x0000002c000000a0 0x80000002c000000a 0x4000003c000000f0 0x04000003c000000f

def z266 : W := mkw 0x000840055028c1c0 0x2000840055028c1c 0x4058c00fd8f9c0cb 0xd4058c00fd8f9c0c

def z267 : W := mkw 0x19cdc00036ef8008 0x019cdc00036ef800 0x31c7c0003fffc00a 0x831c7c0003fffc00

def z268 : W := mkw 0x20830b532dd37f57 0x420830b532dd37f5 0xf1a727333fffffff 0xbf1a727333ffffff

def z269 : W := mkw 0x1d74800006440008 0x01d7480000644000 0x0e00000007000000 0x00e0000000700000

def z270 : W := mkw 0x1dfdc8457effe3c8 0x21dfdc8457effe3c 0xffffd8cfffffe7cf 0xfffffd8cfffffe7c

def z271 : W := mkw 0x000048414830e340 0x2000048414830e34 0x8040d8c3d8f1e70e 0xd8040d8c3d8f1e70

def z272 : W := mkw 0x0638786c5b3cb2a4 0xa0638786c5b3cb2a 0x6e78f8fcff7e38fd 0x76e78f8fcff7e38f

def z273 : W := mkw 0x5ffdf4a8b6ef8008 0x05ffdf4a8b6ef800 0x3fffd8ccffffc00b 0xf3fffd8ccffffc00

def z274 : W := mkw 0x000848055828e1c0 0x2000848055828e1c 0x4018d80fd809e0cf 0x54018d80fd809e0c

def z275 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x7fffe0303ffff8ff 0xf7fffe0303ffff8f

def z276 : W := mkw 0x4f76b7bb80004d52 0x44f76b7bb80004d5 0xdfffffffc0003ff7 0xfdfffffffc0003ff

def z277 : W := mkw 0x0083021320834150 0x4008302132083415 0x71a70033208fc0fb 0xb71a70033208fc0f

def z278 : W := mkw 0x0208382c1b0c30a4 0x80208382c1b0c30a 0x6000383c3f0e38fc 0x06000383c3f0e38f

def z279 : W := mkw 0x0000084448102280 0x2000008444810228 0x000018ccc0000000 0x0000018ccc000000

def z280 : W := mkw 0x0002021200000000 0x0000202120000000 0x9187070300000002 0x8918707030000000

def z281 : W := mkw 0x0b42369200000000 0x00b4236920000000 0xdfe73ff300000007 0xfdfe73ff30000000

def z282 : W := mkw 0x00000845481063c0 0x200000845481063c 0xc00018cfc00027c4 0x0c00018cfc00027c

def z283 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0xc058d8cfd87027c4 0x4c058d8cfd87027c

def z284 : W := mkw 0x09c0010024c00c02 0x009c0010024c00c0 0xafc027003ff03f0c 0xfafc027003ff03f0

def z285 : W := mkw 0x1dfd800036cf0008 0x01dfd800036cf000 0x3fbf00003f0e0009 0x73fbf00003f0e000

def z286 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0x9fe7e7f3c0000002 0xa9fe7e7f3c000000

def z287 : W := mkw 0x043808041a0c2080 0x0043808041a0c208 0x6e38180c3f0e20cd 0x76e38180c3f0e20c

def z288 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0x5e7fd8ffc0000003 0x45e7fd8ffc000000

def z289 : W := mkw 0x4436823a80000000 0x04436823a8000000 0xd1bfe73fc0000007 0xbd1bfe73fc000000

def z290 : W := mkw 0x6ff6bffaadd03e07 0x06ff6bffaadd03e0 0xbfe73ff03ff03f0c 0xfbfe73ff03ff03f0

def z291 : W := mkw 0x000848455b3cf3e4 0xa000848455b3cf3e 0xe058d8cfffffffff 0xde058d8cffffffff

def z292 : W := mkw 0x29c045c164f0cf43 0x229c045c164f0cf4 0x81c0c7c3c0f1c702 0x881c0c7c3c0f1c70

def z293 : W := mkw 0x22803dc029903e07 0x022803dc029903e0 0xa1803fc020803f0c 0xba1803fc020803f0

def z294 : W := mkw 0x0200380009003004 0x0020038000900300 0x0000380000003804 0x0000038000000380

def z295 : W := mkw 0x0638782d5b2cf1e4 0xa0638782d5b2cf1e 0x6e38f83fff0ff8ff 0x76e38f83fff0ff8f

def z296 : W := mkw 0x00000005400041c0 0x200000005400041c 0x4000000fc00000c0 0x04000000fc00000c

def z297 : W := mkw 0x0638386c1b1c32a4 0x80638386c1b1c32a 0xee7838fc3ffe3ffd 0xfee7838fc3ffe3ff

def z298 : W := mkw 0x2bc87dc57df8ffc7 0x22bc87dc57df8ffc 0xafc03fc03ff9ffcc 0xfafc03fc03ff9ffc

def z299 : W := mkw 0x0000000000000000 0x0000000000000000 0x200020002000380c 0x3200020002000380

def z300 : W := mkw 0x4b46b69280000000 0x04b46b6928000000 0x9fc7ffc3c0000006 0xf9fc7ffc3c000000

def z301 : W := mkw 0x0002031300004d52 0x40002031300004d5 0x8000070300000700 0x0800007030000070

def z302 : W := mkw 0x29c00dc02cd02e03 0x029c00dc02cd02e0 0x81c01fc018f0270c 0xd81c01fc018f0270

def z303 : W := mkw 0x29c307d324d34f53 0x429c307d324d34f5 0x91c707c300f1c702 0x891c707c300f1c70

def z304 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0x2fc03fc03f701800 0x62fc03fc03f70180

def z305 : W := mkw 0x4f7efefed838a280 0x24f7efefed838a28 0xdfffffffd8700007 0xfdfffffffd870000

def z306 : W := mkw 0x6f76befa8d503205 0x06f76befa8d50320 0xdfffffffdf700007 0xfdfffffffdf70000

def z307 : W := mkw 0x2bc03cc02dd03205 0x02bc03cc02dd0320 0x2fc018c03ff00008 0xf2fc018c03ff0000

def z308 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0xdfa73fffc0000004 0x2dfa73fffc000000

def z309 : W := mkw 0x4f77b6bb80034150 0x44f77b6bb8003415 0xdfffffffc00fc0f7 0xfdfffffffc00fc0f

def z310 : W := mkw 0x043848455a3ce3c0 0x2043848455a3ce3c 0xee78d8cfffffe7cf 0xfee78d8cfffffe7c

def z311 : W := mkw 0x29c307d324d34f53 0x429c307d324d34f5 0xf1e727f320ffffff 0xbf1e727f320fffff

def z312 : W := mkw 0x6ff6b7faa4d00e03 0x06ff6b7faa4d00e0 0xdfffffffc0f00707 0xfdfffffffc0f0070

def z313 : W := mkw 0x6f76bffa89103e07 0x06f76bffa89103e0 0xdfffffffc0003f07 0xfdfffffffc0003f0

def z314 : W := mkw 0x0083031220830c12 0x40083031220830c1 0x71a72730200e38fd 0x371a72730200e38f

def z315 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xefd8ffcffff03f0f 0xfefd8ffcffff03f0

def z316 : W := mkw 0x0638382c18082080 0x00638382c1808208 0x4e38383c180820cd 0x74e38383c180820c

def z317 : W := mkw 0x6ff4bde8add03e07 0x06ff4bde8add03e0 0xafd8ffccfff03f0c 0xfafd8ffccfff03f0

def z318 : W := mkw 0x0002021200000000 0x0000202120000000 0xd1ffffffc0000007 0xfd1ffffffc000000

def z319 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0xffffffffe00e38ff 0xfffffffffe00e38f

def z320 : W := mkw 0x0638786d5b3cf3e4 0xa0638786d5b3cf3e 0xce58d8cfdff9e7cf 0xdce58d8cfdff9e7c

def z321 : W := mkw 0x1dffc31236ef8c1a 0x41dffc31236ef8c1 0x3fffe7303fffd83b 0xf3fffe7303fffd83

def z322 : W := mkw 0x0080000020800000 0x0008000002080000 0x2180000020800008 0xb218000002080000

def z323 : W := mkw 0x2b487cc55d78f3c5 0x22b487cc55d78f3c 0xce58d8cfdff9e7cf 0xdce58d8cfdff9e7c

def z324 : W := mkw 0x2bc07dc16df0ff47 0x22bc07dc16df0ff4 0xafc0ffc3fff1ff0e 0xfafc0ffc3fff1ff0

def z325 : W := mkw 0x420236ba80000000 0x0420236ba8000000 0x0000273000000000 0x0000027300000000

def z326 : W := mkw 0x62023ffa89103e07 0x062023ffa89103e0 0xc0003fffc0003f04 0x0c0003fffc0003f0

def z327 : W := mkw 0x22087dc55938ffc7 0x222087dc55938ffc 0xc058ffcfd8f9ffcf 0xdc058ffcfd8f9ffc

def z328 : W := mkw 0x4002069280000000 0x0400206928000000 0x800007c3c0000000 0x0800007c3c000000

def z329 : W := mkw 0x2080014024d00e03 0x02080014024d00e0 0x0000000000f00700 0x00000000000f0070

def z330 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0x8040c0c3d8f9e7ca 0x88040c0c3d8f9e7c

def z331 : W := mkw 0x1dfdc8043fefb0ac 0x81dfdc8043fefb0a 0x3fffc0003ffff8fb 0xf3fffc0003ffff8f

def z332 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000089c00b 0x9000000000089c00

def z333 : W := mkw 0x49c78793a0834d52 0x449c78793a0834d5 0xf1e7e7f3e08fffff 0xbf1e7e7f3e08ffff

def z334 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000000200e38f8 0x020000000200e38f

def z335 : W := mkw 0x0630382809003004 0x0063038280900300 0x6e38383c3f00380d 0x76e38383c3f00380

def z336 : W := mkw 0x0003021300034150 0x4000302130003415 0xd1a72733000fc0f7 0xbd1a72733000fc0f

def z337 : W := mkw 0x2bcb7fd77dfbffd7 0x62bcb7fd77dfbffd 0xffffffffffffffff 0xffffffffffffffff

def z338 : W := mkw 0x4946869280000000 0x0494686928000000 0x1187070000000000 0x0118707000000000

def z339 : W := mkw 0x5ffffefffeffe3c8 0x25ffffefffeffe3c 0xffffffffffffe7cf 0xfffffffffffffe7c

def z340 : W := mkw 0x4f76befa88102200 0x04f76befa8810220 0xdfffffffd8f0270f 0xfdfffffffd8f0270

def z341 : W := mkw 0x1ffffb3f3feffdfe 0xc1ffffb3f3feffdf 0xffffff3f3fffffff 0xfffffff3f3ffffff

def z342 : W := mkw 0x49c78793a0834d52 0x449c78793a0834d5 0x91c7c7c3c081c702 0x891c7c7c3c081c70

def z343 : W := mkw 0x000840011028c140 0x0000840011028c14 0xc058c00318f9e7cf 0xdc058c00318f9e7c

def z344 : W := mkw 0x0002021200000000 0x0000202120000000 0xf1a72733200e38ff 0xbf1a72733200e38f

def z345 : W := mkw 0x4f74b4a880000000 0x04f74b4a88000000 0xce58d8cfc0000007 0xdce58d8cfc000000

def z346 : W := mkw 0x0940000004400000 0x0094000000440000 0x0e4000001f700000 0x40e4000001f70000

def z347 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0x0058c00018f9e7cb 0xd0058c00018f9e7c

def z348 : W := mkw 0x0083031220830c12 0x40083031220830c1 0xf1a7273320061837 0xbf1a727332006183

def z349 : W := mkw 0x10084000166c8008 0x010084000166c800 0x000000001f700000 0x0000000001f70000

def z350 : W := mkw 0x208809443fdc3ea7 0x8208809443fdc3ea 0x200000003ffe3ff8 0x0200000003ffe3ff

def z351 : W := mkw 0x0083031220830c12 0x40083031220830c1 0x1187070000000000 0x0118707000000000

def z352 : W := mkw 0x4f7ebebe9b0c30a4 0x84f7ebebe9b0c30a 0x7fbf3f3c3f0e38fd 0x77fbf3f3c3f0e38f

def z353 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x2e18380c3f00380c 0x72e18380c3f00380

def z354 : W := mkw 0x26b8396c3fdc3ea7 0x826b8396c3fdc3ea 0x6e38383c3ffe3ffd 0x76e38383c3ffe3ff

def z355 : W := mkw 0x0008400010288000 0x0000840001028800 0x0018c0000009c003 0x00018c0000009c00

def z356 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x2e18180c3f0e38f8 0x42e18180c3f0e38f

def z357 : W := mkw 0x0008000410080080 0x0000800041008008 0x4018000c000800c1 0x04018000c000800c

def z358 : W := mkw 0x29c0058024c00c03 0x029c0058024c00c0 0x0180070000000000 0x0018007000000000

def z359 : W := mkw 0x0200300001001004 0x0020030000100100 0x2e00200027001800 0x22e0020002700180

def z360 : W := mkw 0x0083031220830c12 0x40083031220830c1 0x31a72730208fd83b 0xb31a72730208fd83

def z361 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0x8058d8cfd8f1c702 0xc8058d8cfd8f1c70

def z362 : W := mkw 0x1d7cc000166c8008 0x01d7cc000166c800 0x1fffc0001f700003 0xf1fffc0001f70000

def z363 : W := mkw 0x0638302c120c00a0 0x80638302c120c00a 0x4e38383c000e00f5 0x74e38383c000e00f

def z364 : W := mkw 0x29c009402dd03e07 0x029c009402dd03e0 0x2fc000003ff03f08 0xf2fc000003ff03f0

def z365 : W := mkw 0x0630382c0b0430a4 0x80630382c0b0430a 0x6e20383c270638f4 0x26e20383c270638f

def z366 : W := mkw 0x0b40348000000000 0x00b4034800000000 0xcfd8ffcfc0000007 0xfcfd8ffcfc000000

def z367 : W := mkw 0x0280390029803c06 0x00280390029803c0 0xaf803f003f803f0c 0xfaf803f003f803f0

def z368 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xd18727330081fff6 0x8d18727330081fff

def z369 : W := mkw 0x4f7eb6ba920c0000 0x04f7eb6ba920c000 0xffffffffff0e000f 0xfffffffffff0e000

def z370 : W := mkw 0x19c5c00024e38008 0x019c5c00024e3800 0x31e7c00020ffc00b 0xb31e7c00020ffc00

def z371 : W := mkw 0x0002021200000000 0x0000202120000000 0xc000273300000004 0x0c00027330000000

def z372 : W := mkw 0x0081010120834d52 0x40081010120834d5 0x31a70000208ffffb 0xb31a70000208ffff

def z373 : W := mkw 0x2b40348005401005 0x02b4034800540100 0x0e00000007000000 0x00e0000000700000

def z374 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0x1fffe73000000003 0xf1fffe7300000000

def z375 : W := mkw 0x19cdc8457cfbe3c8 0x219cdc8457cfbe3c 0xd1dfd8cfd8f9e7cf 0xdd1dfd8cfd8f9e7c

def z376 : W := mkw 0x1dfdc02c36ef80a8 0x81dfdc02c36ef80a 0x7fffc03c3fffc0fb 0xf7fffc03c3fffc0f

def z377 : W := mkw 0x228039402dd03e07 0x0228039402dd03e0 0x2e0038003ff03f0c 0x72e0038003ff03f0

def z378 : W := mkw 0x2bc87dc47df8be87 0x22bc87dc47df8be8 0xafd8ffccfff03f0c 0xfafd8ffccfff03f0

def z379 : W := mkw 0x2bc035c024d00e03 0x02bc035c024d00e0 0x8fc03fc000f00704 0xf8fc03fc000f0070

def z380 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x2e2020303f0e38f8 0x22e2020303f0e38f

def z381 : W := mkw 0x4d76869280000000 0x04d7686928000000 0x9fffc7c3c0000003 0xf9fffc7c3c000000

def z382 : W := mkw 0x22003dc549107fc7 0x222003dc549107fc 0xc0003fcfc0003fc4 0x0c0003fcfc0003fc

def z383 : W := mkw 0x0000000000000000 0x0000000000000000 0x11a7000000000003 0xb11a700000000000

def z384 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0xce58ffffc0000004 0x4ce58ffffc000000

def z385 : W := mkw 0x5ff7f6baa4e38008 0x05ff7f6baa4e3800 0xdfffffffc0f1c007 0xfdfffffffc0f1c00

def z386 : W := mkw 0x0d7cc8455838e3c0 0x20d7cc8455838e3c 0xdfffd8cfd8f9e7cf 0xfdfffd8cfd8f9e7c

def z387 : W := mkw 0x0630302803041024 0x8063030280304102 0x6e38383c27061835 0x76e38383c2706183

def z388 : W := mkw 0x1081400024e38008 0x01081400024e3800 0x0000000000f1c000 0x00000000000f1c00

def z389 : W := mkw 0x0200382c090030a4 0x80200382c090030a 0x6e00383c3f0038fc 0x76e00383c3f0038f

def z390 : W := mkw 0x0008400010288000 0x0000840001028800 0xc058d8cfd8f9c00f 0xdc058d8cfd8f9c00

def z391 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x4e18180c1f0820cd 0x54e18180c1f0820c

def z392 : W := mkw 0x00000845481063c0 0x200000845481063c 0x00000000000027c0 0x000000000000027c

def z393 : W := mkw 0x0083031220830c12 0x40083031220830c1 0xb1a7273020863f3c 0xbb1a7273020863f3

def z394 : W := mkw 0x3bc5fdc02df3be0f 0x03bc5fdc02df3be0 0xbfc7ffc03ff1ff0e 0xfbfc7ffc03ff1ff0

def z395 : W := mkw 0x0081010020830c12 0x40081010020830c1 0x2000000020061830 0x0200000002006183

def z396 : W := mkw 0x463236ba80000000 0x0463236ba8000000 0xce383fffc0000005 0x7ce383fffc000000

def z397 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xd1a70733008fc7f3 0x8d1a70733008fc7f

def z398 : W := mkw 0x0f74b48000000000 0x00f74b4800000000 0x9fffffc000000007 0xf9fffffc00000000

def z399 : W := mkw 0x00000845481063c0 0x200000845481063c 0xc058d8cfc00027c7 0xdc058d8cfc00027c

def z400 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x3fffc0003f760000 0x63fffc0003f76000

def z401 : W := mkw 0x06383028130c1024 0x806383028130c102 0x2e3820303f0e1839 0x72e3820303f0e183

def z402 : W := mkw 0x208109412dd37f57 0x4208109412dd37f5 0x200000003ffffff8 0x0200000003ffffff

def z403 : W := mkw 0x1dffc21336efc158 0x41dffc21336efc15 0x7fffc0333fffc0fb 0xf7fffc0333fffc0f

def z404 : W := mkw 0x4f76beffc81063c0 0x24f76beffc81063c 0xdfffffffc00027c7 0xfdfffffffc00027c

def z405 : W := mkw 0x0080010120804d42 0x00080010120804d4 0xe18027032089ffcf 0xbe18027032089ffc

def z406 : W := mkw 0x000a4b575838efd2 0x6000a4b575838efd 0xc058ffffd8f9ffff 0xdc058ffffd8f9fff

def z407 : W := mkw 0x4b4236ba80000000 0x04b4236ba8000000 0xcfc03fffc0000004 0xfcfc03fffc000000

def z408 : W := mkw 0x0000080009003004 0x0000008000900300 0x200000003f003808 0x0200000003f00380

def z409 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0x5fbf3f3c00000005 0x75fbf3f3c0000000

def z410 : W := mkw 0x200008400d503205 0x0200008400d50320 0x000000001f700000 0x0000000001f70000

def z411 : W := mkw 0x1df5c00024e38008 0x01df5c00024e3800 0x1fffc00000f1c003 0xf1fffc00000f1c00

def z412 : W := mkw 0x0ff8382c3fcc30a4 0x80ff8382c3fcc30a 0x6ff8383c3ffe38fd 0xf6ff8383c3ffe38f

def z413 : W := mkw 0x02023b3f09007df6 0xc02023b3f09007df 0xc0003f3f00003ff4 0x0c0003f3f00003ff

def z414 : W := mkw 0x2bc03d802dc03c07 0x02bc03d802dc03c0 0x2f803f003f00380c 0x72f803f003f00380

def z415 : W := mkw 0x0083031320834d52 0x40083031320834d5 0x31a72730208ffff8 0x231a72730208ffff

def z416 : W := mkw 0x4f76bebe890030a4 0x84f76bebe890030a 0xdfffffffc00038f7 0xfdfffffffc00038f

def z417 : W := mkw 0x008b431330abcd52 0x4008b431330abcd5 0xf1ffe73338ffffff 0xff1ffe73338fffff

def z418 : W := mkw 0x5f7cf4a8966c8008 0x05f7cf4a8966c800 0x0e58d8ccdf700000 0x40e58d8ccdf70000

def z419 : W := mkw 0x22003dec09103ea7 0x822003dec09103ea 0xc0003ffc00003ff4 0x0c0003ffc00003ff

def z420 : W := mkw 0x0003031300034d52 0x40003031300034d5 0xd0272733000ffff7 0x0d0272733000ffff

def z421 : W := mkw 0x00000845481063c0 0x200000845481063c 0xc04018cfd8f027cc 0xdc04018cfd8f027c

def z422 : W := mkw 0x1dffc21236ef8008 0x01dffc21236ef800 0xffffe7333fffc00f 0xfffffe7333fffc00

def z423 : W := mkw 0x0638386d5b1c73e4 0xa0638386d5b1c73e 0xee3838ffff0e3ffd 0x7ee3838ffff0e3ff

def z424 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xf1a7273320063ff4 0x2f1a7273320063ff

def z425 : W := mkw 0x2bc33fd32dd37f57 0x42bc33fd32dd37f5 0xbfc73fc33ff1ff0e 0xfbfc73fc33ff1ff0

def z426 : W := mkw 0x4f74b4a880000000 0x04f74b4a88000000 0x4e78f8fcc0000005 0x74e78f8fcc000000

def z427 : W := mkw 0x020878455938f3c4 0x2020878455938f3c 0xee58f8cffff9ffcf 0xfee58f8cffff9ffc

def z428 : W := mkw 0x5dffc23ab6ef8008 0x05dffc23ab6ef800 0x7fffc03fffffc00b 0xf7fffc03fffffc00

def z429 : W := mkw 0x4ffffffff8bbefd2 0x64ffffffff8bbefd 0xfffffffff8ffffff 0xffffffffff8fffff

def z430 : W := mkw 0x19c5c04164f3c348 0x219c5c04164f3c34 0x91c7c0c3c0f1c702 0x891c7c0c3c0f1c70

def z431 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00018cfc0000004 0x0c00018cfc000000

def z432 : W := mkw 0x6ff7bffbadd37f57 0x46ff7bffbadd37f5 0xffffffffffffffff 0xffffffffffffffff

def z433 : W := mkw 0x4ff7b7baa0830c12 0x44ff7b7baa0830c1 0xffffffffe0061837 0xfffffffffe006183

def z434 : W := mkw 0x0088494578b8efc2 0x20088494578b8efc 0xe1d8ffcff8f9ffcf 0xfe1d8ffcff8f9ffc

def z435 : W := mkw 0x14bdc00036ef8008 0x014bdc00036ef800 0x303fc0003fffc00b 0x0303fc0003fffc00

def z436 : W := mkw 0x4ff7b7bba0834d52 0x44ff7b7bba0834d5 0xdfffffffc081c707 0xfdfffffffc081c70

def z437 : W := mkw 0x4436823a80000000 0x04436823a8000000 0xd07fd8ffc0000007 0xdd07fd8ffc000000

def z438 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0x4058d8cfd879c0c3 0x44058d8cfd879c0c

def z439 : W := mkw 0x4f7cbcac9b0c30a4 0x84f7cbcac9b0c30a 0x0e58d8ccdf000000 0x40e58d8ccdf00000

def z440 : W := mkw 0x0b403cc008102200 0x00b403cc00810220 0x8fc03fc018f0270c 0xf8fc03fc018f0270

def z441 : W := mkw 0x4434802880000000 0x0443480288000000 0x0018c00cc0000000 0x00018c00cc000000

def z442 : W := mkw 0x2ff87ded7ffcffe7 0xa2ff87ded7ffcffe 0xeff8ffffffffffff 0xfeff8fffffffffff

def z443 : W := mkw 0x2bc83dc43dd83e87 0x02bc83dc43dd83e8 0xefd83fcc3ff83fcd 0xfefd83fcc3ff83fc

def z444 : W := mkw 0x0000000000000000 0x0000000000000000 0x4018180c00000005 0x54018180c0000000

def z445 : W := mkw 0x0200300000000000 0x0020030000000000 0x0e00380000000004 0x70e0038000000000

def z446 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x3fbfc000270fc003 0x23fbfc000270fc00

def z447 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0xffffd8cfffffc00f 0xfffffd8cfffffc00

def z448 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xefe03ff03ffe3ffd 0xfefe03ff03ffe3ff

def z449 : W := mkw 0x1f7cf82c1f6cb0ac 0x81f7cf82c1f6cb0a 0x6e78f83c3f7e38fd 0x76e78f83c3f7e38f

def z450 : W := mkw 0x2b403cc00d503205 0x02b403cc00d50320 0x8fc03fc01f700004 0xf8fc03fc01f70000

def z451 : W := mkw 0x0638786d5838e3c0 0x20638786d5838e3c 0xce78f8ffd8f9e7cf 0xfce78f8ffd8f9e7c

def z452 : W := mkw 0x0080094028902e02 0x00080094028902e0 0xa1c03fc038f03f0c 0xfa1c03fc038f03f0

def z453 : W := mkw 0x443ec23fd028c1c0 0x2443ec23fd028c1c 0x503fc03fc009c0c3 0x0503fc03fc009c0c

def z454 : W := mkw 0x008b4b5778bbefd2 0x6008b4b5778bbefd 0xd1dfdfcfd8f9e7cf 0xdd1dfdfcfd8f9e7c

def z455 : W := mkw 0x1ffdf02836ef8008 0x01ffdf02836ef800 0x7ffff83c3fffc00f 0xf7ffff83c3fffc00

def z456 : W := mkw 0x0940000000000000 0x0094000000000000 0x0fc0000000000000 0xf0fc000000000000

def z457 : W := mkw 0x294004c004500201 0x0294004c00450020 0x004000c000700000 0x0004000c00070000

def z458 : W := mkw 0x4d7686ba80000000 0x04d7686ba8000000 0xd1ffc7ffc0000003 0x8d1ffc7ffc000000

def z459 : W := mkw 0x04bb033f328f4df2 0xc04bb033f328f4df 0xf1bf273f208fffff 0xbf1bf273f208ffff

def z460 : W := mkw 0x0f783cac1b0c30a4 0x80f783cac1b0c30a 0xeff83ffc3f0e38fd 0xfeff83ffc3f0e38f

def z461 : W := mkw 0x0000000000000000 0x0000000000000000 0x40002030000038f4 0x040002030000038f

def z462 : W := mkw 0x09c848457cf8e3c0 0x209c848457cf8e3c 0xefd8d8cffff9e7cf 0xfefd8d8cffff9e7c

def z463 : W := mkw 0x143dc8455a3fe3c8 0x2143dc8455a3fe3c 0xd07fd8cfd8ffe7cf 0xdd07fd8cfd8ffe7c

def z464 : W := mkw 0x22833fd329937f57 0x422833fd329937f5 0xf1a73ff3208fffff 0xbf1a73ff3208ffff

def z465 : W := mkw 0x043808041b0c30a4 0x8043808041b0c30a 0x2e3800003f0e38f9 0x72e3800003f0e38f

def z466 : W := mkw 0x0438082c1b0c30a4 0x80438082c1b0c30a 0x6038003c3f0e38f9 0x06038003c3f0e38f

def z467 : W := mkw 0x06b8392c3b8c3ca6 0x806b8392c3b8c3ca 0xefb83f3c3f8e3ffd 0xfefb83f3c3f8e3ff

def z468 : W := mkw 0x39c5c5c024f38e0b 0x039c5c5c024f38e0 0x91c7c7c000f1c702 0x891c7c7c000f1c70

def z469 : W := mkw 0x6f74bce88d503205 0x06f74bce88d50320 0x0e58d8ccdf700000 0x40e58d8ccdf70000

def z470 : W := mkw 0x69c687d2a4d00e03 0x069c687d2a4d00e0 0x91c7c7c3c0f00702 0x891c7c7c3c0f0070

def z471 : W := mkw 0x2ff4bdc02dd03e07 0x02ff4bdc02dd03e0 0xbfffffc03ff03f0f 0xfbfffffc03ff03f0

def z472 : W := mkw 0x04380000120c0000 0x004380000120c000 0x0e1800001f000000 0x40e1800001f00000

def z473 : W := mkw 0x19c7c31324e3cd5a 0x419c7c31324e3cd5 0xf1e7e73320ffffff 0xbf1e7e73320fffff

def z474 : W := mkw 0x143dc005522fc1c8 0x2143dc005522fc1c 0x503fc00fc00fc0c3 0x0503fc00fc00fc0c

def z475 : W := mkw 0x1d7cc8455e7ce3c8 0x21d7cc8455e7ce3c 0xce58d8cfdff9e7cf 0xdce58d8cfdff9e7c

def z476 : W := mkw 0x063a3a3e1b0c30a4 0x8063a3a3e1b0c30a 0xffbf3f3f3f0e38ff 0xfffbf3f3f3f0e38f

def z477 : W := mkw 0x09c0000024c00000 0x009c0000024c0000 0x01c0000000f00000 0x801c0000000f0000

def z478 : W := mkw 0x2b403cc00d503205 0x02b403cc00d50320 0x8e4018c01ff0270c 0xd8e4018c01ff0270

def z479 : W := mkw 0x2bc3379325c35d57 0x42bc3379325c35d5 0xffa72733278fffff 0xbffa72733278ffff

def z480 : W := mkw 0x000848401838a200 0x0000848401838a20 0x8058d8c018f9e70f 0xd8058d8c018f9e70

def z481 : W := mkw 0x0630382c090030a4 0x80630382c090030a 0x4e38383c000038f5 0x74e38383c000038f

def z482 : W := mkw 0x0008084418182280 0x0000808441818228 0xc05818cc18f827cd 0xdc05818cc18f827c

def z483 : W := mkw 0x1f7cf82c1f6cb0ac 0x81f7cf82c1f6cb0a 0x0e58d80c1f700000 0x40e58d80c1f70000

def z484 : W := mkw 0x008b4b5778bbefd2 0x6008b4b5778bbefd 0xf1a7273338ffffff 0xbf1a7273338fffff

def z485 : W := mkw 0x06b9382c3b8f30a4 0x806b9382c3b8f30a 0x7fbf383c3f8ff8ff 0xf7fbf383c3f8ff8f

def z486 : W := mkw 0x00080000120c0000 0x000080000120c000 0x200000003f0e0008 0x0200000003f0e000

def z487 : W := mkw 0x008b0b173b8f7df6 0xc008b0b173b8f7df 0xf1a727333f8fffff 0xbf1a727333f8ffff

def z488 : W := mkw 0x0638382d1b0c71e4 0x80638382d1b0c71e 0xee38383f3f8fffff 0xfee38383f3f8ffff

def z489 : W := mkw 0x22003dc009103e07 0x022003dc009103e0 0x80403fc018f03f0c 0xd80403fc018f03f0

def z490 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0xee78f8ffff0e38ff 0xfee78f8ffff0e38f

def z491 : W := mkw 0x1944c00004608008 0x01944c0000460800 0x0040c00000700000 0x00040c0000070000

def z492 : W := mkw 0x0001000100034150 0x4000100010003415 0x00000000000fc0f0 0x000000000000fc0f

def z493 : W := mkw 0x29c00dc02dd03e07 0x029c00dc02dd03e0 0xa1c007c03ff03f08 0x8a1c007c03ff03f0

def z494 : W := mkw 0x19c9400036ef8008 0x019c9400036ef800 0x2fc000003fffc008 0xf2fc000003fffc00

def z495 : W := mkw 0x0002021300004140 0x0000202130000414 0xd1a727330089e7cf 0xbd1a727330089e7c

def z496 : W := mkw 0x1dffc31336efcd5a 0x41dffc31336efcd5 0xbfffc7033fffc70b 0xfbfffc7033fffc70

def z497 : W := mkw 0x4ff7b7baa0830c12 0x44ff7b7baa0830c1 0x3fa7273020061830 0x23fa727302006183

def z498 : W := mkw 0x208849457df8ffc7 0x2208849457df8ffc 0xe058d8cffff9ffcf 0xde058d8cffff9ffc

def z499 : W := mkw 0x0632323a00000000 0x00632323a0000000 0xdfbf3f3f00000007 0xfdfbf3f3f0000000

def z500 : W := mkw 0x0000000003041024 0x8000000000304102 0x2000000027061830 0x0200000002706183

def z501 : W := mkw 0x1dfcc00036ec8008 0x01dfcc00036ec800 0x2fd8c0003ff00008 0xf2fd8c0003ff0000

def z502 : W := mkw 0x0d7c8000120c0000 0x00d7c8000120c000 0x3fffc0003f0e000b 0xf3fffc0003f0e000

def z503 : W := mkw 0x163df82c1b2fb0ac 0x8163df82c1b2fb0a 0x7e3ff83c3f0ff8ff 0x77e3ff83c3f0ff8f

def z504 : W := mkw 0x22803dc02dd03e07 0x022803dc02dd03e0 0xa0003fc03ff03f0c 0x0a0003fc03ff03f0

def z505 : W := mkw 0x3bc97dc03fffbe0f 0x03bc97dc03fffbe0 0xafc03fc03fffff0c 0xfafc03fc03fffff0

def z506 : W := mkw 0x2b403cc00d503205 0x02b403cc00d50320 0x2e4038c03f70380c 0x72e4038c03f70380

def z507 : W := mkw 0x0083021220830000 0x0008302122083000 0xf1a72733208fc00f 0xbf1a72733208fc00

def z508 : W := mkw 0x0430002802040020 0x8043000280204002 0x0020003000060030 0x0002000300006003

def z509 : W := mkw 0x4006821280000000 0x0400682128000000 0x1007c003c0000002 0x01007c003c000000

def z510 : W := mkw 0x4f76b6ba83041024 0x84f76b6ba8304102 0x3fa7273027061830 0x23fa727302706183

def z511 : W := mkw 0x443eca7fd838e3c0 0x2443eca7fd838e3c 0xd07fd8ffd8f9e7cf 0xdd07fd8ffd8f9e7c

def z512 : W := mkw 0x008b431770abcdd2 0x6008b431770abcdd 0xf1bfe73fe08fffff 0xbf1bfe73fe08ffff

def z513 : W := mkw 0x3ffdfdec3fffbeaf 0x83ffdfdec3fffbea 0xfffffffc3fffffff 0xffffffffc3ffffff

def z514 : W := mkw 0x0000004000100200 0x0000000400010020 0x804000c000f00700 0x8804000c000f0070

def z515 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0xdfa7273300000007 0xbdfa727330000000

def z516 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040000018f00008 0xd0040000018f0000

def z517 : W := mkw 0x0081000120834140 0x0008100012083414 0xf1a70003208fe7cf 0xbf1a70003208fe7c

def z518 : W := mkw 0x000b4a57583be3d0 0x6000b4a57583be3d 0xd07fd8ffd8ffe7ff 0xdd07fd8ffd8ffe7f

def z519 : W := mkw 0x208849457df8ffc7 0x2208849457df8ffc 0x200000003ff9ffc8 0x0200000003ff9ffc

def z520 : W := mkw 0x0f7034a800000000 0x00f7034a80000000 0xcff83ffc00000005 0xfcff83ffc0000000

def z521 : W := mkw 0x0000084008102200 0x0000008400810220 0x800018c000002704 0x0800018c00000270

def z522 : W := mkw 0x0000000000000000 0x0000000000000000 0x20200000200e0009 0x320200000200e000

def z523 : W := mkw 0x04380000120c0000 0x004380000120c000 0x00380000000e0001 0x000380000000e000

def z524 : W := mkw 0x0000080008002000 0x0000008000800200 0x000018001800200c 0x5000018001800200

def z525 : W := mkw 0x0000000000000000 0x0000000000000000 0x40200030000e00f1 0x040200030000e00f

def z526 : W := mkw 0x4944848080000000 0x0494484808000000 0x0040c0c0c0000000 0x00040c0c0c000000

def z527 : W := mkw 0x000840055028c1c0 0x2000840055028c1c 0xc018c00fc089e7cf 0x9c018c00fc089e7c

def z528 : W := mkw 0x4636b6ba80000000 0x04636b6ba8000000 0xd03fffffc0000007 0x0d03fffffc000000

def z529 : W := mkw 0x0000000000000000 0x0000000000000000 0x4018c00fc0000003 0x04018c00fc000000

def z530 : W := mkw 0x06b3333b23875d76 0xc06b3333b23875d7 0xffa72733278fffff 0xbffa72733278ffff

def z531 : W := mkw 0x4b46b6ba80000000 0x04b46b6ba8000000 0xd1c7ffffc0000006 0x8d1c7ffffc000000

def z532 : W := mkw 0x0000000100004140 0x0000000010000414 0xe0202033208fffff 0xbe0202033208ffff

def z533 : W := mkw 0x3ffdfdc57fffffcf 0x23ffdfdc57fffffc 0xffffffcfffffffcf 0xfffffffcfffffffc

def z534 : W := mkw 0x0940048000000000 0x0094004800000000 0x81c007c000000000 0x881c007c00000000

def z535 : W := mkw 0x108948457effe3c8 0x2108948457effe3c 0xe058d8cfffffe7cf 0xde058d8cfffffe7c

def z536 : W := mkw 0x1df5800026c70008 0x01df5800026c7000 0x3fe700003ff60008 0xf3fe700003ff6000

def z537 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z538 : W := mkw 0x0008400010288000 0x0000840001028800 0x0058c00018700000 0x40058c0001870000

def z539 : W := mkw 0x420236ba80000000 0x0420236ba8000000 0xd1a73fffc0000007 0xbd1a73fffc000000

def z540 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0xc000000318f9e7cf 0x9c000000318f9e7c

def z541 : W := mkw 0x000840415038c340 0x2000840415038c34 0x8058c0c3d8f9c70b 0xd8058c0c3d8f9c70

def z542 : W := mkw 0x463a3ebe9b0c30a4 0x8463a3ebe9b0c30a 0xee383fffff0e38fd 0x7ee383fffff0e38f

def z543 : W := mkw 0x0df5800020830000 0x00df580002083000 0x3fffc000208fc00b 0xf3fffc000208fc00

def z544 : W := mkw 0x59c7c692a4e38008 0x059c7c692a4e3800 0x91c7c7c3c0f1c002 0x891c7c7c3c0f1c00

def z545 : W := mkw 0x14bdc00032af8008 0x014bdc00032af800 0x31bfc000208fc00b 0xb31bfc000208fc00

def z546 : W := mkw 0x0434800000000000 0x0043480000000000 0x103fc00000000003 0x0103fc0000000000

def z547 : W := mkw 0x0000000100004140 0x0000000010000414 0xc0000003000027c4 0x0c0000003000027c

def z548 : W := mkw 0x2200358001001c07 0x02200358001001c0 0x0000270000001800 0x0000027000000180

def z549 : W := mkw 0x0081000020830000 0x0008100002083000 0x20000000208fc008 0x020000000208fc00

def z550 : W := mkw 0x0000000000000000 0x0000000000000000 0x804018c000000004 0xd804018c00000000

def z551 : W := mkw 0x2ffb3fff3fdf7ff7 0xc2ffb3fff3fdf7ff 0xffff3fff3fffffff 0xfffff3fff3ffffff

def z552 : W := mkw 0x0000000000000000 0x0000000000000000 0x8180270000000004 0xb818027000000000

def z553 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0x0058d8ccd8f9e7c8 0x40058d8ccd8f9e7c

def z554 : W := mkw 0x00080845581863c0 0x200080845581863c 0xc01818cfd80827cd 0x5c01818cfd80827c

def z555 : W := mkw 0x6bc23ffaadd03e07 0x06bc23ffaadd03e0 0xefc03ffffff03f0c 0xfefc03ffffff03f0

def z556 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0x9fe73ff000000004 0xf9fe73ff00000000

def z557 : W := mkw 0x00830b5328936f52 0x400830b5328936f5 0xf1e73ff338ffffff 0xff1e73ff338fffff

def z558 : W := mkw 0x0083031320834d52 0x40083031320834d5 0x71a72733200fd8f3 0x271a72733200fd8f

def z559 : W := mkw 0x0080010020800c02 0x00080010020800c0 0xe1a02730208e3ffd 0xbe1a02730208e3ff

def z560 : W := mkw 0x0008400450288080 0x2000840045028808 0x0018c00cc0000000 0x00018c00cc000000

def z561 : W := mkw 0x1089400036ef8008 0x01089400036ef800 0x2058c0003fffc00b 0xd2058c0003fffc00

def z562 : W := mkw 0x0208380419083084 0x0020838041908308 0x6e18380c3f0838cd 0x76e18380c3f0838c

def z563 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xd1a727330081c707 0xbd1a727330081c70

def z564 : W := mkw 0x19cdc00034eb8008 0x019cdc00034eb800 0x11dfc00018f9c00b 0xd11dfc00018f9c00

def z565 : W := mkw 0x1df7831226c70c1a 0x41df7831226c70c1 0x3fa7273027061830 0x23fa727302706183

def z566 : W := mkw 0x04bb0313328f4d52 0x404bb0313328f4d5 0xffbf27333f8fffff 0xfffbf27333f8ffff

def z567 : W := mkw 0x00020b5748106fd2 0x600020b5748106fd 0xc0003fffc0003ff4 0x0c0003fffc0003ff

def z568 : W := mkw 0x0000000000000000 0x0000000000000000 0x2020203020061830 0x2202020302006183

def z569 : W := mkw 0x4636b23a80000000 0x04636b23a8000000 0x5e3ff83fc0000007 0x75e3ff83fc000000

def z570 : W := mkw 0x0081010120834d52 0x40081010120834d5 0x60202030208ffffd 0x360202030208ffff

def z571 : W := mkw 0x2bc035c025d01e07 0x02bc035c025d01e0 0xafc027c027f01f00 0xaafc027c027f01f0

def z572 : W := mkw 0x2ff03de82dd03e07 0x02ff03de82dd03e0 0xeff83ffc3ff03f0d 0xfeff83ffc3ff03f0

def z573 : W := mkw 0x0d7cc00010288000 0x00d7cc0001028800 0x1fffc00018f9c00b 0xf1fffc00018f9c00

def z574 : W := mkw 0x200005c000100e03 0x0200005c000100e0 0x800007c000000700 0x0800007c00000070

def z575 : W := mkw 0x0083031320834d52 0x40083031320834d5 0x70270033208ffffb 0x070270033208ffff

def z576 : W := mkw 0x4f7ef6ba90288000 0x04f7ef6ba9028800 0xdfffffffd8f9c00f 0xfdfffffffd8f9c00

def z577 : W := mkw 0x0003021300034150 0x4000302130003415 0xd0270033008fe7ff 0x9d0270033008fe7f

def z578 : W := mkw 0x1005c00000238008 0x01005c0000023800 0x1007c0000001c002 0x01007c0000001c00

def z579 : W := mkw 0x0000004140104340 0x2000000414010434 0x800000c3c0000700 0x0800000c3c000070

def z580 : W := mkw 0x2b487cc45d78b285 0x22b487cc45d78b28 0x0e58d8ccdf700000 0x40e58d8ccdf70000

def z581 : W := mkw 0x000048454830e3c0 0x2000048454830e3c 0xc040d8cfc0f1e7c6 0x8c040d8cfc0f1e7c

def z582 : W := mkw 0x2ff83dc03fdc3e07 0x02ff83dc03fdc3e0 0xaff83fc03ffe3f0d 0xfaff83fc03ffe3f0

def z583 : W := mkw 0x06b3333b20834d52 0x406b3333b20834d5 0xffbf3f3f208fffff 0xfffbf3f3f208ffff

def z584 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0x5fbfe73fc0000003 0x25fbfe73fc000000

def z585 : W := mkw 0x0080000024c00000 0x00080000024c0000 0x200000003ff00008 0x0200000003ff0000

def z586 : W := mkw 0x5f7ff6ba922f8008 0x05f7ff6ba922f800 0xdfffffffc00fc007 0xfdfffffffc00fc00

def z587 : W := mkw 0x0000000000000000 0x0000000000000000 0x2e0000003f000008 0x72e0000003f00000

def z588 : W := mkw 0x1df5800026c70008 0x01df5800026c7000 0x3fa70000278fc00b 0xb3fa70000278fc00

def z589 : W := mkw 0x0f7cb82c1b0c30a4 0x80f7cb82c1b0c30a 0x7ffff83c3f0e38ff 0xf7ffff83c3f0e38f

def z590 : W := mkw 0x6ff6b7baa5c01c07 0x06ff6b7baa5c01c0 0xffffffffe7001807 0xfffffffffe700180

def z591 : W := mkw 0x00080805180861c0 0x000080805180861c 0xc018180f1889e7cf 0xdc018180f1889e7c

def z592 : W := mkw 0x2bc3379225c31c17 0x42bc3379225c31c1 0x3fa7273027061830 0x23fa727302706183

def z593 : W := mkw 0x3ffdfcc03fffb20d 0x03ffdfcc03fffb20 0x3fffd8c03fffc00b 0xf3fffd8c03fffc00

def z594 : W := mkw 0x0008080418082080 0x0000808041808208 0x00000000180820c8 0x000000000180820c

def z595 : W := mkw 0x0080010020800c02 0x00080010020800c0 0x8180070000800700 0x8818007000080070

def z596 : W := mkw 0x000040414030c340 0x2000040414030c34 0xc040c0c3c0f9e7cf 0x9c040c0c3c0f9e7c

def z597 : W := mkw 0x0200382c090030a4 0x80200382c090030a 0x6020383c200e38fd 0x36020383c200e38f

def z598 : W := mkw 0x26383dec1b1c3ea7 0x826383dec1b1c3ea 0xee383ffc3f0e3ffd 0x7ee383ffc3f0e3ff

def z599 : W := mkw 0x4f7efeffdb3cf3e4 0xa4f7efeffdb3cf3e 0xffffffffffffffff 0xffffffffffffffff

def z600 : W := mkw 0x4946c6d3c030c340 0x24946c6d3c030c34 0x91c7c7c3c0f1c702 0x891c7c7c3c0f1c70

def z601 : W := mkw 0x0008080418082080 0x0000808041808208 0xc058d8cfd80820cf 0xdc058d8cfd80820c

def z602 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x2e38383c3f061830 0x62e38383c3f06183

def z603 : W := mkw 0x0080010020800c02 0x00080010020800c0 0x2180270020001800 0x2218027002000180

def z604 : W := mkw 0x3dfdc9403fffbe0f 0x03dfdc9403fffbe0 0x3fffc0003fffff0b 0xf3fffc0003fffff0

def z605 : W := mkw 0x0081010120834d52 0x40081010120834d5 0x000000000081c700 0x0000000000081c70

def z606 : W := mkw 0x22003cc009103205 0x022003cc00910320 0x000018c000000000 0x0000018c00000000

def z607 : W := mkw 0x0081010020830c02 0x00081010020830c0 0xb1a72700208fff0f 0xbb1a72700208fff0

def z608 : W := mkw 0x4002023a80000000 0x04002023a8000000 0x4000003fc0000000 0x04000003fc000000

def z609 : W := mkw 0x0200302800000000 0x0020030280000000 0x4000383c00000004 0x04000383c0000000

def z610 : W := mkw 0x4f7eb6be920c00a0 0x84f7eb6be920c00a 0xdfffffffc00e00f7 0xfdfffffffc00e00f

def z611 : W := mkw 0x420236ba80000000 0x0420236ba8000000 0xc058ffffc0000007 0xdc058ffffc000000

def z612 : W := mkw 0x5ffff6bab6ef8008 0x05ffff6bab6ef800 0x3fffe7303fffc00b 0xf3fffe7303fffc00

def z613 : W := mkw 0x00000804090030a4 0x800000804090030a 0x00000000000038f0 0x000000000000038f

def z614 : W := mkw 0x000848455b3cf3e4 0xa000848455b3cf3e 0x200000003ffffff8 0x0200000003ffffff

def z615 : W := mkw 0x4ff7b7bba0834d52 0x44ff7b7bba0834d5 0xffa72733208fffff 0xbffa72733208ffff

def z616 : W := mkw 0x0200382c090030a4 0x80200382c090030a 0x0000180c00000000 0x00000180c0000000

def z617 : W := mkw 0x1dfdc8043eefa088 0x01dfdc8043eefa08 0x7fffd80c3fffe0cf 0xf7fffd80c3fffe0c

def z618 : W := mkw 0x0b40348000000000 0x00b4034800000000 0x0f80270000000000 0x20f8027000000000

def z619 : W := mkw 0x0080010020800c02 0x00080010020800c0 0x2000000020803f08 0x02000000020803f0

def z620 : W := mkw 0x0438002c120c00a0 0x80438002c120c00a 0x6e38003c3f0e00f9 0x76e38003c3f0e00f

def z621 : W := mkw 0x1dfdc00136efc148 0x01dfdc00136efc14 0xffffc0033fffe7cf 0xfffffc0033fffe7c

def z622 : W := mkw 0x0089400030ab8000 0x00089400030ab800 0x31ffc00038ffc00b 0xf31ffc00038ffc00

def z623 : W := mkw 0x108948457effe3c8 0x2108948457effe3c 0x200000003fffe7c8 0x0200000003fffe7c

def z624 : W := mkw 0x2bc23fd32dd07f57 0x42bc23fd32dd07f5 0xefc03ff33ff03ffc 0xfefc03ff33ff03ff

def z625 : W := mkw 0x22003dc009103e07 0x022003dc009103e0 0xae003fc03f003f0c 0x7ae003fc03f003f0

def z626 : W := mkw 0x06bb7b7f7bbffff6 0xe06bb7b7f7bbffff 0xffffffffffffffff 0xffffffffffffffff

def z627 : W := mkw 0x0200302801001024 0x8020030280100102 0x0000203000001830 0x0000020300000183

def z628 : W := mkw 0x4f76beba89003004 0x04f76beba8900300 0xffffffffff00380f 0xfffffffffff00380

def z629 : W := mkw 0x0000000100004140 0x0000000010000414 0x800000030081c702 0x8800000030081c70

def z630 : W := mkw 0x1dfdc00576efc1c8 0x21dfdc00576efc1c 0x7fffc00fffffc0cb 0xf7fffc00fffffc0c

def z631 : W := mkw 0x4f7cfcecd838a280 0x24f7cfcecd838a28 0x0e58d8ccd8700000 0x40e58d8ccd870000

def z632 : W := mkw 0x0008080418082080 0x0000808041808208 0x0018180c18000000 0x40018180c1800000

def z633 : W := mkw 0x0000000000000000 0x0000000000000000 0x8040c0c3c0000002 0x88040c0c3c000000

def z634 : W := mkw 0x000808041b0c30a4 0x8000808041b0c30a 0x6018180c3f0e38fd 0x56018180c3f0e38f

def z635 : W := mkw 0x2bc83dc43fdc3ea7 0x82bc83dc43fdc3ea 0xafc03fc03ffe3ffc 0xfafc03fc03ffe3ff

def z636 : W := mkw 0x0082031320804d52 0x40082031320804d5 0xe180273320803ffc 0xbe180273320803ff

def z637 : W := mkw 0x4f7ef6bfd028c1c0 0x24f7ef6bfd028c1c 0xdfffffffc009c0c7 0xfdfffffffc009c0c

def z638 : W := mkw 0x0000010000000c02 0x00000010000000c0 0x8000270000003f04 0x08000270000003f0

def z639 : W := mkw 0x0081000020830000 0x0008100002083000 0x71a72030208ff8ff 0xb71a72030208ff8f

def z640 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xb1a727332087df32 0xab1a727332087df3

def z641 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x4e38383c1f000005 0x74e38383c1f00000

def z642 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x4e38183c1f0e00f1 0x44e38183c1f0e00f

def z643 : W := mkw 0x0df7831320834d52 0x40df7831320834d5 0xffffe733208fffff 0xfffffe733208ffff

def z644 : W := mkw 0x2bc03dc56dd07fc7 0x22bc03dc56dd07fc 0xefc03fcffff03fcc 0xfefc03fcffff03fc

def z645 : W := mkw 0x14bfc31332afcd5a 0x414bfc31332afcd5 0xf1bfe733208fffff 0xbf1bfe733208ffff

def z646 : W := mkw 0x0638786c5b3cb2a4 0xa0638786c5b3cb2a 0x0e58d8ccdf700000 0x40e58d8ccdf70000

def z647 : W := mkw 0x1ffdf48036ef8008 0x01ffdf48036ef800 0xbfffffc03fffc00f 0xfbfffffc03fffc00

def z648 : W := mkw 0x0000000000000000 0x0000000000000000 0x4020203000000005 0x3402020300000000

def z649 : W := mkw 0x0000000000000000 0x0000000000000000 0x0058c00000000003 0xd0058c0000000000

def z650 : W := mkw 0x09c8400034e88000 0x009c8400034e8800 0x2fd8c0003ff9c00b 0xf2fd8c0003ff9c00

def z651 : W := mkw 0x143dc000122f8008 0x0143dc000122f800 0x107fc00018ffc00b 0xd107fc00018ffc00

def z652 : W := mkw 0x2bc33fd22dd33e17 0x42bc33fd22dd33e1 0xbfe73ff03ff63f3c 0xfbfe73ff03ff63f3

def z653 : W := mkw 0x0000084008102200 0x0000008400810220 0x0000000018f02708 0x00000000018f0270

def z654 : W := mkw 0x10094000122f8008 0x010094000122f800 0x00000000000fc000 0x000000000000fc00

def z655 : W := mkw 0x0000000100004140 0x0000000010000414 0x000000000089e7c8 0x0000000000089e7c

def z656 : W := mkw 0x0000084008102200 0x0000008400810220 0xc058d8cfd8f0270f 0xdc058d8cfd8f0270

def z657 : W := mkw 0x0000000100004140 0x0000000010000414 0xc058d8cfc089e7cf 0xdc058d8cfc089e7c

def z658 : W := mkw 0x4f7cbcac9b0c30a4 0x84f7cbcac9b0c30a 0x6e78f8fcff0e38fd 0x76e78f8fcff0e38f

def z659 : W := mkw 0x063038280b043024 0x8063038280b04302 0x2e2038303f06383c 0x72e2038303f06383

def z660 : W := mkw 0x0d74800000000000 0x00d7480000000000 0x0e58c00000000000 0x40e58c0000000000

def z661 : W := mkw 0x208009402dd03e07 0x0208009402dd03e0 0xa04018c03ff03f0c 0xda04018c03ff03f0

def z662 : W := mkw 0x143cc000122c8008 0x0143cc000122c800 0x0018c00000000000 0x00018c0000000000

def z663 : W := mkw 0x4d76823a80000000 0x04d76823a8000000 0x5fffc03fc0000003 0xf5fffc03fc000000

def z664 : W := mkw 0x6ff6b7baa5c01c07 0x06ff6b7baa5c01c0 0x3fa7273027001800 0x23fa727302700180

def z665 : W := mkw 0x428337bba0834d52 0x4428337bba0834d5 0xf1a73fffe08fffff 0xbf1a73fffe08ffff

def z666 : W := mkw 0x0081010120834d52 0x40081010120834d5 0xa1802700208ffffc 0xba1802700208ffff

def z667 : W := mkw 0x1d7cc000166c8008 0x01d7cc000166c800 0x0e58c0001ff9c00b 0xd0e58c0001ff9c00

def z668 : W := mkw 0x1d7dc000122f8008 0x01d7dc000122f800 0x1fffc000000fc003 0xf1fffc000000fc00

def z669 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xb1870703208ffffa 0x8b1870703208ffff

def z670 : W := mkw 0x4f76b6bb80004140 0x04f76b6bb8000414 0xdfffffffc089e7cf 0xfdfffffffc089e7c

def z671 : W := mkw 0x000b4217502bc1d0 0x6000b4217502bc1d 0x503fc03fc00fc0f3 0x0503fc03fc00fc0f

def z672 : W := mkw 0x4ff7b6baa0830000 0x04ff7b6baa083000 0xffffffffe08fc00f 0xfffffffffe08fc00

def z673 : W := mkw 0x000808041b0c30a4 0x8000808041b0c30a 0x602020303f0e38fd 0x3602020303f0e38f

def z674 : W := mkw 0x2000094009103e07 0x02000094009103e0 0x0000000000003f00 0x00000000000003f0

def z675 : W := mkw 0x4f74b4a880000000 0x04f74b4a88000000 0x0e00000000000000 0x00e0000000000000

def z676 : W := mkw 0x0081000020830000 0x0008100002083000 0x118700000081c002 0x8118700000081c00

def z677 : W := mkw 0x14b9400036ef8008 0x014b9400036ef800 0x2e3800003fffc009 0x72e3800003fffc00

def z678 : W := mkw 0x3fffffd33fffff5f 0x43fffffd33fffff5 0xfffffff33fffffff 0xffffffff33ffffff

def z679 : W := mkw 0x063838001b0c3004 0x0063838001b0c300 0x2e3838003f0e380d 0x72e3838003f0e380

def z680 : W := mkw 0x0630302800000000 0x0063030280000000 0x6e38383c200e38fd 0x76e38383c200e38f

def z681 : W := mkw 0x1dfdc10136efcd5a 0x41dfdc10136efcd5 0x3fffc0003ffffffb 0xf3fffc0003ffffff

def z682 : W := mkw 0x0000400000208000 0x0000040000020800 0x0040c00000f1c002 0x80040c00000f1c00

def z683 : W := mkw 0x1ffdb82c3fcf30ac 0x81ffdb82c3fcf30a 0x7fbf383c3f0e38fd 0x77fbf383c3f0e38f

def z684 : W := mkw 0x008909053b8f7df6 0xc008909053b8f7df 0x200000003f8ffff8 0x0200000003f8ffff

def z685 : W := mkw 0x420a7effd838e3c0 0x2420a7effd838e3c 0xc058ffffd8f9e7cf 0xdc058ffffd8f9e7c

def z686 : W := mkw 0x000848445838a280 0x2000848445838a28 0x8058d8ccd8f0270c 0xd8058d8ccd8f0270

def z687 : W := mkw 0x0d74800000000000 0x00d7480000000000 0xdfffd8cfc0000007 0xfdfffd8cfc000000

def z688 : W := mkw 0x1df7831326c74d5a 0x41df7831326c74d5 0xffa72733278fffff 0xbffa72733278ffff

def z689 : W := mkw 0x0002021200000000 0x0000202120000000 0x11a7273000000000 0x211a727300000000

def z690 : W := mkw 0x0430000002040000 0x0043000000204000 0x2e20000027060000 0x22e2000002706000

def z691 : W := mkw 0x0630302800000000 0x0063030280000000 0x0e18180c00000000 0x40e18180c0000000

def z692 : W := mkw 0x420034a880000000 0x0420034a88000000 0x000018ccc0000000 0x0000018ccc000000

def z693 : W := mkw 0x0200348000000000 0x0020034800000000 0x80003fc000000004 0x080003fc00000000

def z694 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x2e58c0003fffc008 0x42e58c0003fffc00

def z695 : W := mkw 0x2bc13dc12dd37f57 0x42bc13dc12dd37f5 0xafc03fc03ffffffc 0xfafc03fc03ffffff

def z696 : W := mkw 0x0003021300034150 0x4000302130003415 0x70272033200ff8ff 0x370272033200ff8f

def z697 : W := mkw 0x494eced7d838e3c0 0x2494eced7d838e3c 0xd1dfdfcfd8f9e7cf 0xdd1dfdfcfd8f9e7c

def z698 : W := mkw 0x0008080418082080 0x0000808041808208 0x6038383c380e38fd 0x76038383c380e38f

def z699 : W := mkw 0x208009402dd03e07 0x0208009402dd03e0 0xa18027003ff03f0c 0xba18027003ff03f0

def z700 : W := mkw 0x5f7ef6ba966c8008 0x05f7ef6ba966c800 0xdfffffffdf700007 0xfdfffffffdf70000

def z701 : W := mkw 0x2ff035a827c41c27 0x82ff035a827c41c2 0x2fa0273027061830 0x22fa027302706183

def z702 : W := mkw 0x00080004120c00a0 0x800080004120c00a 0x00000000000e00f0 0x000000000000e00f

def z703 : W := mkw 0x0000000100004140 0x0000000010000414 0x400000030009c0c3 0x0400000030009c0c

def z704 : W := mkw 0x1df5c00026e78008 0x01df5c00026e7800 0x3fe7c00027f7c002 0xa3fe7c00027f7c00

def z705 : W := mkw 0x1dfdc8457effe3c8 0x21dfdc8457effe3c 0x3fffc0003fffe7cb 0xf3fffc0003fffe7c

def z706 : W := mkw 0x000840455038c3c0 0x2000840455038c3c 0xc058c0cfc0f9c7c3 0x8c058c0cfc0f9c7c

def z707 : W := mkw 0x143fc217522fc1d8 0x6143fc217522fc1d 0x503fc03fc00fc0f3 0x0503fc03fc00fc0f

def z708 : W := mkw 0x008b4b5678bbae92 0x6008b4b5678bbae9 0x31fffffcf8761830 0x631fffffcf876183

def z709 : W := mkw 0x4d7686ba80000000 0x04d7686ba8000000 0xd1ffdfffc0000007 0xdd1ffdfffc000000

def z710 : W := mkw 0x0630302803041024 0x8063030280304102 0x6e38383c270e38fd 0x76e38383c270e38f

def z711 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0xdfffffffd8f0000f 0xfdfffffffd8f0000

def z712 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x7fbf383c3f0e38ff 0xf7fbf383c3f0e38f

def z713 : W := mkw 0x163cf82c1b2cb0ac 0x8163cf82c1b2cb0a 0x6e38f83c3f0e38fd 0x76e38f83c3f0e38f

def z714 : W := mkw 0x0208382c1b0c30a4 0x80208382c1b0c30a 0x6e00383c3f0e38fc 0x76e00383c3f0e38f

def z715 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0x9fffdfcfc0000003 0xf9fffdfcfc000000

def z716 : W := mkw 0x6bc4bdc0add03e07 0x06bc4bdc0add03e0 0xafc0ffc0fff03f0c 0xfafc0ffc0fff03f0

def z717 : W := mkw 0x1dfdc10036ef8c0a 0x01dfdc10036ef8c0 0xbfffc7003fffc70b 0xfbfffc7003fffc70

def z718 : W := mkw 0x0438002c120c00a0 0x80438002c120c00a 0x6e38203c3f0e38fd 0x76e38203c3f0e38f

def z719 : W := mkw 0x1bc5f82c2de3b0ac 0x81bc5f82c2de3b0a 0x51c7f83c00f1f8f6 0x851c7f83c00f1f8f

def z720 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x3fa700003fffc00b 0xb3fa700003fffc00

def z721 : W := mkw 0x4f76b6ba82040000 0x04f76b6ba8204000 0xffffffffe7060007 0xfffffffffe706000

def z722 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xbfe73fc03ff03f0f 0xfbfe73fc03ff03f0

def z723 : W := mkw 0x46383cac9b0c30a4 0x846383cac9b0c30a 0x6e3838fcff0e38fd 0x76e3838fcff0e38f

def z724 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x7fffc0003fffe0cf 0xf7fffc0003fffe0c

def z725 : W := mkw 0x64b68b7aadd03e07 0x064b68b7aadd03e0 0x703fc03ffff03f0b 0x0703fc03ffff03f0

def z726 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xafc03fc03f703f04 0x6afc03fc03f703f0

def z727 : W := mkw 0x0208380419083084 0x0020838041908308 0x6e38383c3f0e38fd 0x76e38383c3f0e38f

def z728 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0xe058d8cff8ffffff 0xde058d8cff8fffff

def z729 : W := mkw 0x0638782c1b2cb0a4 0x80638782c1b2cb0a 0x6e78f83c3f7e38fd 0x76e78f83c3f7e38f

def z730 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xf1a73fffe08fffff 0xbf1a73fffe08ffff

def z731 : W := mkw 0x2bc8758575e8ddc7 0x22bc8758575e8ddc 0x6f98e70fe709d8c3 0x26f98e70fe709d8c

def z732 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xafc03fc03ffe3ffc 0xfafc03fc03ffe3ff

def z733 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0xd1ffffffc0000007 0x8d1ffffffc000000

def z734 : W := mkw 0x2df805ec36dc0ea3 0x82df805ec36dc0ea 0xc1f807fc00fe07f1 0x8c1f807fc00fe07f

def z735 : W := mkw 0x494e8e969b0c30a4 0x8494e8e969b0c30a 0xb1c7c7c3ff0e38fa 0x8b1c7c7c3ff0e38f

def z736 : W := mkw 0x543fc23fd22fc1c8 0x2543fc23fd22fc1c 0x503fc03fc00fc0c3 0x0503fc03fc00fc0c

def z737 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x3fffe0003ffff80f 0xf3fffe0003ffff80

def z738 : W := mkw 0x0630302c030410a4 0x80630302c030410a 0x6e20203c270618f0 0x26e20203c270618f

def z739 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x6e38383c270e38f5 0x26e38383c270e38f

def z740 : W := mkw 0x5dfdc028b6ef8008 0x05dfdc028b6ef800 0x3fffc00cffffc00b 0xf3fffc00cffffc00

def z741 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xafd8ffc03ff03f0f 0xfafd8ffc03ff03f0

def z742 : W := mkw 0x14bdc10032af8c0a 0x014bdc10032af8c0 0xb1bfe700208fff0f 0xbb1bfe700208fff0

def z743 : W := mkw 0x69c787d3a4d34f53 0x469c787d3a4d34f5 0x91c7c7c3c0f1c702 0x891c7c7c3c0f1c70

def z744 : W := mkw 0x063070694334d364 0xa063070694334d36 0xae60e0f3e7f7df32 0xaae60e0f3e7f7df3

def z745 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0xffffffffe0061837 0xfffffffffe006183

def z746 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x3fdfc0003ff1c00a 0xf3fdfc0003ff1c00

def z747 : W := mkw 0x528b76bab6ef8008 0x0528b76bab6ef800 0xe0003fffffffc00c 0x0e0003fffffffc00

def z748 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xd1a72733008ffff7 0x8d1a72733008ffff

def z749 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0x9fffffffc0000002 0xe9fffffffc000000

def z750 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0xee38383f3f0e38ff 0xfee38383f3f0e38f

def z751 : W := mkw 0x2bc13dc02dd33e17 0x42bc13dc02dd33e1 0xafc03fc03ff63f3c 0xfafc03fc03ff63f3

def z752 : W := mkw 0x4f76b6ba82040020 0x84f76b6ba8204002 0xdfffffffc0060037 0xfdfffffffc006003

def z753 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0x9fdfffcfc0000006 0xf9fdfffcfc000000

def z754 : W := mkw 0x1d7ec313166ccd5a 0x41d7ec313166ccd5 0xce58e7331f703ff4 0x4ce58e7331f703ff

def z755 : W := mkw 0x4f76b6ba83041024 0x84f76b6ba8304102 0xffffffffe70e38ff 0xfffffffffe70e38f

def z756 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x7fffc0303fffc0fb 0xf7fffc0303fffc0f

def z757 : W := mkw 0x0200382c090030a4 0x80200382c090030a 0x6e20383c3f0e38fd 0x76e20383c3f0e38f

def z758 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x3fffd8ccffffc00b 0xf3fffd8ccffffc00

def z759 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0x8fc03fc01ff03f04 0xc8fc03fc01ff03f0

def z760 : W := mkw 0x22023fff09107ff7 0xc22023fff09107ff 0xc0003fff00003ff4 0x0c0003fff00003ff

def z761 : W := mkw 0x14b9400036ef8008 0x014b9400036ef800 0x3fbf00003fffc00b 0xf3fbf00003fffc00

def z762 : W := mkw 0x06bb3b3f3b8f7df6 0xc06bb3b3f3b8f7df 0x9f9f1f0f1f81c702 0xc9f9f1f0f1f81c70

def z763 : W := mkw 0x1dfdc02c36ef80a8 0x81dfdc02c36ef80a 0x3fffc00c3fffc00b 0xf3fffc00c3fffc00

def z764 : W := mkw 0x4636b6ba80000000 0x04636b6ba8000000 0xd1bfffffc0000007 0xbd1bfffffc000000

def z765 : W := mkw 0x19cdc00036ef8008 0x019cdc00036ef800 0x3fc7c0003fffc00a 0xf3fc7c0003fffc00

def z766 : W := mkw 0x1dfdc48036ef8008 0x01dfdc48036ef800 0xbfffc7c03fffc00b 0xfbfffc7c03fffc00

def z767 : W := mkw 0x0638302c130c10a4 0x80638302c130c10a 0x2e202030270e18f0 0x22e202030270e18f

def z768 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0xc1d8ffcfd8f9e7cf 0xfc1d8ffcfd8f9e7c

def z769 : W := mkw 0x000848455938f3c4 0x2000848455938f3c 0xe058d8cffff9ffcf 0xde058d8cffff9ffc

def z770 : W := mkw 0x0638786c1b3cb2a4 0x80638786c1b3cb2a 0xee78f8fc3fffffff 0xfee78f8fc3ffffff

def z771 : W := mkw 0x008949457bbffff6 0xe008949457bbffff 0x200000003ffffff8 0x0200000003ffffff

def z772 : W := mkw 0x2bc03de82dd03e07 0x02bc03de82dd03e0 0xefc03ffc3ff03f0c 0xfefc03ffc3ff03f0

def z773 : W := mkw 0x4b46b6ba80000000 0x04b46b6ba8000000 0xd1dfffffc0000007 0xdd1dfffffc000000

def z774 : W := mkw 0x0bc0358024c00c02 0x00bc0358024c00c0 0xafc03fc03ff03f0c 0xfafc03fc03ff03f0

def z775 : W := mkw 0x09c9400034eb8000 0x009c9400034eb800 0x3fffc0003fffc00b 0xf3fffc0003fffc00

def z776 : W := mkw 0x0638302c130c10a4 0x80638302c130c10a 0x6e38203c3f0e18f9 0x76e38203c3f0e18f

def z777 : W := mkw 0x2b433ed30d537355 0x42b433ed30d53735 0x5e6718f31f7fc0f3 0x45e6718f31f7fc0f

def z778 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0xffffc0033fffc00f 0xfffffc0033fffc00

def z779 : W := mkw 0x0638782c5b2cb0a4 0xa0638782c5b2cb0a 0x6e38f83cff0e38fd 0x76e38f83cff0e38f

def z780 : W := mkw 0x0b42369200000000 0x00b4236920000000 0xdfffffffc0000007 0xfdfffffffc000000

def z781 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xafc0ffc3fff03f0e 0xfafc0ffc3fff03f0

def z782 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0x8fc03fc01ff00704 0xf8fc03fc01ff0070

def z783 : W := mkw 0x19c5c00024e38008 0x019c5c00024e3800 0x3fe7c0003fffc00b 0xf3fe7c0003fffc00

def z784 : W := mkw 0x000848455a3ce3c0 0x2000848455a3ce3c 0xe058d8cfffffe7cf 0xde058d8cfffffe7c

def z785 : W := mkw 0x09c009402cd02e02 0x009c009402cd02e0 0xafc03fc03ff03f0c 0xfafc03fc03ff03f0

def z786 : W := mkw 0x2bc13dc02dd33e07 0x02bc13dc02dd33e0 0xafc03fc03fffff0c 0xfafc03fc03fffff0

def z787 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xf1e73ff3208fffff 0xff1e73ff3208ffff

def z788 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xf1a72733200ffff7 0x2f1a72733200ffff

def z789 : W := mkw 0x0003031300034d52 0x40003031300034d5 0xd1a72733000ffff7 0xbd1a72733000ffff

def z790 : W := mkw 0x02023b7f49107ff6 0xe02023b7f49107ff 0xc0003fffc0003ff4 0x0c0003fffc0003ff

def z791 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0xdfffffffc080270f 0xfdfffffffc080270

def z792 : W := mkw 0x2bc03de82dd03e27 0x82bc03de82dd03e2 0xafc03ff03ff03f3c 0xfafc03ff03ff03f3

def z793 : W := mkw 0x0630302803041024 0x8063030280304102 0x2e202030270e38f8 0x22e202030270e38f

def z794 : W := mkw 0x0430000002040000 0x0043000000204000 0x6e202030270e38fd 0x36e202030270e38f

def z795 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xafd8ffccfff03f0c 0xfafd8ffccfff03f0

def z796 : W := mkw 0x29c00dc02cd02e03 0x029c00dc02cd02e0 0xafc01fc03ff0270c 0xfafc01fc03ff0270

def z797 : W := mkw 0x1d7dc000166f8008 0x01d7dc000166f800 0x1e5fc0001f71c002 0x41e5fc0001f71c00

def z798 : W := mkw 0x09c2031324c04d52 0x409c2031324c04d5 0xefc027333ff03ffc 0xfefc027333ff03ff

def z799 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xafe03fc03ffe3f0d 0xfafe03fc03ffe3f0

def z800 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xf1ffe733208fffff 0xff1ffe733208ffff

def z801 : W := mkw 0x543fc23b922fc158 0x4543fc23b922fc15 0x503fc03fc00fc0f3 0x0503fc03fc00fc0f

def z802 : W := mkw 0x06383cac1b0c30a4 0x806383cac1b0c30a 0xee383ffc3f0e38fd 0x7ee383ffc3f0e38f

def z803 : W := mkw 0x208949457dfbffd7 0x6208949457dfbffd 0x200000003ffffff8 0x0200000003ffffff

def z804 : W := mkw 0x0630302803041024 0x8063030280304102 0x6e202030270e18f1 0x26e202030270e18f

def z805 : W := mkw 0x2bc4bdc02dd03e07 0x02bc4bdc02dd03e0 0xbfc7ffc03ff03f0e 0xfbfc7ffc03ff03f0

def z806 : W := mkw 0x363dfdc01b3fbe0f 0x0363dfdc01b3fbe0 0x903fffc0000fff07 0x0903fffc0000fff0

def z807 : W := mkw 0x0630382c0b0430a4 0x80630382c0b0430a 0x6e20383c3f0638fc 0x76e20383c3f0638f

def z808 : W := mkw 0x4f7efeffd838e3c0 0x24f7efeffd838e3c 0x1fa7273018f9e7c8 0x21fa7273018f9e7c

def z809 : W := mkw 0x0df5800024c30000 0x00df5800024c3000 0x3fffc0003fffc00b 0xf3fffc0003fffc00

def z810 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0x8058d8cfd8f9e7ca 0xc8058d8cfd8f9e7c

def z811 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0x8fc01fc01ff0270c 0xd8fc01fc01ff0270

def z812 : W := mkw 0x1dfdc10036ef8c1a 0x41dfdc10036ef8c1 0x3fffc0003fffd83b 0xf3fffc0003fffd83

def z813 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xafc03fc03ff01f00 0xeafc03fc03ff01f0

def z814 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x3fe7c0003fffc00a 0xa3fe7c0003fffc00

def z815 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x3fdfc0003fffc00a 0xc3fdfc0003fffc00

def z816 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0xdfffffffc00e00f7 0xfdfffffffc00e00f

def z817 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0xc078f8ffd8f9e7cf 0xfc078f8ffd8f9e7c

def z818 : W := mkw 0x4f76b6ba84400000 0x04f76b6ba8440000 0xdfffffffdf700007 0xfdfffffffdf70000

def z819 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xaf803fc03ff03f0c 0x2af803fc03ff03f0

def z820 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0xc058d8cfd8f9e7cc 0x4c058d8cfd8f9e7c

def z821 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0x5fffffffc0000003 0x65fffffffc000000

def z822 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xefc03ff03ff03ffc 0xfefc03ff03ff03ff

def z823 : W := mkw 0x1df5c00026e78008 0x01df5c00026e7800 0x3fe7c0003ff7c00a 0xf3fe7c0003ff7c00

def z824 : W := mkw 0x000040414030c340 0x2000040414030c34 0x8058d8cfc0f1c702 0xc8058d8cfc0f1c70

def z825 : W := mkw 0x443ec23fd22cc1e0 0xa443ec23fd22cc1e 0x503fc03fc00fc0f3 0x0503fc03fc00fc0f

def z826 : W := mkw 0x0638782c1b2cb0a4 0x80638782c1b2cb0a 0x6e38383c3ffff8fd 0x76e38383c3ffff8f

def z827 : W := mkw 0x2b403dc00d503e07 0x02b403dc00d503e0 0x8fc03fc01f703f04 0xf8fc03fc01f703f0

def z828 : W := mkw 0x000048454830e3c0 0x2000048454830e3c 0xc058d8cfc0f1e7c7 0xdc058d8cfc0f1e7c

def z829 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x6e38203c3f0e38f9 0x26e38203c3f0e38f

def z830 : W := mkw 0x22023fd309107f57 0x422023fd309107f5 0x80003fc300003f04 0x080003fc300003f0

def z831 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x3fffc0003fffc008 0x63fffc0003fffc00

def z832 : W := mkw 0x1dfdc10036ef8c0a 0x01dfdc10036ef8c0 0x3fffe7003fffd80b 0xf3fffe7003fffd80

def z833 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x6e38383c3f0638f4 0x66e38383c3f0638f

def z834 : W := mkw 0x1df588456ed763c8 0x21df588456ed763c 0xffa718cfe70627c4 0x2ffa718cfe70627c

def z835 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0xc058d8cfd8f9c7c3 0xcc058d8cfd8f9c7c

def z836 : W := mkw 0x6ff7b7baa5c31c17 0x46ff7b7baa5c31c1 0x3fa7273027061830 0x23fa727302706183

def z837 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0x2fc03fc03ff03f08 0x62fc03fc03ff03f0

def z838 : W := mkw 0x5f76b6ba86440008 0x05f76b6ba8644000 0xdfffffffc7000007 0xfdfffffffc700000

def z839 : W := mkw 0x420236ba80000000 0x0420236ba8000000 0xd1ffffffc0000007 0xfd1ffffffc000000

def z840 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0xefb83f3c3f0e38fd 0xfefb83f3c3f0e38f

def z841 : W := mkw 0x2bc13dc02dd33e07 0x02bc13dc02dd33e0 0xffe73ff03fffffff 0xfffe73ff03ffffff

def z842 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xefc03fc33ff03f0f 0xfefc03fc33ff03f0

def z843 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0xdfbfffffc0000007 0x2dfbfffffc000000

def z844 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xf1bfe73fe08fffff 0xbf1bfe73fe08ffff

def z845 : W := mkw 0x26383cec1b1c32a5 0x826383cec1b1c32a 0x6e3838fc3f0e38fd 0x76e3838fc3f0e38f

def z846 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x1fdfc0001ff9c00b 0xd1fdfc0001ff9c00

def z847 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0xbfffc0c3ffffc00b 0xfbfffc0c3ffffc00

def z848 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x2e2038303f0e38fc 0x72e2038303f0e38f

def z849 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xafc01fc03ff03f08 0xcafc01fc03ff03f0

def z850 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xae403fc03ff03f0c 0x4ae403fc03ff03f0

def z851 : W := mkw 0x62023fffc9107fc7 0x262023fffc9107fc 0xc0003fffc0003fc4 0x0c0003fffc0003fc

def z852 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xb1a72730208ffffc 0xbb1a72730208ffff

def z853 : W := mkw 0x3bc5bdc02dd33e0f 0x03bc5bdc02dd33e0 0xbfc73fc03ff03f0c 0xfbfc73fc03ff03f0

def z854 : W := mkw 0x000040414030c340 0x2000040414030c34 0xc058d8cfc0f9e7cf 0xdc058d8cfc0f9e7c

def z855 : W := mkw 0x000048414830e340 0x2000048414830e34 0xc058d8cfd8f1e70f 0xdc058d8cfd8f1e70

def z856 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0xc058f8ffd8f9ffff 0xdc058f8ffd8f9fff

def z857 : W := mkw 0x14bdc00036ef8008 0x014bdc00036ef800 0x3e3fc0003fffc00b 0x73e3fc0003fffc00

def z858 : W := mkw 0x19c7c35364f3cf5a 0x619c7c35364f3cf5 0x91c7c7c3c0f1c702 0x891c7c7c3c0f1c70

def z859 : W := mkw 0x143fc23f122fc1f8 0xc143fc23f122fc1f 0x503fc03f000fc0f3 0x0503fc03f000fc0f

def z860 : W := mkw 0x0638782c1b2cb0a4 0x80638782c1b2cb0a 0xee78f8fffffff8ff 0xfee78f8fffffff8f

def z861 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0xdfffffffc089c00f 0xfdfffffffc089c00

def z862 : W := mkw 0x1dfdc02836ef8028 0x81dfdc02836ef802 0x3fffc0303fffc03b 0xf3fffc0303fffc03

def z863 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0xdfffffffc0000004 0x6dfffffffc000000

def z864 : W := mkw 0x4946869280000000 0x0494686928000000 0x91dfdfcfc0000002 0xc91dfdfcfc000000

def z865 : W := mkw 0x0638782c1b2cb0a4 0x80638782c1b2cb0a 0x6e38f83c3f0ff8ff 0x76e38f83c3f0ff8f

def z866 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x3fbfc0003fffc00b 0x23fbfc0003fffc00

def z867 : W := mkw 0x0000000000000000 0x0000000000000000 0x6e2020303f0e38fd 0x76e2020303f0e38f

def z868 : W := mkw 0x4946869280000000 0x0494686928000000 0xd1ffffffc0000007 0xfd1ffffffc000000

def z869 : W := mkw 0x0d76821200000000 0x00d7682120000000 0xdfffffffc0000007 0xfdfffffffc000000

def z870 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x6e78f8fcff0e38fd 0x76e78f8fcff0e38f

def z871 : W := mkw 0x6bc03de8add03e07 0x06bc03de8add03e0 0xafc03fccfff03f0c 0xfafc03fccfff03f0

def z872 : W := mkw 0x3dfdc58036ef8c0b 0x03dfdc58036ef8c0 0x3fffc7003fffc00b 0xf3fffc7003fffc00

def z873 : W := mkw 0x1dfdc00436ef80a8 0x81dfdc00436ef80a 0x3fffc0003fffc0fb 0xf3fffc0003fffc0f

def z874 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xafc01fc03ff00708 0xfafc01fc03ff0070

def z875 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0xbfffd8c03fffc00f 0xfbfffd8c03fffc00

def z876 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0xdfffffffc00038f7 0xfdfffffffc00038f

def z877 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0xffffffffff00000f 0xfffffffffff00000

def z878 : W := mkw 0x1df5800026c70008 0x01df5800026c7000 0x3fe700003fffc00b 0xf3fe700003fffc00

def z879 : W := mkw 0x000848401838a200 0x0000848401838a20 0xc058d8cfd8f9e70f 0xdc058d8cfd8f9e70

def z880 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x6e38183c3f0e38f9 0x46e38183c3f0e38f

def z881 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0xc058d8cfd8f1e7c6 0xcc058d8cfd8f1e7c

def z882 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x3fffc0003ffff8fb 0xf3fffc0003ffff8f

def z883 : W := mkw 0x0002021200000000 0x0000202120000000 0xd1dfdfcfc0000007 0xdd1dfdfcfc000000

def z884 : W := mkw 0x4ff5b5a9a0834d52 0x44ff5b5a9a0834d5 0x2e58d8cce08ffff8 0x42e58d8cce08ffff

def z885 : W := mkw 0x0638786c5b3cb2a4 0xa0638786c5b3cb2a 0x6e38383c3f7e38fd 0x76e38383c3f7e38f

def z886 : W := mkw 0x0638386c1b1c32a4 0x80638386c1b1c32a 0x6e38383c3ffe3ffd 0x76e38383c3ffe3ff

def z887 : W := mkw 0x063038280b043024 0x8063038280b04302 0x6e2038303f0e38fd 0x76e2038303f0e38f

def z888 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0xee7838fc3f0e38fd 0xfee7838fc3f0e38f

def z889 : W := mkw 0x1dfdc10036ef8c0a 0x01dfdc10036ef8c0 0x3fffc0003fffff0b 0xf3fffc0003fffff0

def z890 : W := mkw 0x29c00dc02dd03e07 0x029c00dc02dd03e0 0xafc007c03ff03f08 0xfafc007c03ff03f0

def z891 : W := mkw 0x0083031320834d52 0x40083031320834d5 0x71a72730208ffffd 0x371a72730208ffff

def z892 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xefc03fcffff03f0c 0xfefc03fcffff03f0

def z893 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xefe03ff03ff03f0d 0xfefe03ff03ff03f0

def z894 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0xee38383c3f8e3ffd 0xfee38383c3f8e3ff

def z895 : W := mkw 0x42023effc91073e4 0xa42023effc91073e 0xc0003fffc0003ff4 0x0c0003fffc0003ff

def z896 : W := mkw 0x0083031320834d52 0x40083031320834d5 0x31a72730208ffffb 0xb31a72730208ffff

def z897 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0xdfffdfffc0000003 0xcdfffdfffc000000

def z898 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0xdfdfdfcfc0000007 0xddfdfdfcfc000000

def z899 : W := mkw 0x09c1000024c30000 0x009c1000024c3000 0x3fc700003ff1c00a 0xf3fc700003ff1c00

def z900 : W := mkw 0x2bc03dec2dd03ea7 0x82bc03dec2dd03ea 0xafc03fcc3ff03f0c 0xfafc03fcc3ff03f0

def z901 : W := mkw 0x0638302c130c10a4 0x80638302c130c10a 0x6e38203c270e38fd 0x36e38203c270e38f

def z902 : W := mkw 0x0d7cc000122c8000 0x00d7cc000122c800 0x3fffc0003fffc00b 0xf3fffc0003fffc00

def z903 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0xe058f8cff8f9ffcf 0xfe058f8cff8f9ffc

def z904 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0xc078d8ffd8ffe7ff 0xdc078d8ffd8ffe7f

def z905 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0xffffffffe00e000f 0xfffffffffe00e000

def z906 : W := mkw 0x0638786c5b3cb2a4 0xa0638786c5b3cb2a 0xee78f8ffff7e38ff 0xfee78f8ffff7e38f

def z907 : W := mkw 0x0638386c1b1c32a4 0x80638386c1b1c32a 0xee78f8fffffe3fff 0xfee78f8fffffe3ff

def z908 : W := mkw 0x2b403dc00d503e07 0x02b403dc00d503e0 0xae403fc03f703f0c 0x7ae403fc03f703f0

def z909 : W := mkw 0x29c347d364f3cf53 0x629c347d364f3cf5 0x91c7c7c3c0f1c702 0x891c7c7c3c0f1c70

def z910 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0x2f803f003ff03f0c 0x72f803f003ff03f0

def z911 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0xee58d8cffff9e7cf 0xfee58d8cffff9e7c

def z912 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xafc03fc03ff9ff0f 0xfafc03fc03ff9ff0

def z913 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xffa727333f8fffff 0xfffa727333f8ffff

def z914 : W := mkw 0x0083031324c34d52 0x40083031324c34d5 0xf1a727333fffffff 0xbf1a727333ffffff

def z915 : W := mkw 0x0b403cc009103204 0x00b403cc00910320 0xafc03fc03ff03f0c 0xfafc03fc03ff03f0

def z916 : W := mkw 0x62023ffb89107f57 0x462023ffb89107f5 0xc0003fffc0003ff4 0x0c0003fffc0003ff

def z917 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0xc058d8cfc0f9e7c7 0x8c058d8cfc0f9e7c

def z918 : W := mkw 0x0630382c0b0430a4 0x80630382c0b0430a 0x6e38383c270638f5 0x76e38383c270638f

def z919 : W := mkw 0x308949457fffffcf 0x2308949457fffffc 0x200000003fffffc8 0x0200000003fffffc

def z920 : W := mkw 0x143fc213122fc158 0x4143fc213122fc15 0x103fc003000fc003 0x0103fc003000fc00

def z921 : W := mkw 0x000840011028c140 0x0000840011028c14 0xc058d8cfd8f9e7cf 0xdc058d8cfd8f9e7c

def z922 : W := mkw 0x0200300001001004 0x0020030000100100 0x6e202030270e38fd 0x36e202030270e38f

def z923 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0xbfffe7003fffc00f 0xfbfffe7003fffc00

def z924 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x6e78383c3ffe38fd 0xf6e78383c3ffe38f

def z925 : W := mkw 0x22803dc02dd03e07 0x022803dc02dd03e0 0xae003fc03ff03f0c 0x7ae003fc03ff03f0

def z926 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x3fffc0003ff7c002 0xe3fffc0003ff7c00

def z927 : W := mkw 0x0638386c1b1c32a4 0x80638386c1b1c32a 0xee3838fc3f0e3ffd 0x7ee3838fc3f0e3ff

def z928 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0xdfdfffffc0000006 0xcdfdfffffc000000

def z929 : W := mkw 0x19c9400036ef8008 0x019c9400036ef800 0x3fe700003fffc00b 0xf3fe700003fffc00

def z930 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xf1a72733208ffffc 0x2f1a72733208ffff

def z931 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xb1a72733208ffffa 0xab1a72733208ffff

def z932 : W := mkw 0x2b403dc00d503e07 0x02b403dc00d503e0 0x8e403fc01ff03f0c 0xd8e403fc01ff03f0

def z933 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xf1e7273338ffffff 0xff1e7273338fffff

def z934 : W := mkw 0x0632323a00000000 0x00632323a0000000 0xdfffffffc0000007 0xfdfffffffc000000

def z935 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xefd83fcc3ff03f0d 0xfefd83fcc3ff03f0

def z936 : W := mkw 0x0638786c5b3cb2a4 0xa0638786c5b3cb2a 0x6e78f8fcfffff8ff 0xf6e78f8fcfffff8f

def z937 : W := mkw 0x063838001b0c3004 0x0063838001b0c300 0x6e3838303f0e38fd 0x76e3838303f0e38f

def z938 : W := mkw 0x0089494578bbefd2 0x60089494578bbefd 0x0000000018f9e7c8 0x00000000018f9e7c

def z939 : W := mkw 0x2bc03dc42dd03ea7 0x82bc03dc42dd03ea 0xafc03fc03ff03ffc 0xfafc03fc03ff03ff

def z940 : W := mkw 0x2bc13dc02dd33e07 0x02bc13dc02dd33e0 0xbfe73fc03ff63f0c 0xfbfe73fc03ff63f0

def z941 : W := mkw 0x0bc03cc02cd02200 0x00bc03cc02cd0220 0xafc03fc03ff0270c 0xfafc03fc03ff0270

def z942 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x2e38383c3f0e38f8 0x62e38383c3f0e38f

def z943 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x1fffc0001ff1c003 0xf1fffc0001ff1c00

def z944 : W := mkw 0x0df9000036cf0000 0x00df9000036cf000 0x3fff00003fffc00b 0xf3fff00003fffc00

def z945 : W := mkw 0x043808041a0c2080 0x0043808041a0c208 0x6e38383c3f0e38fd 0x76e38383c3f0e38f

def z946 : W := mkw 0x04b9400032af8000 0x004b9400032af800 0x3fffc0003fffc00b 0xf3fffc0003fffc00

def z947 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x6e78f83c3f0e38ff 0xf6e78f83c3f0e38f

def z948 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x3fe700003fffc008 0xf3fe700003fffc00

def z949 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0xe078d8cff8ffe7cf 0xfe078d8cff8ffe7c

def z950 : W := mkw 0x020838041b0c30a4 0x8020838041b0c30a 0x6e2038303f0e38fd 0x76e2038303f0e38f

def z951 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0xffffffffe000380f 0xfffffffffe000380

def z952 : W := mkw 0x4f7cfcecdb3cb2a4 0xa4f7cfcecdb3cb2a 0x0e58d8ccdf700000 0x40e58d8ccdf70000

def z953 : W := mkw 0x0638386c1b1c32a4 0x80638386c1b1c32a 0x6e7838fc3f7e38fd 0x76e7838fc3f7e38f

def z954 : W := mkw 0x2b403cc00d503205 0x02b403cc00d50320 0x8fc03fc01ff0270c 0xf8fc03fc01ff0270

def z955 : W := mkw 0x143dc000122f8008 0x0143dc000122f800 0x3e7fc0003fffc00b 0xf3e7fc0003fffc00

def z956 : W := mkw 0x19c5c00024e38008 0x019c5c00024e3800 0x1fc7c0001ff1c002 0xc1fc7c0001ff1c00

def z957 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x6e38383c3f0e18f1 0x66e38383c3f0e18f

def z958 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x7fffe0303fffc00f 0xf7fffe0303fffc00

def z959 : W := mkw 0x1d7dc000166f8008 0x01d7dc000166f800 0x1e7fc0001fffc00b 0xd1e7fc0001fffc00

def z960 : W := mkw 0x1d7dc000166f8008 0x01d7dc000166f800 0x3e7fc0003f7fc00b 0x73e7fc0003f7fc00

def z961 : W := mkw 0x2bc035c024d00e03 0x02bc035c024d00e0 0xafc03fc03ff0070c 0xfafc03fc03ff0070

def z962 : W := mkw 0x1d7cc000166c8008 0x01d7cc000166c800 0x1fffc0001ff9c00b 0xf1fffc0001ff9c00

def z963 : W := mkw 0x22023fd749107fd7 0x622023fd749107fd 0xc0003fffc0003ff4 0x0c0003fffc0003ff

def z964 : W := mkw 0x000848455938f3e4 0xa000848455938f3e 0xc058d8cfd8f9ffff 0xdc058d8cfd8f9fff

def z965 : W := mkw 0x1dfdc10036ef8c0a 0x01dfdc10036ef8c0 0xffffe7303fffffff 0xfffffe7303ffffff

def z966 : W := mkw 0x063cb82c1b0c30a4 0x8063cb82c1b0c30a 0x7e3ff83c3f0e38ff 0x77e3ff83c3f0e38f

def z967 : W := mkw 0x0630382c0b0430a4 0x80630382c0b0430a 0x6e20383c270e38fd 0x36e20383c270e38f

def z968 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x3e7fc0003fffc00b 0x43e7fc0003fffc00

def z969 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0xbfffc0003fffe70f 0xfbfffc0003fffe70

def z970 : W := mkw 0x39c7c7d324f3cf5b 0x439c7c7d324f3cf5 0x91c7c7c300f1c702 0x891c7c7c300f1c70

def z971 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x6e20383c3f0e38fc 0x26e20383c3f0e38f

def z972 : W := mkw 0x5ff7b7baa6c70c1a 0x45ff7b7baa6c70c1 0x3fa7273027061830 0x23fa727302706183

def z973 : W := mkw 0x06383028120c0000 0x006383028120c000 0x6e38383c3f0e38fd 0x76e38383c3f0e38f

def z974 : W := mkw 0x043b423f522fc1f0 0xe043b423f522fc1f 0x503fc03fc00fc0f3 0x0503fc03fc00fc0f

def z975 : W := mkw 0x1dfdc00476ef8088 0x21dfdc00476ef808 0x3fffc00cffffc00b 0xf3fffc00cffffc00

def z976 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xf1e7e7f3e08fffff 0xbf1e7e7f3e08ffff

def z977 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xafe03ff03ff63f3c 0xfafe03ff03ff63f3

def z978 : W := mkw 0x4f76b6ba81001004 0x04f76b6ba8100100 0xffffffffe7001807 0xfffffffffe700180

def z979 : W := mkw 0x5dfdc480b6ef8008 0x05dfdc480b6ef800 0x3fffc0c0ffffc00b 0xf3fffc0c0ffffc00

def z980 : W := mkw 0x4d76869280000000 0x04d7686928000000 0xdfffdfcfc0000007 0xfdfffdfcfc000000

def z981 : W := mkw 0x0083031320834d52 0x40083031320834d5 0x71a72733208ffffb 0x271a72733208ffff

def z982 : W := mkw 0x000848455b3cf3e4 0xa000848455b3cf3e 0xe078f8ffffffffff 0xfe078f8fffffffff

def z983 : W := mkw 0x4436823a80000000 0x04436823a8000000 0xd1ffffffc0000007 0xfd1ffffffc000000

def z984 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xefc03fc03ff83fcd 0xfefc03fc03ff83fc

def z985 : W := mkw 0x4f76b6ba83041024 0x84f76b6ba8304102 0xdfffffffc7000007 0xfdfffffffc700000

def z986 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xaf8027003ff03f0c 0xbaf8027003ff03f0

def z987 : W := mkw 0x29c005c024d00e03 0x029c005c024d00e0 0xafc027c03ff03f0c 0xfafc027c03ff03f0

def z988 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x6e38f83fff0e38ff 0x76e38f83fff0e38f

def z989 : W := mkw 0x000848455a3ce3e0 0xa000848455a3ce3e 0xc058d8cfd8ffe7ff 0xdc058d8cfd8ffe7f

def z990 : W := mkw 0x0f74b48000000000 0x00f74b4800000000 0xdfffffcfc0000007 0xfdfffffcfc000000

def z991 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0x8058d8cfd8f1e70e 0xd8058d8cfd8f1e70

def z992 : W := mkw 0x0630382c0b0430a4 0x80630382c0b0430a 0x2e202030270638f0 0x22e202030270638f

def z993 : W := mkw 0x0083031320834d52 0x40083031320834d5 0xf1bf3f3f208fffff 0xff1bf3f3f208ffff

def z994 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x3fbf00003fffc009 0x73fbf00003fffc00

def z995 : W := mkw 0x29c3079324c34d53 0x429c3079324c34d5 0x918707030081c702 0x8918707030081c70

def z996 : W := mkw 0x228039402dd03e07 0x0228039402dd03e0 0xaf803f003ff03f0c 0xfaf803f003ff03f0

def z997 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0xafc027c03ff03f08 0xaafc027c03ff03f0

def z998 : W := mkw 0x0630382809003004 0x0063038280900300 0x6e38383c3f0e38fd 0x76e38383c3f0e38f

def z999 : W := mkw 0x0438082c1b0c30a4 0x80438082c1b0c30a 0x6e38003c3f0e38f9 0x76e38003c3f0e38f

def z1000 : W := mkw 0x2bc03dc02dd03e07 0x02bc03dc02dd03e0 0x2fc027003ff03f08 0xf2fc027003ff03f0

def z1001 : W := mkw 0x3f7cfcec1f7cb2ad 0x83f7cfcec1f7cb2a 0x0e58d8cc1f700000 0x40e58d8cc1f70000

def z1002 : W := mkw 0x1dfdc02836ef8008 0x01dfdc02836ef800 0x7fffc03c3fffc00b 0xf7fffc03c3fffc00

def z1003 : W := mkw 0x22813dc029933e07 0x022813dc029933e0 0xb1a73fc0208fff0f 0xbb1a73fc0208fff0

def z1004 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0xee3838ffff0e38fd 0x7ee3838ffff0e38f

def z1005 : W := mkw 0x1d7dc000166f8008 0x01d7dc000166f800 0x1fffc0001f7fc003 0xf1fffc0001f7fc00

def z1006 : W := mkw 0x0638386c5b1c32a4 0xa0638386c5b1c32a 0x6e3838fcff0e38fd 0x76e3838fcff0e38f

def z1007 : W := mkw 0x2bc0358025c01c07 0x02bc0358025c01c0 0xafc027003ff03f0c 0xfafc027003ff03f0

def z1008 : W := mkw 0x4f76b6ba81001024 0x84f76b6ba8100102 0xdfffffffc0001837 0xfdfffffffc000183

def z1009 : W := mkw 0x2bc03dc42dd03e87 0x02bc03dc42dd03e8 0xefc03fcc3ff03fcc 0xfefc03fcc3ff03fc

def z1010 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0xc058d8cfd8f1c707 0xdc058d8cfd8f1c70

def z1011 : W := mkw 0x1dfdc02c36ef80a8 0x81dfdc02c36ef80a 0x7fffe03c3ffff8ff 0xf7fffe03c3ffff8f

def z1012 : W := mkw 0x000840455038c3c0 0x2000840455038c3c 0xc058d8cfc0f9c7c7 0xdc058d8cfc0f9c7c

def z1013 : W := mkw 0x0bc039002dc03c06 0x00bc039002dc03c0 0xafc03f003ff03f0c 0xfafc03f003ff03f0

def z1014 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x3fffc0003f7fc003 0x63fffc0003f7fc00

def z1015 : W := mkw 0x1dfdc00436ef8088 0x01dfdc00436ef808 0x7fffc00c3fffc0cb 0xf7fffc00c3fffc0c

def z1016 : W := mkw 0x22003dc009103e07 0x022003dc009103e0 0xae403fc03ff03f0c 0xfae403fc03ff03f0

def z1017 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x1fffc0001fffc003 0xc1fffc0001fffc00

def z1018 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x3fffe0303fffd83b 0xf3fffe0303fffd83

def z1019 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x7fffc00fffffc00b 0xf7fffc00fffffc00

def z1020 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x6e18383c3f0e38fc 0x46e18383c3f0e38f

def z1021 : W := mkw 0x0630302803041024 0x8063030280304102 0x6e202030270638f4 0x26e202030270638f

def z1022 : W := mkw 0x2bc03dec2dd03ea7 0x82bc03dec2dd03ea 0xefe03ffc3ffe3ffd 0xfefe03ffc3ffe3ff

def z1023 : W := mkw 0x4f76b6ba80000000 0x04f76b6ba8000000 0xdfffffffc00820cf 0xfdfffffffc00820c

def z1024 : W := mkw 0x29c005c024d00e03 0x029c005c024d00e0 0x8fc007c01ff00700 0xc8fc007c01ff0070

def z1025 : W := mkw 0x0002021300004140 0x0000202130000414 0xf1a72733208fffff 0xbf1a72733208ffff

def z1026 : W := mkw 0x0000084108106340 0x0000008410810634 0xc058d8cfd8f9e7cf 0xdc058d8cfd8f9e7c

def z1027 : W := mkw 0x1df5c00024e38008 0x01df5c00024e3800 0x3fffc0003ff1c00b 0xf3fffc0003ff1c00

def z1028 : W := mkw 0x000848455b3cf3e4 0xa000848455b3cf3e 0xc058d8cfdff9e7cf 0xdc058d8cfdff9e7c

def z1029 : W := mkw 0x0280394029903e06 0x00280394029903e0 0xafc03fc03ff03f0c 0xfafc03fc03ff03f0

def z1030 : W := mkw 0x09c3021324c34150 0x409c3021324c3415 0x7fe700333fffc0fb 0xf7fe700333fffc0f

def z1031 : W := mkw 0x6f76b6ba85401005 0x06f76b6ba8540100 0xdfffffffc7000007 0xfdfffffffc700000

def z1032 : W := mkw 0x2b403dc00d503e07 0x02b403dc00d503e0 0x8e401fc01f700700 0x48e401fc01f70070

def z1033 : W := mkw 0x000840415038c340 0x2000840415038c34 0xc058d8cfd8f9c70f 0xdc058d8cfd8f9c70

def z1034 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x2e3820303f0e38f9 0x72e3820303f0e38f

def z1035 : W := mkw 0x0638302c130c10a4 0x80638302c130c10a 0x6e38383c270e18f5 0x76e38383c270e18f

def z1036 : W := mkw 0x09c0010024c00c02 0x009c0010024c00c0 0xafc007003ff00708 0xfafc007003ff0070

def z1037 : W := mkw 0x108949457effefda 0x6108949457effefd 0x200000003ffffff8 0x0200000003ffffff

def z1038 : W := mkw 0x043808041b0c30a4 0x8043808041b0c30a 0x6e3820303f0e38fd 0x76e3820303f0e38f

def z1039 : W := mkw 0x4b46b69280000000 0x04b46b6928000000 0xdfdfffcfc0000007 0xfdfdfffcfc000000

def z1040 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0x8058d8cfd8f9c70b 0xd8058d8cfd8f9c70

def z1041 : W := mkw 0x0dfcc00034e88000 0x00dfcc00034e8800 0x3fffc0003ff9c00b 0xf3fffc0003ff9c00

def z1042 : W := mkw 0x19c7831324c34d5a 0x419c7831324c34d5 0x918707030081c702 0x8918707030081c70

def z1043 : W := mkw 0x0638786c5b3cb2a4 0xa0638786c5b3cb2a 0xee78f8fcfffe3ffd 0xfee78f8fcfffe3ff

def z1044 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x6e38383c3f8ff8ff 0xf6e38383c3f8ff8f

def z1045 : W := mkw 0x1dfdc00036ef8008 0x01dfdc00036ef800 0x7fffd80c3fffc00f 0xf7fffd80c3fffc00

def z1046 : W := mkw 0x463cb82c9b0c30a4 0x8463cb82c9b0c30a 0x6e38f83cff0e38fd 0x76e38f83cff0e38f

def z1047 : W := mkw 0x0081010020830c02 0x00081010020830c0 0xf1a72730208fffff 0xbf1a72730208ffff

def z1048 : W := mkw 0x29c009402dd03e07 0x029c009402dd03e0 0xafc027003ff03f0c 0xfafc027003ff03f0

def z1049 : W := mkw 0x2bc03dc46dd03e87 0x22bc03dc46dd03e8 0xafc03fccfff03f0c 0xfafc03fccfff03f0

def z1050 : W := mkw 0x09c3031324c34d52 0x409c3031324c34d5 0x91c7070300f1c702 0x891c7070300f1c70

def z1051 : W := mkw 0x7ff7b7baa7c71c0f 0x07ff7b7baa7c71c0 0x3fa7273027061800 0x23fa727302706180

def z1052 : W := mkw 0x2bc035c025d01e07 0x02bc035c025d01e0 0xafc027c03ff01f08 0xfafc027c03ff01f0

def z1053 : W := mkw 0x2bc13dc02dd33e07 0x02bc13dc02dd33e0 0xbfc73fc03ff1ff0e 0xfbfc73fc03ff1ff0

def z1054 : W := mkw 0x59c7c793a4e3cd5a 0x459c7c793a4e3cd5 0x91c7c7c3c0f1c702 0x891c7c7c3c0f1c70

def z1055 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0x4058d8cfd8f9e7cb 0x44058d8cfd8f9e7c

def z1056 : W := mkw 0x000848455838e3c0 0x2000848455838e3c 0xd1ffd8cfd8f9e7cf 0xfd1ffd8cfd8f9e7c

def z1057 : W := mkw 0x0638382c1b0c30a4 0x80638382c1b0c30a 0x6e2020303f0e38fd 0x36e2020303f0e38f

def z1058 : W := mkw 0x06383028130c1024 0x806383028130c102 0x6e3820303f0e38fd 0x76e3820303f0e38f

def z1059 : W := mkw 0x19cdc00034eb8008 0x019cdc00034eb800 0x3fdfc0003ff9c00b 0xf3fdfc0003ff9c00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z4,z7,z5,z6]),(1,[z0,z1,z2,z8,z5,z6]),(0,[z9,z0,z1,z2,z4,z5,z10]),(0,[z0,z1,z2,z4,z5,z11,z6]),(0,[z0,z1,z2,z4,z5,z6,z12]),(0,[z0,z1,z2,z4,z13,z5,z14])],[(0,[z0,z1,z15,z2,z4,z5,z6]),(0,[z0,z1,z16,z2,z4,z5,z6])],[(0,[z0,z1,z2,z8,z5,z17,z6]),(0,[z0,z1,z2,z18,z19,z5,z6])],[(0,[z0,z1,z20,z2,z4,z5,z6]),(0,[z0,z1,z2,z21,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z22]),(0,[z0,z23,z1,z2,z4,z24,z6]),(0,[z25,z26,z1,z2,z4,z5,z6]),(0,[z27,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z28,z6])],[(0,[z29,z0,z1,z30,z4,z5,z6]),(0,[z0,z1,z31,z2,z4,z5,z6]),(0,[z0,z32,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z33,z6]),(0,[z34,z0,z1,z2,z35,z4,z6]),(1,[z26,z0,z1,z4,z5,z36]),(0,[z0,z1,z2,z4,z5,z37,z6])],[(0,[z0,z1,z2,z4,z38,z5,z6]),(0,[z0,z1,z2,z39,z40,z5,z6]),(0,[z26,z0,z1,z2,z4,z5,z36])],[(0,[z0,z1,z41,z2,z4,z5,z6]),(0,[z0,z1,z42,z2,z40,z5,z6]),(0,[z0,z1,z2,z4,z43,z5,z6]),(0,[z0,z1,z2,z44,z4,z5,z6])],[(0,[z0,z23,z1,z2,z4,z5,z6]),(0,[z0,z1,z42,z45,z4,z5,z6]),(0,[z26,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z46,z2,z4,z5,z6]),(0,[z0,z1,z47,z2,z4,z5,z6]),(0,[z0,z1,z2,z48,z4,z5,z6]),(1,[z0,z1,z2,z4,z13,z14]),(0,[z0,z1,z49,z2,z4,z5,z6])],[(0,[z0,z50,z1,z2,z4,z5,z6]),(0,[z51,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z19,z5,z52,z6])],[(0,[z0,z1,z2,z4,z5,z6,z53]),(0,[z0,z1,z2,z4,z5,z6,z54])],[(0,[z0,z1,z2,z4,z55,z5,z6]),(0,[z0,z1,z2,z4,z56,z5,z6]),(0,[z0,z57,z1,z2,z4,z5,z6]),(0,[z0,z1,z42,z2,z4,z58,z6]),(0,[z0,z1,z2,z4,z5,z36,z6])],[(0,[z59,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z60,z6])],[(0,[z1,z61,z2,z30,z4,z5,z6]),(0,[z62,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z63,z6]),(0,[z9,z64,z0,z1,z2,z4,z5]),(0,[z65,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z66,z40,z5,z6]),(0,[z34,z0,z1,z2,z4,z17,z6]),(0,[z0,z1,z2,z4,z5,z67,z6]),(0,[z68,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z69,z4,z5,z6]),(0,[z0,z1,z70,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z71]),(0,[z0,z72,z1,z2,z4,z5,z6])],[(0,[z73,z74,z1,z2,z4,z5,z6]),(0,[z0,z1,z61,z2,z4,z5,z75]),(0,[z76,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z77,z6]),(0,[z0,z1,z45,z4,z40,z5,z6]),(0,[z0,z1,z2,z4,z78,z5,z6]),(0,[z0,z1,z2,z4,z5,z79,z6]),(0,[z0,z1,z2,z18,z4,z5,z6]),(0,[z80,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z81,z6]),(0,[z0,z1,z2,z4,z13,z82,z6]),(0,[z0,z1,z83,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z84,z6]),(0,[z85,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z52,z6])]],
   [[(0,[z0,z1,z2,z4,z82,z5,z6]),(1,[z0,z1,z86,z4,z5,z6]),(0,[z0,z1,z86,z4,z39,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z87])],[(0,[z88,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z89,z6]),(0,[z0,z1,z2,z5,z52,z6,z71])],[],[(0,[z0,z1,z2,z4,z90,z6,z91]),(0,[z0,z1,z2,z4,z5,z92,z6]),(0,[z0,z1,z2,z4,z93,z5,z6])],[(0,[z0,z1,z94,z95,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z6,z96]),(0,[z0,z1,z2,z4,z97,z5,z6]),(0,[z0,z1,z2,z4,z5,z98,z6]),(0,[z0,z1,z2,z18,z4,z5,z52])],[(0,[z0,z99,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z100,z6]),(0,[z29,z0,z1,z2,z101,z5,z6]),(0,[z29,z0,z1,z4,z102,z5,z6]),(0,[z0,z1,z103,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z10,z104]),(0,[z0,z1,z2,z4,z13,z5,z91])],[(0,[z0,z1,z2,z30,z4,z5,z6]),(0,[z0,z1,z105,z2,z4,z5,z6]),(0,[z0,z1,z2,z106,z4,z5,z6]),(0,[z107,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z108,z5,z6])]],
   [[(0,[z109,z0,z95,z2,z4,z5,z6]),(0,[z1,z2,z30,z4,z5,z110,z6]),(0,[z0,z1,z61,z4,z5,z111,z6]),(0,[z112,z0,z1,z2,z4,z5,z6]),(0,[z113,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z114,z4,z5,z6]),(0,[z0,z1,z2,z19,z4,z5,z6]),(0,[z0,z1,z2,z115,z4,z5,z6])],[(0,[z0,z1,z2,z4,z116,z5,z6]),(0,[z0,z1,z2,z4,z5,z117,z6]),(0,[z29,z0,z1,z118,z4,z5,z6]),(0,[z0,z1,z2,z4,z119,z5,z6])],[(0,[z0,z1,z2,z4,z120,z5,z6]),(0,[z0,z32,z1,z61,z4,z5,z6]),(0,[z0,z1,z2,z121,z4,z5,z6]),(0,[z0,z1,z2,z4,z122,z5,z6]),(0,[z0,z1,z123,z2,z4,z5,z6]),(0,[z34,z0,z1,z2,z4,z24,z6])],[(0,[z109,z0,z1,z124,z4,z5,z6]),(0,[z0,z1,z2,z4,z125,z5,z6]),(1,[z0,z1,z126,z4,z5,z6]),(0,[z0,z1,z2,z127,z4,z5,z6])],[(0,[z128,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z129,z4,z5,z6]),(0,[z0,z1,z2,z4,z130,z5,z6]),(0,[z0,z131,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z132,z6])],[(1,[z133,z1,z30,z4,z5,z6]),(0,[z0,z1,z2,z4,z134,z5,z6]),(0,[z26,z0,z1,z61,z4,z5,z6]),(0,[z0,z1,z2,z135,z4,z5,z6])],[(0,[z133,z0,z1,z30,z4,z5,z6]),(0,[z0,z1,z2,z4,z136,z5,z6]),(0,[z0,z1,z2,z4,z4,z5,z6]),(0,[z0,z1,z137,z2,z4,z5,z6]),(0,[z0,z1,z2,z138,z4,z5,z6]),(0,[z34,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z19,z4,z5,z52])],[(1,[z0,z1,z124,z4,z5,z6]),(0,[z0,z1,z124,z2,z4,z5,z6]),(0,[z0,z1,z2,z139,z4,z5,z6]),(0,[z29,z0,z1,z140,z4,z5,z6]),(0,[z0,z1,z2,z141,z4,z5,z6])]],
   [[(0,[z74,z133,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z142,z5,z6,z71]),(0,[z0,z1,z2,z143,z4,z5,z6]),(0,[z0,z1,z144,z2,z4,z5,z6]),(0,[z0,z1,z2,z145,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z146,z6]),(0,[z29,z0,z1,z147,z4,z5,z6]),(0,[z0,z2,z4,z24,z5,z17,z6]),(0,[z0,z1,z2,z4,z148,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z149])],[(0,[z26,z0,z1,z150,z4,z5,z6]),(0,[z0,z1,z2,z44,z4,z6,z91])],[(0,[z151,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z152,z2,z4,z5,z6]),(0,[z153,z0,z1,z2,z4,z5,z6]),(0,[z154,z0,z1,z2,z4,z5,z6]),(0,[z155,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z102,z24,z6]),(0,[z0,z1,z2,z156,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z157,z6]),(0,[z0,z1,z2,z4,z5,z158,z6]),(0,[z0,z1,z2,z44,z4,z5,z14])],[(0,[z0,z1,z2,z4,z5,z6,z159]),(0,[z0,z1,z2,z4,z5,z6,z160]),(0,[z0,z1,z2,z4,z5,z6,z161]),(0,[z0,z1,z2,z162,z4,z5,z6]),(0,[z25,z0,z1,z2,z4,z5,z6])],[(0,[z163,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z164]),(0,[z0,z1,z2,z4,z5,z6,z165]),(0,[z0,z1,z2,z4,z5,z6,z6]),(0,[z0,z1,z2,z4,z166,z5,z6]),(0,[z0,z1,z2,z4,z13,z14,z6])],[(0,[z0,z1,z167,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z168,z6]),(0,[z0,z169,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z170,z6])],[(0,[z171,z1,z2,z4,z5,z90,z6]),(0,[z0,z1,z172,z2,z4,z5,z6]),(0,[z0,z1,z173,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z102,z5,z6]),(0,[z0,z1,z174,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z175])]],
   [[(1,[z0,z32,z147,z4,z5,z6])],[(0,[z0,z1,z2,z176,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z177])],[(0,[z0,z1,z2,z178,z4,z5,z6]),(0,[z179,z0,z1,z2,z4,z5,z6]),(0,[z0,z23,z1,z2,z180,z5,z6]),(0,[z0,z1,z181,z2,z4,z5,z6])],[(0,[z0,z1,z2,z118,z4,z5,z6]),(0,[z0,z1,z2,z182,z4,z5,z6]),(1,[z0,z1,z181,z40,z5,z6]),(0,[z183,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z82,z6,z91]),(0,[z0,z1,z184,z2,z4,z5,z6])],[(1,[z0,z185,z2,z39,z5,z6]),(0,[z0,z1,z2,z126,z4,z5,z6])],[(0,[z1,z2,z4,z5,z110,z6,z160]),(0,[z0,z1,z186,z2,z4,z5,z6]),(0,[z0,z185,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z187])],[(0,[z0,z188,z189,z2,z4,z5,z6]),(0,[z0,z1,z190,z2,z4,z5,z6]),(0,[z0,z1,z2,z191,z4,z5,z6]),(0,[z0,z1,z2,z192,z4,z5,z6]),(0,[z0,z1,z2,z193,z4,z5,z6]),(0,[z194,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z195,z2,z4,z5,z6]),(0,[z0,z1,z196,z2,z4,z5,z6]),(1,[z0,z1,z2,z35,z79,z6])]],
   [[(0,[z0,z1,z197,z2,z4,z5,z6]),(0,[z0,z1,z2,z198,z4,z5,z6]),(0,[z0,z1,z150,z2,z4,z5,z36])],[(1,[z199,z95,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z200,z5,z6]),(0,[z0,z1,z2,z4,z5,z201,z6]),(0,[z202,z0,z1,z2,z4,z5,z6])],[(0,[z203,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z150,z2,z4,z5,z6])],[(0,[z204,z0,z1,z198,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z205]),(0,[z206,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z207,z4,z79,z6])],[(0,[z199,z0,z95,z2,z4,z5,z6]),(0,[z0,z1,z208,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z209,z6]),(0,[z0,z1,z2,z210,z4,z5,z6])],[(0,[z0,z1,z211,z2,z4,z5,z6]),(0,[z212,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z213,z4,z5,z6]),(0,[z0,z188,z2,z4,z5,z10,z6]),(0,[z0,z1,z214,z2,z4,z5,z6]),(0,[z0,z1,z2,z215,z4,z5,z6])],[(0,[z0,z1,z2,z4,z216,z5,z6]),(0,[z217,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z218,z5,z6])],[(0,[z0,z1,z219,z2,z4,z5,z6]),(0,[z220,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z221,z4,z5,z6]),(0,[z0,z1,z2,z39,z5,z79,z6]),(0,[z0,z1,z222,z2,z4,z5,z6]),(0,[z0,z1,z2,z223,z4,z5,z6])]],
   [[(0,[z224,z0,z1,z2,z4,z5,z6]),(0,[z0,z185,z1,z2,z4,z225,z6]),(0,[z0,z226,z1,z2,z4,z5,z6]),(0,[z227,z0,z1,z2,z4,z5,z6]),(0,[z228,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z44,z4,z5,z91])],[(0,[z0,z1,z2,z4,z5,z229,z6]),(0,[z0,z1,z2,z230,z4,z5,z6]),(0,[z0,z1,z2,z8,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z231])],[(0,[z0,z1,z232,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z233,z6]),(0,[z64,z0,z1,z2,z4,z5,z36]),(0,[z234,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z235,z6]),(0,[z0,z1,z2,z236,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z5,z6]),(0,[z64,z0,z1,z2,z4,z5,z160])],[(0,[z64,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z237,z4,z5,z6])],[(0,[z0,z0,z1,z2,z4,z5,z6]),(0,[z238,z0,z1,z2,z4,z5,z6]),(0,[z239,z0,z1,z2,z4,z5,z6]),(0,[z240,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z241,z4,z5,z6])],[(0,[z0,z1,z2,z242,z4,z5,z6]),(0,[z0,z1,z2,z243,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z244,z6]),(0,[z0,z1,z245,z2,z4,z5,z6]),(0,[z0,z1,z246,z2,z247,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z248]),(0,[z0,z1,z2,z66,z5,z79,z6]),(0,[z0,z1,z2,z249,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z250,z5,z6]),(0,[z0,z1,z2,z251,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z36,z252]),(0,[z0,z253,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z254])],[(0,[z0,z1,z255,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z256,z6]),(0,[z0,z257,z1,z2,z4,z5,z6]),(0,[z258,z0,z1,z2,z4,z5,z6])],[(0,[z259,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z45,z260,z5,z6]),(0,[z0,z1,z2,z261,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z262,z6])],[(0,[z263,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z264]),(0,[z0,z32,z1,z4,z102,z5,z6]),(0,[z0,z1,z15,z4,z5,z17,z6]),(0,[z265,z0,z1,z2,z4,z5,z6]),(0,[z266,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z267,z4,z5,z6]),(0,[z0,z1,z2,z35,z207,z5,z6]),(0,[z0,z1,z2,z4,z268,z5,z6])],[(0,[z0,z1,z2,z269,z4,z5,z6]),(0,[z204,z1,z2,z4,z270,z5,z6]),(0,[z73,z9,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z225,z6]),(0,[z271,z0,z1,z2,z4,z5,z6])],[(1,[z0,z1,z272,z4,z5,z6]),(0,[z73,z0,z188,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z6,z273]),(1,[z0,z1,z246,z4,z102,z6])],[(0,[z0,z32,z1,z118,z4,z5,z6]),(0,[z274,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z42,z2,z4,z5,z6]),(1,[z0,z1,z2,z207,z260,z6])],[],[(0,[z74,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z275,z5,z6]),(0,[z29,z0,z1,z2,z275,z5,z6]),(0,[z0,z188,z1,z2,z4,z5,z10])],[(0,[z0,z189,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z276]),(0,[z0,z1,z2,z4,z58,z5,z6]),(0,[z0,z277,z1,z2,z4,z5,z6]),(0,[z0,z1,z278,z2,z4,z5,z6])],[(0,[z279,z0,z1,z2,z4,z5,z6]),(0,[z280,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z281,z4,z5,z6]),(0,[z0,z1,z2,z260,z5,z79,z6])],[(0,[z282,z0,z1,z2,z270,z5,z6])],[(0,[z0,z1,z61,z2,z4,z5,z6]),(0,[z282,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z101,z4,z5,z6]),(0,[z283,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z66,z4,z5,z6]),(0,[z0,z1,z2,z284,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z285,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z286,z6]),(0,[z0,z1,z287,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z288,z6]),(0,[z0,z1,z2,z4,z5,z289,z6])],[(1,[z0,z1,z2,z4,z5,z75]),(0,[z0,z1,z2,z4,z5,z6,z290]),(1,[z291,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z292,z5,z6]),(0,[z0,z1,z2,z4,z293,z5,z6]),(0,[z0,z1,z294,z2,z4,z5,z6])],[(0,[z0,z1,z2,z295,z4,z5,z6])],[(0,[z1,z95,z2,z30,z4,z5,z6]),(0,[z296,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z297,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z298,z6]),(0,[z299,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z17,z79,z6]),(0,[z0,z1,z2,z4,z5,z300,z6]),(0,[z0,z1,z2,z4,z14,z6,z91])],[(1,[z109,z189,z2,z4,z5,z6]),(0,[z301,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z302,z5,z6]),(0,[z64,z0,z1,z2,z4,z5,z110]),(1,[z0,z1,z4,z303,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z91])]],
   [[(0,[z0,z1,z2,z4,z304,z5,z6]),(0,[z0,z1,z2,z272,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z305]),(1,[z0,z1,z2,z101,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z306])],[(0,[z0,z1,z2,z4,z307,z5,z6])],[(0,[z109,z189,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z252])],[(0,[z0,z1,z2,z4,z5,z308,z6]),(1,[z0,z1,z2,z284,z4,z6]),(0,[z0,z1,z2,z4,z5,z6,z309]),(1,[z9,z0,z2,z4,z5,z252]),(0,[z0,z1,z310,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z311,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z312]),(0,[z0,z1,z2,z4,z5,z6,z313])],[(1,[z0,z1,z94,z2,z4,z5]),(0,[z0,z314,z1,z2,z4,z5,z6]),(0,[z74,z1,z61,z2,z4,z5,z6]),(1,[z0,z1,z46,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z315,z6]),(0,[z0,z1,z316,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z317])],[(0,[z318,z0,z1,z95,z2,z4,z5]),(1,[z0,z1,z2,z4,z5,z319]),(0,[z29,z0,z1,z2,z4,z5,z319]),(0,[z0,z1,z2,z320,z4,z5,z6])],[(0,[z0,z1,z2,z4,z321,z5,z6]),(0,[z0,z1,z42,z61,z4,z5,z6]),(0,[z0,z322,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z77,z5,z6]),(0,[z0,z1,z2,z4,z323,z5,z6]),(0,[z0,z1,z2,z44,z4,z13,z6])],[]],
   [[(0,[z0,z1,z2,z4,z5,z324,z6]),(0,[z74,z0,z1,z61,z4,z5,z6]),(0,[z0,z1,z2,z4,z39,z5,z6]),(0,[z0,z1,z2,z207,z4,z5,z6])],[(1,[z0,z1,z198,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z325,z6]),(0,[z0,z1,z2,z4,z13,z90,z6]),(0,[z0,z1,z181,z4,z40,z5,z6]),(0,[z0,z1,z150,z4,z5,z6,z104]),(0,[z0,z1,z2,z4,z5,z6,z326])],[(0,[z0,z1,z2,z4,z327,z5,z6])],[(0,[z34,z0,z23,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z328,z6]),(0,[z0,z1,z2,z4,z329,z5,z6]),(0,[z330,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z331,z5,z6])],[(0,[z204,z0,z1,z2,z270,z5,z6])],[(0,[z332,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z260,z17,z6]),(0,[z0,z1,z2,z4,z5,z333,z6])],[(0,[z334,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z10,z6]),(0,[z0,z1,z246,z2,z4,z5,z6]),(0,[z0,z1,z335,z2,z4,z5,z6]),(0,[z336,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z337,z6]),(0,[z0,z1,z2,z4,z5,z338,z6]),(0,[z0,z1,z2,z4,z5,z6,z339]),(0,[z282,z0,z1,z2,z142,z5,z6]),(0,[z0,z1,z2,z297,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z340]),(0,[z0,z1,z2,z4,z341,z5,z6]),(0,[z0,z1,z2,z4,z5,z342,z6])]],
   [[(0,[z199,z0,z1,z2,z4,z5,z6]),(0,[z109,z1,z2,z30,z4,z5,z6]),(0,[z343,z0,z1,z2,z4,z5,z6]),(0,[z344,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z303,z5,z6])],[(0,[z0,z1,z2,z4,z5,z345,z6]),(0,[z73,z0,z1,z2,z4,z5,z104]),(0,[z0,z1,z2,z346,z4,z5,z6]),(0,[z347,z0,z1,z2,z4,z5,z6])],[(0,[z0,z348,z1,z2,z4,z5,z6]),(1,[z29,z0,z118,z4,z5,z6]),(0,[z0,z1,z2,z349,z4,z5,z6]),(0,[z0,z1,z2,z4,z350,z5,z6]),(1,[z0,z1,z2,z247,z5,z6])],[(0,[z0,z351,z1,z2,z4,z5,z6]),(0,[z171,z0,z1,z2,z4,z90,z6])],[(0,[z0,z1,z2,z4,z5,z6,z352]),(0,[z29,z0,z1,z181,z4,z5,z6]),(0,[z0,z1,z353,z2,z4,z5,z6]),(0,[z26,z0,z1,z4,z5,z36,z6]),(0,[z0,z1,z2,z4,z354,z5,z6])],[(0,[z355,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z356,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z111,z6])],[(0,[z357,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z358,z5,z6]),(0,[z0,z1,z359,z2,z4,z5,z6])]],
   [[(0,[z0,z360,z1,z2,z4,z5,z6]),(0,[z0,z185,z1,z2,z39,z5,z6])],[(1,[z282,z1,z2,z142,z5,z6]),(0,[z361,z0,z1,z2,z4,z5,z6]),(0,[z212,z0,z1,z2,z66,z5,z6]),(0,[z0,z1,z2,z362,z4,z5,z6]),(0,[z0,z1,z4,z5,z36,z6,z104]),(0,[z0,z1,z363,z2,z4,z5,z6])],[(1,[z131,z1,z2,z4,z5,z6]),(0,[z29,z131,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z364,z5,z6])],[(1,[z0,z1,z365,z4,z5,z6]),(0,[z0,z1,z2,z142,z4,z5,z6]),(0,[z0,z1,z2,z366,z4,z5,z6]),(0,[z0,z1,z367,z2,z4,z5,z6])],[(0,[z0,z32,z1,z30,z4,z5,z6]),(1,[z0,z1,z2,z7,z5,z6]),(0,[z0,z368,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z369])],[(0,[z0,z1,z365,z2,z4,z5,z6]),(0,[z0,z1,z2,z370,z4,z5,z6]),(0,[z371,z0,z1,z2,z4,z5,z6]),(0,[z0,z372,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z373,z5,z6]),(0,[z0,z1,z2,z4,z5,z374,z6]),(0,[z212,z0,z1,z2,z39,z5,z6]),(0,[z0,z1,z2,z375,z4,z5,z6]),(0,[z0,z1,z246,z2,z376,z5,z6]),(0,[z0,z1,z2,z4,z377,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z378,z6]),(0,[z0,z1,z30,z4,z5,z111,z6]),(0,[z26,z0,z1,z30,z4,z5,z6]),(1,[z0,z1,z2,z191,z5,z6]),(0,[z0,z1,z2,z4,z379,z5,z6])],[(0,[z0,z1,z380,z2,z4,z5,z6]),(0,[z9,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z381,z6])],[(0,[z0,z1,z2,z4,z382,z5,z6]),(0,[z383,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z384,z6]),(0,[z0,z1,z2,z4,z5,z6,z385]),(0,[z0,z1,z2,z35,z45,z5,z6]),(0,[z0,z1,z2,z386,z4,z5,z6])],[(0,[z0,z1,z387,z2,z4,z5,z6]),(0,[z0,z1,z2,z388,z4,z5,z6]),(0,[z0,z1,z389,z2,z4,z5,z6]),(0,[z390,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z391,z2,z4,z5,z6]),(0,[z0,z1,z246,z61,z4,z5,z6]),(0,[z392,z0,z1,z2,z4,z5,z6]),(0,[z0,z393,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z24,z5,z6]),(0,[z0,z1,z2,z4,z5,z394,z6])],[(0,[z0,z395,z1,z2,z4,z5,z6]),(0,[z204,z0,z1,z2,z142,z5,z6]),(0,[z0,z1,z2,z4,z5,z396,z6]),(0,[z0,z397,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z398,z4,z5,z6]),(0,[z399,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z14,z6])],[(0,[z0,z1,z2,z400,z4,z5,z6]),(0,[z0,z1,z61,z4,z5,z6,z104]),(0,[z0,z1,z401,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z402,z5,z6]),(0,[z0,z1,z2,z4,z403,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z404]),(0,[z0,z405,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z200,z6]),(0,[z0,z406,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z207,z4,z102,z6]),(0,[z0,z1,z2,z4,z5,z407,z6])]],
   [[(0,[z408,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z409,z6]),(0,[z0,z1,z2,z3,z4,z39,z6]),(0,[z0,z1,z2,z4,z410,z5,z6]),(0,[z0,z1,z2,z411,z4,z5,z6]),(0,[z0,z1,z2,z412,z4,z5,z6]),(1,[z0,z1,z2,z44,z4,z91])],[(1,[z361,z1,z2,z4,z5,z6]),(0,[z29,z361,z1,z2,z4,z5,z6]),(0,[z0,z1,z413,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z414,z5,z6]),(0,[z0,z2,z4,z5,z10,z6,z252]),(0,[z26,z291,z1,z2,z4,z5,z6])],[(1,[z0,z415,z2,z4,z5,z6]),(1,[z0,z23,z2,z4,z17,z6]),(0,[z0,z1,z2,z35,z40,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z416])],[(0,[z0,z1,z417,z2,z4,z5,z6]),(0,[z0,z1,z246,z2,z4,z102,z6]),(0,[z0,z1,z2,z4,z5,z6,z418])],[(0,[z133,z1,z2,z30,z4,z5,z6]),(0,[z0,z1,z61,z4,z40,z5,z6]),(0,[z282,z1,z2,z142,z4,z5,z6])],[(0,[z51,z0,z1,z2,z4,z90,z6]),(0,[z0,z1,z2,z4,z419,z5,z6])]],
   [[(0,[z0,z95,z2,z4,z5,z6,z252])],[(0,[z204,z0,z1,z365,z4,z5,z6]),(0,[z0,z1,z126,z4,z39,z5,z6]),(0,[z0,z1,z2,z247,z4,z5,z6]),(0,[z420,z0,z1,z2,z4,z5,z6]),(0,[z421,z0,z1,z2,z4,z5,z6])],[(0,[z74,z1,z95,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z422,z5,z6])],[(0,[z0,z1,z2,z423,z4,z5,z6]),(0,[z0,z147,z2,z118,z4,z5,z6]),(1,[z0,z1,z2,z18,z5,z71])],[(0,[z0,z424,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z425,z6]),(0,[z0,z1,z2,z4,z5,z426,z6]),(0,[z0,z1,z427,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z428])],[(0,[z0,z1,z2,z4,z5,z6,z429]),(0,[z0,z1,z2,z430,z4,z5,z6]),(0,[z431,z0,z1,z2,z4,z5,z6]),(0,[z212,z0,z185,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z432])],[(0,[z0,z1,z2,z4,z5,z6,z433]),(1,[z0,z1,z2,z119,z5,z6]),(0,[z0,z1,z4,z102,z5,z111,z6])],[(0,[z109,z0,z1,z2,z4,z5,z6]),(0,[z0,z188,z95,z2,z4,z5,z6]),(0,[z0,z1,z434,z2,z4,z5,z6]),(0,[z0,z1,z2,z435,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z436]),(0,[z0,z32,z1,z140,z4,z5,z6]),(0,[z212,z0,z2,z66,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z437,z6]),(0,[z0,z415,z1,z2,z4,z5,z6]),(0,[z438,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z439])],[(0,[z0,z1,z2,z4,z5,z6,z264]),(0,[z0,z1,z2,z440,z4,z5,z6]),(0,[z0,z32,z1,z147,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z441,z6]),(0,[z0,z1,z2,z4,z24,z79,z6]),(0,[z0,z1,z2,z4,z5,z36,z10]),(0,[z0,z1,z140,z4,z5,z111,z6])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z442,z6]),(0,[z29,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z207,z4,z111,z6])],[(0,[z0,z1,z2,z4,z5,z443,z6]),(0,[z444,z0,z1,z2,z4,z5,z6]),(0,[z73,z1,z2,z30,z4,z5,z6])],[(0,[z29,z0,z1,z45,z4,z5,z6]),(0,[z0,z1,z445,z2,z4,z5,z6]),(1,[z0,z1,z140,z4,z111,z6])],[(0,[z0,z1,z2,z446,z4,z5,z6]),(0,[z73,z0,z1,z2,z447,z5,z6]),(0,[z0,z1,z2,z4,z5,z448,z6]),(0,[z0,z1,z2,z4,z449,z5,z6]),(0,[z0,z1,z2,z4,z450,z5,z6]),(0,[z0,z1,z2,z451,z4,z5,z6])],[(0,[z0,z452,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z453,z6]),(0,[z0,z1,z454,z2,z4,z5,z6]),(0,[z0,z1,z4,z303,z5,z17,z6]),(0,[z0,z1,z2,z4,z5,z104,z252]),(0,[z0,z1,z2,z4,z455,z5,z6]),(0,[z0,z1,z2,z456,z4,z5,z6]),(0,[z0,z1,z2,z207,z4,z260,z6])]],
   [[(0,[z0,z1,z2,z4,z457,z5,z6]),(0,[z0,z1,z86,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z458,z6]),(0,[z0,z1,z459,z2,z4,z5,z6]),(0,[z0,z1,z2,z460,z4,z5,z6])],[(0,[z461,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z58,z6]),(0,[z0,z1,z246,z2,z4,z111,z6]),(0,[z0,z1,z2,z462,z4,z5,z6]),(0,[z0,z1,z2,z35,z4,z79,z6]),(0,[z0,z1,z2,z463,z4,z5,z6])],[(0,[z29,z0,z32,z2,z4,z5,z6]),(0,[z0,z185,z2,z4,z39,z5,z6]),(0,[z0,z1,z2,z4,z464,z5,z6]),(0,[z0,z1,z465,z2,z4,z5,z6]),(0,[z0,z1,z466,z2,z4,z5,z6])],[(0,[z0,z32,z1,z181,z4,z5,z6]),(0,[z0,z1,z2,z467,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z468,z6])],[(0,[z0,z1,z2,z207,z66,z5,z6]),(1,[z25,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z469]),(0,[z0,z1,z2,z4,z5,z6,z470])],[(1,[z0,z1,z2,z4,z225,z6])],[(0,[z0,z1,z2,z4,z5,z471,z6])],[(0,[z0,z1,z472,z2,z4,z5,z6]),(0,[z0,z1,z2,z473,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z474,z4,z5,z6]),(0,[z73,z0,z1,z2,z191,z5,z6]),(0,[z0,z1,z2,z475,z4,z5,z6]),(0,[z0,z1,z140,z246,z4,z5,z6]),(1,[z0,z1,z150,z4,z5,z104])],[(0,[z74,z109,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z476,z4,z5,z6]),(0,[z0,z1,z2,z477,z4,z5,z6])],[(0,[z0,z1,z2,z4,z478,z5,z6]),(0,[z0,z1,z2,z4,z5,z479,z6]),(0,[z73,z1,z2,z4,z5,z6,z160]),(0,[z0,z1,z2,z207,z39,z5,z6]),(0,[z0,z1,z2,z35,z4,z102,z6]),(0,[z480,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z481,z2,z4,z5,z6])],[(0,[z482,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z483,z5,z6]),(1,[z0,z1,z2,z376,z5,z6])],[(0,[z0,z1,z2,z2,z4,z5,z6]),(0,[z0,z1,z484,z2,z4,z5,z6]),(0,[z0,z1,z2,z485,z4,z5,z6]),(0,[z486,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z487,z2,z4,z5,z6])],[(0,[z0,z1,z2,z488,z4,z5,z6]),(0,[z0,z1,z2,z4,z489,z5,z6]),(1,[z0,z1,z490,z4,z5,z6])],[(0,[z73,z0,z1,z2,z4,z200,z6]),(0,[z0,z1,z2,z491,z4,z5,z6]),(0,[z492,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z45,z4,z5,z6]),(0,[z0,z1,z2,z4,z493,z5,z6]),(0,[z0,z1,z2,z494,z4,z5,z6])]],
   [[(0,[z204,z0,z1,z2,z4,z5,z6])],[(0,[z29,z0,z1,z61,z4,z5,z6]),(0,[z495,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z496,z5,z6]),(0,[z0,z185,z1,z2,z4,z77,z6]),(0,[z0,z1,z2,z4,z5,z6,z497]),(0,[z0,z1,z2,z4,z498,z5,z6])],[(0,[z0,z1,z499,z2,z4,z5,z6])],[(0,[z500,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z501,z4,z5,z6]),(0,[z0,z1,z2,z502,z4,z5,z6]),(0,[z0,z1,z2,z503,z4,z5,z6]),(0,[z0,z1,z2,z4,z504,z5,z6]),(0,[z0,z1,z2,z4,z5,z505,z6])],[(0,[z73,z0,z415,z2,z4,z5,z6]),(0,[z64,z1,z2,z4,z5,z110,z6]),(0,[z0,z1,z147,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z319]),(0,[z0,z1,z2,z4,z506,z5,z6]),(0,[z0,z507,z1,z2,z4,z5,z6])],[(0,[z133,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z508,z2,z4,z5,z6]),(0,[z1,z2,z4,z82,z5,z90,z6]),(0,[z0,z1,z2,z4,z5,z110,z6]),(0,[z29,z0,z1,z2,z4,z56,z6]),(0,[z0,z185,z1,z2,z66,z5,z6]),(0,[z0,z1,z2,z4,z5,z509,z6]),(0,[z0,z1,z2,z4,z5,z6,z510])],[(1,[z0,z83,z2,z4,z5,z6]),(0,[z9,z0,z1,z2,z4,z5,z252]),(0,[z0,z1,z2,z4,z5,z511,z6])],[(0,[z0,z1,z512,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z24,z111,z6]),(0,[z0,z1,z2,z4,z5,z513,z6])]],
   [[(0,[z514,z0,z1,z2,z4,z5,z6]),(0,[z171,z0,z1,z297,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z515,z6]),(0,[z0,z189,z2,z4,z5,z6,z252]),(0,[z516,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z447,z5,z6])],[(0,[z282,z204,z1,z2,z4,z5,z6]),(0,[z0,z517,z1,z2,z4,z5,z6]),(0,[z0,z518,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z519,z5,z6]),(0,[z0,z23,z1,z2,z4,z17,z6]),(0,[z0,z1,z2,z520,z4,z5,z6])],[(0,[z521,z0,z1,z2,z4,z5,z6]),(0,[z522,z0,z1,z2,z4,z5,z6]),(0,[z0,z185,z1,z2,z35,z5,z6]),(0,[z0,z1,z523,z2,z4,z5,z6])],[(0,[z524,z0,z1,z2,z4,z5,z6]),(0,[z525,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z526,z6]),(0,[z0,z1,z2,z4,z17,z111,z6]),(0,[z527,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z260,z24,z6]),(0,[z0,z1,z2,z4,z5,z528,z6])],[(0,[z529,z0,z1,z2,z4,z5,z6]),(0,[z26,z0,z1,z2,z4,z5,z104]),(0,[z0,z1,z2,z35,z5,z79,z6])],[(0,[z0,z1,z2,z530,z4,z5,z6]),(0,[z171,z0,z1,z46,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z531,z6])]],
   [[(0,[z532,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z533,z6]),(0,[z0,z1,z2,z490,z4,z5,z6]),(0,[z0,z1,z2,z534,z4,z5,z6]),(0,[z0,z1,z2,z535,z4,z5,z6])],[(0,[z0,z1,z42,z30,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z90,z6]),(0,[z0,z1,z2,z536,z4,z5,z6]),(0,[z73,z0,z1,z2,z4,z5,z36]),(0,[z0,z291,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z260,z5,z6])],[(0,[z537,z0,z1,z2,z4,z5,z6]),(0,[z538,z0,z1,z2,z4,z5,z6]),(0,[z74,z1,z2,z4,z5,z110,z6]),(0,[z0,z1,z2,z4,z5,z539,z6]),(0,[z540,z0,z1,z2,z4,z5,z6]),(0,[z541,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z542,z6])],[(0,[z74,z0,z1,z30,z4,z5,z6]),(1,[z51,z1,z2,z4,z82,z6]),(0,[z73,z0,z1,z2,z4,z5,z6]),(0,[z212,z0,z1,z2,z35,z5,z6]),(0,[z0,z1,z2,z543,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z544])],[(0,[z0,z1,z2,z4,z5,z22,z6]),(0,[z0,z32,z147,z2,z4,z5,z6]),(0,[z0,z1,z2,z545,z4,z5,z6]),(0,[z0,z1,z546,z2,z4,z5,z6])],[(0,[z547,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z19,z4,z5,z71])],[(0,[z0,z1,z2,z270,z5,z6,z71]),(0,[z0,z1,z2,z4,z548,z5,z6]),(0,[z0,z549,z1,z2,z4,z5,z6])],[(0,[z199,z109,z1,z2,z4,z5,z6]),(0,[z550,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z551,z6]),(0,[z552,z0,z1,z2,z4,z5,z6]),(0,[z553,z0,z1,z2,z4,z5,z6]),(0,[z554,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z555])]],
   [[(0,[z0,z1,z95,z2,z4,z5,z6]),(0,[z29,z0,z1,z2,z4,z5,z22]),(0,[z0,z2,z66,z4,z39,z5,z6])],[(0,[z0,z1,z2,z4,z5,z556,z6])],[(0,[z0,z1,z557,z2,z4,z5,z6]),(0,[z0,z1,z2,z180,z4,z5,z6])],[(0,[z133,z0,z1,z61,z4,z5,z6]),(0,[z0,z558,z1,z2,z4,z5,z6]),(0,[z0,z32,z1,z45,z4,z5,z6]),(0,[z0,z188,z1,z2,z4,z5,z6]),(0,[z0,z559,z1,z2,z4,z5,z6])],[(0,[z560,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z561,z4,z5,z6])],[(0,[z0,z1,z562,z2,z4,z5,z6]),(0,[z0,z563,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z564,z4,z5,z6]),(0,[z0,z1,z2,z565,z4,z5,z6]),(0,[z0,z1,z2,z119,z5,z17,z6]),(0,[z0,z1,z566,z2,z4,z5,z6]),(0,[z0,z1,z2,z35,z4,z5,z6])],[(0,[z567,z0,z1,z2,z4,z5,z6]),(0,[z568,z0,z1,z2,z4,z5,z6]),(0,[z64,z0,z188,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z569,z6]),(0,[z0,z570,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z571,z5,z6]),(0,[z0,z1,z2,z4,z5,z572,z6])],[(0,[z0,z1,z2,z573,z4,z5,z6]),(0,[z0,z185,z1,z2,z260,z5,z6]),(0,[z0,z1,z2,z4,z574,z5,z6]),(0,[z0,z1,z140,z2,z4,z5,z6]),(0,[z0,z575,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z576]),(0,[z577,z0,z1,z2,z4,z5,z6]),(0,[z29,z0,z2,z118,z4,z5,z6]),(0,[z9,z0,z188,z2,z4,z5,z6])],[(1,[z0,z1,z380,z4,z5,z6]),(0,[z0,z1,z2,z578,z4,z5,z6])],[(0,[z579,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z580,z5,z6])],[(0,[z581,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z582,z6]),(0,[z0,z1,z2,z583,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z584,z6]),(0,[z73,z0,z1,z490,z4,z5,z6]),(0,[z0,z585,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z586])],[(1,[z64,z1,z2,z4,z5,z110])]],
   [[(0,[z0,z1,z2,z284,z4,z39,z6]),(0,[z212,z0,z1,z2,z260,z5,z6]),(0,[z587,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z42,z45,z5,z6]),(1,[z0,z1,z2,z19,z5,z52])],[(0,[z0,z1,z2,z588,z4,z5,z6]),(1,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z589,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z590]),(0,[z591,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z592,z6]),(0,[z0,z1,z2,z4,z5,z593,z6])],[(0,[z594,z0,z1,z2,z4,z5,z6]),(0,[z0,z595,z1,z2,z4,z5,z6]),(0,[z596,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z597,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z102,z17,z6]),(0,[z0,z1,z2,z4,z598,z5,z6])],[(0,[z199,z0,z189,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z599]),(0,[z0,z1,z2,z19,z270,z5,z6]),(0,[z0,z1,z2,z4,z5,z600,z6]),(0,[z601,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z104])],[(0,[z0,z1,z602,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z275,z5,z6])],[(0,[z0,z603,z1,z2,z4,z5,z6]),(0,[z73,z0,z83,z2,z4,z5,z6]),(0,[z73,z0,z1,z2,z4,z5,z110]),(0,[z0,z1,z2,z4,z5,z604,z6])],[(0,[z0,z1,z246,z30,z4,z5,z6]),(0,[z171,z0,z1,z2,z4,z82,z6]),(0,[z0,z605,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z606,z5,z6]),(0,[z0,z607,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z608,z6])]],
   [[(0,[z0,z1,z609,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z610])],[(0,[z0,z1,z2,z4,z5,z611,z6]),(0,[z0,z1,z2,z4,z5,z6,z612]),(0,[z613,z0,z1,z2,z4,z5,z6])],[(0,[z0,z614,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z270,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z615]),(0,[z0,z1,z616,z2,z4,z5,z6])],[],[(1,[z318,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z617,z5,z6]),(0,[z51,z1,z2,z4,z82,z5,z6]),(0,[z0,z1,z2,z618,z4,z5,z6]),(0,[z73,z64,z1,z2,z4,z5,z6]),(0,[z73,z0,z1,z2,z4,z315,z6]),(0,[z0,z619,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z40,z5,z6]),(0,[z0,z1,z2,z4,z5,z209,z6]),(0,[z0,z1,z620,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z621,z5,z6]),(0,[z0,z1,z622,z2,z4,z5,z6]),(0,[z0,z1,z2,z623,z4,z5,z6]),(1,[z73,z1,z2,z4,z5,z160]),(0,[z0,z1,z2,z4,z5,z624,z6]),(0,[z0,z1,z2,z4,z625,z5,z6])],[(0,[z0,z1,z2,z626,z4,z5,z6]),(0,[z0,z1,z30,z4,z5,z6,z104]),(0,[z0,z1,z627,z2,z4,z5,z6]),(1,[z34,z0,z2,z4,z24,z6]),(0,[z0,z1,z181,z2,z45,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z628])],[(0,[z629,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z75,z6]),(0,[z0,z1,z2,z4,z630,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z631]),(0,[z9,z0,z2,z4,z5,z6,z252]),(0,[z0,z1,z42,z181,z4,z5,z6]),(0,[z0,z1,z2,z40,z260,z5,z6])]],
   [[(0,[z189,z1,z95,z2,z4,z5,z6])],[(0,[z632,z0,z1,z2,z4,z5,z6]),(0,[z633,z0,z1,z2,z4,z5,z6]),(0,[z634,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z150,z2,z4,z5,z104]),(0,[z0,z1,z2,z4,z5,z635,z6]),(0,[z0,z636,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z637]),(0,[z638,z0,z1,z2,z4,z5,z6]),(0,[z0,z639,z1,z2,z4,z5,z6])],[(0,[z0,z640,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z45,z66,z5,z6]),(0,[z0,z1,z641,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z13,z5,z6])],[(0,[z0,z1,z642,z2,z4,z5,z6]),(0,[z0,z1,z2,z643,z4,z5,z6])],[(0,[z1,z2,z142,z4,z270,z5,z6]),(0,[z0,z1,z2,z4,z5,z644,z6]),(0,[z0,z23,z1,z2,z207,z4,z6]),(1,[z0,z1,z15,z4,z5,z6]),(0,[z0,z1,z2,z645,z4,z5,z6])],[(0,[z0,z1,z2,z646,z4,z5,z6]),(0,[z0,z1,z30,z4,z40,z5,z6]),(0,[z0,z1,z2,z4,z647,z5,z6])],[(0,[z648,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z17,z6])]],
   [[(0,[z649,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z650,z4,z5,z6]),(0,[z0,z1,z2,z651,z4,z5,z6]),(0,[z0,z1,z181,z2,z40,z5,z6]),(0,[z0,z1,z140,z2,z4,z102,z6]),(0,[z0,z1,z246,z4,z102,z5,z6])],[(0,[z0,z1,z2,z4,z5,z652,z6]),(0,[z653,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z45,z39,z5,z6]),(0,[z0,z23,z1,z2,z7,z5,z6]),(0,[z34,z0,z2,z4,z24,z5,z6]),(0,[z0,z1,z42,z2,z4,z209,z6]),(0,[z0,z1,z2,z654,z4,z5,z6])],[(0,[z655,z0,z1,z2,z4,z5,z6]),(0,[z171,z51,z1,z2,z4,z5,z6]),(0,[z656,z0,z1,z2,z4,z5,z6])],[(0,[z199,z1,z95,z2,z4,z5,z6]),(0,[z64,z0,z1,z2,z4,z5,z104]),(0,[z657,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z658])],[(0,[z0,z1,z659,z2,z4,z5,z6]),(0,[z0,z1,z2,z660,z4,z5,z6]),(0,[z0,z1,z2,z4,z376,z5,z6])],[(0,[z0,z1,z2,z19,z142,z5,z6]),(0,[z0,z1,z2,z4,z661,z5,z6]),(0,[z0,z1,z2,z662,z4,z5,z6]),(0,[z0,z23,z1,z2,z35,z4,z6]),(0,[z0,z1,z2,z4,z5,z663,z6]),(0,[z0,z1,z2,z4,z5,z6,z664])],[(0,[z171,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z448,z6]),(0,[z29,z0,z1,z2,z4,z448,z6]),(0,[z0,z1,z2,z4,z5,z665,z6]),(0,[z0,z666,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z667,z4,z5,z6]),(0,[z0,z1,z2,z668,z4,z5,z6])]],
   [[(1,[z0,z1,z2,z4,z56,z6]),(0,[z0,z669,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z670]),(0,[z0,z671,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z672]),(0,[z673,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z674,z5,z6])],[(0,[z0,z1,z2,z4,z5,z675,z6]),(0,[z51,z0,z1,z2,z4,z82,z6]),(0,[z0,z676,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z677,z4,z5,z6])],[(0,[z73,z0,z1,z380,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z678,z6]),(0,[z0,z1,z679,z2,z4,z5,z6])],[(0,[z0,z1,z1,z2,z4,z5,z6]),(0,[z0,z1,z680,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z681,z5,z6])],[(0,[z682,z0,z1,z2,z4,z5,z6]),(1,[z204,z1,z2,z270,z5,z6])],[(0,[z0,z1,z94,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z683,z5,z6]),(0,[z0,z1,z684,z2,z4,z5,z6]),(0,[z0,z1,z2,z18,z4,z5,z71]),(0,[z0,z1,z2,z4,z5,z685,z6])],[(1,[z0,z1,z2,z4,z315,z6]),(1,[z212,z0,z2,z66,z5,z6])]],
   [[(0,[z686,z0,z1,z2,z4,z5,z6]),(0,[z0,z188,z1,z2,z4,z5,z252])],[(0,[z0,z1,z2,z4,z447,z5,z6]),(1,[z0,z1,z2,z180,z5,z6]),(0,[z0,z1,z2,z35,z4,z111,z6])],[(0,[z0,z1,z2,z687,z4,z5,z6]),(0,[z0,z1,z2,z688,z4,z5,z6]),(0,[z0,z23,z2,z4,z5,z17,z6])],[(0,[z109,z0,z189,z2,z4,z5,z6]),(0,[z689,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z690,z2,z4,z5,z6]),(1,[z171,z1,z2,z4,z90,z6]),(0,[z0,z1,z691,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z692,z6]),(0,[z0,z1,z2,z207,z260,z5,z6]),(0,[z0,z1,z693,z2,z4,z5,z6])],[(0,[z318,z0,z1,z2,z4,z5,z6]),(1,[z74,z1,z61,z4,z5,z6]),(0,[z34,z0,z1,z2,z207,z4,z6]),(0,[z0,z1,z2,z694,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z695,z6]),(0,[z0,z1,z42,z2,z45,z5,z6]),(0,[z0,z1,z140,z2,z4,z111,z6]),(0,[z696,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z697,z6])],[(0,[z698,z0,z1,z2,z4,z5,z6]),(0,[z73,z0,z1,z2,z4,z5,z160]),(0,[z0,z1,z2,z4,z699,z5,z6]),(0,[z0,z1,z2,z35,z4,z260,z6]),(0,[z0,z1,z2,z18,z5,z6,z71])],[(0,[z0,z1,z2,z4,z5,z6,z700]),(0,[z0,z1,z2,z4,z5,z701,z6]),(0,[z702,z0,z1,z2,z4,z5,z6])],[(0,[z703,z0,z1,z2,z4,z5,z6]),(0,[z109,z0,z1,z272,z4,z5,z6]),(0,[z0,z1,z2,z704,z4,z5,z6]),(0,[z0,z1,z61,z2,z4,z5,z264]),(0,[z0,z1,z2,z4,z705,z5,z6]),(0,[z706,z0,z1,z2,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z707,z4,z6]),(0,[z189,z708,z2,z4,z5,z6]),(0,[z0,z1,z2,z66,z225,z6])],[(0,[z133,z1,z30,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z709]),(0,[z0,z185,z1,z2,z284,z6])],[(0,[z0,z1,z710,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z711]),(0,[z390,z1,z2,z270,z5,z6]),(0,[z0,z1,z712,z4,z5,z6])],[(0,[z318,z0,z1,z2,z4,z5]),(0,[z0,z1,z713,z4,z5,z6]),(0,[z0,z1,z2,z8,z102,z6]),(0,[z0,z1,z714,z4,z5,z6])],[(0,[z361,z1,z2,z4,z448,z6]),(0,[z0,z1,z2,z4,z5,z715]),(0,[z0,z1,z45,z496,z5,z6])],[(0,[z0,z1,z2,z4,z6,z716])],[(0,[z29,z0,z118,z275,z5,z6]),(0,[z0,z1,z2,z101,z5,z319]),(0,[z0,z1,z2,z717,z5,z6]),(0,[z0,z1,z718,z4,z5,z6]),(0,[z0,z1,z181,z719,z5,z6])],[(0,[z0,z1,z2,z720,z5,z6]),(0,[z0,z1,z2,z4,z5,z721]),(0,[z0,z1,z2,z35,z225,z6]),(0,[z0,z1,z2,z4,z722,z6])]],
   [[(0,[z0,z1,z181,z275,z5,z6]),(0,[z0,z1,z4,z5,z723,z6])],[(0,[z0,z1,z2,z724,z5,z6]),(0,[z109,z189,z124,z4,z5,z6]),(0,[z0,z1,z2,z284,z45,z6]),(0,[z0,z1,z2,z4,z5,z725])],[(0,[z0,z1,z2,z4,z726,z6]),(0,[z0,z1,z727,z4,z5,z6]),(0,[z728,z1,z2,z4,z5,z6])],[(0,[z0,z1,z729,z4,z5,z6]),(0,[z0,z730,z2,z4,z5,z6]),(0,[z171,z1,z2,z4,z731,z6]),(0,[z0,z1,z2,z4,z732,z6]),(0,[z0,z1,z680,z4,z5,z104])],[(0,[z0,z1,z15,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z733]),(0,[z0,z1,z2,z4,z734,z6]),(0,[z0,z1,z4,z5,z735,z104])],[(0,[z1,z124,z30,z4,z5,z6]),(0,[z0,z1,z2,z4,z6,z736]),(0,[z0,z83,z380,z4,z5,z6]),(0,[z0,z1,z2,z737,z5,z6]),(0,[z0,z1,z738,z4,z5,z6])],[(0,[z271,z1,z61,z4,z5,z6])],[(0,[z0,z1,z2,z4,z13,z437])]],
   [[(0,[z0,z1,z2,z207,z419,z6])],[(0,[z0,z1,z739,z4,z5,z6])],[],[(0,[z0,z1,z380,z4,z315,z6]),(0,[z0,z1,z2,z5,z6,z740]),(0,[z0,z1,z2,z35,z79,z6])],[(0,[z0,z1,z2,z4,z741,z6]),(0,[z29,z0,z118,z101,z5,z6]),(0,[z0,z1,z2,z742,z4,z6])],[(0,[z0,z1,z2,z4,z448,z6]),(0,[z0,z1,z4,z5,z6,z743])],[],[(0,[z133,z1,z744,z4,z5,z6])]],
   [[],[(0,[z0,z1,z2,z4,z5,z745]),(0,[z0,z1,z2,z746,z5,z6]),(0,[z29,z0,z118,z4,z5,z319]),(0,[z0,z1,z172,z4,z102,z6]),(0,[z0,z1,z2,z35,z98,z6]),(0,[z0,z1,z2,z5,z747,z71])],[(0,[z361,z1,z30,z4,z5,z6]),(0,[z0,z1,z119,z303,z5,z6]),(0,[z0,z748,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z749]),(0,[z0,z1,z750,z4,z5,z6]),(0,[z131,z1,z2,z101,z5,z6]),(0,[z212,z0,z2,z464,z5,z6])],[(0,[z0,z1,z2,z4,z751,z6])],[(0,[z0,z1,z2,z4,z5,z752]),(0,[z0,z1,z2,z4,z5,z753]),(0,[z0,z1,z2,z284,z40,z6]),(0,[z212,z0,z2,z754,z5,z6])],[(0,[z0,z1,z124,z4,z5,z755]),(0,[z29,z0,z530,z4,z5,z6]),(0,[z0,z1,z2,z756,z5,z6]),(0,[z0,z1,z757,z4,z5,z6])],[(0,[z0,z1,z2,z758,z5,z6]),(0,[z1,z2,z4,z5,z731,z6]),(0,[z0,z1,z2,z4,z759,z6]),(0,[z0,z1,z2,z760,z5,z6]),(0,[z0,z1,z2,z761,z5,z6])]],
   [[(0,[z29,z0,z762,z4,z5,z6])],[(0,[z0,z1,z2,z4,z731,z6])],[(0,[z171,z1,z2,z4,z90,z6])],[(1,[z708,z2,z4,z5,z6]),(0,[z74,z1,z61,z4,z5,z6])],[(0,[z0,z1,z2,z763,z5,z6]),(0,[z0,z1,z2,z4,z5,z764]),(0,[z0,z1,z2,z765,z5,z6]),(0,[z0,z1,z2,z766,z5,z6]),(0,[z0,z1,z767,z4,z5,z6])],[(0,[z73,z1,z2,z4,z315,z160]),(0,[z25,z26,z1,z4,z5,z36])],[(0,[z0,z762,z118,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z264]),(0,[z768,z1,z2,z4,z5,z6]),(0,[z769,z1,z2,z4,z5,z6])]],
   [[(0,[z74,z83,z2,z4,z5,z6]),(0,[z0,z1,z770,z4,z5,z6])],[(0,[z0,z1,z771,z2,z4,z5]),(0,[z0,z1,z2,z4,z772,z6])],[(0,[z0,z1,z272,z4,z5,z6])],[(0,[z0,z1,z61,z4,z448,z6]),(0,[z0,z1,z2,z4,z5,z773]),(0,[z361,z1,z2,z101,z5,z6]),(0,[z0,z1,z2,z774,z4,z6]),(0,[z344,z0,z2,z4,z5,z252])],[(0,[z0,z1,z2,z775,z5,z6]),(0,[z0,z1,z776,z4,z5,z6]),(0,[z0,z23,z4,z303,z17,z6]),(0,[z0,z1,z2,z719,z5,z6]),(1,[z0,z1,z4,z5,z735])],[(0,[z0,z2,z4,z24,z777,z6])],[(0,[z0,z607,z2,z39,z5,z6]),(0,[z0,z1,z45,z719,z5,z6])],[(0,[z25,z1,z2,z4,z5,z104]),(0,[z0,z1,z2,z4,z13,z14])]],
   [[(0,[z0,z1,z2,z778,z5,z6]),(0,[z0,z1,z779,z4,z5,z6]),(0,[z361,z1,z2,z4,z5,z319])],[(0,[z0,z1,z620,z40,z5,z6]),(0,[z0,z1,z2,z45,z58,z6]),(0,[z26,z291,z1,z4,z5,z36])],[(0,[z0,z1,z2,z780,z4,z5]),(0,[z0,z1,z2,z4,z781,z6]),(0,[z0,z1,z86,z3,z4,z6])],[(0,[z0,z1,z2,z4,z782,z6]),(0,[z0,z1,z2,z783,z5,z6]),(0,[z784,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z785,z4,z6]),(0,[z25,z1,z30,z4,z5,z6]),(0,[z0,z1,z2,z4,z786,z6])],[(0,[z361,z1,z124,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z75]),(0,[z291,z1,z2,z4,z5,z6]),(0,[z0,z787,z2,z4,z5,z6]),(0,[z0,z1,z2,z346,z79,z6]),(0,[z0,z1,z15,z8,z5,z6])],[(0,[z532,z95,z2,z4,z5,z6]),(0,[z0,z1,z2,z207,z293,z6])]],
   [[(0,[z0,z788,z2,z4,z5,z6]),(1,[z0,z762,z4,z5,z6]),(0,[z0,z1,z2,z754,z5,z6]),(0,[z789,z0,z2,z4,z5,z6])],[(0,[z0,z1,z790,z2,z5,z6]),(0,[z696,z0,z2,z4,z24,z6])],[(0,[z0,z1,z2,z4,z5,z791]),(0,[z0,z1,z2,z4,z792,z6]),(0,[z0,z1,z793,z4,z5,z6])],[(0,[z0,z1,z31,z4,z111,z6]),(0,[z0,z1,z794,z4,z5,z6]),(0,[z0,z1,z246,z376,z102,z6])],[(0,[z0,z1,z2,z4,z795,z6]),(0,[z0,z1,z30,z376,z5,z6]),(0,[z0,z1,z2,z4,z796,z6]),(0,[z73,z1,z380,z4,z5,z160]),(0,[z64,z1,z144,z2,z4,z5]),(0,[z0,z1,z2,z101,z5,z6]),(0,[z0,z1,z2,z797,z5,z6]),(0,[z0,z1,z2,z141,z79,z6]),(1,[z0,z1,z2,z4,z725])],[(0,[z0,z1,z2,z249,z260,z6])],[(0,[z0,z2,z754,z4,z5,z6])],[(0,[z0,z1,z2,z284,z4,z6]),(0,[z0,z1,z2,z798,z5,z6]),(0,[z0,z1,z15,z4,z111,z6]),(0,[z9,z0,z2,z4,z5,z252])]],
   [[(0,[z0,z1,z2,z4,z799,z6])],[(0,[z0,z1,z744,z4,z5,z6]),(0,[z0,z800,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z319]),(0,[z0,z1,z2,z4,z6,z801]),(0,[z0,z1,z802,z4,z5,z6])],[(0,[z0,z1,z2,z4,z803,z5]),(0,[z0,z1,z2,z4,z448,z22]),(0,[z0,z1,z126,z4,z5,z6]),(0,[z0,z1,z804,z4,z5,z6]),(0,[z0,z1,z2,z4,z805,z6]),(0,[z0,z1,z2,z207,z806,z6])],[],[(0,[z0,z1,z807,z4,z5,z6]),(0,[z1,z2,z4,z5,z110,z808]),(0,[z0,z1,z2,z4,z56,z22]),(0,[z0,z1,z2,z809,z5,z6])],[(0,[z0,z1,z198,z4,z5,z6]),(0,[z74,z1,z380,z4,z5,z6]),(0,[z810,z1,z2,z4,z5,z6]),(0,[z0,z1,z246,z247,z102,z6])],[(0,[z0,z1,z124,z4,z5,z6]),(0,[z0,z1,z2,z4,z811,z6]),(0,[z1,z2,z4,z5,z808,z160])],[(0,[z0,z1,z2,z812,z5,z6]),(0,[z1,z744,z30,z4,z5,z6]),(0,[z0,z1,z387,z4,z5,z104])]],
   [[(0,[z0,z1,z2,z4,z813,z6]),(0,[z0,z1,z2,z814,z5,z6]),(0,[z0,z1,z2,z191,z200,z6]),(1,[z1,z2,z4,z5,z808]),(0,[z0,z1,z2,z815,z5,z6]),(0,[z0,z1,z2,z7,z17,z6])],[(0,[z109,z708,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z816]),(0,[z817,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z818]),(0,[z0,z1,z196,z45,z5,z6])],[(0,[z0,z1,z2,z4,z819,z6]),(0,[z820,z1,z2,z4,z5,z6]),(0,[z0,z23,z2,z7,z17,z6]),(0,[z0,z1,z2,z35,z806,z6])],[(0,[z0,z1,z2,z4,z5,z821]),(0,[z0,z1,z4,z102,z734,z6]),(0,[z0,z1,z2,z4,z14,z725])],[(0,[z0,z1,z2,z4,z822,z6]),(0,[z0,z1,z2,z545,z260,z6])],[(0,[z199,z318,z95,z2,z4,z5]),(0,[z109,z314,z2,z4,z5,z6]),(0,[z0,z1,z2,z823,z5,z6]),(0,[z0,z415,z2,z191,z5,z6])],[(0,[z399,z1,z2,z142,z5,z6]),(0,[z824,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z825,z6]),(0,[z0,z1,z826,z4,z5,z6]),(0,[z29,z0,z118,z4,z5,z6]),(0,[z0,z32,z147,z4,z5,z6])]],
   [[(0,[z131,z1,z2,z275,z5,z6]),(0,[z0,z1,z2,z4,z827,z6]),(0,[z828,z1,z2,z4,z5,z6])],[(0,[z0,z1,z829,z4,z5,z6]),(0,[z0,z1,z2,z830,z5,z6])],[(0,[z0,z1,z2,z831,z5,z6]),(0,[z1,z2,z30,z4,z5,z75]),(0,[z83,z2,z30,z4,z5,z6]),(1,[z1,z2,z4,z731,z6]),(0,[z0,z1,z181,z40,z5,z6])],[(0,[z0,z1,z2,z832,z5,z6]),(0,[z1,z61,z744,z4,z5,z6])],[(0,[z0,z1,z833,z4,z5,z6]),(0,[z282,z1,z2,z834,z5,z6]),(0,[z0,z415,z2,z4,z200,z6]),(0,[z835,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z102,z448,z6]),(0,[z0,z185,z2,z39,z5,z6]),(0,[z1,z2,z4,z5,z6,z836])],[(0,[z0,z1,z2,z4,z837,z6]),(0,[z0,z1,z2,z4,z5,z838]),(0,[z0,z1,z2,z4,z5,z839]),(0,[z80,z1,z2,z4,z82,z6])],[(0,[z0,z1,z840,z4,z5,z6]),(0,[z0,z1,z8,z303,z5,z6]),(0,[z0,z1,z2,z4,z841,z6])],[(0,[z0,z1,z61,z4,z5,z319])]],
   [[(0,[z199,z95,z2,z4,z5,z6]),(0,[z0,z1,z389,z4,z111,z6])],[(0,[z0,z1,z2,z4,z842,z6]),(0,[z0,z1,z2,z4,z5,z843]),(0,[z0,z844,z2,z4,z5,z6]),(0,[z0,z1,z4,z845,z5,z6])],[(0,[z0,z1,z2,z846,z5,z6]),(0,[z194,z0,z2,z66,z5,z6]),(0,[z0,z1,z2,z8,z111,z6])],[(0,[z0,z1,z2,z847,z5,z6]),(0,[z0,z1,z848,z4,z5,z6]),(0,[z0,z1,z2,z4,z849,z6]),(0,[z0,z1,z2,z4,z209,z6])],[(0,[z0,z1,z2,z191,z5,z6]),(0,[z0,z1,z2,z4,z850,z6])],[(0,[z0,z1,z2,z5,z6,z851]),(0,[z0,z852,z2,z4,z5,z6]),(0,[z0,z1,z4,z5,z735,z6])],[(0,[z1,z2,z834,z270,z5,z6]),(0,[z0,z185,z2,z39,z225,z6]),(0,[z0,z1,z2,z8,z260,z6])],[(0,[z0,z1,z2,z4,z853,z6]),(0,[z854,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z260,z225,z6]),(0,[z0,z1,z4,z5,z734,z6]),(0,[z855,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z260,z806,z6])]],
   [[(0,[z51,z1,z2,z4,z731,z6]),(0,[z361,z1,z2,z275,z5,z6]),(0,[z856,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z857,z5,z6])],[(0,[z0,z1,z858,z4,z5,z6]),(0,[z0,z1,z2,z4,z13,z725])],[(0,[z0,z1,z2,z859,z4,z6]),(0,[z0,z1,z2,z4,z777,z6]),(0,[z0,z1,z860,z4,z5,z6])],[(0,[z0,z1,z2,z4,z200,z6]),(0,[z64,z1,z2,z4,z5,z510]),(0,[z131,z1,z2,z4,z5,z319]),(0,[z0,z23,z2,z119,z17,z6])],[(0,[z0,z1,z2,z4,z5,z861]),(0,[z204,z1,z198,z270,z5,z6])],[(0,[z0,z1,z2,z862,z5,z6]),(0,[z0,z1,z2,z19,z5,z611]),(0,[z0,z1,z4,z734,z111,z6]),(0,[z0,z1,z2,z44,z4,z91])],[(0,[z0,z1,z2,z4,z5,z863]),(0,[z1,z708,z2,z4,z5,z6]),(0,[z0,z1,z124,z4,z5,z864]),(0,[z0,z1,z865,z4,z5,z6]),(0,[z0,z1,z2,z866,z5,z6])],[(0,[z1,z380,z30,z4,z5,z6]),(0,[z0,z1,z15,z4,z448,z6]),(0,[z0,z1,z2,z4,z5,z735])]],
   [[],[(0,[z867,z0,z1,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z868])],[],[(0,[z0,z1,z2,z869,z4,z5]),(0,[z0,z1,z870,z4,z5,z6]),(0,[z0,z1,z2,z4,z6,z871])],[(0,[z601,z1,z30,z4,z5,z6]),(0,[z0,z1,z2,z5,z872,z6]),(0,[z541,z1,z61,z4,z5,z6]),(0,[z0,z1,z246,z4,z102,z6]),(0,[z0,z1,z2,z873,z5,z6])],[(0,[z0,z1,z380,z4,z5,z75])],[(0,[z0,z1,z490,z191,z5,z6]),(0,[z0,z1,z2,z4,z874,z6]),(0,[z0,z1,z2,z207,z260,z6])]],
   [[(0,[z0,z1,z2,z875,z5,z6])],[(0,[z318,z0,z83,z2,z4,z5]),(0,[z73,z1,z2,z4,z5,z599]),(0,[z0,z1,z61,z4,z209,z6]),(0,[z0,z1,z2,z275,z5,z6]),(0,[z0,z1,z2,z4,z5,z876]),(0,[z0,z185,z2,z3,z39,z6]),(0,[z0,z1,z3,z126,z4,z6]),(0,[z0,z1,z2,z4,z5,z877])],[(0,[z0,z1,z2,z878,z5,z6]),(1,[z1,z744,z4,z5,z6]),(0,[z614,z1,z2,z4,z5,z110]),(0,[z879,z1,z2,z4,z5,z6])],[(0,[z0,z1,z45,z275,z5,z6]),(0,[z0,z1,z880,z4,z5,z6])],[(0,[z881,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z882,z5,z6]),(0,[z883,z0,z1,z2,z4,z5])],[],[(0,[z0,z1,z490,z4,z200,z6]),(0,[z0,z1,z2,z4,z5,z884])],[(0,[z0,z83,z2,z191,z5,z6]),(0,[z0,z32,z4,z311,z5,z6])]],
   [[(0,[z0,z1,z885,z4,z5,z6]),(0,[z0,z1,z886,z4,z5,z6]),(0,[z29,z131,z118,z4,z5,z6]),(0,[z0,z32,z473,z4,z5,z6]),(0,[z0,z2,z4,z777,z17,z6])],[(0,[z0,z1,z887,z4,z5,z6]),(0,[z0,z23,z1,z2,z8,z6]),(0,[z0,z1,z140,z4,z111,z6])],[],[(0,[z0,z1,z888,z4,z5,z6]),(0,[z0,z415,z490,z4,z5,z6]),(1,[z0,z1,z2,z5,z747])],[(0,[z0,z1,z297,z4,z5,z6])],[(0,[z109,z189,z2,z4,z5,z6]),(0,[z0,z1,z2,z889,z5,z6]),(0,[z0,z1,z2,z207,z403,z6]),(0,[z0,z1,z2,z4,z58,z6]),(0,[z0,z1,z2,z4,z890,z6])],[(0,[z0,z83,z2,z4,z200,z6]),(0,[z0,z1,z4,z303,z5,z6]),(0,[z0,z185,z2,z141,z5,z6]),(0,[z0,z1,z2,z40,z58,z6])],[(0,[z29,z361,z118,z4,z5,z6]),(0,[z0,z2,z762,z4,z5,z6]),(0,[z0,z639,z2,z39,z5,z6])]],
   [[(0,[z25,z1,z2,z4,z5,z6]),(0,[z73,z1,z2,z4,z5,z697]),(0,[z0,z2,z754,z39,z5,z6])],[(0,[z0,z891,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z892,z6]),(0,[z0,z1,z2,z447,z200,z6]),(0,[z0,z1,z2,z4,z893,z6]),(0,[z0,z1,z2,z35,z394,z6])],[(0,[z0,z1,z894,z4,z5,z6]),(0,[z0,z1,z2,z5,z895,z6]),(0,[z0,z1,z2,z44,z4,z725])],[(0,[z0,z1,z94,z2,z4,z5]),(0,[z0,z1,z46,z4,z5,z6]),(0,[z0,z896,z2,z4,z5,z6]),(0,[z34,z0,z1,z2,z8,z6])],[(0,[z0,z83,z2,z4,z5,z104]),(0,[z0,z1,z2,z4,z5,z897])],[],[(0,[z0,z1,z2,z4,z5,z898]),(0,[z0,z1,z30,z4,z448,z6]),(0,[z0,z415,z2,z447,z5,z6]),(0,[z0,z1,z2,z899,z5,z6]),(0,[z0,z147,z762,z4,z5,z6]),(0,[z0,z1,z2,z4,z900,z6])],[(0,[z0,z1,z901,z4,z5,z6]),(0,[z0,z1,z2,z902,z5,z6]),(0,[z0,z1,z61,z275,z5,z6])]],
   [[(0,[z903,z1,z2,z4,z5,z6]),(0,[z904,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z376,z5,z6])],[(0,[z74,z1,z2,z4,z5,z75]),(0,[z0,z2,z4,z777,z5,z6])],[(0,[z0,z1,z2,z4,z5,z905])],[(0,[z0,z1,z2,z275,z56,z6]),(0,[z0,z1,z906,z4,z5,z6]),(0,[z0,z1,z907,z4,z5,z6])],[(0,[z0,z185,z2,z39,z77,z6])],[(0,[z0,z1,z2,z687,z5,z71]),(0,[z0,z1,z2,z4,z908,z6]),(0,[z0,z1,z4,z102,z425,z6])],[(0,[z0,z1,z4,z909,z5,z6]),(0,[z0,z1,z2,z4,z910,z6]),(0,[z0,z1,z2,z834,z5,z6]),(0,[z656,z1,z2,z4,z90,z6]),(0,[z0,z185,z86,z39,z5,z6]),(0,[z212,z0,z1,z2,z284,z6]),(0,[z911,z1,z2,z4,z5,z6]),(1,[z0,z1,z4,z734,z6])],[]],
   [[(0,[z0,z1,z2,z4,z912,z6]),(0,[z74,z1,z61,z4,z5,z264]),(0,[z0,z185,z2,z754,z5,z6]),(0,[z0,z913,z2,z4,z5,z6]),(0,[z0,z914,z2,z4,z5,z6])],[(0,[z0,z1,z2,z915,z4,z6]),(0,[z0,z1,z2,z5,z6,z916])],[(0,[z0,z1,z2,z4,z5,z755]),(0,[z73,z57,z1,z2,z4,z5]),(0,[z0,z1,z2,z247,z5,z6])],[(0,[z112,z1,z30,z4,z5,z6]),(0,[z0,z2,z66,z754,z5,z6]),(0,[z917,z1,z2,z4,z5,z6])],[(0,[z74,z1,z744,z4,z5,z6]),(0,[z0,z1,z918,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z919]),(0,[z0,z1,z2,z366,z4,z91]),(0,[z0,z1,z380,z191,z5,z6]),(0,[z0,z1,z2,z920,z4,z6]),(0,[z921,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z447,z5,z6]),(0,[z0,z2,z4,z5,z884,z252])],[(0,[z318,z1,z2,z30,z4,z5]),(0,[z25,z1,z61,z4,z5,z6]),(0,[z0,z1,z922,z4,z5,z6]),(0,[z0,z1,z2,z923,z5,z6])],[(0,[z0,z1,z2,z4,z5,z864]),(0,[z0,z1,z197,z4,z5,z104]),(0,[z0,z1,z2,z101,z448,z6]),(0,[z26,z0,z1,z4,z5,z735]),(1,[z0,z1,z2,z806,z6])]],
   [[(0,[z282,z1,z2,z142,z5,z6]),(0,[z0,z1,z2,z7,z24,z6]),(0,[z0,z1,z42,z45,z209,z6]),(0,[z0,z1,z140,z4,z734,z6])],[(0,[z131,z1,z2,z4,z5,z6]),(0,[z74,z1,z124,z4,z5,z6]),(0,[z0,z1,z924,z4,z5,z6]),(0,[z0,z1,z2,z101,z56,z6]),(0,[z0,z1,z2,z5,z52,z747])],[(0,[z0,z1,z2,z4,z925,z6])],[(0,[z0,z1,z365,z4,z5,z6])],[(0,[z0,z1,z2,z926,z5,z6]),(0,[z0,z1,z2,z4,z448,z319]),(0,[z0,z1,z2,z7,z5,z6]),(0,[z0,z1,z2,z19,z5,z747])],[(0,[z68,z189,z2,z4,z5,z6]),(0,[z0,z1,z927,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z928]),(0,[z0,z1,z2,z929,z5,z6])],[(0,[z0,z1,z61,z376,z5,z6]),(0,[z0,z1,z2,z275,z5,z22]),(0,[z0,z1,z2,z4,z56,z319])],[(0,[z74,z1,z61,z4,z5,z75]),(0,[z0,z930,z2,z4,z5,z6]),(0,[z0,z607,z1,z2,z35,z6])]],
   [[(0,[z0,z559,z2,z4,z17,z6]),(0,[z0,z1,z719,z40,z5,z6]),(0,[z0,z1,z246,z4,z734,z6]),(0,[z0,z1,z2,z35,z468,z6])],[(0,[z0,z931,z2,z4,z5,z6]),(0,[z0,z1,z380,z4,z5,z104]),(0,[z0,z1,z140,z4,z448,z6]),(0,[z29,z0,z195,z4,z5,z6])],[(0,[z0,z1,z2,z4,z932,z6]),(0,[z1,z2,z834,z4,z5,z6]),(1,[z0,z2,z754,z5,z6]),(0,[z0,z1,z2,z806,z79,z6])],[(0,[z0,z1,z4,z5,z75,z104])],[(0,[z0,z933,z2,z4,z5,z6])],[(0,[z0,z1,z934,z2,z4,z5])],[(0,[z0,z1,z2,z4,z935,z6]),(0,[z73,z1,z2,z191,z5,z160])],[(0,[z0,z1,z936,z4,z5,z6]),(0,[z0,z23,z2,z4,z777,z6]),(0,[z0,z2,z4,z5,z6,z884])]],
   [[(0,[z0,z1,z490,z447,z5,z6]),(0,[z0,z1,z86,z45,z5,z6]),(0,[z0,z1,z937,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z747])],[(0,[z361,z1,z2,z4,z5,z6]),(0,[z26,z0,z1,z4,z5,z75]),(0,[z0,z1,z938,z2,z4,z5]),(0,[z65,z0,z1,z2,z35,z6]),(0,[z0,z1,z2,z4,z939,z6])],[(0,[z29,z0,z118,z4,z448,z6])],[(0,[z0,z415,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z940,z6]),(0,[z0,z1,z86,z275,z5,z6]),(0,[z0,z23,z2,z4,z17,z6])],[(0,[z199,z94,z95,z2,z4,z5]),(0,[z0,z1,z2,z101,z5,z22]),(0,[z29,z0,z118,z4,z56,z6])],[(0,[z0,z1,z2,z941,z4,z6]),(0,[z73,z1,z2,z4,z200,z160])],[(0,[z0,z1,z942,z4,z5,z6]),(0,[z0,z1,z2,z943,z5,z6]),(0,[z0,z1,z2,z944,z5,z6])],[(0,[z0,z1,z945,z4,z5,z6]),(0,[z0,z1,z2,z5,z6,z747])]],
   [[(0,[z0,z1,z946,z2,z5,z6]),(0,[z0,z1,z947,z4,z5,z6]),(0,[z0,z1,z2,z948,z5,z6]),(0,[z0,z83,z2,z447,z5,z6]),(0,[z949,z1,z2,z4,z5,z6])],[(0,[z0,z1,z950,z4,z5,z6]),(0,[z34,z0,z2,z4,z777,z6]),(0,[z0,z1,z2,z247,z102,z6])],[(0,[z9,z0,z83,z2,z4,z5]),(0,[z73,z415,z2,z4,z5,z160]),(0,[z0,z1,z2,z4,z5,z951]),(0,[z0,z1,z2,z18,z5,z71])],[(0,[z0,z2,z4,z5,z6,z952]),(0,[z0,z188,z83,z2,z4,z5]),(0,[z131,z1,z2,z4,z56,z6])],[(0,[z0,z1,z953,z4,z5,z6]),(0,[z0,z1,z2,z4,z954,z6]),(0,[z0,z1,z2,z955,z5,z6]),(0,[z0,z1,z2,z35,z513,z6]),(0,[z0,z1,z196,z4,z102,z6]),(0,[z0,z1,z2,z19,z5,z52])],[(0,[z0,z1,z2,z119,z5,z6]),(0,[z0,z1,z2,z956,z5,z6]),(0,[z0,z1,z42,z719,z5,z6])],[(0,[z0,z1,z957,z4,z5,z6])],[(0,[z0,z1,z2,z958,z5,z6])]],
   [[(0,[z25,z1,z380,z4,z5,z6]),(0,[z0,z1,z2,z18,z5,z747])],[(0,[z0,z1,z2,z284,z207,z6])],[(0,[z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z959,z5,z6]),(0,[z204,z1,z365,z270,z5,z6]),(0,[z0,z1,z2,z960,z5,z6]),(0,[z0,z23,z15,z4,z17,z6]),(0,[z0,z1,z42,z45,z58,z6]),(0,[z0,z1,z2,z4,z961,z6])],[(0,[z0,z1,z2,z962,z5,z6]),(0,[z0,z188,z484,z2,z4,z5])],[(0,[z1,z2,z4,z5,z6,z808]),(0,[z0,z1,z86,z284,z4,z6])],[(0,[z0,z1,z2,z963,z5,z6]),(0,[z964,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z965,z5,z6]),(0,[z0,z1,z966,z4,z5,z6])],[(0,[z0,z1,z967,z4,z5,z6]),(0,[z0,z1,z2,z284,z7,z6])],[(0,[z0,z32,z646,z4,z5,z6]),(0,[z361,z1,z61,z4,z5,z6]),(1,[z1,z2,z834,z5,z6]),(0,[z29,z0,z118,z4,z5,z22]),(0,[z0,z1,z2,z968,z5,z6])]],
   [[(0,[z0,z1,z2,z969,z5,z6]),(0,[z634,z1,z30,z4,z5,z6]),(0,[z0,z1,z2,z191,z315,z6]),(0,[z73,z1,z2,z4,z5,z600]),(0,[z0,z1,z284,z126,z4,z6]),(0,[z0,z1,z4,z5,z970,z6])],[(0,[z0,z1,z971,z4,z5,z6]),(0,[z73,z1,z2,z4,z5,z160]),(0,[z1,z2,z4,z5,z6,z972]),(0,[z0,z1,z973,z4,z5,z6]),(0,[z25,z1,z2,z4,z5,z36])],[(0,[z708,z95,z2,z4,z5,z6]),(0,[z0,z1,z974,z2,z4,z6]),(0,[z0,z1,z2,z975,z5,z6]),(0,[z0,z976,z2,z4,z5,z6]),(0,[z73,z1,z2,z4,z5,z164]),(0,[z34,z0,z2,z4,z24,z6]),(0,[z0,z1,z2,z4,z725,z91])],[(0,[z361,z1,z2,z4,z56,z6]),(0,[z0,z1,z2,z39,z225,z6]),(0,[z34,z0,z2,z645,z4,z6])],[(0,[z199,z708,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z977,z6]),(0,[z0,z1,z2,z4,z5,z978]),(0,[z0,z1,z2,z5,z6,z979]),(0,[z0,z1,z2,z4,z225,z6]),(0,[z0,z1,z15,z119,z5,z6]),(0,[z0,z1,z2,z4,z806,z6])],[(0,[z0,z1,z2,z4,z5,z980]),(0,[z1,z2,z142,z834,z5,z6]),(0,[z0,z981,z2,z4,z5,z6]),(0,[z982,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z247,z111,z6]),(0,[z0,z1,z150,z4,z5,z735])],[(0,[z0,z1,z2,z4,z5,z983]),(0,[z131,z1,z2,z4,z5,z22]),(0,[z0,z1,z597,z45,z5,z6]),(0,[z0,z636,z2,z66,z5,z6]),(0,[z9,z0,z2,z4,z5,z884])],[(0,[z1,z2,z4,z731,z90,z6]),(0,[z0,z1,z150,z4,z5,z104])]],
   [[(0,[z0,z1,z2,z4,z984,z6]),(0,[z0,z1,z2,z4,z5,z985]),(0,[z0,z1,z2,z4,z986,z6]),(0,[z0,z1,z2,z4,z987,z6])],[(0,[z0,z1,z988,z4,z5,z6]),(0,[z989,z1,z2,z4,z5,z6])],[],[(0,[z0,z1,z2,z990,z4,z5]),(0,[z0,z23,z2,z141,z4,z6])],[(0,[z0,z1,z30,z4,z209,z6]),(0,[z0,z415,z2,z4,z315,z6]),(0,[z0,z1,z2,z275,z448,z6]),(0,[z991,z1,z2,z4,z5,z6]),(0,[z29,z0,z566,z4,z5,z6]),(1,[z0,z2,z4,z777,z6]),(0,[z0,z1,z992,z4,z5,z6])],[(0,[z0,z993,z2,z4,z5,z6]),(0,[z0,z1,z490,z4,z5,z6]),(0,[z0,z1,z380,z447,z5,z6]),(0,[z0,z1,z4,z5,z36,z735])],[(0,[z0,z1,z2,z994,z5,z6]),(0,[z0,z1,z762,z4,z5,z6]),(0,[z0,z23,z2,z180,z17,z6])],[(0,[z0,z1,z4,z995,z5,z6])]],
   [[],[(0,[z0,z1,z2,z4,z996,z6])],[(0,[z0,z1,z2,z4,z997,z6]),(0,[z0,z1,z998,z4,z5,z6]),(0,[z0,z1,z999,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1000,z6]),(0,[z0,z83,z2,z4,z5,z36])],[(0,[z657,z95,z2,z4,z5,z6]),(0,[z73,z1,z490,z4,z5,z160]),(0,[z0,z1,z2,z4,z5,z808]),(0,[z0,z1,z2,z4,z56,z6]),(0,[z0,z1,z2,z207,z7,z6])],[(0,[z0,z83,z2,z4,z5,z6]),(0,[z0,z32,z762,z4,z5,z6]),(0,[z0,z23,z2,z8,z17,z6]),(0,[z0,z2,z4,z5,z1001,z6]),(0,[z0,z1,z2,z1002,z5,z6])],[(0,[z1,z744,z2,z4,z5,z6]),(0,[z361,z1,z2,z4,z5,z22]),(0,[z0,z1,z2,z1003,z5,z6])],[(0,[z482,z1,z30,z4,z5,z6]),(0,[z0,z1,z1004,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z1005,z5,z6])],[(0,[z318,z0,z188,z2,z4,z5]),(0,[z0,z1,z1006,z4,z5,z6]),(0,[z204,z1,z2,z270,z5,z6])],[(0,[z0,z1,z2,z4,z1007,z6]),(0,[z0,z1,z2,z4,z5,z1008])],[(0,[z0,z1,z2,z4,z1009,z6]),(0,[z0,z1,z2,z4,z315,z6]),(0,[z1010,z1,z2,z4,z5,z6]),(0,[z212,z0,z2,z66,z5,z6]),(0,[z0,z607,z2,z4,z17,z6]),(0,[z0,z1,z2,z1011,z5,z6]),(0,[z1012,z1,z2,z4,z5,z6])],[(0,[z73,z83,z2,z4,z5,z160]),(0,[z73,z1,z2,z4,z5,z808]),(0,[z0,z1,z2,z1013,z4,z6]),(0,[z0,z185,z126,z39,z5,z6]),(0,[z0,z1,z2,z35,z7,z6]),(0,[z0,z277,z2,z4,z24,z6])],[(0,[z0,z1,z2,z1014,z5,z6]),(0,[z0,z1,z2,z1015,z5,z6]),(0,[z0,z1,z152,z40,z5,z6]),(0,[z0,z1,z2,z4,z1016,z6]),(0,[z0,z1,z2,z1017,z5,z6]),(0,[z0,z1,z2,z180,z5,z6])],[(0,[z0,z1,z380,z4,z200,z6])],[(0,[z0,z1,z2,z1018,z5,z6]),(0,[z0,z1,z2,z1019,z5,z6]),(0,[z73,z1,z2,z447,z5,z160])]],
   [[(0,[z698,z1,z30,z4,z5,z6]),(0,[z0,z1,z1020,z4,z5,z6]),(0,[z0,z1,z1021,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1022,z6]),(0,[z0,z1,z2,z5,z806,z6])],[(0,[z0,z1,z2,z4,z5,z1023]),(0,[z73,z1,z30,z4,z5,z104]),(0,[z0,z1,z30,z275,z5,z6]),(0,[z51,z1,z2,z4,z82,z6]),(0,[z0,z1,z2,z4,z1024,z6]),(0,[z0,z1,z719,z4,z5,z6])],[(0,[z1025,z0,z2,z4,z5,z6]),(0,[z0,z415,z380,z4,z5,z6]),(0,[z1026,z1,z2,z4,z5,z6])],[(0,[z171,z1,z297,z4,z90,z6]),(0,[z0,z1,z2,z8,z5,z6])],[(0,[z0,z1,z2,z1027,z5,z6])],[(0,[z1028,z1,z2,z4,z5,z6])],[(0,[z0,z1,z1029,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z22]),(0,[z0,z1,z2,z1030,z4,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z1031]),(0,[z0,z83,z490,z4,z5,z6]),(0,[z0,z1,z15,z4,z102,z6]),(0,[z26,z0,z1,z4,z5,z36])],[],[(0,[z74,z318,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z1032,z6]),(0,[z1033,z1,z2,z4,z5,z6])],[(0,[z0,z1,z1034,z4,z5,z6]),(0,[z171,z1,z46,z4,z90,z6])],[(0,[z0,z1,z1035,z4,z5,z6]),(0,[z0,z1,z2,z1036,z4,z6]),(0,[z673,z0,z1,z4,z5,z36])],[(0,[z0,z1,z2,z1037,z4,z5]),(0,[z109,z189,z272,z4,z5,z6]),(0,[z0,z1,z1038,z4,z5,z6])],[(0,[z0,z1,z490,z4,z315,z6]),(0,[z0,z1,z2,z8,z225,z6])],[(0,[z0,z1,z2,z4,z5,z1039]),(0,[z1040,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z1041,z5,z6]),(0,[z0,z1,z380,z4,z5,z36])],[(0,[z183,z1,z30,z4,z5,z6]),(0,[z204,z1,z2,z834,z5,z6]),(0,[z0,z1,z1042,z4,z5,z6]),(1,[z0,z1,z719,z5,z6])],[(0,[z0,z708,z2,z4,z5,z6]),(0,[z0,z1,z380,z4,z5,z6]),(0,[z0,z1,z2,z4,z77,z6]),(0,[z0,z1,z1043,z4,z5,z6])],[(0,[z0,z1,z2,z4,z6,z725])],[(0,[z0,z1,z1044,z4,z5,z6]),(0,[z0,z1,z2,z1045,z5,z6]),(0,[z1,z2,z4,z82,z731,z6]),(0,[z131,z1,z2,z4,z448,z6]),(0,[z0,z1,z86,z4,z5,z6])],[(0,[z0,z1,z30,z4,z5,z319]),(0,[z64,z1,z2,z4,z5,z808]),(0,[z0,z1,z86,z40,z5,z6]),(0,[z0,z1,z2,z284,z79,z6]),(0,[z0,z1,z4,z5,z1046,z6])],[(0,[z64,z1,z2,z4,z5,z110]),(0,[z0,z83,z2,z4,z315,z6]),(0,[z0,z1047,z2,z4,z5,z6])],[(0,[z0,z1,z2,z260,z624,z6]),(0,[z0,z1,z42,z45,z5,z6])]],
   [[(0,[z0,z1,z2,z275,z5,z319]),(0,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z1048,z6])],[(0,[z0,z1,z2,z4,z1049,z6]),(0,[z0,z1,z42,z564,z5,z6]),(0,[z0,z1,z246,z4,z302,z6]),(0,[z0,z1,z2,z447,z315,z6]),(0,[z0,z1,z1050,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1051])],[(0,[z0,z1,z2,z8,z79,z6])],[(0,[z0,z1,z2,z4,z1052,z6]),(0,[z0,z1,z2,z4,z1053,z6]),(0,[z0,z185,z2,z284,z39,z6])],[(0,[z0,z1,z4,z5,z6,z1054]),(0,[z1055,z1,z2,z4,z5,z6])],[(0,[z1056,z1,z2,z4,z5,z6])],[(0,[z318,z0,z2,z4,z5,z252]),(0,[z0,z1,z1057,z4,z5,z6])],[(0,[z0,z1,z1058,z4,z5,z6]),(0,[z0,z1,z2,z1059,z5,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 563) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 563).take 470) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1033)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [563, 470] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 185).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 185).take 71).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [185, 71] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_39155

theorem PEqualNP.Outside.L_meta_39155 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4207462592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4207462592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39155.solve