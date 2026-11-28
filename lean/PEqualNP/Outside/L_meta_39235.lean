import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39235

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
  Nat.testBit (4277074602 * 2 ^ 32 + 4241287296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0044404ae24c0db2#64 ++ 0x20044404ae24c0db#64 ++ 0x70ccc1ffe24c1fff#64 ++ 0xd70ccc1ffe24c1ff#64 : BitVec 256),
   (0x01113126009562d5#64 ++ 0x401113126009562d#64 ++ 0x9333312603ffe3ff#64 ++ 0xb9333312603ffe3f#64 : BitVec 256),
   (0x143c16382c70b461#64 ++ 0x8143c16382c70b46#64 ++ 0xfc3c3e387c70fc7d#64 ++ 0x7fc3c3e387c70fc7#64 : BitVec 256),
   (0x2bc02bc05780db06#64 ++ 0x02bc02bc05780db0#64 ++ 0xffc03fc07f80ff8c#64 ++ 0xfffc03fc07f80ff8#64 : BitVec 256),
   (0x0eeec0007b6a0008#64 ++ 0x00eeec0007b6a000#64 ++ 0xafffc0007fff000b#64 ++ 0xfafffc0007fff000#64 : BitVec 256),
   (0x4fbbbdb500000000#64 ++ 0x04fbbbdb50000000#64 ++ 0x4fffffff80000007#64 ++ 0xf4fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 2]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [1, 10]⟩, ⟨.and, [11, 9]⟩, ⟨.and, [12, 7]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x70ccc1ffe24c1fff 0xd70ccc1ffe24c1ff

def z1 : W := mkw 0x01113126009562d5 0x401113126009562d 0x9333312603ffe3ff 0xb9333312603ffe3f

def z2 : W := mkw 0x0eae800039620008 0x00eae80003962000 0xaf3f00007df30009 0x7af3f00007df3000

def z3 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xafffc0007fff000b 0xfafffc0007fff000

def z4 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xfc3c3e387c70fc7d 0x7fc3c3e387c70fc7

def z5 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xffc03fc07f80ff8c 0xfffc03fc07f80ff8

def z6 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x4fffffff80000007 0xf4fffffff8000000

def z7 : W := mkw 0x4fbffdbfa04c04b0 0x24fbffdbfa04c04b 0x4fffffff804c0077 0xf4fffffff804c007

def z8 : W := mkw 0x042c000028600000 0x0042c00002860000 0x2c0c00007c000000 0x42c0c00007c00000

def z9 : W := mkw 0x0438143000102041 0x0043814300010204 0xdc3c3e380070e07d 0x7dc3c3e380070e07

def z10 : W := mkw 0x046ec0007b6a0008 0x0046ec0007b6a000 0xa03fc0007fff000b 0x0a03fc0007fff000

def z11 : W := mkw 0x100402082c70b461 0x8100402082c70b46 0xfc003e007c70fc7c 0x7fc003e007c70fc7

def z12 : W := mkw 0x443b943500000000 0x0443b94350000000 0x003fc03f80000003 0x0003fc03f8000000

def z13 : W := mkw 0x0040004042000902 0x0004000404200090 0x00c001c002000380 0x800c001c00200038

def z14 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xffccffffff80ff8f 0xfffccffffff80ff8

def z15 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0x2cccc0007c000000 0x42cccc0007c00000

def z16 : W := mkw 0x0000000000000000 0x0000000000000000 0x8333000003ff000b 0xb8333000003ff000

def z17 : W := mkw 0x101016380410b461 0x8101016380410b46 0x50003e380000fc74 0x050003e380000fc7

def z18 : W := mkw 0x142c06182c609420 0x8142c06182c60942 0x6c0c0e187c001c00 0x46c0c0e187c001c0

def z19 : W := mkw 0x00111026001520d1 0x400111026001520d 0x00330026007f0073 0x000330026007f007

def z20 : W := mkw 0x2bd13be65795fbd7 0x42bd13be65795fbd 0xfff33fe67fffffff 0xffff33fe67ffffff

def z21 : W := mkw 0x153d373c2c70b461 0x8153d373c2c70b46 0xff3f3f3e7c70fc7f 0xfff3f3f3e7c70fc7

def z22 : W := mkw 0x4fbfbdb528600000 0x04fbfbdb52860000 0xeffffffffc70000f 0xfeffffffffc70000

def z23 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0x03ffc00003ff0003 0x803ffc00003ff000

def z24 : W := mkw 0x0b80298000000000 0x00b8029800000000 0x4fc03fc000000004 0xf4fc03fc00000000

def z25 : W := mkw 0x6ffbbff55780db06 0x06ffbbff55780db0 0xffffffffff80ff8f 0xfffffffffff80ff8

def z26 : W := mkw 0x5fbbbfb50c30b041 0x85fbbbfb50c30b04 0xcfffffff9c30e007 0xfcfffffff9c30e00

def z27 : W := mkw 0x0b80298000000000 0x00b8029800000000 0x0f003e0000000000 0x20f003e000000000

def z28 : W := mkw 0x3fec2fd87fe0df26 0x83fec2fd87fe0df2 0xffcc3fd87f80ff8c 0xfffcc3fd87f80ff8

def z29 : W := mkw 0x4fbbbdb500804204 0x04fbbbdb50080420 0xdfffffff8380e38f 0xfdfffffff8380e38

def z30 : W := mkw 0x2bc2ebc0578adb0e 0x02bc2ebc0578adb0 0xffc3ffc07f8fff8e 0xfffc3ffc07f8fff8

def z31 : W := mkw 0x0a82800000000000 0x00a8280000000000 0x03c3c00000000002 0x803c3c0000000000

def z32 : W := mkw 0x147c56387f7ab469 0x8147c56387f7ab46 0xfc3c3e387ffffc7d 0x7fc3c3e387ffffc7

def z33 : W := mkw 0x004440007b6a0008 0x0004440007b6a000 0xa00000007fff0008 0x0a00000007fff000

def z34 : W := mkw 0x41113db500000000 0x041113db50000000 0x40003fff80000004 0x040003fff8000000

def z35 : W := mkw 0x0eaa800019220008 0x00eaa80001922000 0x8f3300001db30000 0x28f3300001db3000

def z36 : W := mkw 0x2feeebc07feadb0e 0x02feeebc07feadb0 0xffffffc07fffff8f 0xfffffffc07fffff8

def z37 : W := mkw 0x101412282c70b461 0x8101412282c70b46 0xb03030207c70fc7d 0x3b03030207c70fc7

def z38 : W := mkw 0x1010143800102461 0x8101014380010246 0x0000003800000070 0x0000000380000007

def z39 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c003e0000000004 0x74c003e000000000

def z40 : W := mkw 0x00444002624c0090 0x000444002624c009 0x30ccc126624c03ff 0xd30ccc126624c03f

def z41 : W := mkw 0x0ac4404af34c0db2 0x20ac4404af34c0db 0xffccc1ffffcc1fff 0xfffccc1ffffcc1ff

def z42 : W := mkw 0x0eaa800000000000 0x00eaa80000000000 0x0fffc00000000003 0xf0fffc0000000000

def z43 : W := mkw 0x4ffffdb57b6a0008 0x04ffffdb57b6a000 0xefffffffffff000f 0xfefffffffffff000

def z44 : W := mkw 0x31103ff80490ff67 0x831103ff80490ff6 0x50003ff80000fff4 0x050003ff80000fff

def z45 : W := mkw 0x6ffbbdf553804b06 0x06ffbbdf553804b0 0x4fffffff83800387 0xf4fffffff8380038

def z46 : W := mkw 0x0eeec042fb6e099a 0x20eeec042fb6e099 0xafffc1c7ffff038b 0xfafffc1c7ffff038

def z47 : W := mkw 0x443b943500000000 0x0443b94350000000 0x4c3ffe3f80000007 0x74c3ffe3f8000000

def z48 : W := mkw 0x0438143000000000 0x0043814300000000 0x4c3c3e3800000005 0x74c3c3e380000000

def z49 : W := mkw 0x0044400062480000 0x0004440006248000 0x20000000624c0008 0x020000000624c000

def z50 : W := mkw 0x1438143008302041 0x8143814300830204 0x0030000000300000 0x0003000000030000

def z51 : W := mkw 0x4ffffdb57b6a0008 0x04ffffdb57b6a000 0xaffffe007fff000b 0xfaffffe007fff000

def z52 : W := mkw 0x0fefe1067bef429c 0x40fefe1067bef429 0xafffc1067fff038b 0xfafffc1067fff038

def z53 : W := mkw 0x00444042e24c0992 0x200444042e24c099 0x20ccc1c7e24c038b 0xd20ccc1c7e24c038

def z54 : W := mkw 0x0000020004009000 0x0000002000400900 0xfc003e007c00fc0c 0x7fc003e007c00fc0

def z55 : W := mkw 0x0004000820400420 0x0000400082040042 0x700c003860401c7d 0x5700c003860401c7

def z56 : W := mkw 0x042ec000286a0008 0x0042ec000286a000 0x000cc00000000000 0x0000cc0000000000

def z57 : W := mkw 0x21446bcae6ccdfb6 0x221446bcae6ccdfb 0x70ccffffe24cffff 0xd70ccffffe24cfff

def z58 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x700001ffe24c1ffc 0x0700001ffe24c1ff

def z59 : W := mkw 0x6eea8ed157009902 0x06eea8ed15700990 0x6cccced9fc001c00 0x46cccced9fc001c0

def z60 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xbf003e007f80ff88 0x2bf003e007f80ff8

def z61 : W := mkw 0x2bc12bc65785db96 0x42bc12bc65785db9 0xffc33fc67f8fff8e 0xfffc33fc67f8fff8

def z62 : W := mkw 0x0a80088000000000 0x00a8008800000000 0x4cc00ec000000000 0x44cc00ec00000000

def z63 : W := mkw 0x2bc46bcaf7ccdfb6 0x22bc46bcaf7ccdfb 0xffc03fc07fccfffc 0xfffc03fc07fccfff

def z64 : W := mkw 0x40000c9100000000 0x040000c910000000 0x40000ed980000000 0x040000ed98000000

def z65 : W := mkw 0x4011143500000000 0x0401114350000000 0x0000003f80000000 0x00000003f8000000

def z66 : W := mkw 0x00444048e2480d22 0x200444048e2480d2 0x60ccc0d9e0001c00 0x460ccc0d9e0001c0

def z67 : W := mkw 0x0111312400916245 0x4011131240091624 0x8333300001b3e000 0x28333300001b3e00

def z68 : W := mkw 0x0000000000102041 0x0000000000010204 0x900000000070e078 0x0900000000070e07

def z69 : W := mkw 0x204002405780db06 0x0204002405780db0 0xb00000007f80ff88 0x0b00000007f80ff8

def z70 : W := mkw 0x41113db500000000 0x041113db50000000 0x40ccffff80000007 0xd40ccffff8000000

def z71 : W := mkw 0x042c000028600000 0x0042c00002860000 0x003c000000700001 0x0003c00000070000

def z72 : W := mkw 0x0100298000000000 0x0010029800000000 0x40003fc000000004 0x040003fc00000000

def z73 : W := mkw 0x0ac6c000734a0008 0x00ac6c000734a000 0x23cfc00063cf000b 0xd23cfc00063cf000

def z74 : W := mkw 0x143c143828702461 0x8143c14382870246 0x003c003800700071 0x0003c00380070007

def z75 : W := mkw 0x047c547ae24c0db2 0x2047c547ae24c0db 0x7cfcffffe24c1fff 0xf7cfcffffe24c1ff

def z76 : W := mkw 0x0111312600854294 0x4011131260085429 0x03333126038f0387 0xb03333126038f038

def z77 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x30000000624c1ff8 0x030000000624c1ff

def z78 : W := mkw 0x00000002009562d5 0x400000002009562d 0x9000012603ffe3ff 0x99000012603ffe3f

def z79 : W := mkw 0x200002400480db06 0x0200002400480db0 0x100000000000ff80 0x0100000000000ff8

def z80 : W := mkw 0x5fbfbfbd2c70b461 0x85fbfbfbd2c70b46 0xfffffffffc70fc7f 0xffffffffffc70fc7

def z81 : W := mkw 0x204002405780db06 0x0204002405780db0 0xfc003e007f80ff8c 0x7fc003e007f80ff8

def z82 : W := mkw 0x2bc029c053804b06 0x02bc029c053804b0 0x4fc03fc003800384 0xf4fc03fc00380038

def z83 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x0ffffe0000000003 0xf0ffffe000000000

def z84 : W := mkw 0x00404042c20c0992 0x200404042c20c099 0x00c0c1c7820c0382 0x800c0c1c7820c038

def z85 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x70ccc1ffe0001ff4 0x470ccc1ffe0001ff

def z86 : W := mkw 0x0bc0210053804204 0x00bc021005380420 0xbfc031007f80e38c 0xfbfc031007f80e38

def z87 : W := mkw 0x6fbbbff50480db06 0x06fbbbff50480db0 0x5fffffff8000ff87 0xf5fffffff8000ff8

def z88 : W := mkw 0x011133260495f2d5 0x4011133260495f2d 0xff333f267fffffff 0xfff333f267ffffff

def z89 : W := mkw 0x0000000000000000 0x0000000000000000 0x7000000060001c0c 0x57000000060001c0

def z90 : W := mkw 0x0000000000000000 0x0000000000000000 0x40ccc1ff80000007 0xd40ccc1ff8000000

def z91 : W := mkw 0x4eaa8c9100000000 0x04eaa8c910000000 0x4cccced980000000 0x44cccced98000000

def z92 : W := mkw 0x0100210000804204 0x0010021000080420 0x0300010003800380 0x8030001000380038

def z93 : W := mkw 0x143c163a2cf5f6f5 0xc143c163a2cf5f6f 0xfc3c3e387ffffffd 0x7fc3c3e387ffffff

def z94 : W := mkw 0x01113126009562d5 0x401113126009562d 0x8333302601ffe073 0x28333302601ffe07

def z95 : W := mkw 0x0111312400916245 0x4011131240091624 0x9333310003b3e38c 0xb9333310003b3e38

def z96 : W := mkw 0x00000002009562d5 0x400000002009562d 0x9000000003ffe3f8 0x09000000003ffe3f

def z97 : W := mkw 0x0111312400000000 0x0011131240000000 0x0333312600000007 0xb033331260000000

def z98 : W := mkw 0x7fffbffd7ff0ff67 0x87fffbffd7ff0ff6 0xfffffffffff0ffff 0xffffffffffff0fff

def z99 : W := mkw 0x0eeec04afb6e0dba 0x20eeec04afb6e0db 0xffffc1ffffff1fff 0xfffffc1ffffff1ff

def z100 : W := mkw 0x1efed6387f7ab469 0x81efed6387f7ab46 0xfffffe387ffffc7f 0xffffffe387ffffc7

def z101 : W := mkw 0x4b83a98500000000 0x04b83a9850000000 0x43cfc1ff80000007 0xd43cfc1ff8000000

def z102 : W := mkw 0x00000002009562d5 0x400000002009562d 0x100000000000e3f0 0x0100000000000e3f

def z103 : W := mkw 0x3ffc3ff87ff0ff67 0x83ffc3ff87ff0ff6 0xfffc3ff87ff0fffd 0xffffc3ff87ff0fff

def z104 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000012600000007 0x9000001260000000

def z105 : W := mkw 0x147c567aee7cbdf3 0xa147c567aee7cbdf 0xfcfcfffffe7cffff 0xffcfcfffffe7cfff

def z106 : W := mkw 0x442a841100000000 0x0442a84110000000 0x000cc01980000000 0x0000cc0198000000

def z107 : W := mkw 0x1efed4387b7a2469 0x81efed4387b7a246 0xafffc0387fff007b 0xfafffc0387fff007

def z108 : W := mkw 0x0eeac000530a0008 0x00eeac000530a000 0x0fffc000038f0003 0xf0fffc000038f000

def z109 : W := mkw 0x6ffbbff55780db06 0x06ffbbff55780db0 0xfff33fc07f80ff8c 0xffff33fc07f80ff8

def z110 : W := mkw 0x043c102028702041 0x0043c10202870204 0xbc3c30207c70e07d 0x7bc3c30207c70e07

def z111 : W := mkw 0x0011102400000000 0x0001110240000000 0x0033002600000003 0x0003300260000000

def z112 : W := mkw 0x0044404afb6e0dba 0x20044404afb6e0db 0xf0ccc1ffffff1fff 0xdf0ccc1ffffff1ff

def z113 : W := mkw 0x6fbbbfb51580d204 0x06fbbbfb51580d20 0x8f333e001d80e000 0x28f333e001d80e00

def z114 : W := mkw 0x046c40006a680000 0x0046c40006a68000 0xacfcc0007e7c000b 0xfacfcc0007e7c000

def z115 : W := mkw 0x0145614ee2cd4fb6 0x60145614ee2cd4fb 0x73cfc1ffe3cf1fff 0xd73cfc1ffe3cf1ff

def z116 : W := mkw 0x4b83a98500000000 0x04b83a9850000000 0x03c3c1c780000002 0x803c3c1c78000000

def z117 : W := mkw 0x6bc3abc55780db06 0x06bc3abc55780db0 0xffc3ffc7ff80ff8e 0xfffc3ffc7ff80ff8

def z118 : W := mkw 0x00111026001520d1 0x400111026001520d 0x10330126027f03ff 0x910330126027f03f

def z119 : W := mkw 0x0111312400000000 0x0011131240000000 0x0000312600000004 0x0000031260000000

def z120 : W := mkw 0x2bc029c053804b06 0x02bc029c053804b0 0x03c001c003800380 0x803c001c00380038

def z121 : W := mkw 0x0b9139a400000000 0x00b9139a40000000 0x4ff33fe600000007 0xf4ff33fe60000000

def z122 : W := mkw 0x21002bc00480db06 0x021002bc00480db0 0x50003fc00000ff84 0x050003fc00000ff8

def z123 : W := mkw 0x2ac00ac057009902 0x02ac00ac05700990 0x6cc00ec07c001c00 0x46cc00ec07c001c0

def z124 : W := mkw 0x043c143028600000 0x0043c14302860000 0xec3c3e387c70000d 0x7ec3c3e387c70000

def z125 : W := mkw 0x0044424ae64c9db2 0x20044424ae64c9db 0xfcccfffffe4cffff 0xffcccfffffe4cfff

def z126 : W := mkw 0x042ec000286a0008 0x0042ec000286a000 0x003fc000007f0003 0x0003fc000007f000

def z127 : W := mkw 0x0eeec0087b6a0428 0x00eeec0087b6a042 0xffffc0387fff1c7f 0xfffffc0387fff1c7

def z128 : W := mkw 0x01113126009562d5 0x401113126009562d 0x9333300003ffe3f8 0x29333300003ffe3f

def z129 : W := mkw 0x0100210000804204 0x0010021000080420 0x930031000380e38c 0xb930031000380e38

def z130 : W := mkw 0x153d373e2cf5f6f5 0xc153d373e2cf5f6f 0xff3f3f3e7fffffff 0xfff3f3f3e7ffffff

def z131 : W := mkw 0x00000002001520d1 0x400000002001520d 0x00000000007f0070 0x000000000007f007

def z132 : W := mkw 0x2fec2bc07fe0db06 0x02fec2bc07fe0db0 0xfffc3fc07ff0ff8d 0xffffc3fc07ff0ff8

def z133 : W := mkw 0x553d3fbd2c70b461 0x8553d3fbd2c70b46 0xfc3c3ffffc70fc7d 0x7fc3c3ffffc70fc7

def z134 : W := mkw 0x0044404afb6e0dba 0x20044404afb6e0db 0xb00000007fff1ff8 0x0b00000007fff1ff

def z135 : W := mkw 0x0ffff1267bff62dd 0x40ffff1267bff62d 0xbffff1267fffe3ff 0xfbffff1267fffe3f

def z136 : W := mkw 0x0010102000102041 0x0001010200010204 0x903030200070e07d 0x3903030200070e07

def z137 : W := mkw 0x0101210600854294 0x4010121060085429 0x03030106038f0382 0x803030106038f038

def z138 : W := mkw 0x2faaab801da2d20c 0x02faaab801da2d20 0x8f333e001db3e000 0x28f333e001db3e00

def z139 : W := mkw 0x5fbbbfb50c30b041 0x85fbbbfb50c30b04 0x8f333e001c30e000 0x28f333e001c30e00

def z140 : W := mkw 0x0040004042000902 0x0004000404200090 0x70c001c062001f8c 0xd70c001c062001f8

def z141 : W := mkw 0x3efc1ef87f70bd63 0x83efc1ef87f70bd6 0xfcfc3ef87c70fc7d 0x7fcfc3ef87c70fc7

def z142 : W := mkw 0x0ac2c000530a0008 0x00ac2c000530a000 0x03c3c000038f0002 0x803c3c000038f000

def z143 : W := mkw 0x4eaa8c9100000000 0x04eaa8c910000000 0x0c000e0000000000 0x00c000e000000000

def z144 : W := mkw 0x5fffffbd7f7ab469 0x85fffffbd7f7ab46 0xfffffffffffffc7f 0xffffffffffffffc7

def z145 : W := mkw 0x2bc46bcaf7ccdfb6 0x22bc46bcaf7ccdfb 0xffccffffffccffff 0xfffccffffffccfff

def z146 : W := mkw 0x0004400aa04c04b0 0x20004400aa04c04b 0x000cc03f804c0073 0x0000cc03f804c007

def z147 : W := mkw 0x2b802b801580d204 0x02b802b801580d20 0x8f003e001d80e000 0x28f003e001d80e00

def z148 : W := mkw 0x0428000000000000 0x0042800000000000 0x0c3c000000000001 0x70c3c00000000000

def z149 : W := mkw 0x443fd435286a0008 0x0443fd435286a000 0x003fc03f807f0003 0x0003fc03f807f000

def z150 : W := mkw 0x01113126009562d5 0x401113126009562d 0x100031260000e3f4 0x0100031260000e3f

def z151 : W := mkw 0x004440007b6a0008 0x0004440007b6a000 0x200000007c000000 0x0200000007c00000

def z152 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x70ccc0d9e24c1ff8 0x470ccc0d9e24c1ff

def z153 : W := mkw 0x4fbbbdb500102041 0x04fbbbdb50010204 0xdfffffff8070e07f 0xfdfffffff8070e07

def z154 : W := mkw 0x143c143828702461 0x8143c14382870246 0x4c3c3e3800700075 0x74c3c3e380070007

def z155 : W := mkw 0x142c06182c609420 0x8142c06182c60942 0x7c0c0e387c401c7d 0x57c0c0e387c401c7

def z156 : W := mkw 0x046ec04aea6e0dba 0x2046ec04aea6e0db 0x70ffc1ffe27f1fff 0xd70ffc1ffe27f1ff

def z157 : W := mkw 0x100402082c70b461 0x8100402082c70b46 0xb00000007c70fc78 0x0b00000007c70fc7

def z158 : W := mkw 0x2eeec2407feadb0e 0x02eeec2407feadb0 0xbfffc0007fffff8b 0xfbfffc0007fffff8

def z159 : W := mkw 0x0ac4400073480000 0x00ac440007348000 0xafccc0007fcc000b 0xfafccc0007fcc000

def z160 : W := mkw 0x01113126009562d5 0x401113126009562d 0x9000312603ffe3fc 0x09000312603ffe3f

def z161 : W := mkw 0x00000002009562d5 0x400000002009562d 0x9333000003ffe3fb 0xb9333000003ffe3f

def z162 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x00ccc1ff824c03f3 0x800ccc1ff824c03f

def z163 : W := mkw 0x0eeec0407b6a090a 0x00eeec0407b6a090 0xffffc1c07fff1f8f 0xfffffc1c07fff1f8

def z164 : W := mkw 0x0b80298000000000 0x00b8029800000000 0x4fccffff80000007 0xf4fccffff8000000

def z165 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x4ff33fc000000004 0xf4ff33fc00000000

def z166 : W := mkw 0x142c06182c609420 0x8142c06182c60942 0xfc0c3e187c00fc0c 0x7fc0c3e187c00fc0

def z167 : W := mkw 0x4fbbbdb7009562d5 0x44fbbbdb7009562d 0xdfffffff83ffe3ff 0xfdfffffff83ffe3f

def z168 : W := mkw 0x0ac0000053000000 0x00ac000005300000 0xafc000007f800008 0xfafc000007f80000

def z169 : W := mkw 0x1fbc3fb82c70b461 0x81fbc3fb82c70b46 0xfffc3ff87c70fc7d 0xffffc3ff87c70fc7

def z170 : W := mkw 0x143c543aa87c24f1 0xa143c543aa87c24f 0x003cc03f807c0073 0x0003cc03f807c007

def z171 : W := mkw 0x042c000028600000 0x0042c00002860000 0xaf3f00007fff000b 0xfaf3f00007fff000

def z172 : W := mkw 0x4fefe9857b6a0008 0x04fefe9857b6a000 0xafffc1c7ffff000b 0xfafffc1c7ffff000

def z173 : W := mkw 0x21002b800480d204 0x021002b800480d20 0x00003e000000e000 0x000003e000000e00

def z174 : W := mkw 0x0eaa800000000000 0x00eaa80000000000 0x4fffc1ff80000007 0xf4fffc1ff8000000

def z175 : W := mkw 0x0044400ae24c04b0 0x20044400ae24c04b 0x20ccc03fe24c007b 0xd20ccc03fe24c007

def z176 : W := mkw 0x142806100c209000 0x8142806100c20900 0x0c000e001c000000 0x00c000e001c00000

def z177 : W := mkw 0x0100210000804204 0x0010021000080420 0x100031000000e384 0x0100031000000e38

def z178 : W := mkw 0x4fbbbdb500916245 0x44fbbbdb50091624 0x8f333e0001b3e000 0x28f333e0001b3e00

def z179 : W := mkw 0x0110312000906245 0x0011031200090624 0x9330312003f0e3fd 0xb9330312003f0e3f

def z180 : W := mkw 0x0000000000000000 0x0000000000000000 0x8300000003800008 0xb830000000380000

def z181 : W := mkw 0x0000000000000000 0x0000000000000000 0x0333000000000003 0xb033300000000000

def z182 : W := mkw 0x0eaa800019220008 0x00eaa80001922000 0x8f3300001fff000b 0xb8f3300001fff000

def z183 : W := mkw 0x3ffc7ffafffcfff7 0xa3ffc7ffafffcfff 0xfffcfffffffcffff 0xffffcfffffffcfff

def z184 : W := mkw 0x143d143e287524f1 0xc143d143e287524f 0x003f003e007f0073 0x0003f003e007f007

def z185 : W := mkw 0x042c02002c609000 0x0042c02002c60900 0xfc3c3e007c70fc0d 0x7fc3c3e007c70fc0

def z186 : W := mkw 0x142c06182c70b461 0x8142c06182c70b46 0xfc0c0e187c70fc78 0x4fc0c0e187c70fc7

def z187 : W := mkw 0x0000004a80040db2 0x20000004a80040db 0x50ccc1ff80001ff7 0xd50ccc1ff80001ff

def z188 : W := mkw 0x41113db7009562d5 0x441113db7009562d 0xd3333fff83ffe3ff 0xbd3333fff83ffe3f

def z189 : W := mkw 0x0000000800000420 0x0000000080000042 0x5000003800001c74 0x05000003800001c7

def z190 : W := mkw 0x0000004a80040db2 0x20000004a80040db 0x500001ff80001ff4 0x0500001ff80001ff

def z191 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x0f333e0000000000 0x20f333e000000000

def z192 : W := mkw 0x001012200410b041 0x0001012200410b04 0xfc303e207c70fc7d 0x7fc303e207c70fc7

def z193 : W := mkw 0x153d353e28f566f5 0xc153d353e28f566f 0x933f313e03ffe3ff 0xb933f313e03ffe3f

def z194 : W := mkw 0x4b83a98500000000 0x04b83a9850000000 0x4fc3ffc780000006 0xf4fc3ffc78000000

def z195 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0x7c0c3e387c00fc74 0x47c0c3e387c00fc7

def z196 : W := mkw 0x00111026001520d1 0x400111026001520d 0x0000002600000070 0x0000000260000007

def z197 : W := mkw 0x042ec000286a0008 0x0042ec000286a000 0x833fc00003ff000b 0xb833fc00003ff000

def z198 : W := mkw 0x0000000000000000 0x0000000000000000 0xac0000007c000008 0x7ac0000007c00000

def z199 : W := mkw 0x0bc029c042000902 0x00bc029c04200090 0x7fc03fc062001f8c 0xf7fc03fc062001f8

def z200 : W := mkw 0x0ac6c04af34e0dba 0x20ac6c04af34e0db 0x73cfc1ffe3cf1fff 0xd73cfc1ffe3cf1ff

def z201 : W := mkw 0x0bd3f126539f62dd 0x40bd3f126539f62d 0x93f3f12603ffe3ff 0xb93f3f12603ffe3f

def z202 : W := mkw 0x543f963d2c70b461 0x8543f963d2c70b46 0xfc3ffe3ffc70fc7f 0x7fc3ffe3ffc70fc7

def z203 : W := mkw 0x0000000200040090 0x0000000020004009 0x10000126024c03ff 0x910000126024c03f

def z204 : W := mkw 0x0014102820502461 0x0001410282050246 0xf03c30386070fc7d 0x7f03c30386070fc7

def z205 : W := mkw 0x0000004880000d22 0x20000004880000d2 0x400000d980001c00 0x0400000d980001c0

def z206 : W := mkw 0x41113db500000000 0x041113db50000000 0x00003e0000000000 0x000003e000000000

def z207 : W := mkw 0x2bc02bc057009902 0x02bc02bc05700990 0x6fc03fc07c001c04 0xf6fc03fc07c001c0

def z208 : W := mkw 0x004440007b6a0008 0x0004440007b6a000 0xa33300007fff000b 0xba33300007fff000

def z209 : W := mkw 0x042c000028600000 0x0042c00002860000 0xac3c00007c700009 0x7ac3c00007c70000

def z210 : W := mkw 0x2bc029c053804b06 0x02bc029c053804b0 0xafc001c07f800388 0xfafc001c07f80038

def z211 : W := mkw 0x0ffff16efbff6fff 0x60ffff16efbff6ff 0xfffff1ffffffffff 0xffffff1fffffffff

def z212 : W := mkw 0x143816300c30b041 0x8143816300c30b04 0x8c303e001c30e000 0x28c303e001c30e00

def z213 : W := mkw 0x0115712ea0dd66f5 0x60115712ea0dd66f 0x933ff13f83ffe3ff 0xb933ff13f83ffe3f

def z214 : W := mkw 0x353c3ff82cf0ff67 0x8353c3ff82cf0ff6 0xfc3c3ff87c70fffd 0x7fc3c3ff87c70fff

def z215 : W := mkw 0x447fd47fe24c0db2 0x2447fd47fe24c0db 0x70ffc1ffe24c1fff 0xd70ffc1ffe24c1ff

def z216 : W := mkw 0x4eaa8c9100000000 0x04eaa8c910000000 0x4ccccfff80000007 0xd4ccccfff8000000

def z217 : W := mkw 0x0b80298000804204 0x00b8029800080420 0xdfc03fc00380e38c 0xfdfc03fc00380e38

def z218 : W := mkw 0x0111312400804204 0x0011131240080420 0x933331260380e38f 0xb933331260380e38

def z219 : W := mkw 0x143c163a2c74b4f1 0x8143c163a2c74b4f 0xfc3c3f3e7e7cffff 0xffc3c3f3e7e7cfff

def z220 : W := mkw 0x2bc42bc877c0df26 0x02bc42bc877c0df2 0xffcc3ff87fc0fffd 0xfffcc3ff87fc0fff

def z221 : W := mkw 0x0111312400916245 0x4011131240091624 0x8333312601b3e007 0xb8333312601b3e00

def z222 : W := mkw 0x0004400aa04c04b0 0x20004400aa04c04b 0x700cc03fe04c1c7f 0x5700cc03fe04c1c7

def z223 : W := mkw 0x4ffbbdf542000902 0x04ffbbdf54200090 0x7fffffffe2001f8f 0xf7fffffffe2001f8

def z224 : W := mkw 0x4eeecc917b6a0008 0x04eeecc917b6a000 0xefffced9ffff000b 0xfefffced9ffff000

def z225 : W := mkw 0x453bb537009562d5 0x4453bb537009562d 0x933ff13f83ffe3ff 0xb933ff13f83ffe3f

def z226 : W := mkw 0x0115312e20d566f5 0x40115312e20d566f 0xf33f313e63ffffff 0xff33f313e63fffff

def z227 : W := mkw 0x0eeec048fb6a0d2a 0x20eeec048fb6a0d2 0xefffc0d9ffff1c0b 0xfefffc0d9ffff1c0

def z228 : W := mkw 0x0000000000000000 0x0000000000000000 0x40ccc0d980000000 0x440ccc0d98000000

def z229 : W := mkw 0x0044400062480000 0x0004440006248000 0x20ccc000624c000b 0xd20ccc000624c000

def z230 : W := mkw 0x046c404aea6c0db2 0x2046c404aea6c0db 0xfcfcc1fffe7c1fff 0xffcfcc1fffe7c1ff

def z231 : W := mkw 0x01113126009562d5 0x401113126009562d 0x0333012603ff03f3 0x80333012603ff03f

def z232 : W := mkw 0x61113ff50480db06 0x061113ff50480db0 0x50003fff8000ff84 0x050003fff8000ff8

def z233 : W := mkw 0x5eae8e992c609420 0x85eae8e992c60942 0x6cccced9fc001c00 0x46cccced9fc001c0

def z234 : W := mkw 0x101416382450b461 0x8101416382450b46 0x700c3e386040fc7d 0x5700c3e386040fc7

def z235 : W := mkw 0x2bc029c053804b06 0x02bc029c053804b0 0x93c031c00380e38c 0xb93c031c00380e38

def z236 : W := mkw 0x0ac0000053000000 0x00ac000005300000 0xaff300007fff000b 0xfaff300007fff000

def z237 : W := mkw 0x0155716ee2dd6ff7 0x60155716ee2dd6ff 0xf3fff1ffe3ffffff 0xff3fff1ffe3fffff

def z238 : W := mkw 0x2ac008c053000902 0x02ac008c05300090 0x00c000c000000000 0x000c000c00000000

def z239 : W := mkw 0x3eec0ed87f609d22 0x83eec0ed87f609d2 0x6ccc0ed87c001c00 0x46ccc0ed87c001c0

def z240 : W := mkw 0x0000004a80040db2 0x20000004a80040db 0x1000000000001ff0 0x01000000000001ff

def z241 : W := mkw 0x2ac00ac057009902 0x02ac00ac05700990 0xefc00ec07f801c08 0xfefc00ec07f801c0

def z242 : W := mkw 0x01113126009562d5 0x401113126009562d 0x8333310603bfe382 0xa8333310603bfe38

def z243 : W := mkw 0x6fbbbfb51580d204 0x06fbbbfb51580d20 0xcfffffff9d80e007 0xfcfffffff9d80e00

def z244 : W := mkw 0x0101210600854294 0x4010121060085429 0x8333010603ff038b 0xb8333010603ff038

def z245 : W := mkw 0x0040400042080000 0x0004040004208000 0x00c0c000020c0002 0x800c0c000020c000

def z246 : W := mkw 0x0111312400916245 0x4011131240091624 0x8333300003ffe00b 0xb8333300003ffe00

def z247 : W := mkw 0x45393db500000000 0x045393db50000000 0x4c3c3fff80000005 0x74c3c3fff8000000

def z248 : W := mkw 0x00111026001520d1 0x400111026001520d 0x8333002603ff007b 0xb8333002603ff007

def z249 : W := mkw 0x543f943d28702461 0x8543f943d2870246 0x003fc03f80700073 0x0003fc03f8070007

def z250 : W := mkw 0x1044424aee7cbdf3 0xa1044424aee7cbdf 0xb00000007e7cfff8 0x0b00000007e7cfff

def z251 : W := mkw 0x0efed0207b7a2049 0x00efed0207b7a204 0xbffff0207fffe07f 0xfbffff0207fffe07

def z252 : W := mkw 0x143c16382c609420 0x8143c16382c60942 0x6c3c3e387c001c05 0x76c3c3e387c001c0

def z253 : W := mkw 0x0040404ac20c0db2 0x20040404ac20c0db 0x50c0c1ff820c1ff6 0x850c0c1ff820c1ff

def z254 : W := mkw 0x0eaec000396a0008 0x00eaec000396a000 0x8f3fc0001dff0003 0x28f3fc0001dff000

def z255 : W := mkw 0x0000020004009000 0x0000002000400900 0x6c000e007c001c00 0x46c000e007c001c0

def z256 : W := mkw 0x0ac0000053000000 0x00ac000005300000 0x03c0000003800000 0x803c000000380000

def z257 : W := mkw 0x046ec0006a6a0008 0x0046ec0006a6a000 0x20ffc000627f000b 0xd20ffc000627f000

def z258 : W := mkw 0x0155716ee2dd6ff7 0x60155716ee2dd6ff 0xb333312663ffffff 0xbb333312663fffff

def z259 : W := mkw 0x1ebe96382c70b461 0x81ebe96382c70b46 0xfffffe387c70fc7f 0xffffffe387c70fc7

def z260 : W := mkw 0x0000000000000000 0x0000000000000000 0x00330000007f0003 0x000330000007f000

def z261 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000003ff0008 0x08000000003ff000

def z262 : W := mkw 0x00404040c2080902 0x200404040c208090 0x00c0c0c180000000 0x000c0c0c18000000

def z263 : W := mkw 0x153937340cb1f245 0xc153937340cb1f24 0x8f333e001db3e000 0x28f333e001db3e00

def z264 : W := mkw 0x142c041828600420 0x8142c04182860042 0x000c001800000000 0x0000c00180000000

def z265 : W := mkw 0x0438143000000000 0x0043814300000000 0x003c003800000001 0x0003c00380000000

def z266 : W := mkw 0x0eeec04afb6e0dba 0x20eeec04afb6e0db 0xbfffc0007fff1ffb 0xfbfffc0007fff1ff

def z267 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x4cccffff80000004 0x44cccffff8000000

def z268 : W := mkw 0x0010102000102041 0x0001010200010204 0x100030200000e074 0x0100030200000e07

def z269 : W := mkw 0x4a82888100000000 0x04a8288810000000 0x00c0c0c180000000 0x000c0c0c18000000

def z270 : W := mkw 0x0eae800028600000 0x00eae80002860000 0xafffc0007c70000b 0xfafffc0007c70000

def z271 : W := mkw 0x153d373e2cf5f6f5 0xc153d373e2cf5f6f 0xfc3c3f3e7c70fffd 0x7fc3c3f3e7c70fff

def z272 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0x6c3c0e387c701c71 0x46c3c0e387c701c7

def z273 : W := mkw 0x00101022001420d1 0x000101022001420d 0x90303126027ce3ff 0xb90303126027ce3f

def z274 : W := mkw 0x2b913ba61595f2d5 0x42b913ba61595f2d 0x9f333f261fffe3ff 0xb9f333f261fffe3f

def z275 : W := mkw 0x01113126009562d5 0x401113126009562d 0x13033126038fe3f6 0x813033126038fe3f

def z276 : W := mkw 0x6bd13ff55780db06 0x06bd13ff55780db0 0xffc03fffff80ff8c 0xfffc03fffff80ff8

def z277 : W := mkw 0x147c5678ee78bd63 0xa147c5678ee78bd6 0xfcfcfef9fc70fc7d 0x7fcfcfef9fc70fc7

def z278 : W := mkw 0x4bc3e985530a0008 0x04bc3e985530a000 0x03c3c1c7838f0002 0x803c3c1c7838f000

def z279 : W := mkw 0x0044004862400d22 0x00044004862400d2 0x70cc01f862401ffd 0xd70cc01f862401ff

def z280 : W := mkw 0x2b80298011804204 0x02b8029801180420 0x0300000001800000 0x0030000000180000

def z281 : W := mkw 0x21002bca8484dfb6 0x221002bca8484dfb 0x50003fff8000fff4 0x050003fff8000fff

def z282 : W := mkw 0x4eeeccd9e2480d22 0x24eeeccd9e2480d2 0x6cccced9e0001c00 0x46cccced9e0001c0

def z283 : W := mkw 0x0000000200854294 0x4000000020085429 0x00000000038f0380 0x000000000038f038

def z284 : W := mkw 0x4fabad9500000000 0x04fabad950000000 0x4fcfcfdf80000002 0xc4fcfcfdf8000000

def z285 : W := mkw 0x146c465aee6c9db2 0xa146c465aee6c9db 0x7ccccffffe4c1fff 0xd7ccccffffe4c1ff

def z286 : W := mkw 0x2bc129c653854b96 0x42bc129c653854b9 0x03c301c6038f0382 0x803c301c6038f038

def z287 : W := mkw 0x042a800000000000 0x0042a80000000000 0x003fc00000000003 0x0003fc0000000000

def z288 : W := mkw 0x0000004000000902 0x0000000400000090 0x500001c000001f84 0x0500001c000001f8

def z289 : W := mkw 0x4ffffdffe24c0db2 0x24ffffdffe24c0db 0x7fffffffe24c1fff 0xf7fffffffe24c1ff

def z290 : W := mkw 0x143d163e2c75b4f1 0xc143d163e2c75b4f 0xfc3f3e3e7c7ffc7f 0x7fc3f3e3e7c7ffc7

def z291 : W := mkw 0x0fbbb12419b3624d 0x40fbbb12419b3624 0x8f3330001db3e000 0x28f3330001db3e00

def z292 : W := mkw 0x0040004042000902 0x0004000404200090 0x60c000c060001c00 0x460c000c060001c0

def z293 : W := mkw 0x4fbbbdb500916245 0x44fbbbdb50091624 0xcfffffff81b3e007 0xfcfffffff81b3e00

def z294 : W := mkw 0x0feee1007bea420c 0x00feee1007bea420 0xbffff1007fffe38f 0xfbffff1007fffe38

def z295 : W := mkw 0x01113126009562d5 0x401113126009562d 0x10333126007fe3f7 0x010333126007fe3f

def z296 : W := mkw 0x00111026009562d5 0x400111026009562d 0x9033002603ffe3fb 0x09033002603ffe3f

def z297 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xaf3300007fff0008 0x2af3300007fff000

def z298 : W := mkw 0x147c547aea7c2df3 0xa147c547aea7c2df 0x70fcc1ffe27c1fff 0xd70fcc1ffe27c1ff

def z299 : W := mkw 0x0000000000000000 0x0000000000000000 0x8333000001b30000 0x28333000001b3000

def z300 : W := mkw 0x0004000820400420 0x0000400082040042 0x000c003800400071 0x0000c00380040007

def z301 : W := mkw 0x4ffbfdb5530a0008 0x04ffbfdb5530a000 0x4fffffff838f0007 0xf4fffffff838f000

def z302 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xbc303e007c70fc78 0x2bc303e007c70fc7

def z303 : W := mkw 0x0000000000000000 0x0000000000000000 0x900030000000e00c 0x3900030000000e00

def z304 : W := mkw 0x0010143000000000 0x0001014300000000 0x40003e3800000004 0x040003e380000000

def z305 : W := mkw 0x143816380c30b461 0x8143816380c30b46 0xdc303e381c30fc74 0x2dc303e381c30fc7

def z306 : W := mkw 0x6ffbbff75795fbd7 0x46ffbbff75795fbd 0xffffffffffffffff 0xffffffffffffffff

def z307 : W := mkw 0x101416382c70b461 0x8101416382c70b46 0xf0003e387c70fc7c 0x0f0003e387c70fc7

def z308 : W := mkw 0x1115332e2cf5f6f5 0xc1115332e2cf5f6f 0xb33331267fffffff 0xbb33331267ffffff

def z309 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0x8c3c3e381c70e071 0x28c3c3e381c70e07

def z310 : W := mkw 0x010023000480d204 0x0010023000480d20 0xff003f007f80ff8c 0xfff003f007f80ff8

def z311 : W := mkw 0x4faaad9100000000 0x04faaad910000000 0x4fccffd980000004 0xf4fccffd98000000

def z312 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xefffc1ffffff000f 0xfefffc1ffffff000

def z313 : W := mkw 0x2b802b801580d204 0x02b802b801580d20 0xcfc03fc01d80e004 0xfcfc03fc01d80e00

def z314 : W := mkw 0x1111373e0495f6f5 0xc1111373e0495f6f 0x50003f3e0000fff4 0x050003f3e0000fff

def z315 : W := mkw 0x0010102000102041 0x0001010200010204 0x9333302003ffe07f 0xb9333302003ffe07

def z316 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x30ccc000624c1ffb 0xd30ccc000624c1ff

def z317 : W := mkw 0x0eeec048fb6a0d2a 0x20eeec048fb6a0d2 0x6cccc0d9fc001c00 0x46cccc0d9fc001c0

def z318 : W := mkw 0x3ffefff87ffaff6f 0x83ffefff87ffaff6 0xfffffff87fffffff 0xffffffff87ffffff

def z319 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x4f3f3e3800000005 0x74f3f3e380000000

def z320 : W := mkw 0x5ebe9eb92c70b461 0x85ebe9eb92c70b46 0xfcfcfef9fc70fc7d 0x7fcfcfef9fc70fc7

def z321 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x60ccc1dfe20c1f82 0xc60ccc1dfe20c1f8

def z322 : W := mkw 0x21113be60495fbd7 0x421113be60495fbd 0x50003fe60000fff4 0x050003fe60000fff

def z323 : W := mkw 0x0bc3e106538f429c 0x40bc3e106538f429 0x03c3c106038f0382 0x803c3c106038f038

def z324 : W := mkw 0x2bd03be05790fb47 0x02bd03be05790fb4 0xfff03fe07ff0fffd 0xffff03fe07ff0fff

def z325 : W := mkw 0x0000000019220008 0x0000000001922000 0x800000001db30000 0x0800000001db3000

def z326 : W := mkw 0x0438143000000000 0x0043814300000000 0x4cfcffff80000007 0xf4cfcffff8000000

def z327 : W := mkw 0x004440027bff62dd 0x4004440027bff62d 0xb00000007fffe3f8 0x0b00000007fffe3f

def z328 : W := mkw 0x2ac00ac057009902 0x02ac00ac05700990 0xfcc03ec07c00fc0c 0x7fcc03ec07c00fc0

def z329 : W := mkw 0x0eba943000000000 0x00eba94300000000 0x4ffffe3800000007 0xf4ffffe380000000

def z330 : W := mkw 0x4effd4357b6a0008 0x04effd4357b6a000 0xafffc03fffff000b 0xfafffc03fffff000

def z331 : W := mkw 0x01113126009562d5 0x401113126009562d 0x10003126024ce3ff 0x910003126024ce3f

def z332 : W := mkw 0x41113dff80040db2 0x241113dff80040db 0x50003fff80001ff4 0x050003fff80001ff

def z333 : W := mkw 0x0140214042804b06 0x00140214042804b0 0xf3c031c06380ff8c 0xff3c031c06380ff8

def z334 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xfcfcfffffc70fc7f 0xffcfcfffffc70fc7

def z335 : W := mkw 0x3ffd3ffe7ff5fff7 0xc3ffd3ffe7ff5fff 0xffff3ffe7fffffff 0xfffff3ffe7ffffff

def z336 : W := mkw 0x0eaa800000000000 0x00eaa80000000000 0x0f33000000000000 0x20f3300000000000

def z337 : W := mkw 0x015571267bff62dd 0x4015571267bff62d 0xb33331267fffe3ff 0xbb33331267fffe3f

def z338 : W := mkw 0x043fd026287f20d9 0x4043fd026287f20d 0x003fc026007f0073 0x0003fc026007f007

def z339 : W := mkw 0x4eba9cb100000000 0x04eba9cb10000000 0x4cfcfef980000005 0x74cfcfef98000000

def z340 : W := mkw 0x0ac0020057009000 0x00ac002005700900 0xffc03e007f80fc0c 0xfffc03e007f80fc0

def z341 : W := mkw 0x0eeac0005b2a0008 0x00eeac0005b2a000 0x8ff3c0001fbf0002 0xa8ff3c0001fbf000

def z342 : W := mkw 0x101016380410b461 0x8101016380410b46 0xd0303e380070fc7d 0x3d0303e380070fc7

def z343 : W := mkw 0x0eaa800019220008 0x00eaa80001922000 0x8fffc0001db30003 0xf8fffc0001db3000

def z344 : W := mkw 0x0eeec0027b6e0098 0x00eeec0027b6e009 0xbfffc1267fff03ff 0xfbfffc1267fff03f

def z345 : W := mkw 0x2ac00ac057009902 0x02ac00ac05700990 0x7cc00fc07e001f8c 0xd7cc00fc07e001f8

def z346 : W := mkw 0x0438163004009000 0x0043816300400900 0xfc3c3e387c00fc0d 0x7fc3c3e387c00fc0

def z347 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0x2fffc0007c000003 0xf2fffc0007c00000

def z348 : W := mkw 0x4ffbbdb553000000 0x04ffbbdb55300000 0xefffffffff80000f 0xfefffffffff80000

def z349 : W := mkw 0x6ffffff57feadb0e 0x06ffffff57feadb0 0xffffffffffffff8f 0xfffffffffffffff8

def z350 : W := mkw 0x4fbbbdb519220008 0x04fbbbdb51922000 0x8f333e001db30000 0x28f333e001db3000

def z351 : W := mkw 0x1054567ae65cbdf3 0xa1054567ae65cbdf 0x70ccffffe24cffff 0xd70ccffffe24cfff

def z352 : W := mkw 0x157d777eeefdfff7 0xe157d777eeefdfff 0xffffffffffffffff 0xffffffffffffffff

def z353 : W := mkw 0x41113db7009562d5 0x441113db7009562d 0x50003fff8000e3f4 0x050003fff8000e3f

def z354 : W := mkw 0x0000020004009000 0x0000002000400900 0x50003e000000fc04 0x050003e000000fc0

def z355 : W := mkw 0x304402487ff0ff67 0x8304402487ff0ff6 0xb00000007ff0fff8 0x0b00000007ff0fff

def z356 : W := mkw 0x0111312400000000 0x0011131240000000 0x43fff1ff80000007 0xf43fff1ff8000000

def z357 : W := mkw 0x0010102000102041 0x0001010200010204 0x0030002000700071 0x0003000200070007

def z358 : W := mkw 0x4ebb9cb500000000 0x04ebb9cb50000000 0x4cffceff80000003 0x44cffceff8000000

def z359 : W := mkw 0x0bd13126539562d5 0x40bd13126539562d 0xbff331267fffe3ff 0xfbff331267fffe3f

def z360 : W := mkw 0x0044404062480902 0x0004440406248090 0x70ccc1c0624c1f8f 0xd70ccc1c0624c1f8

def z361 : W := mkw 0x4b93b9a7009562d5 0x44b93b9a7009562d 0x93f3f1e783ffe3ff 0xb93f3f1e783ffe3f

def z362 : W := mkw 0x0eea80005b220008 0x00eea80005b22000 0xaff300007fb30008 0xfaff300007fb3000

def z363 : W := mkw 0x00111026001520d1 0x400111026001520d 0x90333026007fe07f 0x390333026007fe07

def z364 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0x2cccc0007e4c000b 0xd2cccc0007e4c000

def z365 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0x503c3e380070fc75 0x0503c3e380070fc7

def z366 : W := mkw 0x0111316e80956ff7 0x60111316e80956ff 0x500031ff8000fff4 0x0500031ff8000fff

def z367 : W := mkw 0x2feeebcaffeedfbe 0x22feeebcaffeedfb 0xffffffffffffffff 0xffffffffffffffff

def z368 : W := mkw 0x2b802b801580d204 0x02b802b801580d20 0xff003e007d80fc0c 0x7ff003e007d80fc0

def z369 : W := mkw 0x3ff83ff05fb0fb47 0x83ff83ff05fb0fb4 0xfff03fc07fb0ff8c 0xffff03fc07fb0ff8

def z370 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0xcfffffff83ff000f 0xfcfffffff83ff000

def z371 : W := mkw 0x0fb83db000000000 0x00fb83db00000000 0x4ffc3ff800000005 0xf4ffc3ff80000000

def z372 : W := mkw 0x05393536009562d5 0x405393536009562d 0xdf3f3f3e03ffe3ff 0xfdf3f3f3e03ffe3f

def z373 : W := mkw 0x2bc46bc077c8db06 0x02bc46bc077c8db0 0xffccffc07fccff8f 0xfffccffc07fccff8

def z374 : W := mkw 0x4ffbfdf7c20c0992 0x24ffbfdf7c20c099 0x4fffffff820c0387 0xf4fffffff820c038

def z375 : W := mkw 0x0000000000000000 0x0000000000000000 0x00ccc00000000003 0xd00ccc0000000000

def z376 : W := mkw 0x4fbbbdff80040db2 0x24fbbbdff80040db 0x5fffffff80001ff7 0xf5fffffff80001ff

def z377 : W := mkw 0x2bc069c2d38c4b96 0x22bc069c2d38c4b9 0x03c0c1c7838c0382 0x803c0c1c7838c038

def z378 : W := mkw 0x5fbfbfbd2c70b461 0x85fbfbfbd2c70b46 0xff3f3e387c70fc7d 0x7ff3f3e387c70fc7

def z379 : W := mkw 0x0040004042000902 0x0004000404200090 0x70ccc1ffe2001f8f 0xd70ccc1ffe2001f8

def z380 : W := mkw 0x0011102400112041 0x4001110240011204 0x0033000000330000 0x0003300000033000

def z381 : W := mkw 0x100402082c70b461 0x8100402082c70b46 0xf00c00387c70fc7d 0x5f00c00387c70fc7

def z382 : W := mkw 0x0055506ee25d2df3 0x60055506ee25d2df 0x70ffc1ffe27f1fff 0xd70ffc1ffe27f1ff

def z383 : W := mkw 0x4fbbbfb504009000 0x04fbbbfb50400900 0xfffffffffc00fc0f 0xffffffffffc00fc0

def z384 : W := mkw 0x443b9437001520d1 0x4443b9437001520d 0x003fc03f807f0073 0x0003fc03f807f007

def z385 : W := mkw 0x0004400020480000 0x0000440002048000 0x000cc000004c0003 0x0000cc000004c000

def z386 : W := mkw 0x1111373e0495f6f5 0xc1111373e0495f6f 0xd3333f3e03ffffff 0xbd3333f3e03fffff

def z387 : W := mkw 0x1efc16387f70b461 0x81efc16387f70b46 0xfffc3e387ff0fc7d 0xffffc3e387ff0fc7

def z388 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x03ffc1ff80000003 0x803ffc1ff8000000

def z389 : W := mkw 0x4fbbbdb7009562d5 0x44fbbbdb7009562d 0x5fffffff8000e3f7 0xf5fffffff8000e3f

def z390 : W := mkw 0x6ffbbff557009902 0x06ffbbff55700990 0x6ffffffffc001c07 0xf6ffffffffc001c0

def z391 : W := mkw 0x0004404aa04c0db2 0x20004404aa04c0db 0x500cc1ff804c1ff7 0x0500cc1ff804c1ff

def z392 : W := mkw 0x6ffffffff7ccdfb6 0x26ffffffff7ccdfb 0xffffffffffccffff 0xfffffffffffccfff

def z393 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x60ccc0ffe04c1c73 0x460ccc0ffe04c1c7

def z394 : W := mkw 0x00444048e2480d22 0x200444048e2480d2 0x70ccc1d9e2001f8c 0xd70ccc1d9e2001f8

def z395 : W := mkw 0x0044404ae2dd6ff7 0x60044404ae2dd6ff 0xf0ccc1ffe3ffffff 0xdf0ccc1ffe3fffff

def z396 : W := mkw 0x100002080410b461 0x8100002080410b46 0x100000000000fc70 0x0100000000000fc7

def z397 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x30c0c1c7e24c1ffa 0x830c0c1c7e24c1ff

def z398 : W := mkw 0x0000000000000000 0x0000000000000000 0x8030000000700009 0x3803000000070000

def z399 : W := mkw 0x0bc469cae24c0db2 0x20bc469cae24c0db 0x7fccffffe24c1fff 0xf7fccffffe24c1ff

def z400 : W := mkw 0x0000000000000000 0x0000000000000000 0x000cc03f80000003 0x0000cc03f8000000

def z401 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0xf3ffc1ffe3ff1fff 0xff3ffc1ffe3ff1ff

def z402 : W := mkw 0x00404000530a0008 0x000404000530a000 0x00000000038f0000 0x000000000038f000

def z403 : W := mkw 0x2a800a8015009000 0x02a800a801500900 0x0c000e001c000000 0x00c000e001c00000

def z404 : W := mkw 0x0100210000000000 0x0010021000000000 0x0300310000000004 0xb030031000000000

def z405 : W := mkw 0x1eeec2087f7ab469 0x81eeec2087f7ab46 0xbfffc0007ffffc7b 0xfbfffc0007ffffc7

def z406 : W := mkw 0x5fffffffee7cbdf3 0xa5fffffffee7cbdf 0xfffffffffe7cffff 0xffffffffffe7cfff

def z407 : W := mkw 0x1efed6387f7ab469 0x81efed6387f7ab46 0xfcfcfe387c70fc7d 0x7fcfcfe387c70fc7

def z408 : W := mkw 0x4fbbbdb700854294 0x44fbbbdb70085429 0x4fffffff838f0387 0xf4fffffff838f038

def z409 : W := mkw 0x100402082c609420 0x8100402082c60942 0x200000007c001c00 0x0200000007c001c0

def z410 : W := mkw 0x0fbbb126009562d5 0x40fbbb126009562d 0x9ffff12603ffe3ff 0xf9ffff12603ffe3f

def z411 : W := mkw 0x0040024046009902 0x0004002404600990 0xfcc03fc07e00ff8c 0xffcc03fc07e00ff8

def z412 : W := mkw 0x00044008a0480420 0x200044008a048042 0x000cc01980000000 0x0000cc0198000000

def z413 : W := mkw 0x143816300c30b041 0x8143816300c30b04 0xcc3c3e381c30e005 0x7cc3c3e381c30e00

def z414 : W := mkw 0x2bc469caf3cc4fb6 0x22bc469caf3cc4fb 0x73ccc1ffe3cc1fff 0xd73ccc1ffe3cc1ff

def z415 : W := mkw 0x0040004042000902 0x0004000404200090 0x3000000062001f88 0x03000000062001f8

def z416 : W := mkw 0x0eeec0027bff62dd 0x40eeec0027bff62d 0xbfffc0007fffe3fb 0xfbfffc0007fffe3f

def z417 : W := mkw 0x2eeecac07f6a990a 0x02eeecac07f6a990 0x6ccccec07c001c00 0x46ccccec07c001c0

def z418 : W := mkw 0x142c06182c609420 0x8142c06182c60942 0xec3c0e187c701c09 0x7ec3c0e187c701c0

def z419 : W := mkw 0x0ac440007b6a0008 0x00ac440007b6a000 0xafc000007fff0008 0xfafc000007fff000

def z420 : W := mkw 0x2bc02bc25784db96 0x02bc02bc25784db9 0xffc03fe67fccffff 0xfffc03fe67fccfff

def z421 : W := mkw 0x2feeeb807fead20c 0x02feeeb807fead20 0xaffffe007fffe00b 0xfaffffe007fffe00

def z422 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xafccc0007f800008 0xfafccc0007f80000

def z423 : W := mkw 0x0002c000000a0008 0x00002c000000a000 0x0003c000000f0002 0x00003c000000f000

def z424 : W := mkw 0x347c16787ff0ff67 0x8347c16787ff0ff6 0xfc3c3e387ff0fffd 0x7fc3c3e387ff0fff

def z425 : W := mkw 0x101016380410b461 0x8101016380410b46 0xfc003e387c00fc7c 0x7fc003e387c00fc7

def z426 : W := mkw 0x101016300410b041 0x8101016300410b04 0x00003e000000e000 0x000003e000000e00

def z427 : W := mkw 0x0ffff1247b6a0008 0x00ffff1247b6a000 0xaffff1267fff000f 0xfaffff1267fff000

def z428 : W := mkw 0x0000020004009000 0x0000002000400900 0x8c003e001c00e000 0x28c003e001c00e00

def z429 : W := mkw 0x2bc46bc8f7c8df26 0x22bc46bc8f7c8df2 0xffccffd9ff80ff8c 0xfffccffd9ff80ff8

def z430 : W := mkw 0x204002405780db06 0x0204002405780db0 0xf0c001c07f80ff8c 0xdf0c001c07f80ff8

def z431 : W := mkw 0x1eeec6187f6a9428 0x81eeec6187f6a942 0x6cccce187c001c00 0x46cccce187c001c0

def z432 : W := mkw 0x3bd03ff85790ff67 0x83bd03ff85790ff6 0xffc03ff87f80fffc 0xfffc03ff87f80fff

def z433 : W := mkw 0x0eec00007b600000 0x00eec00007b60000 0xaffc00007ff00009 0xfaffc00007ff0000

def z434 : W := mkw 0x01002102009562d5 0x401002102009562d 0x9300310003ffe3fc 0xb9300310003ffe3f

def z435 : W := mkw 0x2feeebc07feadb0e 0x02feeebc07feadb0 0xffccffc07f80ff8c 0xfffccffc07f80ff8

def z436 : W := mkw 0x2eeecac07f6a990a 0x02eeecac07f6a990 0xefffcec07fff1c0b 0xfefffcec07fff1c0

def z437 : W := mkw 0x2bc46bc07feadb0e 0x02bc46bc07feadb0 0xffc03fc07fffff8c 0xfffc03fc07fffff8

def z438 : W := mkw 0x4ffffdffe2dd6ff7 0x64ffffdffe2dd6ff 0xffffffffe3ffffff 0xfffffffffe3fffff

def z439 : W := mkw 0x5fbfbfbf2cf5f6f5 0xc5fbfbfbf2cf5f6f 0xffffffffffffffff 0xffffffffffffffff

def z440 : W := mkw 0x204002425795fbd7 0x4204002425795fbd 0xb00000007ffffff8 0x0b00000007ffffff

def z441 : W := mkw 0x215133665795fbd7 0x4215133665795fbd 0xb33331267fffffff 0xbb33331267ffffff

def z442 : W := mkw 0x0101210400814204 0x4010121040081420 0x0303000001830000 0x0030300000183000

def z443 : W := mkw 0x4b83a98700854294 0x44b83a9870085429 0x03c3c1c7838f0382 0x803c3c1c7838f038

def z444 : W := mkw 0x2bc02b805780d204 0x02bc02b805780d20 0xafc03e007f80e008 0xfafc03e007f80e00

def z445 : W := mkw 0x1ebe96383d72b469 0x81ebe96383d72b46 0xff3f3e387df3fc7d 0x7ff3f3e387df3fc7

def z446 : W := mkw 0x2bd13be45780db06 0x02bd13be45780db0 0xfff33fe67f80ff8f 0xffff33fe67f80ff8

def z447 : W := mkw 0x6feaafd15780db06 0x06feaafd15780db0 0xffccffd9ff80ff8c 0xfffccffd9ff80ff8

def z448 : W := mkw 0x0044400862480420 0x0004440086248042 0x70ccc038624c1c7f 0xd70ccc038624c1c7

def z449 : W := mkw 0x0004000820400420 0x0000400082040042 0x600c001860001c00 0x4600c001860001c0

def z450 : W := mkw 0x210029c000804b06 0x0210029c000804b0 0x000001c000000380 0x0000001c00000038

def z451 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z452 : W := mkw 0x0101210600854294 0x4010121060085429 0x1303012603cf03ff 0x91303012603cf03f

def z453 : W := mkw 0x0054506ae25c2df3 0x20054506ae25c2df 0xf0fcf1ffe27cffff 0xff0fcf1ffe27cfff

def z454 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xec3c3e187c30fc00 0x6ec3c3e187c30fc0

def z455 : W := mkw 0x0a80000011000000 0x00a8000001100000 0x8f0000001d800000 0x28f0000001d80000

def z456 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x0ff3ffc780000002 0xa0ff3ffc78000000

def z457 : W := mkw 0x00444048e2480d22 0x200444048e2480d2 0x60ccc0d9e24c1c0b 0xd60ccc0d9e24c1c0

def z458 : W := mkw 0x0040000053000000 0x0004000005300000 0xa00000007f800008 0x0a00000007f80000

def z459 : W := mkw 0x00404042c20c0992 0x200404042c20c099 0x40ccc1ff820c0387 0xd40ccc1ff820c038

def z460 : W := mkw 0x0b9139a6009562d5 0x40b9139a6009562d 0xdff33fe603ffe3ff 0xfdff33fe603ffe3f

def z461 : W := mkw 0x4fbbbdb700040090 0x04fbbbdb70004009 0x5fffffff824c03ff 0xf5fffffff824c03f

def z462 : W := mkw 0x4fbbbdb519220008 0x04fbbbdb51922000 0xcfffffff9db30007 0xfcfffffff9db3000

def z463 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c0c1c780000002 0x800c0c1c78000000

def z464 : W := mkw 0x042ec000286a0008 0x0042ec000286a000 0xac3fc0007c7f000b 0x7ac3fc0007c7f000

def z465 : W := mkw 0x00444048e2480d22 0x200444048e2480d2 0x70ccc0f9e0401c7d 0x570ccc0f9e0401c7

def z466 : W := mkw 0x4b913db500000000 0x04b913db50000000 0x4fc03fff80000004 0xf4fc03fff8000000

def z467 : W := mkw 0x0000000000000000 0x0000000000000000 0x40c001c000000004 0xd40c001c00000000

def z468 : W := mkw 0x453bbdb500000000 0x0453bbdb50000000 0x403fffff80000007 0x0403fffff8000000

def z469 : W := mkw 0x4bc7e9cfe24c0db2 0x24bc7e9cfe24c0db 0x73cfc1ffe24c1fff 0xd73cfc1ffe24c1ff

def z470 : W := mkw 0x0eaec000286a0008 0x00eaec000286a000 0x0fffc000007f0003 0xf0fffc000007f000

def z471 : W := mkw 0x0101210600854294 0x4010121060085429 0x93033106038fe38e 0xb93033106038fe38

def z472 : W := mkw 0x0111316e80956ff7 0x60111316e80956ff 0xd33331ff83ffffff 0xbd33331ff83fffff

def z473 : W := mkw 0x1004020a2cf5f6f5 0xc1004020a2cf5f6f 0xb00000007ffffff8 0x0b00000007ffffff

def z474 : W := mkw 0x0000020004009000 0x0000002000400900 0xb00000007c00fc08 0x0b00000007c00fc0

def z475 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xfff33fc07fffff8f 0xffff33fc07fffff8

def z476 : W := mkw 0x2b913ba41591f245 0x42b913ba41591f24 0x8f333e001db3e000 0x28f333e001db3e00

def z477 : W := mkw 0x2feaabc05780db06 0x02feaabc05780db0 0xffffffc07f80ff8f 0xfffffffc07f80ff8

def z478 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x4f333fff80000004 0x24f333fff8000000

def z479 : W := mkw 0x0438143000000000 0x0043814300000000 0x0c303e0000000000 0x20c303e000000000

def z480 : W := mkw 0x2040004053804b06 0x02040004053804b0 0x0000000003800380 0x0000000000380038

def z481 : W := mkw 0x0004000820400420 0x0000400082040042 0x70ccc1ffe0401c7f 0xd70ccc1ffe0401c7

def z482 : W := mkw 0x00444048e2480d22 0x200444048e2480d2 0x2000000060001c00 0x02000000060001c0

def z483 : W := mkw 0x104442087f7ab469 0x8104442087f7ab46 0xb00000007ffffc78 0x0b00000007ffffc7

def z484 : W := mkw 0x3fb83fb01db0f245 0x83fb83fb01db0f24 0x8f303e001db0e000 0x28f303e001db0e00

def z485 : W := mkw 0x146c4658ee689d22 0xa146c4658ee689d2 0x6cccced9fc001c00 0x46cccced9fc001c0

def z486 : W := mkw 0x1ffff73e7ffff6fd 0xc1ffff73e7ffff6f 0xffffff3e7fffffff 0xfffffff3e7ffffff

def z487 : W := mkw 0x4eeecc917b6a0008 0x04eeecc917b6a000 0x6cccced9fc000000 0x46cccced9fc00000

def z488 : W := mkw 0x2bc02bcad784dfb6 0x22bc02bcad784dfb 0xffc03fffff80fffc 0xfffc03fffff80fff

def z489 : W := mkw 0x5fbfbdbd28702461 0x85fbfbdbd2870246 0x4fffffff80700077 0xf4fffffff8070007

def z490 : W := mkw 0x0155712662dd62d5 0x40155712662dd62d 0xb3fff12663ffe3ff 0xfb3fff12663ffe3f

def z491 : W := mkw 0x4bc3e9c7c20c0992 0x24bc3e9c7c20c099 0x03c3c1c7820c0382 0x803c3c1c7820c038

def z492 : W := mkw 0x4fbbbdb7001520d1 0x44fbbbdb7001520d 0x4fffffff807f0077 0xf4fffffff807f007

def z493 : W := mkw 0x1044424aee7cbdf3 0xa1044424aee7cbdf 0xf0ccc1fffe7cffff 0xdf0ccc1fffe7cfff

def z494 : W := mkw 0x0000000200040090 0x0000000020004009 0x50ccc1ff824c03ff 0xd50ccc1ff824c03f

def z495 : W := mkw 0x00404042c20c0992 0x200404042c20c099 0x00000000020c0380 0x000000000020c038

def z496 : W := mkw 0x0101210600854294 0x4010121060085429 0x0000010600000380 0x0000001060000038

def z497 : W := mkw 0x2ac44acaf74c9db2 0x22ac44acaf74c9db 0x7ccccffffe4c1fff 0xd7ccccffffe4c1ff

def z498 : W := mkw 0x2bd139e653956bd7 0x42bd139e653956bd 0x93f331e603ffe3ff 0xb93f331e603ffe3f

def z499 : W := mkw 0x0111312400916245 0x4011131240091624 0x000030000000e000 0x0000030000000e00

def z500 : W := mkw 0x443b943500000000 0x0443b94350000000 0x0033000000000000 0x0003300000000000

def z501 : W := mkw 0x0044400062480000 0x0004440006248000 0x20ccc00060000000 0x420ccc0006000000

def z502 : W := mkw 0x0ffff1247bfb624d 0x40ffff1247bfb624 0xaffff0007fffe00b 0xfaffff0007fffe00

def z503 : W := mkw 0x0111312400000000 0x0011131240000000 0x0333300000000000 0x2033330000000000

def z504 : W := mkw 0x1004000828702461 0x8100400082870246 0x0000000000700070 0x0000000000070007

def z505 : W := mkw 0x443fd43fa04c04b0 0x2443fd43fa04c04b 0x003fc03f804c0073 0x0003fc03f804c007

def z506 : W := mkw 0x2bd57beef7ddfff7 0x62bd57beef7ddfff 0xffffffffffffffff 0xffffffffffffffff

def z507 : W := mkw 0x0111312400916245 0x4011131240091624 0x9333302001f3e07d 0x39333302001f3e07

def z508 : W := mkw 0x0ac0000053000000 0x00ac000005300000 0x2cc000007c000000 0x42cc000007c00000

def z509 : W := mkw 0x0fbbb12619b762dd 0x40fbbb12619b762d 0x9f3331261fffe3ff 0xb9f3331261fffe3f

def z510 : W := mkw 0x0111312600040090 0x0011131260004009 0x13333126024c03ff 0xb13333126024c03f

def z511 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xefc03ec07d80fc00 0x6efc03ec07d80fc0

def z512 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0x2cffc0007c7f0003 0x42cffc0007c7f000

def z513 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x300cc03fe24c1ffb 0x0300cc03fe24c1ff

def z514 : W := mkw 0x01113126001520d1 0x401113126001520d 0x03333126007f0077 0xb03333126007f007

def z515 : W := mkw 0x0000000200040090 0x0000000020004009 0x00000106020c0382 0x800000106020c038

def z516 : W := mkw 0x0efed4307b6a0008 0x00efed4307b6a000 0xeffffe387fff000f 0xfeffffe387fff000

def z517 : W := mkw 0x0000000200040090 0x0000000020004009 0x10000126000003f4 0x010000126000003f

def z518 : W := mkw 0x4ffffdfde2480d22 0x24ffffdfde2480d2 0x6fffffffe0001c07 0xf6fffffffe0001c0

def z519 : W := mkw 0x0004000820400420 0x0000400082040042 0x3000000060401c78 0x03000000060401c7

def z520 : W := mkw 0x0fbbb12400000000 0x00fbbb1240000000 0x0ffff12600000007 0xf0ffff1260000000

def z521 : W := mkw 0x5fbfbfbd2c609420 0x85fbfbfbd2c60942 0x6ffffffffc001c07 0xf6ffffffffc001c0

def z522 : W := mkw 0x2044424af7ccdfb6 0x22044424af7ccdfb 0xb00000007fccfff8 0x0b00000007fccfff

def z523 : W := mkw 0x0144614ae2cc4fb6 0x20144614ae2cc4fb 0xf3ccf1ffe3ccffff 0xff3ccf1ffe3ccfff

def z524 : W := mkw 0x0100210200844294 0x0010021020084429 0x9300312603cce3ff 0xb9300312603cce3f

def z525 : W := mkw 0x00404042c20c0992 0x200404042c20c099 0x10c0c1e7824c03ff 0x910c0c1e7824c03f

def z526 : W := mkw 0x143c143828702461 0x8143c14382870246 0xac3c00387c700079 0x7ac3c00387c70007

def z527 : W := mkw 0x0000000000916245 0x4000000000091624 0x8000000001b3e000 0x08000000001b3e00

def z528 : W := mkw 0x0000004280040992 0x2000000428004099 0x000001c780000380 0x0000001c78000038

def z529 : W := mkw 0x21113be60495fbd7 0x421113be60495fbd 0xd3333fe603ffffff 0xbd3333fe603fffff

def z530 : W := mkw 0x0ac2c000530a0008 0x00ac2c000530a000 0x00c0c00000000000 0x000c0c0000000000

def z531 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0x6fc00fc07f801f80 0xc6fc00fc07f801f8

def z532 : W := mkw 0x3bc42bc87ff0ff67 0x83bc42bc87ff0ff6 0xffc03fc07ff0fffc 0xfffc03fc07ff0fff

def z533 : W := mkw 0x4fbffdb5286a0008 0x04fbffdb5286a000 0x4fffffff807f0007 0xf4fffffff807f000

def z534 : W := mkw 0x0000000200040090 0x0000000020004009 0x10000000024c03f8 0x010000000024c03f

def z535 : W := mkw 0x0044404ae2dd6ff7 0x60044404ae2dd6ff 0xb000000063fffff8 0x0b000000063fffff

def z536 : W := mkw 0x21002bc00480db06 0x021002bc00480db0 0xfc003fc07c00ff8c 0x7fc003fc07c00ff8

def z537 : W := mkw 0x2feaabc05fa2db0e 0x02feaabc05fa2db0 0xfff33fc07fb3ff8c 0xffff33fc07fb3ff8

def z538 : W := mkw 0x1efed6307f7ab049 0x81efed6307f7ab04 0xaffffe007fffe00b 0xfaffffe007fffe00

def z539 : W := mkw 0x0b802b8004009000 0x00b802b800400900 0xffc03fc07c00fc0c 0xfffc03fc07c00fc0

def z540 : W := mkw 0x143816300c30b041 0x8143816300c30b04 0x9c303e201c70e07d 0x39c303e201c70e07

def z541 : W := mkw 0x1eba96301d32b049 0x81eba96301d32b04 0x8f333e001db3e000 0x28f333e001db3e00

def z542 : W := mkw 0x0044400062480000 0x0004440006248000 0xa3ffc00063ff000b 0xfa3ffc00063ff000

def z543 : W := mkw 0x143ed438287a2469 0x8143ed438287a246 0x003fc038007f0073 0x0003fc038007f007

def z544 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0x7cc03fc07c00ff84 0x47cc03fc07c00ff8

def z545 : W := mkw 0x4eeeccdbe24c0db2 0x24eeeccdbe24c0db 0x7ccccfffe24c1fff 0xd7ccccfffe24c1ff

def z546 : W := mkw 0x147c16786e70bd63 0x8147c16786e70bd6 0xfcfc3ff87e70fffd 0xffcfc3ff87e70fff

def z547 : W := mkw 0x0000000000000000 0x0000000000000000 0x03030000038f0002 0x803030000038f000

def z548 : W := mkw 0x0101210400000000 0x0010121040000000 0x0303010600000002 0x8030301060000000

def z549 : W := mkw 0x0effd0267b7f20d9 0x40effd0267b7f20d 0xafffc0267fff007b 0xfafffc0267fff007

def z550 : W := mkw 0x204442407feadb0e 0x0204442407feadb0 0xb00000007fffff88 0x0b00000007fffff8

def z551 : W := mkw 0x0010102000000000 0x0001010200000000 0x0030302000000005 0x3003030200000000

def z552 : W := mkw 0x2ac002405780db06 0x02ac002405780db0 0xbfc000007f80ff88 0xfbfc000007f80ff8

def z553 : W := mkw 0x01517166c29d6bd7 0x601517166c29d6bd 0x93f3f1e783ffe3ff 0xb93f3f1e783ffe3f

def z554 : W := mkw 0x443b943500000000 0x0443b94350000000 0x40ffc1ff80000007 0xd40ffc1ff8000000

def z555 : W := mkw 0x0040004242040992 0x0004000424204099 0x70c001e6624c1fff 0xd70c001e6624c1ff

def z556 : W := mkw 0x01113126009562d5 0x401113126009562d 0x903031260070e3fd 0x3903031260070e3f

def z557 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x4ffffed980000000 0x64ffffed98000000

def z558 : W := mkw 0x2bc2e9c0538a4b0e 0x02bc2e9c0538a4b0 0x03c3c1c0038f0382 0x803c3c1c0038f038

def z559 : W := mkw 0x0000000200040090 0x0000000020004009 0x9333012603ff03ff 0xb9333012603ff03f

def z560 : W := mkw 0x0ac2c042d30e099a 0x20ac2c042d30e099 0x03c3c1c7838f0382 0x803c3c1c7838f038

def z561 : W := mkw 0x0111312400000000 0x0011131240000000 0x8333312603ff000f 0xb8333312603ff000

def z562 : W := mkw 0x147c56386e78b461 0x8147c56386e78b46 0xfcfcfe387e7cfc7f 0xffcfcfe387e7cfc7

def z563 : W := mkw 0x0a82800011020008 0x00a8280001102000 0x0303000001830000 0x0030300000183000

def z564 : W := mkw 0x100002000c30b041 0x8100002000c30b04 0x800000001c30e000 0x0800000001c30e00

def z565 : W := mkw 0x0151316642956bd7 0x40151316642956bd 0xf3f331e663ffffff 0xff3f331e663fffff

def z566 : W := mkw 0x2040024057009902 0x0204002405700990 0x200000007c001c00 0x0200000007c001c0

def z567 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xafffc0007db30000 0x6afffc0007db3000

def z568 : W := mkw 0x0004020824409420 0x0000402082440942 0xfc0c3e387c40fc7d 0x7fc0c3e387c40fc7

def z569 : W := mkw 0x004440007b6a0008 0x0004440007b6a000 0xa0ccc0007fff000b 0xda0ccc0007fff000

def z570 : W := mkw 0x0ac0004053000902 0x00ac000405300090 0xffc001c07f801f8c 0xfffc001c07f801f8

def z571 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x70c001c0624c1ffc 0xd70c001c0624c1ff

def z572 : W := mkw 0x2b802b801580d204 0x02b802b801580d20 0x9f003f001f80e38c 0xb9f003f001f80e38

def z573 : W := mkw 0x0000000000000000 0x0000000000000000 0x400c003800000005 0x5400c00380000000

def z574 : W := mkw 0x143c143828702461 0x8143c14382870246 0x703c003860701c7d 0x5703c003860701c7

def z575 : W := mkw 0x0eeec04ae24c0db2 0x20eeec04ae24c0db 0x7fffc1ffe24c1fff 0xf7fffc1ffe24c1ff

def z576 : W := mkw 0x0000000000000000 0x0000000000000000 0x100001000200038c 0x9100001000200038

def z577 : W := mkw 0x0000000200040090 0x0000000020004009 0x00000026004c0073 0x000000026004c007

def z578 : W := mkw 0x01012106009562d5 0x401012106009562d 0x9303010603ffe3fa 0x89303010603ffe3f

def z579 : W := mkw 0x0155716ee2dd6ff7 0x60155716ee2dd6ff 0x70ccf1ffe24cffff 0xd70ccf1ffe24cfff

def z580 : W := mkw 0x4faba98500000000 0x04faba9850000000 0x0fffc1c780000003 0xf0fffc1c78000000

def z581 : W := mkw 0x2044424af7ccdfb6 0x22044424af7ccdfb 0xf0ccc1ffffccffff 0xdf0ccc1ffffccfff

def z582 : W := mkw 0x0040000042000000 0x0004000004200000 0x20c0000062000008 0xd20c000006200000

def z583 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xacccc0007fff0008 0x4acccc0007fff000

def z584 : W := mkw 0x153c37382cf0f665 0x8153c37382cf0f66 0xff3c3f387ff0fffd 0xfff3c3f387ff0fff

def z585 : W := mkw 0x0040004ac2040db2 0x20040004ac2040db 0x70c001ffe2001ffc 0xd70c001ffe2001ff

def z586 : W := mkw 0x0428000008200000 0x0042800000820000 0x8c3000001c300000 0x28c3000001c30000

def z587 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x0f3ffe3f80000003 0x20f3ffe3f8000000

def z588 : W := mkw 0x0004400aa04c04b0 0x20004400aa04c04b 0x00000000004c0070 0x000000000004c007

def z589 : W := mkw 0x0ac2c000530a0008 0x00ac2c000530a000 0xafc3c0007f8f000a 0xfafc3c0007f8f000

def z590 : W := mkw 0x4ffffdb562480000 0x04ffffdb56248000 0x6fffffffe24c000f 0xf6fffffffe24c000

def z591 : W := mkw 0x4ffffdfffb6e0dba 0x24ffffdfffb6e0db 0xffffffffffff1fff 0xfffffffffffff1ff

def z592 : W := mkw 0x143c167aac74bdf3 0xa143c167aac74bdf 0xfc3c3ffffc70fffd 0x7fc3c3ffffc70fff

def z593 : W := mkw 0x0001000600050090 0x4000100060005009 0x00030006000f0002 0x000030006000f000

def z594 : W := mkw 0x41557dffe24c0db2 0x241557dffe24c0db 0x70ccffffe24c1fff 0xd70ccffffe24c1ff

def z595 : W := mkw 0x4fbfbdbd20400420 0x04fbfbdbd2040042 0x7fffffffe0401c7f 0xf7fffffffe0401c7

def z596 : W := mkw 0x053d312628f562d5 0x4053d312628f562d 0xbf3f31267fffe3ff 0xfbf3f31267fffe3f

def z597 : W := mkw 0x5fbbbfbd0410b461 0x85fbbbfbd0410b46 0x5fffffff8000fc77 0xf5fffffff8000fc7

def z598 : W := mkw 0x0faaa98000000000 0x00faaa9800000000 0x4fffffc000000007 0xf4fffffc00000000

def z599 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xff3f3e387ffffc7f 0xfff3f3e387ffffc7

def z600 : W := mkw 0x2b802bc00480db06 0x02b802bc00480db0 0x5fc03fc00000ff84 0xf5fc03fc00000ff8

def z601 : W := mkw 0x4ffffdb77bff62dd 0x44ffffdb77bff62d 0xffffffffffffe3ff 0xfffffffffffffe3f

def z602 : W := mkw 0x0100210000804204 0x0010021000080420 0x9333310003ffe38f 0xb9333310003ffe38

def z603 : W := mkw 0x0eea800053000000 0x00eea80005300000 0xafffc0007f80000b 0xfafffc0007f80000

def z604 : W := mkw 0x0000000a800404b0 0x20000000a800404b 0x0000003f80000070 0x00000003f8000007

def z605 : W := mkw 0x00444048e2480d22 0x200444048e2480d2 0x60ccc1ffe0001c07 0xd60ccc1ffe0001c0

def z606 : W := mkw 0x0111312400102041 0x0011131240010204 0x933331260070e07f 0xb933331260070e07

def z607 : W := mkw 0x043c143820400420 0x0043c14382040042 0x7c3c3e3860401c7d 0x77c3c3e3860401c7

def z608 : W := mkw 0x143c143828702461 0x8143c14382870246 0x903c30380070e07d 0x3903c30380070e07

def z609 : W := mkw 0x143c563aac7cb4f1 0xa143c563aac7cb4f 0xfc3cfe3ffc7cfc7f 0x7fc3cfe3ffc7cfc7

def z610 : W := mkw 0x0eaa800000000000 0x00eaa80000000000 0x0cccc00000000000 0x40cccc0000000000

def z611 : W := mkw 0x21402bc04680db06 0x021402bc04680db0 0x70c03fc06200ff8c 0xd70c03fc06200ff8

def z612 : W := mkw 0x046c40007b6a0008 0x0046c40007b6a000 0xac3c00007fff0009 0x7ac3c00007fff000

def z613 : W := mkw 0x3fbc3fb83df0f665 0x83fbc3fb83df0f66 0xff3c3e387df0fc7d 0x7ff3c3e387df0fc7

def z614 : W := mkw 0x053ff12628ff62dd 0x4053ff12628ff62d 0x933ff12603ffe3ff 0xb933ff12603ffe3f

def z615 : W := mkw 0x2bd13be65795fbd7 0x42bd13be65795fbd 0xffc03fe67f80fffc 0xfffc03fe67f80fff

def z616 : W := mkw 0x0ac2c000530a0008 0x00ac2c000530a000 0x83f3c00003ff000b 0xb83f3c00003ff000

def z617 : W := mkw 0x0a80000000000000 0x00a8000000000000 0x0fc0000000000000 0xf0fc000000000000

def z618 : W := mkw 0x143ed6382c7ab469 0x8143ed6382c7ab46 0xfc3ffe387c7ffc7f 0x7fc3ffe387c7ffc7

def z619 : W := mkw 0x0b80298000000000 0x00b8029800000000 0x03c001c000000000 0x803c001c00000000

def z620 : W := mkw 0x1efed67aff7ebdfb 0xa1efed67aff7ebdf 0xffffffffffffffff 0xffffffffffffffff

def z621 : W := mkw 0x4fbbbdb7009562d5 0x44fbbbdb7009562d 0x9f333f2603ffe3ff 0xb9f333f2603ffe3f

def z622 : W := mkw 0x1010167a8414bdf3 0xa1010167a8414bdf 0x50003fff8000fff4 0x050003fff8000fff

def z623 : W := mkw 0x2bc06bc2d78cdb96 0x22bc06bc2d78cdb9 0xffc0ffc7ff8cff8e 0xfffc0ffc7ff8cff8

def z624 : W := mkw 0x1eeec6187f6a9428 0x81eeec6187f6a942 0xefffce187fff1c0b 0xfefffce187fff1c0

def z625 : W := mkw 0x4b93b9a500000000 0x04b93b9a50000000 0x03f3f1e780000007 0xb03f3f1e78000000

def z626 : W := mkw 0x0eaa800019220008 0x00eaa80001922000 0x0c0000001c000000 0x00c0000001c00000

def z627 : W := mkw 0x2b802bc01580db06 0x02b802bc01580db0 0xdf003fc01d80ff84 0x2df003fc01d80ff8

def z628 : W := mkw 0x0eeec00afb6e04b8 0x20eeec00afb6e04b 0xafffc03fffff007b 0xfafffc03fffff007

def z629 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000024c000b 0x900000000024c000

def z630 : W := mkw 0x2ac00ac05780db06 0x02ac00ac05780db0 0xfcc00ec07f80ff88 0x4fcc00ec07f80ff8

def z631 : W := mkw 0x00044000286a0008 0x000044000286a000 0x00000000007f0000 0x000000000007f000

def z632 : W := mkw 0x0eeec2007f6a9008 0x00eeec2007f6a900 0xfffffe007ffffc0f 0xffffffe007ffffc0

def z633 : W := mkw 0x0015502ea05d24f1 0x60015502ea05d24f 0x003fc03f807f0073 0x0003fc03f807f007

def z634 : W := mkw 0x0000004a80040db2 0x20000004a80040db 0x500001ff824c1fff 0x9500001ff824c1ff

def z635 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xb3c001c07f80ff88 0x8b3c001c07f80ff8

def z636 : W := mkw 0x0000000000000000 0x0000000000000000 0x100000200040007d 0x1100000200040007

def z637 : W := mkw 0x21002bc00480db06 0x021002bc00480db0 0xd3003fc00380ff8c 0xbd3003fc00380ff8

def z638 : W := mkw 0x142c02082c70b461 0x8142c02082c70b46 0xbc3c00007c70fc79 0x7bc3c00007c70fc7

def z639 : W := mkw 0x20000ac004009902 0x020000ac00400990 0x40000ec000001c00 0x040000ec000001c0

def z640 : W := mkw 0x41113db500000000 0x041113db50000000 0x43333fff80000007 0xb43333fff8000000

def z641 : W := mkw 0x2bc02bc25795fbd7 0x42bc02bc25795fbd 0xffc03fc07ffffffc 0xfffc03fc07ffffff

def z642 : W := mkw 0x1000061804009420 0x8100006180400942 0x40000e1800001c00 0x040000e1800001c0

def z643 : W := mkw 0x21402bc05780db06 0x021402bc05780db0 0xf0003fc07f80ff8c 0x0f0003fc07f80ff8

def z644 : W := mkw 0x01113126009562d5 0x401113126009562d 0x133331260000e3f7 0xb133331260000e3f

def z645 : W := mkw 0x153d373c2cf1f665 0xc153d373c2cf1f66 0xff3f3e387df3fc7d 0x7ff3f3e387df3fc7

def z646 : W := mkw 0x0000000000000000 0x0000000000000000 0x400001ff80000004 0x0400001ff8000000

def z647 : W := mkw 0x147c567aee7cbdf3 0xa147c567aee7cbdf 0xfc3c3e387e7cfffd 0x7fc3c3e387e7cfff

def z648 : W := mkw 0x200002001580d204 0x0200002001580d20 0x800000001d80e000 0x0800000001d80e00

def z649 : W := mkw 0x01113126009562d5 0x401113126009562d 0xd3fff1ff83ffe3ff 0xfd3fff1ff83ffe3f

def z650 : W := mkw 0x4b93bdb500000000 0x04b93bdb50000000 0x43c3ffff80000006 0x843c3ffff8000000

def z651 : W := mkw 0x00404042c20c0992 0x200404042c20c099 0x70c0c1c7e20c1f8e 0xd70c0c1c7e20c1f8

def z652 : W := mkw 0x01416146c28d4b96 0x601416146c28d4b9 0x03c3c1c7838f0382 0x803c3c1c7838f038

def z653 : W := mkw 0x4101298500000000 0x0410129850000000 0x000001c780000000 0x0000001c78000000

def z654 : W := mkw 0x2bd13be45791fb47 0x42bd13be45791fb4 0xfff33fc07fb3ff8c 0xffff33fc07fb3ff8

def z655 : W := mkw 0x0004400aa04c04b0 0x20004400aa04c04b 0x100cc13f824c03ff 0x9100cc13f824c03f

def z656 : W := mkw 0x01113126009562d5 0x401113126009562d 0x9333312601b3e3f4 0x29333312601b3e3f

def z657 : W := mkw 0x0155716ee24c0db2 0x20155716ee24c0db 0x73fff1ffe24c1fff 0xf73fff1ffe24c1ff

def z658 : W := mkw 0x453bb53500000000 0x0453bb5350000000 0x033ff13f80000007 0xb033ff13f8000000

def z659 : W := mkw 0x2feee9c07bea4b0e 0x02feee9c07bea4b0 0xafffc1c07fff038b 0xfafffc1c07fff038

def z660 : W := mkw 0x0010102000102041 0x0001010200010204 0x803030000030e000 0x2803030000030e00

def z661 : W := mkw 0x2ffffbe67ffffbdf 0x42ffffbe67ffffbd 0xffffffe67fffffff 0xfffffffe67ffffff

def z662 : W := mkw 0x0bc0298053000000 0x00bc029805300000 0xefc03fc07f80000c 0xfefc03fc07f80000

def z663 : W := mkw 0x143816300c30b041 0x8143816300c30b04 0xfc303e007c30fc0c 0x7fc303e007c30fc0

def z664 : W := mkw 0x143c16302c70b041 0x8143c16302c70b04 0xac3c3e007c70e009 0x7ac3c3e007c70e00

def z665 : W := mkw 0x4eaa8c9100000000 0x04eaa8c910000000 0x4fffced980000003 0xf4fffced98000000

def z666 : W := mkw 0x4ffffdb57b6a0008 0x04ffffdb57b6a000 0x6ffffffffc000007 0xf6ffffffffc00000

def z667 : W := mkw 0x4ebb943500000000 0x04ebb94350000000 0x0fffc03f80000003 0xf0fffc03f8000000

def z668 : W := mkw 0x0100210000804204 0x0010021000080420 0x830030000180e000 0x2830030000180e00

def z669 : W := mkw 0x2ac44ac8f7489d22 0x22ac44ac8f7489d2 0x6cccced9fc001c00 0x46cccced9fc001c0

def z670 : W := mkw 0x0428041000000000 0x0042804100000000 0x4c0c0e1800000000 0x44c0c0e180000000

def z671 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x700c0038624c1ffd 0x5700c0038624c1ff

def z672 : W := mkw 0x0feee9807b6a0008 0x00feee9807b6a000 0xefffffc07fff000f 0xfefffffc07fff000

def z673 : W := mkw 0x00004002800c0090 0x200004002800c009 0x0000c007800c0002 0x00000c007800c000

def z674 : W := mkw 0x4003800500000000 0x0400380050000000 0x0003c00780000002 0x00003c0078000000

def z675 : W := mkw 0x0004000028600000 0x0000400002860000 0xa00000007c700008 0x0a00000007c70000

def z676 : W := mkw 0x0eeec04afb6e0dba 0x20eeec04afb6e0db 0x7cccc1fffe4c1fff 0xd7cccc1fffe4c1ff

def z677 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x0f333f2600000007 0xb0f333f260000000

def z678 : W := mkw 0x042a800008220008 0x0042a80000822000 0x0033000000330000 0x0003300000033000

def z679 : W := mkw 0x0004000a204404b0 0x00004000a204404b 0x700c013e624c1fff 0xd700c013e624c1ff

def z680 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xacfcc0007c700009 0x7acfcc0007c70000

def z681 : W := mkw 0x01113126009562d5 0x401113126009562d 0x930031260380e3fc 0xb930031260380e3f

def z682 : W := mkw 0x00101022009562d5 0x400101022009562d 0x9030302003ffe3fd 0x39030302003ffe3f

def z683 : W := mkw 0x51113fbd0410b461 0x851113fbd0410b46 0x50003fff8000fc74 0x050003fff8000fc7

def z684 : W := mkw 0x6bc3a9c553804b06 0x06bc3a9c553804b0 0x03c3c1c783800382 0x803c3c1c78380038

def z685 : W := mkw 0x2bc029c053804b06 0x02bc029c053804b0 0x73c001c063801f8c 0xd73c001c063801f8

def z686 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xb03c00387c70fc79 0x0b03c00387c70fc7

def z687 : W := mkw 0x0004000020400000 0x0000400002040000 0x200c000060400009 0x5200c00006040000

def z688 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0x8fc03fc01f80e380 0xa8fc03fc01f80e38

def z689 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0x2fcfc0007f8f0002 0xc2fcfc0007f8f000

def z690 : W := mkw 0x042ec00aa86e04b8 0x2042ec00aa86e04b 0x003fc03f807f0073 0x0003fc03f807f007

def z691 : W := mkw 0x0eaa800000000000 0x00eaa80000000000 0x8fffc00003ff000b 0xf8fffc00003ff000

def z692 : W := mkw 0x0004004aa0440db2 0x20004004aa0440db 0x700c01ffe0401ffd 0x5700c01ffe0401ff

def z693 : W := mkw 0x0ac6c0007b6a0008 0x00ac6c0007b6a000 0xa3c3c0007fff000a 0x8a3c3c0007fff000

def z694 : W := mkw 0x0eeec00062480000 0x00eeec0006248000 0x2fffc000624c000b 0xf2fffc000624c000

def z695 : W := mkw 0x0044400062480000 0x0004440006248000 0x60ccc1ffe24c000f 0xd60ccc1ffe24c000

def z696 : W := mkw 0x2ff83ff05780db06 0x02ff83ff05780db0 0xfffc3ff87f80ff8d 0xffffc3ff87f80ff8

def z697 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0x53c03fc00380ff84 0x853c03fc00380ff8

def z698 : W := mkw 0x0004400aa04c04b0 0x20004400aa04c04b 0x40ccc1ff804c0077 0xd40ccc1ff804c007

def z699 : W := mkw 0x042c000828600420 0x0042c00082860042 0xfc3c00387c701c7d 0x7fc3c00387c701c7

def z700 : W := mkw 0x0539353400000000 0x0053935340000000 0x4f3f3f3e00000007 0xf4f3f3f3e0000000

def z701 : W := mkw 0x0000000000804204 0x0000000000080420 0x900000000380e388 0x0900000000380e38

def z702 : W := mkw 0x143816380410b461 0x8143816380410b46 0x5c3c3e380000fc75 0x75c3c3e380000fc7

def z703 : W := mkw 0x153937360cb5f2d5 0xc153937360cb5f2d 0x9f333f261fffe3ff 0xb9f333f261fffe3f

def z704 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x30000126624c1fff 0x930000126624c1ff

def z705 : W := mkw 0x214023405780db06 0x0214023405780db0 0xb30031007f80ff8c 0xbb30031007f80ff8

def z706 : W := mkw 0x4b83a98500000000 0x04b83a9850000000 0x0303000000000000 0x0030300000000000

def z707 : W := mkw 0x011139a6009562d5 0x4011139a6009562d 0xd3333fe603ffe3ff 0xbd3333fe603ffe3f

def z708 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xaff3c0007fff000a 0xaaff3c0007fff000

def z709 : W := mkw 0x4fbbbdb500102041 0x04fbbbdb50010204 0x5fffffff8000e077 0xf5fffffff8000e07

def z710 : W := mkw 0x2b802bc00480db06 0x02b802bc00480db0 0xffc03fc07c00ff8c 0xfffc03fc07c00ff8

def z711 : W := mkw 0x543fd43fa87c24f1 0xa543fd43fa87c24f 0x003fc03f807c0073 0x0003fc03f807c007

def z712 : W := mkw 0x142c06182c609420 0x8142c06182c60942 0xfc0c3e387c40fc7d 0x7fc0c3e387c40fc7

def z713 : W := mkw 0x4eaa8c93009562d5 0x44eaa8c93009562d 0xdcccced983ffe3f8 0x4dcccced983ffe3f

def z714 : W := mkw 0x0110312000906245 0x0011031200090624 0x9333312003ffe3ff 0xb9333312003ffe3f

def z715 : W := mkw 0x3ffc3df87bf06f67 0x83ffc3df87bf06f6 0x03fc01f803f003f1 0x803fc01f803f003f

def z716 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xfc3c3e387c30fc74 0x6fc3c3e387c30fc7

def z717 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xefc03fc07f80ff80 0xeefc03fc07f80ff8

def z718 : W := mkw 0x0eeec008fb6a0428 0x20eeec008fb6a042 0xafffc019ffff000b 0xfafffc019ffff000

def z719 : W := mkw 0x4ebb9cb500000000 0x04ebb9cb50000000 0x4cfffeff80000007 0x74cfffeff8000000

def z720 : W := mkw 0x2bc3e9c6538f4b9e 0x42bc3e9c6538f4b9 0x03c3c1c6038f0382 0x803c3c1c6038f038

def z721 : W := mkw 0x4fabad9500000000 0x04fabad950000000 0x4ccccfdf80000000 0x44ccccfdf8000000

def z722 : W := mkw 0x0428000008200000 0x0042800000820000 0x8f3300001fff000b 0xb8f3300001fff000

def z723 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x4fffffff838f0007 0xf4fffffff838f000

def z724 : W := mkw 0x0000000000000000 0x0000000000000000 0x4cccffff80000007 0xf4cccffff8000000

def z725 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x7cccffffe24c1fff 0xf7cccffffe24c1ff

def z726 : W := mkw 0x443b943500000000 0x0443b94350000000 0x4cffffff80000007 0xf4cffffff8000000

def z727 : W := mkw 0x111137360495f2d5 0xc111137360495f2d 0x10003f260000e3f4 0x010003f260000e3f

def z728 : W := mkw 0x01113126009562d5 0x401113126009562d 0x933ff13f83ffe3ff 0xb933ff13f83ffe3f

def z729 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0x7fc03fc07c00ff84 0xf7fc03fc07c00ff8

def z730 : W := mkw 0x01113126009562d5 0x401113126009562d 0xd33331ff83ffe3ff 0xbd33331ff83ffe3f

def z731 : W := mkw 0x01113126009562d5 0x401113126009562d 0x8333312603ffe3f3 0xa8333312603ffe3f

def z732 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x7fffffffe0001c0f 0xf7fffffffe0001c0

def z733 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xff003e007f80ff8c 0x7ff003e007f80ff8

def z734 : W := mkw 0x41557db57b6a0008 0x041557db57b6a000 0xe0003fffffff000c 0x0e0003fffffff000

def z735 : W := mkw 0x0eaa800019220008 0x00eaa80001922000 0x8fffc0001fff000b 0xf8fffc0001fff000

def z736 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xfff33fc07fb3ff8c 0xffff33fc07fb3ff8

def z737 : W := mkw 0x004440007b6a0008 0x0004440007b6a000 0xa33300007fff0008 0x2a33300007fff000

def z738 : W := mkw 0x4fbbbdb500102041 0x04fbbbdb50010204 0xdfffffff83ffe07f 0xfdfffffff83ffe07

def z739 : W := mkw 0x543f943f287524f1 0xc543f943f287524f 0x003fc03f807f0073 0x0003fc03f807f007

def z740 : W := mkw 0x100402082c70b461 0x8100402082c70b46 0xfc0c3e387c70fc7d 0x7fc0c3e387c70fc7

def z741 : W := mkw 0x2bc12bc45780db06 0x02bc12bc45780db0 0xffc33fc67f80ff8e 0xfffc33fc67f80ff8

def z742 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x70ccc1ffe20c1ff6 0xc70ccc1ffe20c1ff

def z743 : W := mkw 0x4ffffdffe24c0db2 0x24ffffdffe24c0db 0x3f333e00624c1ff8 0x23f333e00624c1ff

def z744 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0x7fc03fc07f80ff84 0xc7fc03fc07f80ff8

def z745 : W := mkw 0x543e96392c70b461 0x8543e96392c70b46 0xfc3cfe39fc70fc7d 0x7fc3cfe39fc70fc7

def z746 : W := mkw 0x0eeac0005b2a0008 0x00eeac0005b2a000 0x8ff3c0001fff000b 0xb8ff3c0001fff000

def z747 : W := mkw 0x1eeec658ff6a9d2a 0xa1eeec658ff6a9d2 0x6cccced9fc001c00 0x46cccced9fc001c0

def z748 : W := mkw 0x2ac00ac05780db06 0x02ac00ac05780db0 0xfcc03ec07f80ff8c 0x7fcc03ec07f80ff8

def z749 : W := mkw 0x100002080410b461 0x8100002080410b46 0xfc003e007c00fc7c 0x7fc003e007c00fc7

def z750 : W := mkw 0x143816300c30b041 0x8143816300c30b04 0xfc303e207c70fc7d 0x7fc303e207c70fc7

def z751 : W := mkw 0x142c06182c70b461 0x8142c06182c70b46 0xfc0c3e187c70fc7c 0x7fc0c3e187c70fc7

def z752 : W := mkw 0x143ed6382c7ab469 0x8143ed6382c7ab46 0xff3ffe387ffffc7f 0xfff3ffe387ffffc7

def z753 : W := mkw 0x1044424aff7ebdfb 0xa1044424aff7ebdf 0xb00000007ffffff8 0x0b00000007ffffff

def z754 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x70ccc1ffe04c1ff7 0x470ccc1ffe04c1ff

def z755 : W := mkw 0x21113bee8495fff7 0x621113bee8495fff 0x50003fff8000fff4 0x050003fff8000fff

def z756 : W := mkw 0x2b846b8ab5ccd6b4 0x22b846b8ab5ccd6b 0x8f0cfe3f9dcce073 0x28f0cfe3f9dcce07

def z757 : W := mkw 0x000002000480d204 0x0000002000480d20 0xfc003e007f80ff8c 0x7fc003e007f80ff8

def z758 : W := mkw 0x252eebc02ceadb0e 0x0252eebc02ceadb0 0x503fffc0007fff87 0x0503fffc0007fff8

def z759 : W := mkw 0x0004000028600000 0x0000400002860000 0xa33300007fff000b 0xba33300007fff000

def z760 : W := mkw 0x543f963d2c70b461 0x8543f963d2c70b46 0xfcfffffffc70fc7f 0xffcfffffffc70fc7

def z761 : W := mkw 0x1eeec4187b6a0428 0x81eeec4187b6a042 0xafffc0187fff000b 0xfafffc0187fff000

def z762 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xffc03fc07fccff8f 0xfffc03fc07fccff8

def z763 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0x7c3c3e387c00fc75 0x77c3c3e387c00fc7

def z764 : W := mkw 0x1111377e8495fff7 0xe1111377e8495fff 0x50003fff8000fff4 0x050003fff8000fff

def z765 : W := mkw 0x0eaec000396a0008 0x00eaec000396a000 0x8fffc0001dff0003 0xf8fffc0001dff000

def z766 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x70ccc1ffe24c1ffc 0x470ccc1ffe24c1ff

def z767 : W := mkw 0x0000020804009420 0x0000002080400942 0xfc003e387c00fc7c 0x7fc003e387c00fc7

def z768 : W := mkw 0x6fbbbdb511804204 0x06fbbbdb51180420 0x4fffffff81800007 0xf4fffffff8180000

def z769 : W := mkw 0x5b87ab8d2c70b461 0x85b87ab8d2c70b46 0xb3c3c1c7fc70fc7a 0x8b3c3c1c7fc70fc7

def z770 : W := mkw 0x41113db7009562d5 0x441113db7009562d 0x93333f2603ffe3ff 0xb93333f2603ffe3f

def z771 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xafffc0007fff0008 0x6afffc0007fff000

def z772 : W := mkw 0x543f963d2c70b461 0x8543f963d2c70b46 0xfc3f3e387c70fc7d 0x7fc3f3e387c70fc7

def z773 : W := mkw 0x21002bc00480db06 0x021002bc00480db0 0xff003fc07f80ff8c 0xfff003fc07f80ff8

def z774 : W := mkw 0x2044424af74c9db2 0x22044424af74c9db 0x300000007e4c1ff8 0x0300000007e4c1ff

def z775 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x43ffffff80000007 0x843ffffff8000000

def z776 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xafffc1267fff000f 0xfafffc1267fff000

def z777 : W := mkw 0x0eeec0407b6a090a 0x00eeec0407b6a090 0xefffc0c07fff1c0b 0xfefffc0c07fff1c0

def z778 : W := mkw 0x0000020004009000 0x0000002000400900 0xfc003e207c40fc7d 0x7fc003e207c40fc7

def z779 : W := mkw 0x21002bc00480db06 0x021002bc00480db0 0x7c003fc07c00ff84 0x47c003fc07c00ff8

def z780 : W := mkw 0x0010143000000000 0x0001014300000000 0x40ccffff80000007 0xd40ccffff8000000

def z781 : W := mkw 0x143ed43aa87e24f9 0xa143ed43aa87e24f 0x003fc03f807f0073 0x0003fc03f807f007

def z782 : W := mkw 0x00000002009562d5 0x400000002009562d 0x9333000003ffe3f8 0x29333000003ffe3f

def z783 : W := mkw 0x0eeec0087b6a0428 0x00eeec0087b6a042 0xafffc0387fff007b 0xfafffc0387fff007

def z784 : W := mkw 0x2bc029c253854b96 0x42bc029c253854b9 0x03c001c0038f0380 0x803c001c0038f038

def z785 : W := mkw 0x1ad2d638571ab469 0x81ad2d638571ab46 0x53c3fe38038ffc76 0x853c3fe38038ffc7

def z786 : W := mkw 0x543d163d2c70b461 0x8543d163d2c70b46 0xfc3c3e3ffc70fc7d 0x7fc3c3e3ffc70fc7

def z787 : W := mkw 0x0000024004009902 0x0000002400400990 0xfc003fc07c00ff8c 0x7fc003fc07c00ff8

def z788 : W := mkw 0x4b93bdb500000000 0x04b93bdb50000000 0x43cfffff80000007 0xd43cfffff8000000

def z789 : W := mkw 0x4fabad9500000000 0x04fabad950000000 0x4fcfcfff80000007 0xd4fcfcfff8000000

def z790 : W := mkw 0x0fb83db000000000 0x00fb83db00000000 0x4ffcffff80000007 0xf4ffcffff8000000

def z791 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xbfc03fc07f80ff88 0xabfc03fc07f80ff8

def z792 : W := mkw 0x00101022009562d5 0x400101022009562d 0x9333302003ffe3ff 0xb9333302003ffe3f

def z793 : W := mkw 0x0155716ce2d96f67 0x60155716ce2d96f6 0xe3fff0d9e1b3fc00 0x6e3fff0d9e1b3fc0

def z794 : W := mkw 0x14785672ce3cb9d3 0xa14785672ce3cb9d 0x8cf0ffc79e3ce382 0xa8cf0ffc79e3ce38

def z795 : W := mkw 0x01002102009562d5 0x401002102009562d 0x9333310003ffe3ff 0xb9333310003ffe3f

def z796 : W := mkw 0x0eaac000192a0008 0x00eaac000192a000 0x8f33c0001dbf0002 0x28f33c0001dbf000

def z797 : W := mkw 0x0004404aa04c0db2 0x20004404aa04c0db 0x50ccc1ff804c1ff7 0xd50ccc1ff804c1ff

def z798 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x5fffffff8200038f 0xf5fffffff8200038

def z799 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xaff300007fff0008 0xfaff300007fff000

def z800 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x73cfc1ffe3cf1fff 0xd73cfc1ffe3cf1ff

def z801 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x4fffcfff80000003 0xc4fffcfff8000000

def z802 : W := mkw 0x0eeec048fb6a0d2a 0x20eeec048fb6a0d2 0xefffc1ffffff1c0f 0xfefffc1ffffff1c0

def z803 : W := mkw 0x143c5638ac78b461 0xa143c5638ac78b46 0xfc3cfe39fc70fc7d 0x7fc3cfe39fc70fc7

def z804 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x4fffffff80000004 0x64fffffff8000000

def z805 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0xf3ccc1ffe3cc1fff 0xff3ccc1ffe3cc1ff

def z806 : W := mkw 0x0bc023005780d204 0x00bc023005780d20 0xffc03f007f80ff8c 0xfffc03f007f80ff8

def z807 : W := mkw 0x4fbbbdb500916245 0x44fbbbdb50091624 0xcfffffff83ffe00f 0xfcfffffff83ffe00

def z808 : W := mkw 0x0ffff1267bff62dd 0x40ffff1267bff62d 0x3cccf1267c00e3f4 0x43cccf1267c00e3f

def z809 : W := mkw 0x4fbbbdb519220008 0x04fbbbdb51922000 0xcfffffff9fff000f 0xfcfffffff9fff000

def z810 : W := mkw 0x3044424afffcfff7 0xa3044424afffcfff 0xb00000007ffcfff8 0x0b00000007ffcfff

def z811 : W := mkw 0x647b96755780db06 0x0647b96755780db0 0xb03fc03fff80ff8b 0x0b03fc03fff80ff8

def z812 : W := mkw 0x0eaa800019220008 0x00eaa80001922000 0x8f3300001fbf0002 0xa8f3300001fbf000

def z813 : W := mkw 0x4fbbbdb500112041 0x44fbbbdb50011204 0x4fffffff80330007 0xf4fffffff8033000

def z814 : W := mkw 0x2eeecac8ff6a9d2a 0x22eeecac8ff6a9d2 0x6cccced9fc001c00 0x46cccced9fc001c0

def z815 : W := mkw 0x4fbbbdb508220008 0x04fbbbdb50822000 0x4fffffff80330007 0xf4fffffff8033000

def z816 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xffcc3ff87f80ff8d 0xfffcc3ff87f80ff8

def z817 : W := mkw 0x0eec00007b600000 0x00eec00007b60000 0xafff00007fff000b 0xfafff00007fff000

def z818 : W := mkw 0x0040404ac20c0db2 0x20040404ac20c0db 0x50ccc1ff820c1ff7 0xd50ccc1ff820c1ff

def z819 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xffc03fe67f80ff8f 0xfffc03fe67f80ff8

def z820 : W := mkw 0x0eea80005b220008 0x00eea80005b22000 0xaff300007fff000b 0xfaff300007fff000

def z821 : W := mkw 0x01113126009562d5 0x401113126009562d 0x93fff12603ffe3ff 0xf93fff12603ffe3f

def z822 : W := mkw 0x0eaa804a99260dba 0x20eaa804a99260db 0xdf3301ff9db31ff4 0x2df3301ff9db31ff

def z823 : W := mkw 0x0eaa800019220008 0x00eaa80001922000 0x8f3300001dff0003 0x28f3300001dff000

def z824 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xa3ffc0007fff000b 0x8a3ffc0007fff000

def z825 : W := mkw 0x411139a7009562d5 0x4411139a7009562d 0x933331e783ffe3ff 0xb933331e783ffe3f

def z826 : W := mkw 0x4fbbbdb500102041 0x04fbbbdb50010204 0x4fffffff80700077 0xf4fffffff8070007

def z827 : W := mkw 0x143816380c30b461 0x8143816380c30b46 0xfc303e387c30fc7c 0x7fc303e387c30fc7

def z828 : W := mkw 0x0ac6c0007b6a0008 0x00ac6c0007b6a000 0xa3f3c0007fff000b 0xba3f3c0007fff000

def z829 : W := mkw 0x143816380410b461 0x8143816380410b46 0xfc3c3e387c00fc7d 0x7fc3c3e387c00fc7

def z830 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xfcfcfef9fc70fc7d 0x7fcfcfef9fc70fc7

def z831 : W := mkw 0x543fd63d2c7ab469 0x8543fd63d2c7ab46 0xfc3ffe3ffc7ffc7f 0x7fc3ffe3ffc7ffc7

def z832 : W := mkw 0x45393db500000000 0x045393db50000000 0x4cfcffff80000007 0xf4cfcffff8000000

def z833 : W := mkw 0x7fbbbfb51db0f245 0x87fbbbfb51db0f24 0x8f333e001db0e000 0x28f333e001db0e00

def z834 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xffc03fe07fc0fffd 0xfffc03fe07fc0fff

def z835 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x60ccc1ffe24c1ff3 0xc60ccc1ffe24c1ff

def z836 : W := mkw 0x2ac002405780db06 0x02ac002405780db0 0xffc03e007f80ff8c 0xfffc03e007f80ff8

def z837 : W := mkw 0x01113126009562d5 0x401113126009562d 0x9333302003ffe3fd 0x39333302003ffe3f

def z838 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xefffc1c07fff000f 0xfefffc1c07fff000

def z839 : W := mkw 0x0000020004009000 0x0000002000400900 0xfc003f007e00ff8c 0xffc003f007e00ff8

def z840 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xffccffd9ff80ff8c 0xfffccffd9ff80ff8

def z841 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xfcc03fc07c00ff8c 0x7fcc03fc07c00ff8

def z842 : W := mkw 0x143d543ea87d24f1 0xe143d543ea87d24f 0x003fc03f807f0073 0x0003fc03f807f007

def z843 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xffc0ffc7ff80ff8e 0xfffc0ffc7ff80ff8

def z844 : W := mkw 0x2b802bc01580db06 0x02b802bc01580db0 0xff003fc07d80ff8c 0x7ff003fc07d80ff8

def z845 : W := mkw 0x143c56382c78b461 0x8143c56382c78b46 0xfc3cfe387c7cfc7f 0x7fc3cfe387c7cfc7

def z846 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xfc0c3e387c00fc7c 0x7fc0c3e387c00fc7

def z847 : W := mkw 0x043c163824409420 0x0043c16382440942 0xfc3c3e387c40fc7d 0x7fc3c3e387c40fc7

def z848 : W := mkw 0x0eaec000396a0008 0x00eaec000396a000 0x8f3fc0001fff000b 0xb8f3fc0001fff000

def z849 : W := mkw 0x152d271e2ce5d6b4 0xc152d271e2ce5d6b 0x6f0f0f1e7f8f1f82 0xc6f0f0f1e7f8f1f8

def z850 : W := mkw 0x0eeec8807b6a0008 0x00eeec8807b6a000 0xefffcec07fff000b 0xfefffcec07fff000

def z851 : W := mkw 0x01113126009562d5 0x401113126009562d 0xdf333f2603ffe3ff 0xfdf333f2603ffe3f

def z852 : W := mkw 0x0eeec0407b6a090a 0x00eeec0407b6a090 0xafffc1c07fff038b 0xfafffc1c07fff038

def z853 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xfcc03fc07f80ff8c 0x4fcc03fc07f80ff8

def z854 : W := mkw 0x143d143e287524f1 0xc143d143e287524f 0x003c003e00700071 0x0003c003e0070007

def z855 : W := mkw 0x01113126009562d5 0x401113126009562d 0x9333300003ffe3fb 0xb9333300003ffe3f

def z856 : W := mkw 0x5fbbbfb50cb1f245 0xc5fbbbfb50cb1f24 0x8f333e001db3e000 0x28f333e001db3e00

def z857 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xbc3c3e007c70fc79 0x7bc3c3e007c70fc7

def z858 : W := mkw 0x011133260495f2d5 0x4011133260495f2d 0x50003f260000fff4 0x050003f260000fff

def z859 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xffccffc07f80ff8f 0xfffccffc07f80ff8

def z860 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0x8fffc0001fff0003 0xa8fffc0001fff000

def z861 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0xcfffffff8380000f 0xfcfffffff8380000

def z862 : W := mkw 0x4fbbbdb519b3624d 0x44fbbbdb519b3624 0xcfffffff9db3e007 0xfcfffffff9db3e00

def z863 : W := mkw 0x4fbbbdb500804204 0x04fbbbdb50080420 0x5fffffff8000e387 0xf5fffffff8000e38

def z864 : W := mkw 0x41113db500000000 0x041113db50000000 0x40ccffff80000004 0x440ccffff8000000

def z865 : W := mkw 0x2b802b801580d204 0x02b802b801580d20 0xff003f007f80ff8c 0xfff003f007f80ff8

def z866 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xffffc0007fff1c0f 0xfffffc0007fff1c0

def z867 : W := mkw 0x0000004a80040db2 0x20000004a80040db 0x50ccc1ff80001ff4 0x450ccc1ff80001ff

def z868 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x4cfcffff80000005 0x74cfcffff8000000

def z869 : W := mkw 0x6bc3abc55780db06 0x06bc3abc55780db0 0xffc33fc07f80ff8c 0xfffc33fc07f80ff8

def z870 : W := mkw 0x200002400480db06 0x0200002400480db0 0xfc003e007c00ff8c 0x7fc003e007c00ff8

def z871 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x4ffffeff80000003 0x64ffffeff8000000

def z872 : W := mkw 0x0eeec0087b6a0428 0x00eeec0087b6a042 0xffffc1ffffff1c7f 0xfffffc1ffffff1c7

def z873 : W := mkw 0x6bc3abc55780db06 0x06bc3abc55780db0 0xffcfffffff80ff8f 0xfffcfffffff80ff8

def z874 : W := mkw 0x0ac4400073480000 0x00ac440007348000 0xafffc0007fff000b 0xfafffc0007fff000

def z875 : W := mkw 0x41113537009562d5 0x441113537009562d 0x9333313f83ffe3ff 0xb9333313f83ffe3f

def z876 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xefffc0d9ffff000b 0xfefffc0d9ffff000

def z877 : W := mkw 0x2bc2abc05782db0e 0x02bc2abc05782db0 0xffc33fc07f83ff8c 0xfffc33fc07f83ff8

def z878 : W := mkw 0x0eeec0407b6a090a 0x00eeec0407b6a090 0xbfffc0007fff1f8b 0xfbfffc0007fff1f8

def z879 : W := mkw 0x0ac2c000530a0008 0x00ac2c000530a000 0xaff3c0007fff000b 0xfaff3c0007fff000

def z880 : W := mkw 0x143d163c2c70b461 0x8143d163c2c70b46 0xfc3f3e3e7c70fc7f 0x7fc3f3e3e7c70fc7

def z881 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x73ffc1ffe24c1fff 0xf73ffc1ffe24c1ff

def z882 : W := mkw 0x0eeec040fb6a090a 0x20eeec040fb6a090 0xafffc0c1ffff000b 0xfafffc0c1ffff000

def z883 : W := mkw 0x4fbbbdb500804204 0x04fbbbdb50080420 0xdfffffff83ffe38f 0xfdfffffff83ffe38

def z884 : W := mkw 0x1111332e0495f6f5 0xc1111332e0495f6f 0x100031260000fff4 0x0100031260000fff

def z885 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xfc3c3e387e7cfc7f 0xffc3c3e387e7cfc7

def z886 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xfcfc3ff87c70fc7d 0xffcfc3ff87c70fc7

def z887 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xfc3cfe3ffc70fc7f 0x7fc3cfe3ffc70fc7

def z888 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x70ccc1ffe0001ff7 0xd70ccc1ffe0001ff

def z889 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xfc3c3e187c70fc78 0x6fc3c3e187c70fc7

def z890 : W := mkw 0x2ad11ae65715b9d3 0x42ad11ae65715b9d 0x6cf30ee67c7f1c73 0x46cf30ee67c7f1c7

def z891 : W := mkw 0x6bc12bc55780db06 0x06bc12bc55780db0 0xffc03fc7ff80ff8c 0xfffc03fc7ff80ff8

def z892 : W := mkw 0x4fbbbdb500916245 0x44fbbbdb50091624 0x4fffffff8000e007 0xf4fffffff8000e00

def z893 : W := mkw 0x4eaa8c9100000000 0x04eaa8c910000000 0x4fffcfff80000007 0xf4fffcfff8000000

def z894 : W := mkw 0x01113126009562d5 0x401113126009562d 0x9333312603ffe3fc 0x29333312603ffe3f

def z895 : W := mkw 0x204002405780db06 0x0204002405780db0 0xfcc03fc07f80ff8c 0xffcc03fc07f80ff8

def z896 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xfff33fc07f80ff8f 0xffff33fc07f80ff8

def z897 : W := mkw 0x21402bc05780db06 0x021402bc05780db0 0xfc003fc07f80ff8c 0x7fc003fc07f80ff8

def z898 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x70ccc1ffe2001ffc 0xd70ccc1ffe2001ff

def z899 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0x2fffc0007fff0003 0xc2fffc0007fff000

def z900 : W := mkw 0x0004000a204404b0 0x00004000a204404b 0x70ccc1ffe24c1fff 0xd70ccc1ffe24c1ff

def z901 : W := mkw 0x046c40007b6a0008 0x0046c40007b6a000 0xaf3f00007fff000b 0xfaf3f00007fff000

def z902 : W := mkw 0x0eeac0005b2a0008 0x00eeac0005b2a000 0xaff3c0007fbf000a 0xfaff3c0007fbf000

def z903 : W := mkw 0x0040024046009902 0x0004002404600990 0xfc003e007e00ff8c 0x7fc003e007e00ff8

def z904 : W := mkw 0x0000000000000000 0x0000000000000000 0xaf3300007fff000b 0xfaf3300007fff000

def z905 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xfff03fc07ff0ff8d 0xffff03fc07ff0ff8

def z906 : W := mkw 0x0a80088000000000 0x00a8008800000000 0x4ccccfff80000007 0xd4ccccfff8000000

def z907 : W := mkw 0x0b9139a400000000 0x00b9139a40000000 0x4fffffff80000007 0xf4fffffff8000000

def z908 : W := mkw 0x0eaec000396a0008 0x00eaec000396a000 0xaf3fc0007dff000b 0x7af3fc0007dff000

def z909 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x70ccc1ffe0401ffd 0x570ccc1ffe0401ff

def z910 : W := mkw 0x01113126009562d5 0x401113126009562d 0x9333310603ffe3fa 0xa9333310603ffe3f

def z911 : W := mkw 0x41113db7009562d5 0x441113db7009562d 0xd3ffffff83ffe3ff 0xfd3ffffff83ffe3f

def z912 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x4cffffff80000007 0x44cffffff8000000

def z913 : W := mkw 0x1044424ae65cbdf3 0xa1044424ae65cbdf 0x30000000624cfff8 0x030000000624cfff

def z914 : W := mkw 0x001012200410b041 0x0001012200410b04 0xfc003e207c00fc7c 0x7fc003e207c00fc7

def z915 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xafffc0007dff0003 0x6afffc0007dff000

def z916 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xfc3c3ffffc70fc7d 0x7fc3c3ffffc70fc7

def z917 : W := mkw 0x010023000480d204 0x0010023000480d20 0xfc003f007c00ff8c 0x7fc003f007c00ff8

def z918 : W := mkw 0x0040004242040992 0x0004000424204099 0x70ccc1ffe24c1fff 0xd70ccc1ffe24c1ff

def z919 : W := mkw 0x4fbbbdb508200000 0x04fbbbdb50820000 0xcfffffff9c300007 0xfcfffffff9c30000

def z920 : W := mkw 0x21113ba60495f2d5 0x421113ba60495f2d 0x10003f260000e3f4 0x010003f260000e3f

def z921 : W := mkw 0x046c40006a680000 0x0046c40006a68000 0xafffc0007fff000b 0xfafffc0007fff000

def z922 : W := mkw 0x0eae800039620008 0x00eae80003962000 0xaf3f00007fff000b 0xfaf3f00007fff000

def z923 : W := mkw 0x143c543aa87c24f1 0xa143c543aa87c24f 0x003c0038007c0071 0x0003c0038007c007

def z924 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0xf0ccf1ffe24cffff 0xff0ccf1ffe24cfff

def z925 : W := mkw 0x4fabad9500000000 0x04fabad950000000 0x4fcfffdf80000006 0xf4fcfffdf8000000

def z926 : W := mkw 0x4fbbbdb500804204 0x04fbbbdb50080420 0xcfffffff8180e007 0xfcfffffff8180e00

def z927 : W := mkw 0x101412282c70b461 0x8101412282c70b46 0xfc303e207c70fc7d 0x7fc303e207c70fc7

def z928 : W := mkw 0x4eaa8c9100000000 0x04eaa8c910000000 0x4ccccfff80000004 0x44ccccfff8000000

def z929 : W := mkw 0x0bc02bc046009902 0x00bc02bc04600990 0xffc03fc07e00ff8c 0xfffc03fc07e00ff8

def z930 : W := mkw 0x01113126009562d5 0x401113126009562d 0xd3f331e603ffe3ff 0xfd3f331e603ffe3f

def z931 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x4fffffff824c000f 0xf4fffffff824c000

def z932 : W := mkw 0x00101022001420d1 0x000101022001420d 0x9333312603ffe3ff 0xb9333312603ffe3f

def z933 : W := mkw 0x143c143aa87424f1 0xa143c143aa87424f 0x003c003f80700071 0x0003c003f8070007

def z934 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x4fffffdf80000002 0xe4fffffdf8000000

def z935 : W := mkw 0x0044004862400d22 0x00044004862400d2 0x70ccc1ffe2401fff 0xd70ccc1ffe2401ff

def z936 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xfc3c3f3e7c70fc7f 0xffc3c3f3e7c70fc7

def z937 : W := mkw 0x2044424affeedfbe 0x22044424affeedfb 0xb00000007ffffff8 0x0b00000007ffffff

def z938 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0xeffffffffc00000f 0xfeffffffffc00000

def z939 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xbfffc1007fff038f 0xfbfffc1007fff038

def z940 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xfc3c3e387ffffc7d 0x7fc3c3e387ffffc7

def z941 : W := mkw 0x4faaad9100000000 0x04faaad910000000 0x4fccffff80000007 0xf4fccffff8000000

def z942 : W := mkw 0x0044404afb6e0dba 0x20044404afb6e0db 0x70ccc1fffe4c1fff 0xd70ccc1fffe4c1ff

def z943 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xff003fc07f80ff8c 0x2ff003fc07f80ff8

def z944 : W := mkw 0x01113126009562d5 0x401113126009562d 0x9333012603ffe3fb 0x89333012603ffe3f

def z945 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xbc303e207c70fc7d 0x3bc303e207c70fc7

def z946 : W := mkw 0x042c02082c609420 0x0042c02082c60942 0xfc3c3e387c70fc7d 0x7fc3c3e387c70fc7

def z947 : W := mkw 0x4eeecc917b6a0008 0x04eeecc917b6a000 0xafffce007fff000b 0xfafffce007fff000

def z948 : W := mkw 0x2bc2e9c2d38e4b9e 0x22bc2e9c2d38e4b9 0x03c3c1c7838f0382 0x803c3c1c7838f038

def z949 : W := mkw 0x6bc3e9c7d38c4b96 0x26bc3e9c7d38c4b9 0x03c3c1c7838c0382 0x803c3c1c7838c038

def z950 : W := mkw 0x6bc2abc15780db06 0x06bc2abc15780db0 0xffc0ffc1ff80ff8c 0xfffc0ffc1ff80ff8

def z951 : W := mkw 0x004440007b6a0008 0x0004440007b6a000 0xa3ffc0007fff000b 0xfa3ffc0007fff000

def z952 : W := mkw 0x0b802b800480d204 0x00b802b800480d20 0xffc03fc07f80ff8c 0xfffc03fc07f80ff8

def z953 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xffc03ec07f80ff88 0x6ffc03ec07f80ff8

def z954 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0xcfffffff81b30007 0xfcfffffff81b3000

def z955 : W := mkw 0x4eaa8c9100000000 0x04eaa8c910000000 0x4ccccfdf80000002 0xc4ccccfdf8000000

def z956 : W := mkw 0x01012106009562d5 0x401012106009562d 0x9333010603ffe3fb 0xb9333010603ffe3f

def z957 : W := mkw 0x1044424aeefdfff7 0xe1044424aeefdfff 0xb00000007ffffff8 0x0b00000007ffffff

def z958 : W := mkw 0x0eeec4107b6a0008 0x00eeec4107b6a000 0xefffce187fff000b 0xfefffce187fff000

def z959 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xfc3c3f387e70fffd 0xffc3c3f387e70fff

def z960 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xff3c3e387ff0fc7d 0xfff3c3e387ff0fc7

def z961 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xbf003f007f80ff8c 0xbbf003f007f80ff8

def z962 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xfcfcfe387c70fc7f 0xffcfcfe387c70fc7

def z963 : W := mkw 0x143e96382c70b461 0x8143e96382c70b46 0xfc3ffe387c70fc7f 0x7fc3ffe387c70fc7

def z964 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0x7cc03fc07e00ff8c 0xd7cc03fc07e00ff8

def z965 : W := mkw 0x2bc06bc0d788db06 0x22bc06bc0d788db0 0xffc0ffc1ff80ff8c 0xfffc0ffc1ff80ff8

def z966 : W := mkw 0x0100210200844294 0x0010021020084429 0x9333312603ffe3ff 0xb9333312603ffe3f

def z967 : W := mkw 0x0044404aea6e0dba 0x20044404aea6e0db 0x70ccc1ffe27f1fff 0xd70ccc1ffe27f1ff

def z968 : W := mkw 0x01113126009562d5 0x401113126009562d 0xf333312663ffffff 0xff333312663fffff

def z969 : W := mkw 0x1044424aee6c9db2 0xa1044424aee6c9db 0x300000007e4c1ff8 0x0300000007e4c1ff

def z970 : W := mkw 0x0eeec048fb6a0d2a 0x20eeec048fb6a0d2 0xffffc1d9ffff1f8f 0xfffffc1d9ffff1f8

def z971 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xfc3f3e387c7ffc7f 0x7fc3f3e387c7ffc7

def z972 : W := mkw 0x4fbbbdb500906245 0x04fbbbdb50090624 0xdfffffff83f0e3ff 0xfdfffffff83f0e3f

def z973 : W := mkw 0x01113126009562d5 0x401113126009562d 0x93f3f1e783ffe3ff 0xb93f3f1e783ffe3f

def z974 : W := mkw 0x0044404afb6e0dba 0x20044404afb6e0db 0xf3ffc1ffffff1fff 0xff3ffc1ffffff1ff

def z975 : W := mkw 0x101416382c70b461 0x8101416382c70b46 0xfc003e387c70fc7c 0x7fc003e387c70fc7

def z976 : W := mkw 0x4eab8c9500000000 0x04eab8c950000000 0x4ccfcedf80000002 0x44ccfcedf8000000

def z977 : W := mkw 0x6bc3a9c753854b96 0x46bc3a9c753854b9 0x03c3c1c7838f0382 0x803c3c1c7838f038

def z978 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xfc303e387c70fc7c 0x2fc303e387c70fc7

def z979 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xeffffe007fff000f 0xfeffffe007fff000

def z980 : W := mkw 0x0eeac0005b2a0008 0x00eeac0005b2a000 0x8f3300001fbf0000 0x28f3300001fbf000

def z981 : W := mkw 0x4fbbbdb500916245 0x44fbbbdb50091624 0xdfffffff81f3e07f 0xfdfffffff81f3e07

def z982 : W := mkw 0x143c143a287424f1 0x8143c143a287424f 0x003c003e007c0073 0x0003c003e007c007

def z983 : W := mkw 0x00000002009562d5 0x400000002009562d 0x9333012603ffe3ff 0xb9333012603ffe3f

def z984 : W := mkw 0x214023405780db06 0x0214023405780db0 0xff003f007f80ff8c 0xfff003f007f80ff8

def z985 : W := mkw 0x4fbbbdb519220008 0x04fbbbdb51922000 0x4fffffff9c000007 0xf4fffffff9c00000

def z986 : W := mkw 0x3eeeced87f6a9d2a 0x83eeeced87f6a9d2 0x6cccced87c001c00 0x46cccced87c001c0

def z987 : W := mkw 0x046ec0007b6a0008 0x0046ec0007b6a000 0xa33fc0007fff000b 0xba33fc0007fff000

def z988 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xafffc1c7ffff000b 0xfafffc1c7ffff000

def z989 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xff3f3e387c70fc7f 0xfff3f3e387c70fc7

def z990 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xffc33fc07f8fff8e 0xfffc33fc07f8fff8

def z991 : W := mkw 0x0044404af34c0db2 0x20044404af34c0db 0xf0ccc1ffffcc1fff 0xdf0ccc1ffffcc1ff

def z992 : W := mkw 0x2044424af7ddfff7 0x62044424af7ddfff 0xb00000007ffffff8 0x0b00000007ffffff

def z993 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x4fccffff80000004 0xf4fccffff8000000

def z994 : W := mkw 0x4eaa8c9100000000 0x04eaa8c910000000 0x4cccceff80000003 0x44cccceff8000000

def z995 : W := mkw 0x4eeeccd9fb6a0d2a 0x24eeeccd9fb6a0d2 0xefffced9ffff1c0b 0xfefffced9ffff1c0

def z996 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xffc03fc07fffff8c 0xfffc03fc07fffff8

def z997 : W := mkw 0x143d163c2c71b461 0xc143d163c2c71b46 0xfc3f3e387c73fc7d 0x7fc3f3e387c73fc7

def z998 : W := mkw 0x2044424ae6ccdfb6 0x22044424ae6ccdfb 0x30000000624cfff8 0x030000000624cfff

def z999 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xaf3fc0007fff000b 0x2af3fc0007fff000

def z1000 : W := mkw 0x2bc029c2d3844b96 0x22bc029c2d3844b9 0x03c001c783800380 0x803c001c78380038

def z1001 : W := mkw 0x100402082c70b461 0x8100402082c70b46 0xbc003e007c70fc78 0x2bc003e007c70fc7

def z1002 : W := mkw 0x4ebb9cb500000000 0x04ebb9cb50000000 0x4fffceff80000003 0xf4fffceff8000000

def z1003 : W := mkw 0x0eeec0087b6a0428 0x00eeec0087b6a042 0xefffc0187fff1c0b 0xfefffc0187fff1c0

def z1004 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xafffc0007fbf0002 0xeafffc0007fbf000

def z1005 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xec3c3e387c70fc71 0x6ec3c3e387c70fc7

def z1006 : W := mkw 0x101016380410b461 0x8101016380410b46 0x7c003e387c00fc74 0x47c003e387c00fc7

def z1007 : W := mkw 0x0eeec048fb6a0d2a 0x20eeec048fb6a0d2 0xafffc0007fff1c0b 0xfafffc0007fff1c0

def z1008 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0xf0ccc1ffe3ff1fff 0xdf0ccc1ffe3ff1ff

def z1009 : W := mkw 0x4eeec8817b6a0008 0x04eeec8817b6a000 0xafffc0c1ffff000b 0xfafffc0c1ffff000

def z1010 : W := mkw 0x01113126009562d5 0x401113126009562d 0x1333312603ffe3f7 0x81333312603ffe3f

def z1011 : W := mkw 0x2bc169c6d38d4b96 0x62bc169c6d38d4b9 0x03c3c1c7838f0382 0x803c3c1c7838f038

def z1012 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xffc03fc07d80ff84 0x6ffc03fc07d80ff8

def z1013 : W := mkw 0x4fbbbdb511000000 0x04fbbbdb51100000 0xcfffffff9d800007 0xfcfffffff9d80000

def z1014 : W := mkw 0x2bc06bc0578adb0e 0x02bc06bc0578adb0 0xffc03fc07f8fff8c 0xfffc03fc07f8fff8

def z1015 : W := mkw 0x41113db500000000 0x041113db50000000 0x43ffffff80000007 0xf43ffffff8000000

def z1016 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xbffff0007fffe00f 0xfbffff0007fffe00

def z1017 : W := mkw 0x4fbbbdb511020008 0x04fbbbdb51102000 0x4fffffff81830007 0xf4fffffff8183000

def z1018 : W := mkw 0x01113536009562d5 0x401113536009562d 0xd3333f3e03ffe3ff 0xbd3333f3e03ffe3f

def z1019 : W := mkw 0x2eeec8c07b6a090a 0x02eeec8c07b6a090 0xafffc0c07fff000b 0xfafffc0c07fff000

def z1020 : W := mkw 0x0044404af34e0dba 0x20044404af34e0db 0x70ccc1ffe3cf1fff 0xd70ccc1ffe3cf1ff

def z1021 : W := mkw 0x31113ffe0495fff7 0xc31113ffe0495fff 0x50003ffe0000fff4 0x050003ffe0000fff

def z1022 : W := mkw 0x0ac440007b6a0008 0x00ac440007b6a000 0xaff300007fff000b 0xfaff300007fff000

def z1023 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x4fffffff807f0007 0xf4fffffff807f000

def z1024 : W := mkw 0x042ec000286a0008 0x0042ec000286a000 0xaf3fc0007fff000b 0xfaf3fc0007fff000

def z1025 : W := mkw 0x2bc129c653854b96 0x42bc129c653854b9 0x03c001c603800380 0x803c001c60380038

def z1026 : W := mkw 0x0eeec0487b6a0d2a 0x00eeec0487b6a0d2 0xffffc1f87fff1fff 0xfffffc1f87fff1ff

def z1027 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xbfffc0207fff007f 0xfbfffc0207fff007

def z1028 : W := mkw 0x043816300410b041 0x0043816300410b04 0xfc3c3e387c70fc7d 0x7fc3c3e387c70fc7

def z1029 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xaf3300007fff000b 0xbaf3300007fff000

def z1030 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x4fcfffff80000006 0xc4fcfffff8000000

def z1031 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xfc303e007c70fc7c 0x7fc303e007c70fc7

def z1032 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0xfcccc1fffe4c1fff 0xffcccc1fffe4c1ff

def z1033 : W := mkw 0x0ac0024057009902 0x00ac002405700990 0xffc03fc07f80ff8c 0xfffc03fc07f80ff8

def z1034 : W := mkw 0x4b83a98500000000 0x04b83a9850000000 0x4fcfffff80000007 0xf4fcfffff8000000

def z1035 : W := mkw 0x0044404aea6c0db2 0x20044404aea6c0db 0xf0ccc1fffe7c1fff 0xdf0ccc1fffe7c1ff

def z1036 : W := mkw 0x2bc2abc05780db06 0x02bc2abc05780db0 0xffc3ffc07f80ff8e 0xfffc3ffc07f80ff8

def z1037 : W := mkw 0x4eeecc917b6a0008 0x04eeecc917b6a000 0xefffcfffffff000f 0xfefffcfffffff000

def z1038 : W := mkw 0x40000c9100000000 0x040000c910000000 0x40cccfff80000007 0xd40cccfff8000000

def z1039 : W := mkw 0x6bc3ebc5578adb0e 0x06bc3ebc5578adb0 0xffc3ffc7ff8fff8e 0xfffc3ffc7ff8fff8

def z1040 : W := mkw 0x4ebb9cb500000000 0x04ebb9cb50000000 0x4cffcfff80000007 0xd4cffcfff8000000

def z1041 : W := mkw 0x0eeac0005b2a0008 0x00eeac0005b2a000 0x8fffc0001fbf0003 0xf8fffc0001fbf000

def z1042 : W := mkw 0x01113126009562d5 0x401113126009562d 0x9333310003ffe3fc 0xb9333310003ffe3f

def z1043 : W := mkw 0x2bc12bc45781db06 0x42bc12bc45781db0 0xffc33fc07f83ff8c 0xfffc33fc07f83ff8

def z1044 : W := mkw 0x4ebb9cb500000000 0x04ebb9cb50000000 0x4cccceff80000000 0x44cccceff8000000

def z1045 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xff3f3e387df3fc7d 0x7ff3f3e387df3fc7

def z1046 : W := mkw 0x204002405780db06 0x0204002405780db0 0xbc003e007f80ff88 0x2bc003e007f80ff8

def z1047 : W := mkw 0x143fd43e287f24f9 0xc143fd43e287f24f 0x003fc03e007f0073 0x0003fc03e007f007

def z1048 : W := mkw 0x0004004aa0440db2 0x20004004aa0440db 0x70ccc1ffe0401fff 0xd70ccc1ffe0401ff

def z1049 : W := mkw 0x4b913db500000000 0x04b913db50000000 0x4fccffff80000007 0xf4fccffff8000000

def z1050 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0xdfffffff8000e00f 0xfdfffffff8000e00

def z1051 : W := mkw 0x2bc029c253844b96 0x02bc029c253844b9 0x03c001c6038c0382 0x803c001c6038c038

def z1052 : W := mkw 0x21402bc04680db06 0x021402bc04680db0 0xfcc03fc07e00ff8c 0xffcc03fc07e00ff8

def z1053 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xefffc0387fff000f 0xfefffc0387fff000

def z1054 : W := mkw 0x0eae800028600000 0x00eae80002860000 0xafffc0007fff000b 0xfafffc0007fff000

def z1055 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xfc0c3e387c70fc7c 0x4fc0c3e387c70fc7

def z1056 : W := mkw 0x043c12202c70b041 0x0043c12202c70b04 0xfc3c3e207c70fc7d 0x7fc3c3e207c70fc7

def z1057 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0xcfffffff8070000f 0xfcfffffff8070000

def z1058 : W := mkw 0x0eeec0407b6a090a 0x00eeec0407b6a090 0xffffc1ffffff1f8f 0xfffffc1ffffff1f8

def z1059 : W := mkw 0x0eba943000000000 0x00eba94300000000 0x4fffffff80000007 0xf4fffffff8000000

def z1060 : W := mkw 0x0eeec048fb6a0d2a 0x20eeec048fb6a0d2 0xffffc0f9ffff1c7f 0xfffffc0f9ffff1c7

def z1061 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x30ccc1ffe24c1ffb 0x830ccc1ffe24c1ff

def z1062 : W := mkw 0x5fbbbdb508302041 0x85fbbbdb50830204 0x4fffffff80300007 0xf4fffffff8030000

def z1063 : W := mkw 0x0000000019220008 0x0000000001922000 0x833300001fff000b 0xb833300001fff000

def z1064 : W := mkw 0x101016380410b461 0x8101016380410b46 0xfc303e387c70fc7d 0x7fc303e387c70fc7

def z1065 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x50ccc1ff824c1ff7 0x850ccc1ff824c1ff

def z1066 : W := mkw 0x00111026009562d5 0x400111026009562d 0x9333002603ffe3fb 0xb9333002603ffe3f

def z1067 : W := mkw 0x4fbbbdb500102041 0x04fbbbdb50010204 0xcfffffff8030e007 0xfcfffffff8030e00

def z1068 : W := mkw 0x0040000053000000 0x0004000005300000 0xa33300007fff000b 0xba33300007fff000

def z1069 : W := mkw 0x2bc2ebc0578adb0e 0x02bc2ebc0578adb0 0xffc0ffc07f80ff8c 0xfffc0ffc07f80ff8

def z1070 : W := mkw 0x4fbbbdb500804204 0x04fbbbdb50080420 0x4fffffff83800387 0xf4fffffff8380038

def z1071 : W := mkw 0x0eea800053000000 0x00eea80005300000 0xafffc0007fff000b 0xfafffc0007fff000

def z1072 : W := mkw 0x61113ff70495fbd7 0x461113ff70495fbd 0x50003fff8000fff4 0x050003fff8000fff

def z1073 : W := mkw 0x4eeec4117b6a0008 0x04eeec4117b6a000 0xafffc019ffff000b 0xfafffc019ffff000

def z1074 : W := mkw 0x0eaa800019220008 0x00eaa80001922000 0x8f3300001fff0008 0x28f3300001fff000

def z1075 : W := mkw 0x001412282450b461 0x0001412282450b46 0xfc3c3e387c70fc7d 0x7fc3c3e387c70fc7

def z1076 : W := mkw 0x453bbdb500000000 0x0453bbdb50000000 0x40ffffff80000007 0xd40ffffff8000000

def z1077 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x0fffffff80000003 0xa0fffffff8000000

def z1078 : W := mkw 0x4fbbbdb500916245 0x44fbbbdb50091624 0xdfffffff83b3e38f 0xfdfffffff83b3e38

def z1079 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0x7c3c3e387c70fc75 0x47c3c3e387c70fc7

def z1080 : W := mkw 0x0040004ac2040db2 0x20040004ac2040db 0x70ccc1ffe2001fff 0xd70ccc1ffe2001ff

def z1081 : W := mkw 0x4fbbbdb500814204 0x44fbbbdb50081420 0x4fffffff81830007 0xf4fffffff8183000

def z1082 : W := mkw 0x01113126009562d5 0x401113126009562d 0xbf3331267fffe3ff 0xfbf3331267fffe3f

def z1083 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xbfc03e007f80ff88 0xfbfc03e007f80ff8

def z1084 : W := mkw 0x2bc06bc05788db06 0x02bc06bc05788db0 0xffc0ffc07f8cff8e 0xfffc0ffc07f8cff8

def z1085 : W := mkw 0x0a80000011000000 0x00a8000001100000 0x8f3300001fff000b 0xb8f3300001fff000

def z1086 : W := mkw 0x143ed6382c7ab469 0x8143ed6382c7ab46 0xfc3cfe387c70fc7d 0x7fc3cfe387c70fc7

def z1087 : W := mkw 0x01113126009562d5 0x401113126009562d 0xd33f313e03ffe3ff 0xfd33f313e03ffe3f

def z1088 : W := mkw 0x211133660495fbd7 0x4211133660495fbd 0x100031260000fff4 0x0100031260000fff

def z1089 : W := mkw 0x0faaa98000000000 0x00faaa9800000000 0x4fffffff80000007 0xf4fffffff8000000

def z1090 : W := mkw 0x4fabad9500000000 0x04fabad950000000 0x4fffcfdf80000003 0xf4fffcfdf8000000

def z1091 : W := mkw 0x0000004a80040db2 0x20000004a80040db 0x50ccc1ff824c1fff 0xd50ccc1ff824c1ff

def z1092 : W := mkw 0x101416382450b461 0x8101416382450b46 0xfc0c3e387c40fc7d 0x7fc0c3e387c40fc7

def z1093 : W := mkw 0x0100298000000000 0x0010029800000000 0x40ccffff80000007 0xd40ccffff8000000

def z1094 : W := mkw 0x2ac00ac057009902 0x02ac00ac05700990 0xfcc03fc07e00ff8c 0xffcc03fc07e00ff8

def z1095 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xaf3f00007fff0009 0x7af3f00007fff000

def z1096 : W := mkw 0x0eeec0087b6a0428 0x00eeec0087b6a042 0xbfffc0007fff1c7b 0xfbfffc0007fff1c7

def z1097 : W := mkw 0x6fbbbfb51591f245 0x46fbbbfb51591f24 0x8f333e001db3e000 0x28f333e001db3e00

def z1098 : W := mkw 0x143c56382c7ab469 0x8143c56382c7ab46 0xfc3c3e387c7ffc7d 0x7fc3c3e387c7ffc7

def z1099 : W := mkw 0x0eaec000396a0008 0x00eaec000396a000 0x8f3300001dff0000 0x28f3300001dff000

def z1100 : W := mkw 0x014023404680db06 0x0014023404680db0 0xffc03fc07f80ff8c 0xfffc03fc07f80ff8

def z1101 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0x7c0c3e387c40fc7d 0x57c0c3e387c40fc7

def z1102 : W := mkw 0x2bc02bc05780db06 0x02bc02bc05780db0 0xffc03fffff80ff8c 0xfffc03fffff80ff8

def z1103 : W := mkw 0x143c16382c70b461 0x8143c16382c70b46 0xbc3c3e387c70fc79 0x2bc3c3e387c70fc7

def z1104 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0x70ffc1ffe27f1fff 0xd70ffc1ffe27f1ff

def z1105 : W := mkw 0x0428041000000000 0x0042804100000000 0x4ccccfff80000007 0xd4ccccfff8000000

def z1106 : W := mkw 0x0539353400000000 0x0053935340000000 0x4fffffff80000007 0xf4fffffff8000000

def z1107 : W := mkw 0x2bc2ebc0578adb0e 0x02bc2ebc0578adb0 0xfff3ffc07fffff8f 0xffff3ffc07fffff8

def z1108 : W := mkw 0x000002000410b041 0x0000002000410b04 0xfc003e007c70fc7c 0x7fc003e007c70fc7

def z1109 : W := mkw 0x142c02082c70b461 0x8142c02082c70b46 0xfc3c3e007c70fc7d 0x7fc3c3e007c70fc7

def z1110 : W := mkw 0x2bc069c2d38c4b96 0x22bc069c2d38c4b9 0x03c001c0038c0380 0x803c001c0038c038

def z1111 : W := mkw 0x0044404ae24c0db2 0x20044404ae24c0db 0xf0fcc1ffe27c1fff 0xff0fcc1ffe27c1ff

def z1112 : W := mkw 0x4eba9cb100000000 0x04eba9cb10000000 0x4cfcffff80000007 0xf4cfcffff8000000

def z1113 : W := mkw 0x01113126009562d5 0x401113126009562d 0x9333302603ffe3fb 0x29333302603ffe3f

def z1114 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x4cccffff80000007 0xd4cccffff8000000

def z1115 : W := mkw 0x143e96382c72b469 0x8143e96382c72b46 0xfc3f3e387c73fc7d 0x7fc3f3e387c73fc7

def z1116 : W := mkw 0x0eeec0007b6a0008 0x00eeec0007b6a000 0xafffc03fffff000b 0xfafffc03fffff000

def z1117 : W := mkw 0x0044424ae64c9db2 0x20044424ae64c9db 0xb00000007e4cfff8 0x0b00000007e4cfff

def z1118 : W := mkw 0x4fbbbdb500000000 0x04fbbbdb50000000 0x5fffffff8040007f 0xf5fffffff8040007

def z1119 : W := mkw 0x51113fbf0495f6f5 0xc51113fbf0495f6f 0x50003fff8000fff4 0x050003fff8000fff

def z1120 : W := mkw 0x0004020824409420 0x0000402082440942 0xfc003e007c40fc7c 0x7fc003e007c40fc7

def z1121 : W := mkw 0x143c143a287524f1 0xc143c143a287524f 0x003c0038007f0071 0x0003c0038007f007

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[],[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z7]),(0,[z0,z1,z8,z3,z4,z5,z6]),(0,[z0,z1,z9,z3,z4,z5,z6]),(0,[z0,z1,z10,z3,z4,z5,z6]),(0,[z0,z1,z3,z11,z5,z12,z6])],[(0,[z13,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z14,z6]),(0,[z0,z1,z15,z3,z4,z5,z6])],[(0,[z16,z0,z1,z15,z4,z5,z6]),(0,[z0,z1,z3,z17,z18,z5,z6]),(0,[z19,z0,z1,z3,z4,z20,z6]),(0,[z0,z1,z3,z4,z21,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z22]),(0,[z0,z1,z23,z3,z4,z5,z6]),(1,[z0,z1,z24,z3,z4,z25])],[(0,[z0,z1,z3,z4,z5,z6,z26]),(0,[z0,z1,z27,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z28,z6]),(0,[z0,z1,z3,z4,z5,z6,z29]),(0,[z0,z1,z3,z4,z5,z30,z6]),(0,[z0,z1,z31,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z32,z5,z6]),(0,[z33,z0,z1,z3,z4,z5,z34])],[(0,[z0,z1,z35,z4,z5,z36,z6]),(0,[z0,z1,z3,z37,z4,z5,z6]),(0,[z0,z1,z3,z38,z4,z5,z6]),(0,[z39,z0,z1,z3,z4,z5,z6])],[(0,[z40,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z41,z3,z4,z5,z6]),(0,[z0,z1,z42,z4,z5,z6,z43])],[(0,[z0,z1,z3,z4,z5,z44,z6]),(0,[z0,z1,z3,z4,z5,z6,z45])]],
   [[(0,[z0,z1,z3,z46,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z47,z6]),(0,[z0,z1,z48,z3,z4,z5,z6])],[(0,[z49,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z50,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z51]),(0,[z0,z1,z3,z52,z4,z5,z6]),(0,[z53,z0,z1,z3,z4,z5,z6])],[(0,[z54,z55,z0,z1,z3,z5,z6]),(0,[z0,z1,z56,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z57,z5,z6]),(0,[z58,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z59])],[(0,[z0,z1,z3,z4,z60,z5,z6]),(0,[z0,z1,z3,z4,z5,z61,z6]),(0,[z0,z1,z62,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z63,z6]),(0,[z0,z1,z3,z4,z5,z64,z6]),(1,[z0,z1,z3,z4,z5,z29]),(0,[z0,z1,z3,z4,z5,z65,z6]),(0,[z54,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z24,z3,z4,z5,z25])],[(0,[z66,z67,z1,z3,z4,z5,z6]),(0,[z68,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z69,z12])],[(0,[z16,z0,z1,z35,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z70]),(0,[z0,z1,z71,z3,z4,z5,z6]),(0,[z0,z72,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z69,z5,z6])],[(0,[z0,z1,z73,z3,z4,z5,z6]),(0,[z0,z1,z3,z74,z4,z6,z25]),(0,[z0,z1,z75,z3,z4,z5,z6]),(0,[z0,z76,z1,z3,z4,z5,z6])]],
   [[(0,[z77,z0,z1,z3,z4,z5,z43]),(0,[z78,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z79,z5,z6]),(1,[z0,z1,z48,z3,z5,z80]),(1,[z0,z1,z3,z4,z81,z6])],[(0,[z0,z1,z3,z4,z82,z5,z6])],[(0,[z0,z1,z3,z4,z5,z83,z6]),(0,[z54,z84,z0,z1,z3,z5,z6]),(0,[z16,z85,z1,z3,z4,z5,z6]),(0,[z0,z1,z86,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z87]),(0,[z0,z1,z88,z3,z4,z5,z6])],[(0,[z89,z0,z1,z3,z4,z5,z6]),(0,[z90,z0,z1,z3,z4,z5,z91]),(0,[z0,z92,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z93,z5,z6])],[(0,[z0,z94,z1,z3,z4,z5,z6]),(0,[z0,z95,z1,z3,z4,z5,z6]),(0,[z96,z0,z97,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z98])],[(0,[z66,z1,z3,z99,z4,z5,z6]),(0,[z0,z1,z35,z4,z100,z5,z6]),(0,[z0,z1,z3,z4,z5,z101,z6]),(0,[z102,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z74,z4,z103,z6]),(0,[z0,z1,z48,z3,z4,z5,z80])],[(0,[z104,z0,z1,z3,z4,z5,z6]),(0,[z55,z1,z3,z4,z105,z5,z6]),(0,[z0,z1,z3,z4,z5,z106,z6]),(0,[z0,z1,z3,z4,z5,z34,z91]),(0,[z0,z1,z3,z4,z107,z5,z6]),(0,[z0,z1,z108,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z109]),(0,[z0,z1,z110,z3,z4,z5,z6]),(0,[z0,z1,z3,z18,z4,z5,z6]),(0,[z111,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z90,z0,z1,z3,z4,z5,z43]),(0,[z33,z112,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z113])],[(0,[z0,z1,z114,z3,z4,z5,z6]),(0,[z0,z1,z115,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z116,z6,z117])],[(0,[z118,z0,z1,z3,z4,z5,z6]),(0,[z0,z119,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z120,z5,z103,z6]),(0,[z0,z1,z48,z3,z5,z6,z80]),(0,[z0,z1,z3,z4,z5,z6,z25])],[(0,[z0,z1,z121,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z122,z123,z6]),(0,[z0,z1,z124,z3,z4,z5,z6]),(0,[z0,z125,z1,z3,z4,z5,z6])],[(0,[z0,z1,z126,z35,z4,z5,z6]),(1,[z0,z1,z127,z4,z5,z6]),(1,[z0,z128,z3,z4,z5,z6]),(0,[z54,z0,z129,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z117])],[(0,[z0,z3,z18,z4,z130,z5,z6]),(0,[z131,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z132,z6]),(0,[z0,z1,z3,z4,z5,z6,z133]),(0,[z0,z1,z3,z4,z5,z12,z6])],[(0,[z0,z134,z1,z3,z4,z5,z6]),(0,[z0,z15,z3,z135,z4,z5,z6]),(0,[z136,z0,z137,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z138,z6]),(0,[z54,z0,z1,z3,z5,z6,z80]),(0,[z0,z1,z3,z4,z5,z6,z139])],[(0,[z140,z0,z1,z3,z74,z4,z6]),(0,[z0,z1,z3,z4,z5,z141,z6]),(0,[z0,z1,z142,z3,z4,z30,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z143,z6]),(0,[z0,z1,z3,z4,z5,z6,z144]),(0,[z0,z1,z3,z4,z5,z103,z6])],[(0,[z140,z1,z3,z4,z5,z145,z6]),(0,[z146,z0,z1,z3,z4,z147,z6]),(0,[z0,z1,z148,z3,z4,z5,z6]),(0,[z54,z0,z1,z3,z4,z36,z6]),(0,[z0,z1,z3,z4,z5,z149,z6])],[(0,[z55,z0,z1,z3,z105,z5,z6])],[(0,[z0,z150,z1,z99,z4,z5,z6]),(0,[z0,z1,z3,z135,z4,z5,z6]),(0,[z151,z0,z1,z3,z4,z5,z6]),(0,[z0,z137,z1,z3,z120,z5,z6]),(0,[z152,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z122,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z153]),(0,[z0,z1,z3,z18,z100,z5,z6]),(0,[z0,z1,z3,z154,z4,z5,z6])],[(0,[z0,z1,z3,z155,z4,z5,z6]),(0,[z0,z1,z156,z3,z4,z5,z6]),(0,[z0,z1,z48,z3,z157,z5,z6]),(0,[z0,z1,z3,z4,z5,z158,z6])],[(0,[z0,z1,z159,z3,z4,z5,z6]),(0,[z0,z160,z1,z3,z4,z5,z6]),(0,[z161,z0,z1,z3,z4,z5,z6]),(0,[z162,z0,z1,z3,z4,z5,z6])],[(0,[z140,z0,z1,z163,z4,z5,z6]),(1,[z0,z1,z164,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z165,z6]),(0,[z0,z1,z3,z166,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z116,z167]),(0,[z0,z1,z168,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z169,z5,z6])]],
   [[(1,[z0,z1,z3,z4,z170,z6]),(0,[z0,z1,z171,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z20,z36,z6]),(0,[z0,z1,z3,z4,z5,z91,z43])],[(0,[z0,z1,z3,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z172])],[(0,[z1,z35,z3,z99,z4,z5,z6]),(0,[z33,z0,z1,z99,z4,z5,z6]),(0,[z0,z1,z3,z4,z173,z5,z6]),(0,[z0,z1,z174,z3,z4,z5,z6]),(0,[z175,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z176,z4,z5,z6]),(0,[z0,z177,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z178]),(0,[z0,z179,z1,z3,z4,z5,z6])],[(0,[z90,z0,z1,z3,z157,z4,z5]),(0,[z180,z0,z1,z3,z4,z5,z6]),(0,[z181,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z126,z3,z4,z122,z6])],[(1,[z0,z1,z182,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z183,z6]),(0,[z0,z1,z3,z4,z184,z130,z6]),(0,[z0,z1,z185,z3,z4,z5,z6])],[(0,[z0,z1,z3,z186,z4,z5,z6]),(0,[z187,z33,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z188,z6]),(1,[z0,z1,z3,z157,z5,z116])]],
   [[(0,[z189,z0,z1,z3,z4,z5,z6]),(0,[z190,z1,z3,z4,z5,z191,z6]),(0,[z0,z1,z3,z4,z147,z6,z25]),(1,[z192,z0,z1,z3,z5,z6]),(0,[z33,z0,z1,z3,z4,z5,z43]),(0,[z187,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z193,z5,z6]),(0,[z0,z1,z3,z4,z5,z194,z6]),(0,[z0,z1,z3,z74,z4,z120,z6])],[(0,[z0,z1,z3,z195,z4,z5,z6]),(0,[z196,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z197,z3,z4,z5,z6]),(0,[z198,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z11,z5,z6])],[(0,[z0,z1,z199,z3,z4,z5,z6]),(0,[z0,z1,z200,z3,z4,z5,z6]),(0,[z0,z1,z201,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z12,z6,z202])],[(0,[z203,z66,z1,z3,z4,z5,z6]),(0,[z204,z0,z1,z3,z4,z5,z6]),(0,[z205,z0,z1,z3,z4,z5,z6]),(0,[z16,z0,z1,z99,z4,z5,z6]),(0,[z90,z0,z128,z3,z4,z5,z6]),(0,[z0,z1,z142,z3,z17,z5,z6]),(1,[z0,z1,z126,z4,z122,z6]),(0,[z0,z1,z4,z5,z34,z6,z43])],[(0,[z0,z1,z142,z99,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z206,z6]),(0,[z136,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z207,z5,z6]),(0,[z208,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z209,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z210,z5,z6])],[(0,[z0,z1,z3,z211,z4,z5,z6]),(1,[z84,z1,z3,z212,z5,z6]),(0,[z0,z1,z213,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z214,z6]),(0,[z0,z1,z3,z4,z5,z215,z6])],[(0,[z0,z1,z3,z4,z5,z216,z6]),(0,[z190,z1,z35,z3,z4,z5,z6]),(0,[z90,z190,z1,z3,z4,z5,z6]),(0,[z90,z0,z1,z24,z3,z4,z5]),(0,[z0,z137,z1,z3,z130,z5,z6]),(0,[z0,z97,z3,z4,z5,z6,z167]),(0,[z0,z1,z217,z3,z4,z5,z6]),(0,[z0,z1,z42,z3,z4,z5,z6]),(0,[z0,z218,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z219,z5,z6]),(0,[z0,z1,z3,z4,z5,z220,z6]),(0,[z0,z221,z1,z3,z4,z5,z6]),(0,[z222,z0,z1,z3,z4,z5,z6])]],
   [[(1,[z146,z1,z3,z4,z147,z6]),(0,[z136,z0,z3,z4,z130,z5,z6]),(0,[z0,z1,z3,z74,z4,z69,z6])],[(0,[z0,z1,z35,z3,z4,z5,z70]),(0,[z0,z1,z3,z4,z5,z6,z223]),(0,[z0,z1,z4,z5,z91,z224,z6]),(0,[z0,z1,z3,z4,z5,z225,z6])],[(0,[z0,z1,z226,z3,z4,z5,z6])],[(0,[z0,z1,z3,z227,z4,z5,z6]),(0,[z228,z0,z1,z3,z4,z5,z6])],[(0,[z229,z0,z1,z99,z4,z5,z6]),(0,[z0,z1,z230,z3,z4,z5,z6]),(0,[z0,z1,z168,z3,z4,z36,z6]),(0,[z0,z1,z3,z74,z4,z122,z6]),(0,[z0,z231,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z232])],[(0,[z0,z15,z3,z4,z5,z6,z167]),(0,[z0,z1,z3,z4,z5,z6,z233])],[(0,[z0,z1,z3,z234,z4,z5,z6]),(0,[z0,z1,z3,z4,z235,z5,z6]),(0,[z0,z1,z3,z4,z122,z20,z6]),(1,[z0,z1,z236,z4,z5,z6]),(0,[z19,z0,z1,z3,z74,z4,z6])],[(0,[z203,z0,z237,z3,z4,z5,z6]),(0,[z55,z84,z1,z3,z4,z5,z6]),(0,[z136,z0,z1,z3,z18,z5,z6]),(0,[z0,z1,z3,z4,z238,z5,z6]),(0,[z0,z1,z3,z4,z5,z239,z6])]],
   [[(0,[z240,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z241,z5,z6])],[(0,[z0,z150,z1,z35,z4,z5,z6]),(0,[z0,z242,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z157,z212,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z243]),(0,[z0,z1,z209,z3,z100,z5,z6]),(0,[z0,z244,z1,z3,z4,z5,z6])],[(0,[z245,z0,z1,z3,z4,z5,z6]),(0,[z0,z246,z1,z3,z4,z5,z6]),(0,[z55,z0,z1,z3,z212,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z167]),(0,[z0,z1,z17,z4,z100,z5,z6]),(0,[z0,z1,z3,z4,z5,z247,z6]),(0,[z248,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z249])],[(0,[z0,z1,z3,z250,z4,z5,z6]),(0,[z0,z1,z3,z251,z4,z5,z6]),(0,[z0,z1,z3,z252,z4,z5,z6]),(0,[z253,z0,z1,z3,z4,z5,z6])],[(0,[z140,z0,z1,z254,z4,z5,z6]),(0,[z16,z33,z0,z1,z4,z5,z6]),(0,[z255,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z256,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z116,z6,z80])],[(0,[z140,z0,z1,z3,z4,z145,z6]),(0,[z0,z1,z164,z3,z4,z5,z145]),(0,[z0,z1,z257,z3,z4,z5,z6]),(0,[z0,z1,z258,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z259,z5,z6]),(0,[z0,z1,z3,z4,z5,z116,z6])],[(0,[z66,z0,z1,z3,z4,z5,z6]),(0,[z260,z0,z1,z3,z4,z5,z6]),(0,[z261,z0,z1,z3,z4,z5,z6])],[(0,[z262,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z263,z5,z6]),(0,[z0,z1,z3,z264,z4,z5,z6]),(0,[z0,z1,z265,z3,z4,z5,z6])]],
   [[(0,[z33,z0,z1,z35,z4,z5,z6]),(0,[z0,z1,z3,z266,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z267,z6]),(0,[z0,z3,z4,z5,z34,z188,z6])],[(1,[z229,z1,z99,z4,z5,z6]),(0,[z268,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z269,z6]),(0,[z0,z1,z3,z4,z5,z91,z25]),(0,[z0,z1,z270,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z70,z6]),(0,[z0,z1,z3,z4,z5,z191,z6]),(0,[z0,z97,z1,z3,z4,z5,z167])],[(0,[z55,z0,z1,z127,z4,z5,z6]),(0,[z0,z1,z3,z4,z271,z5,z6]),(0,[z0,z129,z1,z3,z4,z5,z6]),(0,[z19,z0,z129,z3,z4,z5,z6]),(0,[z0,z1,z3,z272,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z167,z43])],[(0,[z273,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z163,z4,z5,z6]),(0,[z146,z0,z1,z3,z74,z4,z6]),(0,[z0,z1,z3,z4,z274,z5,z6]),(0,[z0,z275,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z276])],[(0,[z0,z1,z3,z4,z277,z5,z6]),(0,[z77,z0,z1,z3,z4,z69,z5]),(0,[z0,z1,z3,z4,z5,z278,z6]),(0,[z279,z0,z1,z3,z4,z5,z6])],[(0,[z90,z1,z3,z99,z4,z5,z6]),(0,[z0,z1,z3,z4,z280,z5,z6]),(0,[z0,z1,z3,z4,z281,z5,z6]),(0,[z0,z1,z3,z4,z5,z282,z6]),(0,[z77,z0,z1,z3,z4,z5,z91]),(0,[z283,z0,z1,z3,z4,z5,z6])],[(0,[z66,z0,z237,z3,z4,z5,z6]),(0,[z0,z1,z254,z3,z4,z5,z6]),(0,[z16,z0,z3,z135,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z284])]],
   [[(1,[z136,z0,z3,z130,z5,z6]),(0,[z0,z1,z3,z4,z285,z5,z6])],[(0,[z136,z0,z1,z3,z130,z5,z6]),(0,[z0,z1,z3,z5,z286,z20,z6]),(0,[z0,z1,z287,z3,z4,z5,z6])],[(0,[z288,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z142,z35,z4,z5,z6]),(0,[z1,z3,z4,z5,z191,z6,z289]),(0,[z0,z1,z3,z4,z290,z5,z6]),(0,[z54,z19,z0,z1,z3,z4,z6]),(0,[z0,z1,z24,z3,z4,z69,z6])],[(0,[z0,z1,z3,z4,z145,z6,z25]),(0,[z0,z1,z3,z291,z4,z5,z6]),(0,[z0,z150,z1,z209,z4,z5,z6])],[(0,[z292,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z293]),(0,[z0,z1,z3,z294,z4,z5,z6]),(1,[z0,z1,z142,z17,z5,z6]),(0,[z0,z295,z1,z3,z4,z5,z6]),(0,[z296,z0,z1,z3,z4,z5,z6])],[(0,[z1,z237,z3,z99,z4,z5,z6]),(0,[z1,z3,z4,z147,z5,z145,z6]),(0,[z90,z0,z1,z297,z4,z5,z6]),(0,[z90,z0,z1,z3,z4,z69,z5]),(0,[z0,z1,z3,z4,z298,z5,z6])],[(0,[z299,z0,z1,z3,z4,z5,z6]),(0,[z300,z0,z1,z3,z4,z5,z6]),(0,[z146,z140,z1,z3,z4,z5,z6]),(0,[z0,z1,z297,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z301])],[(1,[z0,z1,z3,z302,z5,z6]),(0,[z303,z0,z1,z3,z4,z5,z6]),(0,[z304,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z66,z0,z1,z227,z4,z5,z6]),(0,[z0,z1,z3,z305,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z306]),(0,[z0,z1,z3,z307,z4,z5,z6]),(0,[z0,z1,z3,z308,z4,z5,z6])],[(0,[z0,z1,z3,z309,z4,z5,z6]),(1,[z0,z310,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z311,z6]),(0,[z0,z1,z3,z4,z123,z36,z6])],[(0,[z229,z0,z1,z35,z4,z5,z6]),(0,[z0,z1,z3,z312,z4,z5,z6]),(0,[z0,z1,z3,z4,z313,z5,z6]),(0,[z77,z1,z3,z4,z5,z191,z6]),(0,[z96,z0,z15,z3,z4,z5,z6]),(1,[z0,z1,z314,z4,z5,z6]),(0,[z315,z0,z1,z3,z4,z5,z6]),(0,[z316,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z317,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z318,z6]),(0,[z54,z0,z1,z3,z17,z5,z6])],[(1,[z0,z1,z3,z4,z5,z293]),(0,[z0,z137,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z184,z6]),(0,[z54,z0,z1,z3,z100,z5,z6])],[(0,[z0,z1,z3,z4,z5,z319,z6]),(0,[z0,z1,z3,z4,z5,z6,z320])],[(0,[z321,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z322,z5,z6])],[(0,[z96,z0,z67,z3,z4,z5,z6]),(0,[z84,z0,z1,z3,z4,z5,z6]),(0,[z16,z96,z0,z3,z4,z5,z6]),(0,[z0,z1,z323,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z324,z6])]],
   [[(0,[z325,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z326,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z6]),(0,[z85,z0,z1,z3,z4,z5,z6]),(0,[z327,z0,z1,z3,z4,z5,z6]),(0,[z0,z150,z1,z4,z5,z6,z43]),(0,[z0,z1,z3,z4,z328,z5,z6]),(0,[z96,z0,z1,z3,z4,z5,z91]),(0,[z0,z1,z3,z4,z5,z224,z6]),(0,[z0,z1,z329,z3,z4,z5,z6]),(0,[z0,z1,z42,z3,z4,z5,z34]),(0,[z0,z1,z3,z4,z5,z330,z6])],[(0,[z0,z331,z1,z3,z4,z5,z6]),(0,[z90,z0,z1,z3,z4,z5,z167]),(0,[z0,z1,z3,z4,z5,z332,z6]),(0,[z0,z150,z15,z3,z4,z5,z6])],[(0,[z0,z1,z333,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z334,z5,z6]),(0,[z0,z1,z3,z4,z5,z335,z6])],[(0,[z190,z1,z237,z3,z4,z5,z6]),(0,[z0,z1,z336,z3,z4,z5,z6]),(0,[z0,z1,z35,z4,z5,z6,z43]),(0,[z16,z0,z1,z209,z4,z5,z6]),(0,[z0,z1,z337,z3,z4,z5,z6]),(0,[z54,z0,z1,z3,z4,z103,z6])],[(0,[z0,z1,z3,z157,z105,z5,z6]),(0,[z0,z1,z338,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z339,z6]),(0,[z0,z1,z3,z4,z5,z34,z167]),(0,[z0,z1,z340,z3,z4,z5,z6])],[(0,[z0,z67,z1,z3,z4,z5,z293]),(1,[z0,z1,z341,z4,z5,z6]),(0,[z0,z1,z3,z342,z4,z5,z6]),(0,[z0,z1,z3,z4,z120,z5,z6])],[(0,[z0,z1,z343,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z188,z6])],[(0,[z0,z1,z3,z344,z4,z5,z6]),(0,[z0,z1,z3,z4,z345,z5,z6]),(0,[z1,z3,z99,z4,z5,z191,z6]),(0,[z77,z0,z1,z3,z157,z4,z5]),(0,[z0,z137,z1,z3,z18,z5,z6]),(0,[z0,z1,z3,z120,z5,z6,z80]),(0,[z0,z1,z346,z3,z4,z5,z6])]],
   [[(0,[z0,z97,z1,z3,z4,z5,z6]),(0,[z0,z1,z347,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z348]),(0,[z0,z1,z3,z4,z5,z6,z349]),(0,[z0,z1,z3,z4,z5,z6,z350])],[(0,[z84,z0,z1,z3,z120,z5,z6]),(1,[z0,z1,z254,z4,z5,z6]),(0,[z0,z1,z3,z351,z4,z5,z6])],[(0,[z0,z1,z3,z4,z352,z5,z6]),(0,[z0,z1,z3,z4,z5,z353,z6]),(0,[z354,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z355,z6])],[(0,[z96,z0,z1,z3,z4,z5,z167])],[(0,[z0,z356,z1,z3,z4,z5,z6]),(0,[z357,z0,z1,z3,z4,z5,z6]),(0,[z0,z129,z1,z3,z4,z5,z358]),(1,[z0,z129,z3,z4,z20,z6]),(0,[z0,z1,z3,z4,z5,z167,z25]),(0,[z0,z1,z359,z3,z4,z5,z6]),(0,[z360,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z361,z6])],[(0,[z0,z1,z362,z3,z4,z5,z6]),(0,[z363,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z80])],[(0,[z0,z1,z364,z3,z4,z5,z6]),(0,[z90,z0,z1,z3,z302,z5,z6]),(1,[z90,z1,z3,z4,z5,z289]),(0,[z16,z0,z3,z4,z5,z6,z167]),(0,[z0,z1,z3,z365,z4,z5,z6])],[(0,[z0,z1,z366,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z367,z6]),(0,[z0,z1,z3,z4,z368,z5,z6]),(0,[z0,z1,z3,z4,z5,z369,z6]),(1,[z0,z1,z3,z334,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z370]),(0,[z16,z0,z1,z17,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z153])]],
   [[(0,[z16,z0,z1,z4,z5,z6,z43]),(0,[z0,z1,z3,z371,z4,z5,z6]),(0,[z0,z1,z372,z3,z4,z5,z6])],[(0,[z0,z67,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z373,z6]),(0,[z0,z1,z3,z4,z5,z6,z374]),(0,[z77,z0,z1,z24,z3,z4,z5])],[(0,[z375,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z376]),(0,[z0,z1,z3,z250,z4,z105,z5]),(0,[z0,z1,z3,z5,z377,z145,z6]),(0,[z0,z1,z3,z4,z5,z6,z378]),(0,[z192,z0,z1,z3,z5,z20,z6]),(0,[z379,z0,z1,z3,z4,z5,z6])],[(0,[z380,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z381,z4,z5,z6]),(0,[z0,z382,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z383])],[(0,[z0,z1,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z384,z6])],[(0,[z385,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z386,z4,z5,z6]),(0,[z0,z1,z3,z4,z387,z5,z6]),(1,[z161,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z388,z6])],[(0,[z0,z1,z3,z4,z5,z6,z389]),(0,[z0,z1,z3,z4,z5,z6,z390]),(0,[z391,z0,z1,z3,z4,z5,z6]),(0,[z33,z0,z1,z4,z5,z34,z6])],[(0,[z67,z1,z237,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z5,z370]),(0,[z0,z1,z171,z4,z130,z5,z6]),(0,[z161,z0,z3,z4,z5,z34,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z392]),(0,[z0,z1,z3,z4,z130,z5,z6]),(0,[z393,z0,z1,z3,z4,z5,z6]),(0,[z394,z0,z1,z3,z4,z5,z6])],[(1,[z203,z237,z3,z4,z5,z6]),(0,[z0,z1,z3,z99,z4,z5,z6]),(0,[z16,z0,z150,z3,z4,z5,z6]),(0,[z0,z395,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z396,z4,z5,z6]),(1,[z33,z0,z1,z4,z5,z34]),(0,[z397,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z81,z116,z6])],[(1,[z0,z1,z227,z4,z5,z6]),(0,[z398,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z399,z3,z4,z5,z6])],[(0,[z0,z1,z99,z4,z5,z36,z6]),(0,[z400,z0,z1,z3,z4,z5,z6]),(1,[z401,z1,z3,z4,z5,z6]),(1,[z0,z1,z209,z100,z5,z6]),(0,[z402,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z69,z147,z6])],[(0,[z0,z1,z237,z3,z4,z5,z6]),(0,[z0,z237,z3,z4,z5,z6,z167]),(0,[z0,z1,z3,z4,z403,z5,z6]),(0,[z0,z404,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z405,z5,z6]),(0,[z0,z1,z24,z3,z4,z5,z12])],[(1,[z66,z67,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z406]),(0,[z0,z1,z3,z4,z407,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z408]),(0,[z0,z1,z3,z409,z4,z5,z6]),(0,[z0,z1,z3,z410,z4,z5,z6])],[(0,[z411,z0,z1,z3,z4,z5,z6]),(0,[z90,z0,z1,z3,z4,z5,z6]),(0,[z16,z0,z1,z3,z195,z5,z6]),(1,[z19,z0,z3,z4,z123,z6])]],
   [[(0,[z0,z1,z126,z3,z4,z36,z6])],[(0,[z412,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z297,z4,z5,z6]),(0,[z0,z1,z3,z413,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z414,z6])],[(0,[z0,z67,z3,z4,z5,z6,z167]),(0,[z415,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z416,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z417,z6]),(0,[z0,z1,z3,z4,z5,z34,z6]),(0,[z0,z1,z3,z11,z4,z5,z6])],[(0,[z0,z1,z209,z3,z17,z5,z6]),(0,[z0,z1,z3,z157,z4,z5,z116])],[(0,[z0,z1,z3,z418,z4,z5,z6]),(0,[z0,z1,z419,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z420,z6]),(0,[z0,z1,z3,z4,z5,z421,z6]),(0,[z0,z1,z422,z3,z4,z5,z6]),(0,[z423,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z74,z120,z5,z6]),(0,[z0,z1,z3,z4,z5,z424,z6])],[(0,[z140,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z5,z6]),(0,[z90,z0,z1,z3,z334,z5,z6]),(0,[z0,z129,z1,z3,z4,z123,z6]),(0,[z0,z1,z236,z4,z5,z20,z6]),(1,[z0,z1,z3,z425,z5,z6])],[(0,[z0,z1,z3,z426,z4,z5,z6]),(0,[z1,z3,z212,z4,z105,z5,z6]),(0,[z54,z136,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z123,z5,z6]),(0,[z0,z1,z3,z427,z4,z5,z6])]],
   [[(0,[z428,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z145,z6])],[(0,[z0,z1,z3,z4,z5,z429,z6]),(0,[z0,z1,z3,z4,z430,z5,z6]),(1,[z0,z1,z3,z4,z5,z358]),(0,[z0,z1,z3,z4,z431,z5,z6]),(0,[z0,z1,z3,z4,z5,z432,z6]),(0,[z0,z1,z433,z3,z4,z5,z6]),(0,[z0,z434,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z195,z5,z6]),(0,[z0,z1,z3,z4,z5,z435,z6]),(0,[z0,z1,z3,z4,z5,z436,z6]),(0,[z54,z0,z1,z3,z4,z122,z6]),(0,[z0,z1,z3,z4,z5,z437,z6])],[(0,[z0,z1,z3,z4,z5,z6,z438]),(0,[z0,z1,z99,z4,z100,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z439]),(0,[z0,z1,z3,z4,z440,z5,z6]),(0,[z0,z1,z3,z4,z441,z5,z6])],[(0,[z0,z442,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z377,z6]),(0,[z0,z1,z3,z4,z5,z443,z6]),(0,[z0,z1,z42,z3,z4,z5,z43])],[(0,[z190,z66,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z444,z5,z6]),(0,[z0,z1,z3,z4,z445,z5,z6]),(0,[z0,z1,z3,z4,z5,z446,z6]),(0,[z0,z1,z3,z4,z5,z6,z447]),(0,[z448,z0,z1,z3,z4,z5,z6])],[(0,[z449,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z209,z142,z4,z5,z6]),(0,[z0,z1,z3,z4,z450,z5,z6]),(0,[z54,z0,z1,z3,z5,z103,z6])],[(0,[z451,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z326,z3,z4,z105,z5]),(0,[z0,z452,z1,z3,z4,z5,z6]),(0,[z0,z453,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z91,z6])]],
   [[(0,[z0,z1,z3,z454,z4,z5,z6]),(0,[z190,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z455,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z456,z6]),(0,[z457,z0,z1,z3,z4,z5,z6]),(0,[z458,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z168,z4,z36,z6]),(0,[z0,z1,z3,z74,z4,z36,z6]),(0,[z459,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z460,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z461]),(0,[z0,z1,z3,z4,z5,z6,z462]),(0,[z463,z0,z1,z3,z4,z5,z6]),(0,[z77,z0,z1,z3,z4,z5,z191]),(0,[z0,z1,z464,z3,z4,z5,z6])],[(0,[z465,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z466,z6])],[(0,[z0,z1,z35,z3,z4,z5,z6]),(1,[z55,z1,z3,z105,z5,z6]),(0,[z467,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z468,z6]),(0,[z0,z1,z3,z4,z5,z469,z6]),(0,[z0,z1,z470,z3,z4,z5,z6])],[(0,[z55,z0,z1,z341,z4,z5,z6]),(1,[z411,z0,z1,z3,z4,z6]),(0,[z0,z471,z1,z3,z4,z5,z6])],[(0,[z0,z310,z1,z3,z4,z130,z6]),(0,[z0,z1,z24,z3,z4,z5,z6])],[(0,[z0,z1,z472,z3,z4,z5,z6]),(0,[z0,z1,z3,z473,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z358,z6]),(0,[z474,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z289]),(0,[z0,z1,z3,z4,z5,z475,z6]),(0,[z0,z1,z3,z4,z476,z5,z6]),(0,[z0,z1,z3,z4,z5,z477,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z478,z6]),(0,[z0,z1,z3,z105,z5,z6,z80]),(0,[z0,z310,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z462]),(1,[z0,z1,z3,z250,z4,z5]),(0,[z0,z1,z479,z3,z4,z5,z6]),(1,[z0,z1,z3,z5,z377,z6]),(0,[z90,z0,z1,z3,z4,z5,z191]),(0,[z0,z1,z168,z4,z5,z36,z6]),(0,[z0,z1,z3,z4,z480,z5,z6]),(0,[z481,z0,z1,z3,z4,z5,z6])],[(0,[z482,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z127,z4,z5,z6]),(0,[z16,z0,z1,z135,z4,z5,z6]),(0,[z16,z0,z1,z4,z122,z5,z6]),(0,[z0,z1,z3,z483,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z484,z6])],[(0,[z190,z229,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z485,z5,z6]),(0,[z0,z1,z3,z4,z486,z5,z6]),(0,[z0,z1,z3,z4,z5,z36,z6]),(0,[z0,z1,z3,z4,z5,z487,z6])],[(0,[z84,z1,z3,z212,z4,z5,z6]),(0,[z77,z0,z1,z3,z4,z5,z167]),(0,[z0,z1,z3,z4,z5,z91,z80])],[(0,[z0,z1,z3,z4,z5,z488,z6]),(1,[z208,z0,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z489])],[(0,[z0,z1,z490,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z491,z6]),(1,[z0,z1,z171,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z492]),(0,[z0,z1,z4,z122,z5,z36,z6]),(0,[z0,z1,z3,z493,z4,z5,z6])],[(0,[z494,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z495,z0,z1,z3,z4,z5,z6]),(0,[z16,z0,z1,z3,z4,z5,z6]),(0,[z0,z496,z1,z3,z4,z5,z6]),(1,[z0,z137,z3,z18,z5,z6]),(0,[z0,z1,z3,z4,z497,z5,z6]),(0,[z54,z0,z1,z3,z4,z6,z25]),(0,[z0,z1,z3,z4,z5,z498,z6])],[(0,[z0,z499,z1,z3,z4,z5,z6]),(0,[z55,z0,z1,z3,z120,z5,z6]),(0,[z0,z1,z3,z4,z5,z500,z6])],[(0,[z501,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z502,z4,z5,z6]),(0,[z0,z503,z1,z3,z4,z5,z6]),(0,[z0,z150,z1,z17,z4,z5,z6]),(0,[z0,z1,z3,z100,z120,z5,z6]),(0,[z0,z1,z3,z504,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z505,z6])],[(0,[z0,z1,z3,z4,z5,z506,z6]),(0,[z0,z1,z3,z212,z4,z5,z6]),(0,[z0,z507,z1,z3,z4,z5,z6]),(1,[z0,z150,z15,z4,z5,z6]),(0,[z0,z1,z508,z3,z4,z5,z6])],[(0,[z0,z1,z3,z509,z4,z5,z6]),(0,[z0,z510,z1,z3,z4,z5,z6]),(0,[z19,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z69,z12,z6])],[(0,[z0,z1,z3,z4,z511,z5,z6]),(0,[z54,z0,z137,z1,z3,z5,z6]),(0,[z0,z1,z512,z3,z4,z5,z6]),(0,[z513,z0,z1,z3,z4,z5,z6]),(0,[z0,z514,z1,z3,z4,z5,z6])],[(0,[z515,z0,z1,z3,z4,z5,z6]),(1,[z54,z0,z1,z3,z103,z6])]],
   [[(0,[z0,z1,z126,z4,z122,z5,z6]),(0,[z0,z1,z3,z516,z4,z5,z6])],[(0,[z517,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z518]),(0,[z519,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z520,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z521]),(0,[z0,z129,z1,z3,z4,z20,z6])],[(0,[z0,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z522,z5,z6]),(0,[z33,z0,z150,z1,z4,z5,z6]),(0,[z0,z1,z523,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z0,z524,z1,z3,z4,z5,z6]),(0,[z525,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z100,z5,z6]),(0,[z0,z1,z3,z526,z4,z5,z6])],[(0,[z527,z0,z1,z3,z4,z5,z6]),(0,[z528,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z529,z5,z6]),(1,[z187,z1,z3,z4,z5,z6])],[(0,[z0,z1,z530,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z531,z5,z6]),(0,[z0,z1,z3,z4,z5,z532,z6]),(0,[z0,z1,z3,z4,z5,z6,z202])],[(0,[z0,z1,z3,z4,z170,z5,z6]),(0,[z0,z128,z1,z3,z4,z5,z6]),(0,[z0,z1,z126,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z533])],[(0,[z534,z0,z1,z3,z4,z5,z6]),(0,[z0,z535,z1,z3,z4,z5,z6]),(0,[z90,z1,z3,z4,z5,z6,z289]),(0,[z16,z0,z1,z3,z4,z5,z370]),(0,[z0,z1,z3,z4,z536,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z537,z6])],[(0,[z0,z1,z3,z4,z538,z5,z6]),(0,[z140,z0,z1,z3,z4,z147,z6]),(0,[z16,z0,z1,z3,z4,z475,z6]),(0,[z0,z1,z3,z4,z5,z12,z91]),(0,[z0,z1,z539,z3,z4,z5,z6])],[(0,[z0,z1,z3,z540,z4,z5,z6]),(0,[z0,z1,z3,z4,z541,z5,z6])],[(0,[z542,z0,z1,z3,z4,z5,z6]),(0,[z146,z0,z1,z3,z4,z5,z6]),(0,[z16,z401,z1,z3,z4,z5,z6]),(0,[z16,z0,z1,z168,z4,z5,z6]),(0,[z0,z1,z3,z4,z543,z5,z6]),(0,[z0,z1,z142,z17,z4,z5,z6])],[(1,[z0,z1,z3,z4,z544,z6]),(0,[z0,z1,z3,z4,z5,z545,z6])],[(0,[z0,z1,z3,z4,z546,z5,z6]),(0,[z146,z0,z1,z3,z4,z145,z6]),(0,[z90,z77,z1,z3,z4,z5,z6]),(0,[z547,z0,z1,z3,z4,z5,z6]),(0,[z0,z548,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z549,z4,z5,z6]),(0,[z0,z1,z3,z4,z550,z5,z6])],[(0,[z0,z1,z3,z212,z5,z6,z80]),(0,[z551,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z322,z5,z20,z6]),(0,[z0,z1,z209,z4,z100,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z43]),(0,[z0,z1,z3,z4,z552,z5,z6])],[(0,[z0,z1,z553,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z554,z6]),(0,[z0,z3,z4,z5,z91,z6,z167])]],
   [[(1,[z77,z1,z3,z4,z5,z191]),(0,[z555,z0,z1,z3,z4,z5,z6]),(0,[z19,z0,z3,z4,z123,z5,z6]),(0,[z0,z556,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z557,z6]),(1,[z0,z1,z3,z4,z5,z216]),(0,[z16,z0,z1,z3,z4,z5,z267]),(0,[z0,z1,z3,z4,z5,z558,z6]),(0,[z33,z0,z1,z42,z4,z5,z6])],[(0,[z559,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z560,z3,z4,z5,z6]),(0,[z77,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z81,z5,z6]),(1,[z0,z1,z3,z5,z6,z202])],[(0,[z229,z1,z3,z99,z4,z5,z6]),(0,[z0,z1,z341,z3,z4,z5,z6]),(0,[z0,z129,z3,z4,z5,z20,z6]),(1,[z96,z0,z3,z4,z5,z91]),(0,[z0,z561,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z562,z5,z6]),(0,[z0,z1,z563,z3,z4,z5,z6]),(0,[z0,z1,z3,z564,z4,z5,z6]),(0,[z0,z1,z565,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z475,z6]),(0,[z0,z1,z3,z4,z566,z5,z6])],[(0,[z0,z1,z567,z3,z4,z5,z6]),(0,[z568,z0,z1,z3,z5,z145,z6]),(0,[z569,z0,z1,z3,z4,z5,z6]),(0,[z0,z401,z1,z3,z4,z5,z6])],[(0,[z0,z1,z570,z3,z4,z5,z6]),(0,[z0,z1,z3,z74,z4,z5,z6]),(0,[z571,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z572,z5,z6]),(0,[z0,z1,z3,z4,z5,z167,z80]),(0,[z0,z1,z3,z17,z120,z5,z6])]],
   [[(0,[z573,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z574,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z286,z6]),(1,[z0,z1,z3,z4,z536,z6]),(0,[z0,z1,z3,z575,z4,z5,z6])],[(0,[z576,z0,z1,z3,z4,z5,z6]),(0,[z577,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z302,z4,z5,z6]),(0,[z0,z1,z126,z168,z4,z5,z6]),(0,[z54,z0,z1,z3,z4,z120,z6]),(0,[z0,z578,z1,z3,z4,z5,z6])],[(0,[z0,z67,z1,z3,z4,z5,z216]),(0,[z0,z1,z579,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z580,z6]),(0,[z0,z1,z3,z4,z581,z5,z6])],[(0,[z582,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z583,z3,z4,z5,z6]),(0,[z0,z1,z3,z157,z5,z116,z6])],[(0,[z0,z1,z35,z3,z4,z5,z462]),(0,[z0,z1,z3,z4,z170,z105,z6]),(1,[z0,z1,z3,z4,z522,z5]),(1,[z0,z1,z3,z4,z5,z267]),(0,[z0,z1,z3,z4,z584,z5,z6]),(0,[z585,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z12,z6,z25])],[(0,[z203,z1,z237,z3,z4,z5,z6]),(0,[z0,z1,z586,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z587,z6])],[(0,[z84,z0,z1,z3,z212,z5,z6]),(0,[z54,z140,z0,z1,z3,z4,z6]),(0,[z588,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z589,z3,z4,z5,z6])]],
   [[(0,[z66,z0,z1,z182,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z590]),(0,[z0,z1,z3,z4,z5,z6,z591]),(0,[z0,z1,z3,z4,z592,z5,z6]),(0,[z593,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z594,z6]),(0,[z0,z1,z3,z4,z69,z5,z25])],[(0,[z203,z0,z67,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z595]),(0,[z54,z146,z0,z1,z3,z4,z6]),(0,[z0,z1,z596,z3,z4,z5,z6]),(0,[z54,z0,z1,z3,z4,z69,z6])],[(0,[z0,z1,z3,z163,z4,z5,z6]),(1,[z140,z1,z3,z4,z145,z6]),(0,[z0,z1,z3,z4,z5,z6,z597]),(0,[z0,z1,z3,z598,z4,z5,z6])],[(0,[z0,z1,z164,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z599,z5,z6]),(0,[z0,z1,z236,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z600,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z601]),(0,[z96,z0,z1,z3,z4,z5,z6]),(0,[z0,z602,z1,z3,z4,z5,z6]),(0,[z0,z1,z126,z3,z425,z5,z6]),(0,[z0,z1,z603,z3,z4,z5,z6])],[(0,[z604,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z69,z145,z6]),(0,[z16,z0,z1,z3,z599,z5,z6]),(0,[z0,z1,z3,z4,z544,z5,z6]),(0,[z0,z150,z1,z135,z4,z5,z6]),(0,[z0,z150,z1,z4,z122,z5,z6]),(0,[z0,z1,z314,z4,z130,z5,z6]),(1,[z0,z1,z3,z5,z286,z6]),(0,[z605,z0,z1,z3,z4,z5,z6]),(0,[z0,z606,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z60,z6]),(0,[z0,z1,z607,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z284,z6]),(0,[z0,z1,z3,z608,z4,z5,z6])],[(0,[z0,z1,z3,z4,z609,z5,z6])]],
   [[(1,[z190,z1,z35,z4,z5,z6]),(0,[z0,z1,z610,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z611,z5,z6]),(0,[z0,z1,z612,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z613,z6]),(0,[z0,z1,z3,z17,z130,z5,z6]),(0,[z0,z1,z614,z3,z4,z5,z6])],[(0,[z568,z0,z1,z3,z4,z5,z6]),(0,[z0,z150,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z615,z6])],[(0,[z0,z1,z616,z3,z4,z5,z6]),(0,[z0,z1,z617,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z618,z5,z6]),(0,[z0,z1,z619,z3,z4,z5,z6])],[(0,[z96,z0,z237,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z620,z5,z6]),(1,[z0,z97,z3,z4,z5,z167])],[(0,[z0,z1,z3,z4,z5,z6,z621])],[(0,[z0,z1,z3,z622,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z623,z6]),(1,[z568,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z624,z5,z6]),(0,[z0,z1,z3,z4,z5,z625,z6])]],
   [[(0,[z0,z1,z626,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z627,z5,z6]),(0,[z411,z0,z1,z3,z4,z105,z6]),(0,[z0,z1,z3,z628,z4,z5,z6]),(1,[z0,z1,z3,z599,z5,z6]),(0,[z136,z0,z1,z3,z4,z5,z284]),(0,[z0,z1,z3,z314,z4,z5,z6])],[(0,[z629,z0,z1,z3,z4,z5,z6]),(0,[z66,z0,z67,z3,z4,z5,z6]),(0,[z0,z1,z99,z4,z5,z6,z43]),(0,[z0,z1,z3,z4,z630,z5,z6]),(0,[z0,z1,z3,z4,z5,z116,z91]),(0,[z631,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z632,z4,z5,z6]),(0,[z0,z1,z3,z157,z4,z5,z6])],[(0,[z633,z0,z1,z3,z4,z5,z6]),(0,[z55,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z326,z3,z4,z5]),(1,[z85,z1,z3,z4,z5,z6]),(0,[z634,z0,z1,z3,z4,z5,z6]),(0,[z33,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z635,z5,z6])],[(0,[z636,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z312,z4,z5,z6]),(0,[z0,z1,z3,z4,z637,z5,z6]),(0,[z0,z1,z3,z638,z4,z5,z6])],[(0,[z0,z1,z3,z4,z639,z5,z6]),(0,[z0,z1,z3,z4,z5,z640,z6]),(0,[z0,z1,z3,z4,z5,z641,z6]),(0,[z208,z0,z1,z4,z5,z91,z6])],[(0,[z0,z1,z3,z642,z4,z5,z6]),(0,[z0,z1,z3,z4,z643,z5,z6]),(0,[z0,z644,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z645,z5,z6]),(0,[z646,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z147,z5,z6]),(0,[z0,z1,z3,z4,z647,z5,z6])]],
   [[(0,[z190,z0,z1,z99,z4,z5,z6]),(1,[z0,z1,z4,z322,z5,z6]),(0,[z19,z0,z1,z3,z4,z123,z6]),(1,[z0,z1,z42,z4,z5,z43])],[(0,[z0,z1,z3,z4,z522,z5,z145]),(1,[z0,z1,z3,z618,z5,z6])],[(0,[z0,z1,z3,z4,z648,z5,z6]),(1,[z0,z1,z4,z5,z224,z6])],[(1,[z0,z649,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z650,z6]),(0,[z651,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z157,z120,z5,z6])],[(0,[z0,z1,z652,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z14,z6]),(0,[z77,z0,z1,z3,z4,z5,z34]),(0,[z0,z129,z1,z3,z74,z4,z6]),(0,[z0,z1,z3,z4,z5,z20,z6]),(0,[z0,z1,z142,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z653,z6]),(0,[z0,z1,z126,z3,z618,z5,z6])],[(0,[z0,z1,z3,z4,z5,z654,z6]),(0,[z90,z0,z1,z3,z4,z60,z6]),(0,[z77,z0,z1,z48,z3,z4,z5]),(0,[z655,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z425,z4,z5,z6])],[(0,[z0,z656,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z105,z5,z6]),(0,[z0,z150,z1,z168,z4,z5,z6]),(0,[z0,z1,z657,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z30,z6]),(0,[z54,z0,z1,z3,z157,z5,z6]),(0,[z0,z1,z3,z157,z4,z5,z80]),(0,[z0,z1,z24,z3,z4,z6,z25])],[(0,[z0,z1,z3,z4,z5,z658,z6]),(0,[z96,z0,z3,z4,z5,z91,z6]),(0,[z0,z1,z3,z4,z5,z659,z6])]],
   [[(0,[z660,z0,z1,z3,z4,z5,z6]),(0,[z146,z1,z3,z4,z147,z5,z6]),(0,[z0,z1,z3,z4,z5,z661,z6]),(0,[z0,z1,z168,z3,z4,z122,z6]),(0,[z0,z1,z662,z3,z4,z5,z6]),(0,[z0,z112,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z663,z4,z5,z6]),(0,[z192,z0,z1,z3,z4,z5,z6]),(1,[z112,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z664,z4,z5,z6]),(0,[z84,z0,z1,z3,z105,z5,z6]),(0,[z0,z1,z3,z4,z5,z665,z6]),(0,[z0,z1,z3,z4,z5,z6,z666]),(0,[z0,z1,z3,z4,z5,z667,z6])],[(0,[z0,z668,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z669,z5,z6]),(0,[z0,z1,z670,z3,z4,z5,z6]),(0,[z54,z0,z1,z3,z74,z5,z6]),(0,[z671,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z672,z4,z5,z6])],[(0,[z229,z0,z1,z3,z4,z5,z6]),(0,[z673,z0,z1,z3,z4,z5,z6]),(0,[z90,z0,z1,z3,z4,z5,z34]),(0,[z16,z0,z1,z3,z4,z544,z6])],[(0,[z90,z0,z1,z48,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z674,z6])],[(0,[z0,z1,z3,z4,z184,z5,z6]),(0,[z0,z3,z4,z123,z5,z20,z6]),(0,[z675,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z649,z3,z4,z5,z6]),(0,[z0,z129,z1,z3,z4,z5,z29])]],
   [[(0,[z0,z1,z3,z676,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z677,z6]),(0,[z77,z0,z1,z3,z4,z5,z289]),(0,[z0,z1,z142,z3,z100,z5,z6])],[(0,[z0,z1,z678,z3,z4,z5,z6]),(0,[z679,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z680,z3,z4,z5,z6])],[(0,[z203,z0,z1,z3,z4,z5,z6]),(0,[z90,z0,z1,z312,z4,z5,z6]),(0,[z0,z150,z1,z15,z4,z5,z6]),(0,[z0,z681,z1,z3,z4,z5,z6]),(0,[z682,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z683]),(0,[z0,z1,z3,z4,z5,z6,z684])],[(0,[z0,z1,z3,z4,z685,z5,z6]),(0,[z0,z1,z48,z3,z4,z5,z116]),(0,[z0,z1,z3,z686,z4,z5,z6])],[(0,[z687,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z688,z5,z6]),(0,[z0,z1,z689,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z69,z5,z12])],[(0,[z0,z1,z690,z3,z4,z5,z6]),(0,[z0,z1,z691,z3,z4,z5,z6]),(0,[z692,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z693,z3,z4,z5,z6])]],
   [[(0,[z136,z0,z1,z3,z4,z5,z153]),(0,[z0,z1,z3,z17,z4,z5,z6])],[(0,[z90,z0,z1,z3,z4,z5,z289]),(0,[z0,z1,z694,z3,z4,z5,z6]),(1,[z16,z0,z135,z4,z5,z6]),(0,[z0,z1,z142,z3,z4,z536,z6]),(0,[z695,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z696,z6])],[(0,[z90,z0,z649,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z697,z5,z6]),(0,[z698,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z699,z3,z4,z5,z6]),(0,[z90,z0,z1,z3,z4,z14,z6]),(0,[z136,z0,z1,z3,z120,z5,z6]),(0,[z0,z1,z700,z3,z4,z5,z6]),(0,[z701,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z702,z4,z5,z6])],[(0,[z0,z1,z3,z4,z703,z5,z6]),(0,[z0,z97,z1,z3,z4,z5,z91]),(1,[z0,z1,z3,z74,z120,z6])],[],[(0,[z0,z1,z126,z99,z4,z5,z6]),(0,[z190,z0,z1,z35,z4,z5,z6]),(0,[z0,z1,z3,z130,z100,z5,z6]),(0,[z704,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z705,z5,z6]),(1,[z0,z1,z3,z4,z6,z117])],[(0,[z0,z1,z182,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z706,z6]),(0,[z0,z137,z3,z18,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z12,z167])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z127,z4,z5,z6]),(0,[z411,z0,z1,z326,z3,z4]),(0,[z0,z1,z48,z3,z334,z5]),(0,[z0,z707,z3,z4,z5,z6])],[(0,[z85,z1,z3,z4,z5,z6]),(0,[z0,z1,z708,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z709]),(0,[z0,z1,z3,z4,z710,z6])],[(0,[z0,z1,z312,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z711])],[(0,[z0,z1,z3,z712,z5,z6]),(0,[z1,z3,z99,z4,z5,z70]),(0,[z90,z1,z99,z4,z5,z43]),(0,[z0,z1,z326,z3,z334,z5]),(0,[z0,z1,z4,z5,z267,z43])],[(0,[z16,z0,z4,z5,z167,z43]),(0,[z0,z1,z3,z4,z5,z713]),(0,[z0,z714,z3,z4,z5,z6]),(0,[z54,z0,z1,z3,z6,z98])],[(0,[z90,z128,z3,z4,z5,z289]),(1,[z0,z1,z3,z715,z6]),(0,[z0,z1,z3,z5,z47,z80])],[(0,[z0,z1,z3,z716,z5,z6]),(0,[z0,z1,z3,z4,z717,z6]),(0,[z0,z1,z718,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z719])]],
   [[(0,[z0,z1,z3,z599,z544,z6]),(0,[z0,z1,z3,z5,z720,z6]),(0,[z0,z1,z3,z618,z5,z6])],[(0,[z96,z401,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z721])],[(0,[z0,z649,z3,z4,z5,z6]),(0,[z0,z1,z127,z120,z5,z6]),(0,[z0,z1,z722,z4,z5,z6]),(0,[z0,z1,z312,z334,z5,z6]),(0,[z85,z1,z3,z4,z544,z6]),(0,[z16,z0,z135,z599,z5,z6]),(0,[z0,z1,z3,z4,z5,z723]),(0,[z16,z112,z1,z4,z5,z6]),(0,[z724,z0,z1,z3,z4,z5]),(0,[z725,z1,z3,z4,z5,z6])],[(0,[z0,z1,z297,z4,z5,z70]),(0,[z0,z1,z3,z4,z5,z726]),(0,[z0,z1,z164,z3,z4,z5]),(0,[z0,z1,z3,z4,z14,z6])],[(0,[z0,z1,z35,z4,z5,z370])],[(0,[z0,z1,z727,z4,z5,z6]),(0,[z0,z728,z3,z4,z5,z6]),(0,[z698,z1,z3,z4,z147,z6]),(0,[z0,z1,z3,z4,z30,z6])],[(0,[z0,z1,z35,z4,z475,z6]),(0,[z411,z84,z0,z1,z3,z6]),(0,[z0,z1,z164,z3,z4,z14]),(0,[z0,z1,z3,z4,z729,z6]),(0,[z0,z129,z3,z286,z20,z6])],[(0,[z0,z730,z3,z4,z5,z6]),(0,[z0,z731,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z732]),(0,[z0,z1,z3,z4,z733,z6]),(0,[z140,z1,z164,z3,z4,z145]),(0,[z0,z310,z1,z3,z17,z6]),(0,[z0,z1,z3,z4,z5,z734])]],
   [[],[(0,[z0,z1,z182,z4,z5,z6]),(0,[z0,z1,z735,z4,z5,z6]),(0,[z0,z1,z3,z4,z736,z6]),(0,[z737,z0,z1,z4,z5,z6]),(0,[z0,z1,z297,z302,z5,z6]),(0,[z0,z1,z3,z4,z5,z738]),(0,[z0,z1,z3,z157,z5,z388]),(0,[z0,z1,z3,z157,z81,z6])],[(0,[z85,z1,z3,z4,z475,z6]),(0,[z0,z1,z3,z4,z6,z739]),(0,[z0,z1,z3,z120,z6,z249])],[(0,[z0,z1,z699,z100,z5,z6]),(0,[z0,z1,z3,z740,z5,z6]),(0,[z16,z327,z0,z4,z5,z6]),(0,[z16,z0,z596,z4,z5,z6]),(0,[z0,z1,z3,z4,z741,z6]),(0,[z0,z1,z3,z157,z5,z116])],[(0,[z55,z125,z1,z3,z5,z6]),(0,[z140,z125,z1,z3,z4,z6])],[(0,[z742,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z11,z5,z6])],[(0,[z77,z1,z3,z4,z5,z743]),(0,[z0,z1,z3,z4,z744,z6]),(0,[z0,z1,z3,z5,z6,z745])],[(0,[z0,z1,z746,z4,z5,z6]),(0,[z0,z3,z4,z747,z5,z6]),(0,[z0,z1,z3,z4,z69,z554]),(0,[z0,z1,z3,z4,z748,z6]),(0,[z0,z1,z126,z4,z122,z6]),(0,[z0,z1,z3,z749,z5,z6])]],
   [[(0,[z0,z1,z3,z750,z5,z6]),(0,[z161,z33,z0,z4,z5,z6]),(0,[z54,z0,z1,z3,z355,z6])],[(0,[z0,z1,z142,z234,z5,z6]),(0,[z0,z128,z297,z4,z5,z6]),(0,[z0,z1,z3,z751,z5,z6])],[(0,[z84,z1,z3,z5,z414,z6]),(0,[z85,z1,z3,z4,z5,z267]),(0,[z0,z1,z3,z752,z5,z6])],[(0,[z0,z1,z3,z753,z4,z5]),(0,[z754,z1,z3,z4,z5,z6])],[(0,[z0,z1,z4,z755,z5,z6]),(0,[z190,z1,z297,z4,z5,z6]),(0,[z146,z1,z3,z4,z147,z6]),(0,[z140,z1,z3,z4,z756,z6]),(0,[z757,z0,z1,z3,z4,z6]),(0,[z0,z1,z4,z122,z758,z6]),(0,[z759,z0,z1,z4,z5,z6])],[(0,[z134,z1,z3,z4,z5,z191]),(0,[z0,z1,z3,z5,z6,z760]),(0,[z0,z1,z4,z761,z5,z6])],[(0,[z0,z1,z3,z4,z762,z6]),(0,[z90,z1,z399,z3,z4,z5]),(0,[z0,z1,z3,z763,z5,z6])],[(0,[z0,z1,z764,z4,z5,z6]),(0,[z0,z1,z765,z4,z5,z6]),(0,[z766,z1,z3,z4,z5,z6])]],
   [[(0,[z767,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z768]),(0,[z0,z3,z4,z5,z91,z713]),(0,[z0,z1,z23,z4,z122,z6]),(0,[z0,z1,z3,z157,z5,z769])],[(0,[z0,z3,z4,z5,z770,z6]),(0,[z0,z3,z4,z5,z713,z167])],[(0,[z0,z1,z771,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z772]),(0,[z0,z1,z236,z4,z5,z6]),(0,[z0,z1,z3,z4,z773,z6]),(0,[z0,z1,z3,z4,z758,z6])],[(0,[z187,z1,z99,z4,z5,z6]),(0,[z192,z0,z129,z3,z20,z6]),(0,[z0,z1,z3,z74,z120,z6])],[(0,[z19,z0,z3,z4,z193,z6]),(0,[z0,z1,z3,z4,z774,z5]),(0,[z0,z1,z3,z4,z5,z775])],[(0,[z55,z411,z1,z3,z105,z6]),(0,[z0,z128,z3,z4,z5,z167]),(0,[z0,z1,z3,z4,z69,z14]),(0,[z0,z1,z3,z4,z6,z117])],[(0,[z0,z1,z776,z4,z5,z6]),(0,[z136,z0,z314,z130,z5,z6]),(0,[z0,z129,z236,z4,z20,z6])],[(0,[z1,z3,z4,z5,z743,z289]),(0,[z136,z0,z171,z130,z5,z6])]],
   [[(0,[z605,z67,z3,z4,z5,z6])],[(0,[z0,z1,z777,z4,z5,z6]),(0,[z16,z0,z135,z4,z544,z6]),(0,[z192,z0,z1,z3,z36,z6]),(0,[z187,z1,z3,z4,z5,z43]),(0,[z161,z0,z4,z5,z6,z43])],[(0,[z778,z0,z1,z3,z5,z6]),(0,[z0,z1,z35,z599,z5,z6]),(0,[z54,z0,z1,z163,z4,z6]),(0,[z0,z1,z3,z334,z5,z91])],[(0,[z0,z1,z3,z4,z779,z6]),(0,[z780,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z425,z122,z6])],[(0,[z0,z1,z3,z4,z781,z6]),(0,[z782,z0,z3,z4,z5,z6]),(0,[z0,z1,z783,z4,z5,z6]),(0,[z140,z1,z3,z377,z145,z6]),(0,[z0,z1,z126,z4,z758,z6])],[(0,[z229,z1,z99,z4,z5,z6]),(0,[z90,z1,z3,z4,z5,z376]),(0,[z585,z1,z35,z4,z5,z6]),(0,[z0,z649,z3,z4,z60,z6]),(0,[z0,z1,z3,z784,z5,z6])],[(0,[z54,z0,z1,z127,z5,z6]),(0,[z85,z1,z3,z599,z5,z6]),(0,[z0,z1,z3,z785,z5,z6]),(0,[z0,z1,z3,z5,z6,z786])],[]],
   [[(0,[z0,z1,z163,z4,z5,z6]),(0,[z787,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z788]),(0,[z96,z208,z0,z4,z5,z6]),(0,[z161,z0,z3,z4,z5,z91])],[(0,[z0,z1,z3,z4,z5,z789]),(0,[z55,z1,z341,z105,z5,z6]),(0,[z0,z1,z3,z790,z4,z5])],[(0,[z0,z1,z3,z4,z791,z6]),(0,[z0,z1,z314,z4,z184,z6]),(0,[z792,z0,z3,z4,z5,z6])],[(0,[z203,z793,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z216,z167]),(0,[z0,z1,z99,z4,z475,z6]),(0,[z1,z3,z4,z794,z5,z6]),(0,[z0,z1,z236,z4,z475,z6]),(0,[z0,z1,z3,z4,z5,z284]),(0,[z0,z1,z3,z4,z5,z29]),(0,[z0,z1,z3,z5,z167,z202]),(0,[z54,z0,z1,z3,z424,z6])],[(0,[z0,z356,z3,z4,z5,z167]),(0,[z1,z182,z99,z4,z5,z6]),(0,[z0,z649,z3,z4,z5,z34]),(0,[z136,z0,z3,z130,z5,z6]),(0,[z0,z1,z197,z4,z122,z6])],[(0,[z67,z793,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z70]),(0,[z0,z1,z168,z4,z758,z6]),(0,[z0,z795,z3,z4,z5,z6]),(0,[z0,z1,z126,z425,z122,z6]),(0,[z0,z1,z796,z4,z5,z6])],[(0,[z797,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z798]),(0,[z0,z1,z799,z4,z5,z6]),(0,[z800,z1,z3,z4,z5,z6]),(0,[z0,z602,z3,z4,z20,z6]),(0,[z0,z1,z236,z4,z36,z6]),(0,[z54,z0,z1,z3,z432,z6]),(0,[z0,z1,z3,z4,z81,z6]),(0,[z0,z1,z48,z3,z5,z80])]],
   [[(0,[z1,z793,z3,z4,z5,z6]),(0,[z0,z1,z174,z4,z5,z43]),(0,[z0,z1,z3,z4,z5,z801]),(0,[z0,z1,z802,z4,z5,z6]),(0,[z0,z1,z142,z17,z5,z6])],[(0,[z0,z1,z3,z803,z5,z6]),(0,[z16,z0,z135,z4,z5,z267])],[],[(0,[z0,z1,z3,z4,z5,z804]),(0,[z0,z1,z3,z302,z5,z6]),(0,[z568,z140,z0,z1,z3,z6]),(0,[z0,z649,z312,z4,z5,z6]),(0,[z77,z0,z1,z4,z5,z224]),(0,[z805,z1,z3,z4,z5,z6]),(0,[z54,z0,z1,z3,z5,z153])],[(0,[z54,z0,z1,z3,z546,z6]),(0,[z0,z1,z312,z4,z14,z6])],[(0,[z692,z1,z35,z4,z5,z6]),(0,[z0,z1,z806,z3,z4,z6]),(0,[z0,z310,z1,z3,z4,z6])],[(0,[z0,z1,z314,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z807]),(0,[z1,z3,z794,z105,z5,z6]),(0,[z0,z1,z3,z794,z5,z6]),(0,[z0,z3,z4,z5,z713,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z293]),(0,[z542,z1,z99,z4,z5,z6]),(0,[z16,z0,z808,z4,z5,z6]),(0,[z0,z1,z691,z4,z5,z43])],[(0,[z0,z1,z182,z4,z5,z809]),(0,[z187,z1,z35,z4,z5,z6]),(0,[z0,z1,z3,z157,z5,z101]),(0,[z90,z1,z3,z302,z5,z289])],[(0,[z0,z1,z3,z4,z5,z810]),(0,[z192,z0,z129,z1,z3,z6]),(0,[z161,z33,z0,z4,z5,z34]),(0,[z0,z1,z3,z4,z811,z25])],[(0,[z0,z128,z3,z4,z5,z6]),(0,[z146,z1,z3,z4,z298,z6]),(0,[z0,z649,z3,z4,z14,z6]),(0,[z0,z1,z812,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z813]),(0,[z0,z3,z4,z5,z814,z6]),(0,[z0,z1,z236,z5,z286,z6])],[(0,[z0,z1,z3,z4,z5,z815]),(0,[z0,z1,z3,z4,z816,z6]),(0,[z0,z3,z4,z5,z267,z167]),(0,[z0,z1,z817,z4,z5,z6]),(0,[z818,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z819,z6]),(0,[z0,z1,z820,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z769])],[(0,[z0,z821,z3,z4,z5,z6]),(0,[z190,z1,z822,z4,z5,z6]),(0,[z0,z1,z823,z4,z5,z6]),(0,[z0,z1,z824,z4,z5,z6])]],
   [[(0,[z0,z3,z4,z5,z825,z6])],[(0,[z0,z1,z341,z4,z5,z6]),(0,[z0,z1,z4,z5,z70,z43]),(0,[z0,z1,z24,z3,z4,z14]),(0,[z0,z1,z3,z4,z5,z826])],[(0,[z0,z1,z3,z827,z5,z6]),(0,[z0,z128,z3,z334,z5,z6]),(0,[z0,z3,z4,z5,z188,z6]),(0,[z0,z1,z828,z4,z5,z6])],[(0,[z0,z1,z3,z5,z6,z769])],[(1,[z1,z3,z794,z5,z6]),(0,[z54,z593,z0,z1,z3,z6]),(0,[z54,z0,z1,z3,z318,z6])],[(0,[z0,z1,z254,z4,z5,z6])],[(0,[z0,z1,z17,z271,z5,z6]),(0,[z192,z0,z1,z236,z5,z6]),(0,[z0,z1,z3,z829,z5,z6])],[(0,[z0,z1,z3,z830,z5,z6]),(0,[z0,z1,z99,z599,z5,z6]),(0,[z0,z1,z3,z4,z170,z6]),(0,[z568,z0,z1,z3,z6,z25]),(0,[z0,z1,z9,z3,z5,z80]),(0,[z0,z1,z3,z5,z6,z831])]],
   [[(0,[z54,z0,z1,z3,z324,z6])],[(0,[z0,z128,z3,z4,z5,z216]),(0,[z85,z1,z99,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z832]),(0,[z77,z1,z3,z493,z4,z5]),(0,[z1,z3,z4,z5,z6,z833])],[(0,[z0,z1,z3,z4,z834,z6]),(0,[z835,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z836,z6])],[(0,[z0,z837,z3,z4,z5,z6]),(0,[z0,z1,z838,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z153])],[(0,[z839,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z840,z6]),(0,[z0,z1,z3,z4,z841,z6]),(0,[z0,z1,z3,z4,z91,z117])],[(0,[z0,z1,z3,z4,z842,z6]),(0,[z55,z1,z3,z170,z105,z6]),(0,[z0,z1,z3,z4,z843,z6]),(0,[z568,z146,z0,z1,z3,z6])],[(0,[z66,z67,z3,z4,z5,z293]),(0,[z0,z1,z3,z4,z844,z6]),(1,[z0,z1,z3,z4,z811])],[(0,[z90,z1,z3,z4,z5,z332]),(0,[z192,z0,z1,z3,z5,z6])]],
   [[(0,[z0,z1,z3,z845,z5,z6]),(0,[z1,z822,z3,z4,z5,z6]),(0,[z0,z1,z570,z4,z36,z6]),(0,[z0,z1,z99,z618,z5,z6]),(0,[z0,z1,z3,z846,z5,z6])],[(0,[z0,z1,z847,z3,z5,z6]),(0,[z90,z1,z3,z334,z5,z289]),(0,[z0,z1,z3,z543,z120,z6])],[(0,[z0,z1,z848,z4,z5,z6]),(0,[z190,z1,z35,z4,z5,z70]),(0,[z0,z3,z18,z849,z5,z6]),(0,[z0,z1,z850,z4,z5,z6])],[(0,[z0,z1,z326,z3,z4,z170]),(0,[z0,z851,z3,z4,z5,z6]),(0,[z54,z0,z1,z3,z532,z6])],[(0,[z96,z0,z3,z4,z5,z216]),(0,[z84,z1,z3,z212,z5,z6]),(0,[z0,z1,z852,z4,z5,z6]),(0,[z0,z1,z3,z4,z853,z6]),(0,[z0,z1,z3,z4,z854,z6])],[(0,[z203,z237,z3,z4,z5,z6]),(0,[z0,z1,z99,z4,z30,z6]),(0,[z411,z0,z1,z3,z157,z6]),(0,[z0,z1,z3,z250,z4,z170]),(0,[z0,z1,z164,z3,z5,z377]),(0,[z0,z1,z3,z120,z5,z153]),(0,[z0,z310,z1,z171,z4,z6]),(0,[z33,z0,z1,z4,z5,z34])],[(0,[z0,z855,z3,z4,z5,z6]),(0,[z0,z15,z4,z5,z353,z6]),(0,[z1,z3,z4,z5,z6,z856]),(0,[z192,z0,z1,z322,z5,z6]),(0,[z0,z1,z3,z74,z558,z6])],[(0,[z0,z3,z849,z130,z5,z6]),(0,[z0,z1,z209,z100,z5,z6])]],
   [[(0,[z0,z1,z3,z857,z5,z6]),(0,[z411,z0,z1,z3,z250,z4]),(0,[z0,z649,z3,z4,z5,z43]),(0,[z0,z1,z4,z785,z5,z6]),(0,[z0,z1,z858,z4,z5,z6])],[(0,[z0,z1,z3,z4,z859,z6]),(0,[z0,z1,z860,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z861]),(0,[z0,z1,z3,z4,z5,z862]),(0,[z0,z1,z3,z4,z5,z863])],[(0,[z66,z67,z3,z4,z5,z6]),(0,[z737,z0,z1,z4,z5,z216])],[(0,[z0,z1,z182,z4,z5,z864]),(0,[z0,z1,z3,z4,z865,z6]),(0,[z0,z1,z866,z4,z5,z6]),(0,[z19,z0,z3,z4,z123,z6]),(0,[z867,z1,z3,z4,z5,z6])],[],[(0,[z0,z1,z297,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z868])],[(0,[z0,z1,z3,z4,z6,z869]),(0,[z187,z1,z297,z4,z5,z6]),(0,[z77,z0,z3,z4,z5,z188])],[(0,[z96,z0,z3,z4,z5,z267]),(0,[z0,z1,z3,z4,z870,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z871]),(0,[z0,z1,z872,z4,z5,z6])],[(0,[z0,z1,z3,z4,z6,z873]),(0,[z0,z1,z312,z4,z60,z6])],[(0,[z695,z1,z99,z4,z5,z6]),(0,[z0,z1,z3,z74,z290,z6])],[(0,[z0,z1,z874,z4,z5,z6]),(0,[z569,z1,z99,z4,z5,z6]),(0,[z90,z1,z297,z4,z5,z289]),(0,[z0,z3,z4,z5,z875,z6])],[(0,[z0,z1,z876,z4,z5,z6]),(0,[z0,z1,z3,z4,z877,z6]),(0,[z0,z1,z878,z4,z5,z6]),(0,[z0,z1,z297,z334,z5,z6]),(0,[z90,z1,z3,z4,z5,z743]),(0,[z0,z1,z879,z4,z5,z6]),(0,[z0,z1,z3,z880,z5,z6])],[(0,[z881,z1,z3,z4,z5,z6])],[(0,[z0,z793,z3,z4,z5,z6]),(0,[z0,z1,z3,z195,z5,z6])],[(0,[z85,z1,z35,z4,z5,z6]),(0,[z0,z129,z88,z3,z4,z6])]],
   [[(0,[z559,z237,z3,z4,z5,z6]),(0,[z0,z1,z882,z4,z5,z6]),(0,[z401,z3,z4,z5,z6,z167]),(0,[z0,z1,z3,z4,z5,z883]),(0,[z0,z1,z884,z4,z5,z6])],[(0,[z0,z1,z3,z885,z5,z6]),(0,[z0,z1,z3,z886,z5,z6]),(0,[z0,z1,z3,z887,z5,z6]),(0,[z16,z85,z135,z4,z5,z6]),(0,[z888,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z889,z5,z6]),(0,[z401,z1,z4,z5,z6,z43]),(1,[z0,z3,z849,z5,z6]),(0,[z0,z3,z4,z890,z5,z6]),(0,[z0,z1,z3,z4,z6,z891])],[(0,[z0,z1,z3,z4,z5,z892]),(0,[z0,z1,z3,z4,z5,z893])],[(0,[z66,z67,z227,z4,z5,z6]),(0,[z0,z894,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z895,z6]),(0,[z0,z1,z3,z4,z896,z6]),(0,[z0,z1,z3,z4,z897,z6]),(0,[z0,z1,z168,z4,z36,z6])],[(0,[z568,z140,z1,z3,z145,z6]),(0,[z898,z1,z3,z4,z5,z6]),(0,[z0,z1,z899,z4,z5,z6])],[(0,[z0,z1,z35,z618,z5,z6]),(0,[z0,z1,z171,z4,z184,z6]),(0,[z900,z1,z3,z4,z5,z6]),(0,[z0,z1,z901,z4,z5,z6])],[(0,[z55,z1,z3,z105,z5,z6]),(0,[z0,z1,z902,z4,z5,z6]),(0,[z903,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z167,z117])]],
   [[(0,[z568,z0,z1,z3,z69,z6]),(0,[z0,z1,z3,z334,z5,z167]),(0,[z904,z0,z1,z4,z5,z6])],[(0,[z1,z35,z822,z4,z5,z6]),(0,[z0,z1,z3,z74,z609,z6]),(0,[z0,z1,z3,z4,z905,z6]),(0,[z0,z310,z137,z1,z3,z6])],[(0,[z0,z15,z808,z4,z5,z6]),(0,[z0,z1,z906,z3,z4,z5]),(0,[z0,z561,z3,z4,z5,z167]),(0,[z0,z1,z3,z74,z715,z6])],[(1,[z793,z3,z4,z5,z6]),(0,[z0,z1,z907,z3,z4,z5]),(0,[z0,z1,z35,z4,z30,z6]),(0,[z0,z1,z908,z4,z5,z6]),(0,[z909,z1,z3,z4,z5,z6])],[(0,[z1,z3,z212,z794,z5,z6]),(0,[z0,z128,z3,z4,z14,z6])],[(0,[z0,z1,z3,z5,z377,z6]),(0,[z0,z1,z343,z4,z5,z43]),(0,[z0,z1,z3,z195,z5,z370])],[(0,[z161,z0,z3,z4,z5,z167])],[(0,[z0,z910,z3,z4,z5,z6]),(0,[z0,z1,z209,z599,z5,z6]),(0,[z0,z1,z3,z195,z475,z6]),(0,[z16,z0,z416,z4,z5,z6]),(0,[z16,z0,z337,z4,z5,z6]),(0,[z0,z1,z3,z425,z36,z6])]],
   [[(0,[z0,z3,z4,z5,z70,z911]),(0,[z1,z3,z4,z5,z191,z743]),(0,[z0,z1,z3,z4,z5,z912]),(0,[z0,z310,z1,z314,z4,z6]),(0,[z0,z1,z3,z913,z4,z5])],[(0,[z401,z1,z3,z195,z5,z6]),(0,[z208,z0,z1,z4,z5,z6]),(0,[z914,z0,z1,z3,z5,z6])],[(0,[z0,z1,z915,z4,z5,z6]),(0,[z448,z1,z99,z4,z5,z6]),(0,[z0,z1,z3,z157,z334,z5]),(0,[z0,z1,z171,z4,z5,z6]),(0,[z136,z0,z3,z849,z5,z6])],[(0,[z85,z1,z182,z4,z5,z6]),(0,[z90,z1,z3,z4,z5,z591]),(0,[z0,z1,z3,z916,z5,z6]),(0,[z0,z1,z3,z4,z184,z6]),(0,[z248,z0,z3,z4,z123,z6]),(0,[z54,z0,z1,z3,z715,z6])],[],[(0,[z0,z917,z1,z3,z4,z6]),(0,[z918,z1,z3,z4,z5,z6]),(0,[z96,z0,z4,z5,z91,z224]),(0,[z0,z1,z3,z4,z12,z811])],[(0,[z0,z1,z3,z4,z5,z919]),(1,[z1,z3,z4,z756,z6]),(0,[z0,z1,z4,z920,z5,z6]),(0,[z16,z0,z4,z5,z6,z601])],[]],
   [[(0,[z0,z1,z921,z4,z5,z6]),(0,[z136,z0,z310,z3,z130,z6]),(0,[z0,z1,z142,z785,z5,z6])],[(0,[z0,z1,z922,z4,z5,z6]),(0,[z0,z1,z3,z4,z923,z6])],[(0,[z924,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z925])],[(0,[z0,z1,z3,z4,z5,z926]),(0,[z1,z297,z99,z4,z5,z6]),(0,[z0,z1,z17,z599,z5,z6]),(0,[z0,z129,z3,z4,z890,z6]),(0,[z0,z1,z3,z927,z5,z6])],[(0,[z0,z1,z3,z4,z5,z928]),(0,[z0,z1,z929,z3,z4,z6]),(0,[z0,z930,z3,z4,z5,z6])],[(0,[z0,z3,z4,z890,z20,z6]),(0,[z33,z112,z1,z4,z5,z34])],[(0,[z0,z1,z3,z4,z5,z931])],[(0,[z0,z1,z3,z4,z5,z6]),(0,[z932,z0,z3,z4,z5,z6]),(0,[z782,z0,z3,z4,z5,z70]),(0,[z0,z1,z297,z4,z5,z34]),(0,[z33,z0,z1,z4,z5,z267])]],
   [[(0,[z187,z1,z3,z4,z5,z6]),(0,[z0,z1,z822,z4,z5,z6]),(0,[z0,z1,z3,z933,z4,z6]),(0,[z0,z150,z1,z4,z5,z462]),(0,[z0,z3,z4,z5,z911,z6]),(0,[z77,z1,z3,z4,z5,z178]),(0,[z0,z97,z3,z4,z5,z713]),(0,[z0,z1,z142,z17,z536,z6]),(0,[z0,z1,z126,z618,z122,z6])],[(0,[z0,z1,z3,z4,z5,z934]),(0,[z90,z0,z1,z4,z5,z224]),(0,[z0,z1,z3,z715,z103,z6])],[(0,[z140,z1,z163,z4,z145,z6]),(0,[z54,z0,z1,z3,z4,z29]),(0,[z935,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z936,z5,z6]),(0,[z0,z1,z3,z4,z937,z5]),(0,[z0,z221,z3,z4,z5,z167]),(0,[z0,z129,z3,z4,z20,z6]),(0,[z54,z279,z0,z1,z3,z6])],[(0,[z55,z411,z0,z1,z3,z6])],[(0,[z360,z1,z99,z4,z5,z6]),(0,[z90,z1,z3,z4,z5,z289]),(0,[z0,z1,z3,z157,z647,z5]),(0,[z682,z0,z3,z4,z5,z91]),(0,[z0,z1,z3,z4,z5,z938])],[(0,[z0,z1,z939,z4,z5,z6]),(0,[z0,z1,z3,z334,z5,z6]),(0,[z1,z3,z4,z5,z6,z743])],[(0,[z568,z0,z1,z164,z3,z5]),(0,[z0,z1,z312,z4,z5,z91]),(0,[z0,z1,z3,z940,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z941]),(0,[z16,z401,z135,z4,z5,z6]),(0,[z942,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z943,z6]),(0,[z0,z1,z3,z74,z6,z684])],[(0,[z0,z1,z4,z122,z475,z6]),(0,[z208,z0,z1,z4,z5,z267]),(0,[z0,z944,z3,z4,z5,z6])],[(0,[z0,z1,z3,z945,z5,z6]),(0,[z229,z1,z822,z4,z5,z6]),(0,[z0,z1,z946,z3,z5,z6]),(0,[z0,z1,z3,z4,z715,z6])],[(0,[z77,z1,z3,z4,z5,z191]),(0,[z161,z0,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z216]),(0,[z0,z1,z4,z5,z947,z6]),(1,[z1,z822,z4,z5,z6]),(0,[z0,z1,z3,z5,z948,z6]),(0,[z0,z1,z3,z5,z6,z949]),(0,[z112,z150,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z950]),(0,[z0,z218,z3,z4,z5,z167]),(0,[z0,z434,z3,z4,z5,z91]),(1,[z0,z1,z785,z5,z6])],[(0,[z951,z0,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z370]),(0,[z0,z1,z952,z3,z4,z6]),(0,[z0,z1,z3,z5,z6,z202])],[(0,[z0,z1,z3,z4,z953,z6]),(0,[z0,z1,z3,z4,z5,z954]),(0,[z0,z1,z3,z4,z5,z955]),(0,[z0,z1,z3,z4,z14,z91]),(0,[z0,z956,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z957,z4,z5]),(0,[z0,z1,z3,z4,z475,z6]),(0,[z0,z1,z958,z4,z5,z6])],[(0,[z0,z1,z227,z4,z5,z6]),(0,[z0,z1,z3,z959,z5,z6]),(0,[z0,z1,z3,z302,z60,z6]),(0,[z0,z1,z3,z960,z5,z6]),(0,[z0,z3,z808,z4,z5,z6]),(0,[z0,z137,z3,z849,z5,z6]),(0,[z0,z1,z4,z5,z734,z6])],[(0,[z401,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z961,z6]),(0,[z0,z1,z3,z962,z5,z6]),(0,[z16,z0,z509,z4,z5,z6]),(0,[z0,z1,z3,z963,z5,z6])],[(0,[z0,z1,z3,z4,z964,z6]),(0,[z0,z1,z326,z3,z157,z5]),(0,[z90,z1,z3,z4,z5,z545])],[(0,[z494,z237,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z965,z6]),(0,[z84,z1,z3,z794,z5,z6]),(0,[z0,z1,z3,z4,z536,z6])],[(0,[z649,z3,z99,z4,z5,z6]),(0,[z411,z0,z1,z3,z6,z80]),(0,[z0,z1,z616,z17,z5,z6]),(0,[z0,z1,z3,z120,z715,z6])],[(0,[z0,z966,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z665,z43]),(0,[z0,z310,z1,z3,z100,z6]),(0,[z967,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z120,z623,z6]),(0,[z0,z1,z3,z4,z544,z370]),(1,[z0,z808,z4,z5,z6])]],
   [[(0,[z0,z968,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z522,z5]),(0,[z0,z1,z3,z4,z5,z267]),(0,[z0,z1,z3,z969,z4,z5]),(0,[z0,z1,z970,z4,z5,z6]),(0,[z867,z208,z1,z4,z5,z6])],[(0,[z190,z1,z3,z4,z5,z70]),(0,[z0,z128,z3,z4,z60,z6]),(0,[z0,z1,z3,z11,z6,z25])],[(1,[z1,z3,z4,z5,z743]),(0,[z0,z1,z3,z971,z5,z6]),(0,[z0,z1,z3,z4,z5,z972])],[(0,[z0,z973,z3,z4,z5,z6]),(0,[z401,z1,z3,z4,z544,z6]),(0,[z974,z1,z3,z4,z5,z6]),(0,[z208,z0,z1,z4,z5,z34]),(0,[z0,z1,z3,z975,z5,z6]),(0,[z0,z1,z4,z5,z34,z734]),(0,[z0,z1,z3,z4,z5,z976]),(0,[z0,z1,z3,z4,z69,z811])],[(0,[z140,z1,z3,z4,z522,z145]),(0,[z0,z1,z164,z3,z4,z25]),(0,[z0,z1,z3,z5,z6,z977])],[(0,[z0,z1,z3,z978,z5,z6]),(0,[z457,z1,z99,z4,z5,z6]),(0,[z0,z1,z3,z425,z5,z6]),(0,[z0,z1,z979,z4,z5,z6]),(0,[z0,z1,z980,z4,z5,z6])],[(0,[z66,z793,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z981]),(0,[z1,z3,z4,z147,z756,z6]),(0,[z0,z1,z209,z785,z5,z6])],[(0,[z0,z1,z3,z982,z4,z6]),(0,[z983,z0,z3,z4,z5,z6]),(0,[z140,z1,z254,z4,z145,z6]),(0,[z0,z1,z312,z302,z5,z6]),(0,[z0,z1,z171,z599,z5,z6]),(0,[z0,z1,z3,z4,z475,z370]),(0,[z0,z1,z3,z4,z984,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z985]),(0,[z0,z1,z3,z4,z5,z358]),(0,[z0,z1,z3,z4,z194,z25])],[(0,[z401,z1,z3,z4,z5,z370]),(0,[z0,z1,z3,z5,z286,z6]),(0,[z0,z3,z4,z5,z986,z6]),(1,[z0,z1,z3,z5,z769])],[(0,[z0,z1,z987,z4,z5,z6]),(0,[z0,z606,z3,z4,z5,z167])],[(0,[z66,z67,z3,z4,z5,z216]),(0,[z401,z1,z3,z4,z475,z6]),(0,[z0,z1,z168,z4,z475,z6]),(0,[z16,z0,z359,z4,z5,z6])],[(0,[z190,z1,z35,z4,z5,z6]),(0,[z0,z1,z988,z4,z5,z6]),(0,[z0,z1,z3,z989,z5,z6]),(0,[z0,z129,z3,z4,z20,z358])],[(0,[z161,z0,z3,z4,z5,z267])],[(0,[z0,z649,z3,z302,z5,z6]),(0,[z0,z1,z3,z4,z990,z6]),(0,[z0,z1,z142,z17,z30,z6]),(0,[z991,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z758,z36,z6])],[(0,[z0,z1,z3,z4,z992,z5]),(0,[z0,z128,z312,z4,z5,z6]),(0,[z0,z1,z3,z302,z14,z6]),(0,[z0,z1,z3,z4,z5,z993]),(0,[z0,z1,z3,z849,z5,z6]),(0,[z0,z244,z3,z18,z5,z6])]],
   [[(0,[z90,z1,z3,z4,z60,z289]),(0,[z0,z808,z135,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z994]),(0,[z0,z1,z3,z4,z475,z267])],[(0,[z55,z1,z326,z3,z105,z5]),(0,[z0,z1,z3,z195,z544,z6]),(0,[z0,z1,z3,z11,z69,z12])],[(0,[z568,z0,z1,z3,z5,z6]),(0,[z411,z0,z1,z3,z4,z6]),(0,[z0,z1,z297,z4,z5,z43]),(0,[z0,z1,z4,z5,z995,z6]),(0,[z401,z1,z3,z4,z5,z267]),(0,[z0,z1,z3,z4,z996,z6]),(0,[z0,z1,z3,z4,z705,z12]),(0,[z0,z1,z3,z157,z81,z116])],[(0,[z0,z1,z3,z997,z5,z6]),(0,[z55,z1,z3,z250,z105,z5]),(0,[z1,z3,z4,z756,z145,z6]),(0,[z0,z1,z3,z4,z756,z6]),(0,[z90,z0,z3,z4,z5,z188]),(0,[z0,z1,z3,z599,z5,z6]),(0,[z0,z1,z3,z4,z998,z5])],[(0,[z0,z1,z999,z4,z5,z6])],[(0,[z0,z1,z3,z1000,z5,z6]),(0,[z0,z1,z326,z3,z4,z5]),(0,[z0,z137,z3,z5,z498,z6])],[(0,[z0,z1,z3,z4,z5,z809]),(0,[z0,z1,z3,z1001,z5,z6]),(0,[z0,z1,z3,z4,z5,z1002])]],
   [[(0,[z0,z1,z1003,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z462]),(0,[z0,z1,z3,z250,z4,z5]),(0,[z0,z1,z3,z522,z5,z377]),(0,[z192,z19,z0,z1,z3,z6]),(1,[z0,z3,z4,z5,z713])],[(0,[z0,z1,z1004,z4,z5,z6]),(0,[z0,z1,z3,z1005,z5,z6]),(0,[z190,z649,z3,z4,z5,z6]),(0,[z19,z0,z3,z4,z890,z6]),(1,[z0,z1,z4,z5,z734])],[],[(0,[z0,z1,z3,z4,z69,z63]),(0,[z0,z1,z3,z1006,z5,z6])],[(0,[z0,z1,z1007,z4,z5,z6]),(0,[z1008,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z322,z5,z6]),(0,[z0,z1,z4,z5,z1009,z6]),(0,[z96,z0,z3,z4,z5,z713]),(0,[z96,z208,z0,z4,z5,z91]),(0,[z0,z1010,z3,z4,z5,z6]),(0,[z0,z1,z42,z4,z5,z43])],[(0,[z0,z150,z808,z4,z5,z6]),(0,[z136,z0,z310,z1,z3,z6])],[(0,[z0,z1,z3,z5,z1011,z6]),(0,[z459,z1,z3,z212,z5,z6]),(0,[z90,z1,z312,z4,z5,z289]),(0,[z0,z1,z4,z5,z224,z6]),(0,[z0,z1,z3,z5,z715,z6])],[(0,[z0,z1,z3,z4,z1012,z6]),(0,[z0,z1,z3,z4,z5,z1013]),(0,[z0,z137,z3,z18,z5,z6]),(0,[z0,z1,z3,z4,z1014,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z1015]),(0,[z190,z1,z182,z4,z5,z6]),(0,[z16,z0,z1,z4,z5,z462]),(0,[z0,z1,z1016,z4,z5,z6]),(0,[z0,z129,z4,z322,z20,z6]),(0,[z0,z1,z3,z4,z6,z811])],[(0,[z0,z1,z3,z4,z5,z1017]),(0,[z0,z1,z163,z74,z4,z6]),(0,[z0,z1,z217,z3,z4,z25]),(0,[z0,z1018,z3,z4,z5,z6])],[(0,[z379,z1,z3,z4,z145,z6]),(0,[z0,z1,z3,z195,z5,z267]),(0,[z0,z1,z4,z5,z1019,z6]),(0,[z1020,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z769,z80])],[(0,[z0,z1,z297,z4,z60,z6]),(0,[z0,z150,z15,z4,z5,z6]),(0,[z0,z1,z3,z599,z5,z370]),(0,[z0,z1,z4,z5,z1021,z6]),(0,[z0,z1,z1022,z4,z5,z6]),(0,[z33,z0,z4,z5,z34,z188])],[(0,[z0,z1,z3,z4,z5,z1023]),(0,[z0,z1,z1024,z4,z5,z6]),(0,[z0,z1,z3,z74,z4,z29])],[(0,[z112,z1,z3,z4,z5,z6]),(0,[z90,z649,z3,z4,z5,z289]),(0,[z77,z1,z3,z4,z5,z350]),(0,[z85,z1,z3,z4,z5,z370]),(0,[z0,z1,z3,z599,z475,z6]),(0,[z0,z1,z3,z5,z1025,z6]),(0,[z0,z1,z3,z5,z91,z202]),(0,[z0,z1,z1026,z4,z5,z6])],[(0,[z66,z246,z3,z4,z5,z6]),(0,[z0,z649,z3,z334,z5,z6]),(0,[z90,z1,z3,z4,z14,z289]),(0,[z54,z0,z1,z3,z103,z6])],[(0,[z0,z1,z1027,z4,z5,z6]),(0,[z0,z1,z3,z334,z14,z6]),(0,[z401,z1,z3,z599,z5,z6]),(0,[z0,z1,z24,z3,z4,z811])]],
   [[],[(0,[z90,z1,z75,z3,z4,z5]),(0,[z0,z1,z171,z17,z5,z6]),(0,[z0,z1,z1028,z3,z5,z6])],[(0,[z0,z1,z1029,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1030]),(0,[z0,z1,z171,z100,z5,z6]),(0,[z0,z1,z3,z11,z69,z6])],[],[(0,[z568,z0,z1,z3,z522,z5]),(0,[z0,z1,z3,z1031,z5,z6]),(0,[z1032,z1,z3,z4,z5,z6]),(1,[z0,z1,z4,z758,z6])],[(0,[z0,z1,z1033,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z1034]),(0,[z0,z1,z3,z599,z5,z267]),(0,[z192,z0,z1,z3,z122,z6]),(0,[z1035,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1036,z6]),(0,[z0,z1,z3,z81,z6,z80])],[(0,[z0,z1,z4,z5,z216,z1037]),(0,[z0,z1,z126,z4,z611,z6]),(0,[z0,z1,z3,z4,z5,z1038]),(0,[z0,z1,z4,z122,z615,z6]),(0,[z0,z1,z464,z100,z5,z6]),(0,[z0,z1,z3,z4,z6,z1039])],[(0,[z0,z1,z3,z4,z5,z1040]),(0,[z0,z1,z1041,z4,z5,z6]),(0,[z481,z1,z3,z105,z5,z6]),(0,[z0,z1042,z3,z4,z5,z6]),(0,[z0,z128,z3,z4,z5,z91]),(0,[z208,z0,z1,z4,z5,z43])]],
   [[(0,[z0,z1,z3,z4,z1043,z6]),(0,[z136,z0,z3,z130,z5,z284]),(0,[z0,z1,z3,z4,z5,z1044])],[(0,[z33,z0,z1,z4,z5,z70]),(0,[z0,z1,z322,z5,z286,z6]),(0,[z54,z0,z179,z1,z3,z6])],[(0,[z0,z1,z3,z1045,z5,z6]),(0,[z0,z1,z3,z4,z1046,z6]),(0,[z0,z1,z3,z4,z1047,z6]),(0,[z0,z150,z4,z5,z487,z6]),(0,[z0,z3,z4,z5,z640,z167]),(0,[z136,z0,z88,z3,z5,z6]),(0,[z1048,z1,z3,z4,z5,z6])],[(0,[z146,z1,z3,z4,z756,z6]),(0,[z0,z1,z3,z4,z544,z6]),(0,[z0,z1,z3,z120,z61,z6])],[(0,[z0,z1,z3,z4,z5,z1049]),(0,[z0,z1,z3,z4,z5,z1050]),(0,[z187,z33,z1,z4,z5,z34])],[(0,[z0,z1,z3,z1051,z5,z6]),(0,[z793,z237,z3,z4,z5,z6]),(0,[z0,z150,z317,z4,z5,z6]),(0,[z0,z1,z3,z4,z1052,z6]),(0,[z16,z0,z135,z4,z5,z6])],[(0,[z0,z1,z1053,z4,z5,z6]),(0,[z0,z1,z1054,z4,z5,z6])],[(0,[z55,z1,z3,z794,z5,z6]),(0,[z0,z1,z3,z1055,z5,z6]),(0,[z0,z1,z1056,z3,z5,z6])]],
   [[(0,[z0,z649,z297,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z743]),(0,[z85,z1,z3,z195,z5,z6]),(0,[z0,z1,z3,z4,z5,z1057]),(0,[z0,z1,z1058,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z864]),(0,[z0,z1,z1059,z3,z4,z5]),(0,[z0,z1,z297,z4,z14,z6]),(0,[z0,z3,z4,z849,z5,z6]),(0,[z0,z1,z1060,z4,z5,z6]),(0,[z0,z1,z48,z3,z5,z769])],[(0,[z96,z0,z3,z4,z5,z91]),(0,[z1061,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1062]),(0,[z1063,z0,z1,z4,z5,z6]),(1,[z0,z3,z4,z890,z6]),(0,[z0,z1,z236,z4,z122,z6]),(0,[z54,z0,z1,z3,z214,z6]),(0,[z0,z1,z3,z69,z12,z202])],[(0,[z66,z67,z182,z4,z5,z6]),(0,[z0,z1,z3,z1064,z5,z6]),(0,[z1065,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z758,z5,z6]),(0,[z1066,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z157,z116,z117])],[(0,[z0,z1,z3,z4,z5,z1067]),(0,[z190,z1,z35,z4,z5,z462]),(0,[z54,z0,z1,z3,z220,z6]),(0,[z0,z1,z312,z4,z5,z167]),(0,[z0,z1,z3,z4,z890,z6]),(0,[z1068,z0,z1,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1069,z6]),(0,[z0,z1,z3,z4,z5,z1070]),(0,[z0,z1,z1071,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z1072]),(0,[z208,z0,z4,z5,z6,z167])],[(0,[z0,z1,z4,z5,z1073,z6]),(0,[z0,z1,z1074,z4,z5,z6]),(0,[z0,z1,z24,z3,z4,z25])]],
   [[(0,[z1075,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z1076]),(0,[z55,z1,z127,z105,z5,z6]),(0,[z0,z1,z3,z4,z5,z1077]),(0,[z0,z1,z3,z4,z5,z1078]),(0,[z0,z1,z3,z1079,z5,z6])],[(0,[z1080,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1081]),(0,[z136,z0,z3,z184,z130,z6]),(0,[z0,z1082,z3,z4,z5,z6])],[(0,[z0,z1,z4,z5,z1037,z6]),(0,[z1,z822,z99,z4,z5,z6]),(0,[z0,z1,z3,z4,z1083,z6]),(0,[z0,z150,z4,z529,z5,z6]),(0,[z0,z1,z785,z100,z5,z6]),(0,[z0,z1,z589,z4,z36,z6])],[(0,[z16,z0,z135,z4,z5,z370]),(0,[z0,z1,z808,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1084,z6]),(0,[z0,z1,z1085,z4,z5,z6]),(0,[z0,z1,z3,z4,z14,z167]),(0,[z0,z1,z3,z1086,z5,z6]),(0,[z0,z1,z3,z5,z116,z769])],[(0,[z0,z1,z99,z4,z5,z370]),(0,[z0,z1087,z3,z4,z5,z6]),(0,[z33,z401,z1,z4,z5,z6]),(0,[z16,z0,z135,z4,z475,z6]),(0,[z0,z1,z42,z4,z5,z734]),(0,[z0,z1,z3,z4,z5,z811]),(0,[z0,z1,z4,z1088,z5,z6])],[(0,[z0,z1,z3,z1089,z4,z5]),(0,[z54,z673,z0,z1,z3,z6]),(0,[z0,z128,z3,z302,z5,z6]),(0,[z54,z0,z1,z3,z584,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z1090]),(0,[z315,z0,z3,z130,z5,z6])],[(0,[z140,z1,z3,z4,z145,z6]),(0,[z1091,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z37,z5,z116]),(0,[z0,z1,z23,z17,z5,z6]),(0,[z0,z1,z3,z4,z69,z12])],[(0,[z0,z1,z3,z1092,z5,z6]),(0,[z0,z1093,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z1094,z6]),(0,[z0,z1,z1095,z4,z5,z6]),(0,[z0,z1,z164,z3,z4,z69]),(0,[z0,z1,z3,z17,z536,z6])],[(0,[z0,z1,z1096,z4,z5,z6]),(0,[z77,z1,z3,z4,z581,z5]),(0,[z0,z1,z3,z4,z544,z267]),(0,[z0,z129,z3,z4,z20,z29]),(0,[z0,z1,z3,z100,z536,z6]),(0,[z0,z1,z3,z4,z69,z388])],[(0,[z0,z1,z3,z4,z60,z6]),(0,[z1,z3,z4,z5,z6,z1097]),(0,[z0,z1,z3,z1098,z5,z6]),(0,[z0,z1,z1099,z4,z5,z6])],[(0,[z0,z1,z1100,z3,z4,z6]),(0,[z0,z1,z3,z1101,z5,z6]),(0,[z0,z1,z3,z4,z1102,z6]),(0,[z0,z1,z3,z1103,z5,z6]),(0,[z1104,z1,z3,z4,z5,z6]),(0,[z0,z1,z1105,z3,z4,z5]),(0,[z33,z0,z1,z4,z5,z734])],[(0,[z0,z1,z1106,z3,z4,z5]),(0,[z0,z150,z386,z4,z5,z6]),(0,[z0,z1,z3,z4,z1107,z6]),(0,[z0,z1,z4,z5,z734,z43])]],
   [[(0,[z0,z1,z326,z3,z5,z80]),(0,[z90,z1,z3,z4,z5,z594]),(0,[z136,z0,z3,z130,z5,z153]),(0,[z0,z3,z4,z123,z890,z6]),(0,[z54,z0,z1,z3,z44,z6])],[(0,[z1108,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z1109,z5,z6])],[(0,[z0,z1,z3,z5,z1110,z6]),(0,[z1111,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1112]),(0,[z0,z1113,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1114]),(0,[z0,z1,z3,z1115,z5,z6]),(0,[z0,z1,z1116,z4,z5,z6]),(0,[z0,z1,z3,z334,z60,z6]),(0,[z0,z97,z3,z4,z5,z167]),(0,[z208,z974,z1,z4,z5,z6]),(0,[z0,z1117,z1,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z1118]),(0,[z1,z3,z4,z756,z5,z6]),(0,[z0,z1,z4,z5,z6,z1119]),(0,[z0,z1,z17,z785,z5,z6]),(0,[z187,z1,z3,z4,z5,z34])],[(0,[z1120,z0,z1,z3,z5,z6])],[(0,[z16,z0,z135,z195,z5,z6]),(0,[z0,z1,z3,z1121,z4,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 546) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 546).take 544) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1090).take 8) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1098)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [546, 544, 8] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 152).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 152).take 104).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [152, 104] = true :=
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

end PEqualNP.Outside.L_meta_39235

theorem PEqualNP.Outside.L_meta_39235 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074602 * 2 ^ 32 + 4241287296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074602 * 2 ^ 32 + 4241287296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39235.solve