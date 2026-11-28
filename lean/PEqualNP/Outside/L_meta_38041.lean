import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38041

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
  Nat.testBit (4277075690 * 2 ^ 32 + 4277071592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x000080000100208a#64 ++ 0x0000400000801045#64 ++ 0xfbdf42904f0a699f#64 ++ 0xfdefa148278534cf#64 : BitVec 256),
   (0x4211002094008224#64 ++ 0x210880104a004112#64 ++ 0xf7bee561b4159667#64 ++ 0xfbdf72b0da0acb33#64 : BitVec 256),
   (0x04a0098628661850#64 ++ 0x825004c314330c28#64 ++ 0xaf75d98e38e61879#64 ++ 0x57baecc71c730c3c#64 : BitVec 256),
   (0xa84a160b40b81d01#64 ++ 0x54250b05a05c0e80#64 ++ 0x9ef3fe0fc0f81f80#64 ++ 0xcf79ff07e07c0fc0#64 : BitVec 256),
   (0x308c1fd000df4001#64 ++ 0x98460fe8006fa000#64 ++ 0x7e0fdff000ffe000#64 ++ 0x3f07eff8007ff000#64 : BitVec 256),
   (0xc0f01ffdfe000001#64 ++ 0xe0780ffeff000000#64 ++ 0x01ffdfffff000000#64 ++ 0x00ffefffff800000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [10, 4]⟩, ⟨.and, [6, 11]⟩, ⟨.or, [7, 5]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x000080000100208a 0x0000400000801045 0x508a021047086186 0xa8450108238430c3

def z1 : W := mkw 0x000080000100208a 0x0000400000801045 0xfbdf42904f0a699f 0xfdefa148278534cf

def z2 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xaf75d98e38e61879 0x57baecc71c730c3c

def z3 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7e0fdff000ffe000 0x3f07eff8007ff000

def z4 : W := mkw 0x4211002094008224 0x210880104a004112 0xf7bee561b4159667 0xfbdf72b0da0acb33

def z5 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9ef3fe0fc0f81f80 0xcf79ff07e07c0fc0

def z6 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x01f0000fff000000 0x00f80007ff800000

def z7 : W := mkw 0x0000000000000000 0x0000000000000000 0x08010290000a6000 0x0400814800053000

def z8 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01ffdfffff000000 0x00ffefffff800000

def z9 : W := mkw 0x4211002094008224 0x210880104a004112 0xd1ba2461b4119667 0xe8dd1230da08cb33

def z10 : W := mkw 0xb8ce9fdb41ff7d8b 0xdc674feda0ffbec5 0xffffffffcfffff9f 0xffffffffe7ffffcf

def z11 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01f11a9fff000000 0x00f88d4fff800000

def z12 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0xf7ffffffff159667 0xfbffffffff8acb33

def z13 : W := mkw 0xc0501679d6000001 0x60280b3ceb000000 0x008a0671c7000000 0x00450338e3800000

def z14 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x00209d6fb0000000 0x00104eb7d8000000

def z15 : W := mkw 0x34ac1fd628ff5851 0x9a560feb147fac28 0xff7fdffe38fff879 0x7fbfefff1c7ffc3c

def z16 : W := mkw 0x46b109a6bc669a74 0xa35884d35e334d3a 0xfffffdefbcf79e7f 0xfffffef7de7bcf3f

def z17 : W := mkw 0x0000000000000000 0x0000000000000000 0xa734c10030041061 0x539a608018020830

def z18 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x2e05db9000ee6000 0x1702edc800773000

def z19 : W := mkw 0x000080000100208a 0x0000400000801045 0xfb554080080a699f 0xfdaaa040040534cf

def z20 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x04009d6000f58000 0x02004eb0007ac000

def z21 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x01ff429fff000000 0x00ffa14fff800000

def z22 : W := mkw 0xe8fa1ffffeb81d01 0xf47d0fffff5c0e80 0x9ef3ff6ff0f81f80 0xcf79ffb7f87c0fc0

def z23 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x18c33e0fc0f80f80 0x8c619f07e07c07c0

def z24 : W := mkw 0x0000000200201800 0x0000000100100c00 0x8e71d80e00e01800 0x4738ec0700700c00

def z25 : W := mkw 0x8842000b40201d00 0x44210005a0100e80 0x80f0200fc0001f80 0xc0781007e0000fc0

def z26 : W := mkw 0x729d1ff094dfc225 0xb94e8ff84a6fe112 0x0420bd61b0f59660 0x02105eb0d87acb30

def z27 : W := mkw 0xa8ca1fdb40b81d01 0xd4650feda05c0e80 0x9effffffc0f81f80 0xcf7fffffe07c0fc0

def z28 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x7fffdfffffffe000 0x3fffeffffffff000

def z29 : W := mkw 0x0000000000000000 0x0000000000000000 0x96b2e40180101600 0xcb597200c0080b00

def z30 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x00411a9e4b000000 0x00208d4f25800000

def z31 : W := mkw 0x46b189a6bd66bafe 0xa358c4d35eb35d7f 0xffffffffffffffff 0xffffffffffffffff

def z32 : W := mkw 0x4211002094008224 0x210880104a004112 0x0420a561b0159660 0x021052b0d80acb30

def z33 : W := mkw 0x4211002094008224 0x210880104a004112 0x508a246184118606 0xa8451230c208c303

def z34 : W := mkw 0x0000000000000000 0x0000000000000000 0xf39e400004000007 0xf9cf200002000003

def z35 : W := mkw 0x40b089f4bf00208a 0xa05844fa5f801045 0x610c01f03f02601f 0x308600f81f81300f

def z36 : W := mkw 0x0000000000000000 0x0000000000000000 0x2a05408000020000 0x1502a04000010000

def z37 : W := mkw 0x308c9fd001df608b 0x98464fe800efb045 0x7f0fdff00fffe01f 0x3f87eff807fff00f

def z38 : W := mkw 0xc6f11ffffe669a75 0xe3788fffff334d3a 0xfffffffffff79e7f 0xfffffffffffbcf3f

def z39 : W := mkw 0xe8fa1ffffeb81d01 0xf47d0fffff5c0e80 0x9ffffffffff81f80 0xcffffffffffc0fc0

def z40 : W := mkw 0x34ac1fd628ff5851 0x9a560feb147fac28 0x7e2fdffe30fff060 0x3f17efff187ff830

def z41 : W := mkw 0x46b109a6bc669a74 0xa35884d35e334d3a 0xf7befd6fb4f59667 0xfbdf7eb7da7acb33

def z42 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9e20bc0f80f81f80 0xcf105e07c07c0fc0

def z43 : W := mkw 0x300c165000994001 0x18060b28004ca000 0x500a06700019e000 0x28050338000cf000

def z44 : W := mkw 0x00809fd00100208b 0x80404fe800801045 0xfbdfdff04f0a699f 0xfdefeff8278534cf

def z45 : W := mkw 0x46b109a6bc669a74 0xa35884d35e334d3a 0x0420bd6fb0f59660 0x02105eb7d87acb30

def z46 : W := mkw 0x0400000200661850 0x0200000100330c28 0xaf34c10030e61879 0x579a608018730c3c

def z47 : W := mkw 0x0000000000000000 0x0000000000000000 0x9ad3420040080980 0xcd69a100200404c0

def z48 : W := mkw 0x4211002094008224 0x210880104a004112 0x652ca561b4159667 0x329652b0da0acb33

def z49 : W := mkw 0x000080000100208a 0x0000400000801045 0x600000000002601f 0x300000000001300f

def z50 : W := mkw 0x4211002094008224 0x210880104a004112 0x81b02001b4001667 0xc0d81000da000b33

def z51 : W := mkw 0x729d1ff094dfc225 0xb94e8ff84a6fe112 0xffbffff1b4fff667 0xffdffff8da7ffb33

def z52 : W := mkw 0x00a009d42a000000 0x805004ea15000000 0x000000900b000000 0x0000004805800000

def z53 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xff5fdff008ffe819 0x7fafeff8047ff40c

def z54 : W := mkw 0x308c9fd001df608b 0x98464fe800efb045 0xffdfdff04fffe99f 0xffefeff827fff4cf

def z55 : W := mkw 0x000080000100208a 0x0000400000801045 0xfa000000000a699f 0xfd000000000534cf

def z56 : W := mkw 0xb8ce1fdb40ff5d01 0xdc670feda07fae80 0x7e4fdffe40ffe980 0x3f27efff207ff4c0

def z57 : W := mkw 0x000080000100208a 0x0000400000801045 0xfb9e4000040a699f 0xfdcf2000020534cf

def z58 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x0c61998e38e61878 0x0630ccc71c730c3c

def z59 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x0420bc0f80f01600 0x02105e07c0780b00

def z60 : W := mkw 0x8040160940000001 0x40200b04a0000000 0x9af3de0fc0080980 0xcd79ef07e00404c0

def z61 : W := mkw 0x4211002094008224 0x210880104a004112 0xe1bc2161b4059667 0xf0de10b0da02cb33

def z62 : W := mkw 0x0000000000000000 0x0000000000000000 0x7bdf42904f0a6000 0x3defa14827853000

def z63 : W := mkw 0x000080000100208a 0x0000400000801045 0x89d102904f0a699f 0xc4e88148278534cf

def z64 : W := mkw 0xc0f009fdfe000000 0xe07804feff000000 0x01fc01ffff000000 0x00fe00ffff800000

def z65 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x00aa9f7ff7000000 0x00554fbffb800000

def z66 : W := mkw 0x0201000000008224 0x0100800000004112 0xf600200000159667 0xfb001000000acb33

def z67 : W := mkw 0x421180209500a2ae 0x2108c0104a805157 0xffffe7f1ff1fffff 0xfffff3f8ff8fffff

def z68 : W := mkw 0x000080000100208a 0x0000400000801045 0xeb5d40900f02681f 0x75aea0480781340f

def z69 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x0420990e30e41060 0x02104c8718720830

def z70 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xff9fdff004ffe007 0xffcfeff8027ff003

def z71 : W := mkw 0xb8ce1fdb40ff5d01 0xdc670feda07fae80 0xfeffffffc0ffff80 0xff7fffffe07fffc0

def z72 : W := mkw 0xa84a160940980501 0x54250b04a04c0280 0x10822601c0180780 0x88411300e00c03c0

def z73 : W := mkw 0xa84a960b41b83d8b 0x54254b05a0dc1ec5 0xfffffe9fcffa7f9f 0xffffff4fe7fd3fcf

def z74 : W := mkw 0xeefb1faffcfe9f75 0xf77d8fd7fe7f4fba 0xffffffeffcff9fff 0xfffffff7fe7fcfff

def z75 : W := mkw 0x0201000000008224 0x0100800000004112 0x5000200000118606 0xa80010000008c303

def z76 : W := mkw 0x0000000000000000 0x0000000000000000 0x01df42904f000000 0x00efa14827800000

def z77 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7e009d6000ffe000 0x3f004eb0007ff000

def z78 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xbff7fd8fb8f61e79 0xdffbfec7dc7b0f3c

def z79 : W := mkw 0x0000165000000001 0x00000b2800000000 0x000a067000000000 0x0005033800000000

def z80 : W := mkw 0x0000000000000000 0x0000000000000000 0xf200000000000007 0xf900000000000003

def z81 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x08011a9000ea6000 0x04008d4800753000

def z82 : W := mkw 0xc0509679d700208b 0x60284b3ceb801045 0xfbdf46f1cf0a699f 0xfdefa378e78534cf

def z83 : W := mkw 0x2008160200b81801 0x10040b01005c0c00 0x9e73de0e00f81800 0x4f39ef07007c0c00

def z84 : W := mkw 0x0400000200661850 0x0200000100330c28 0xae71d80e00e61879 0x5738ec0700730c3c

def z85 : W := mkw 0x000080000100208a 0x0000400000801045 0xabd540804f02099f 0xd5eaa040278104cf

def z86 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x08411a0e40e80980 0x04208d07207404c0

def z87 : W := mkw 0x40b009f4be000000 0xa05804fa5f000000 0x010c01f03f000000 0x008600f81f800000

def z88 : W := mkw 0x300c800001df608a 0x1806400000efb045 0xfe00000000ffe99f 0xff000000007ff4cf

def z89 : W := mkw 0xc0f009adfe000000 0xe07804d6ff000000 0x01f5d98fff000000 0x00faecc7ff800000

def z90 : W := mkw 0x4211002094008224 0x210880104a004112 0xf70c216034159667 0xfb8610b01a0acb33

def z91 : W := mkw 0x0000000000000000 0x0000000000000000 0x000f429000000000 0x0007a14800000000

def z92 : W := mkw 0x0000000000000000 0x0000000000000000 0xf6bee56180159600 0xfb5f72b0c00acb00

def z93 : W := mkw 0x4211002094008224 0x210880104a004112 0x81bee561b4001667 0xc0df72b0da000b33

def z94 : W := mkw 0x8040160940000001 0x40200b04a0000000 0x00f3de0fc0000000 0x0079ef07e0000000

def z95 : W := mkw 0x000080000100208a 0x0000400000801045 0x610c00900f02601f 0x308600480781300f

def z96 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x77ffdfffff158000 0x3bffefffff8ac000

def z97 : W := mkw 0x380e000200ff5d00 0x1c070001007fae80 0xfe00200000ffff80 0xff001000007fffc0

def z98 : W := mkw 0x348c1fd200ff5851 0x9a460fe9007fac28 0xfe0fdff000fff879 0x7f07eff8007ffc3c

def z99 : W := mkw 0x000080000100208a 0x0000400000801045 0xffffe691cf1a7f9f 0xfffff348e78d3fcf

def z100 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x7bffdfffff0a6000 0x3dffefffff853000

def z101 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x00f3df6ff0000000 0x0079efb7f8000000

def z102 : W := mkw 0x76bd1ff6bcffda75 0xbb5e8ffb5e7fed3a 0xffffffffbcfffe7f 0xffffffffde7fff3f

def z103 : W := mkw 0x04a0098428460050 0x825004c214230028 0x2104018038060079 0x108200c01c03003c

def z104 : W := mkw 0x34ac1fd428df4051 0x9a560fea146fa028 0x7f0fdff038ffe079 0x3f87eff81c7ff03c

def z105 : W := mkw 0x108409d000474000 0x884204e80023a000 0x600c01f00007e000 0x300600f80003f000

def z106 : W := mkw 0x4211002094008224 0x210880104a004112 0x0000246180118600 0x00001230c008c300

def z107 : W := mkw 0x729d1ff094dfc225 0xb94e8ff84a6fe112 0x7e2ffff1b0fff660 0x3f17fff8d87ffb30

def z108 : W := mkw 0x4211002094008224 0x210880104a004112 0xf620a561b0159667 0xfb1052b0d80acb33

def z109 : W := mkw 0x000080000100208a 0x0000400000801045 0xfa8a0210470a699f 0xfd450108238534cf

def z110 : W := mkw 0x8040165942000001 0x40200b2ca1000000 0x0000021043000000 0x0000010821800000

def z111 : W := mkw 0x280a000200b81d00 0x14050001005c0e80 0x9e00200000f81f80 0xcf001000007c0fc0

def z112 : W := mkw 0x2008160000980001 0x10040b00004c0000 0x1002060000180000 0x08010300000c0000

def z113 : W := mkw 0x000080000100208a 0x0000400000801045 0x81d000004f00099f 0xc0e80000278004cf

def z114 : W := mkw 0x00a0098428000000 0x805004c214000000 0x0175d98e38000000 0x00baecc71c000000

def z115 : W := mkw 0x8060000d6a000000 0x40300006b5000000 0x0040000e4b000000 0x0020000725800000

def z116 : W := mkw 0x04a08986296638da 0x825044c314b31c6d 0xaff5d98e7fe619ff 0xd7faecc73ff30cff

def z117 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9ffffe9fcff81f80 0xcfffff4fe7fc0fc0

def z118 : W := mkw 0x80c01fd940000001 0xc0600feca0000000 0x00ffdfffc0000000 0x007fefffe0000000

def z119 : W := mkw 0x0000000000000000 0x0000000000000000 0xab55408008020819 0x55aaa0400401040c

def z120 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x14a2be0fc0f81780 0x8a515f07e07c0bc0

def z121 : W := mkw 0x00a0098428000000 0x805004c214000000 0x01ffdb9e7f000000 0x00ffedcf3f800000

def z122 : W := mkw 0x0000000000000000 0x0000000000000000 0x500a046000118000 0x280502300008c000

def z123 : W := mkw 0x280a000200b81d00 0x14050001005c0e80 0x9e71f80e00f81f80 0xcf38fc07007c0fc0

def z124 : W := mkw 0x42b109f4be008224 0xa15884fa5f004112 0x610c01f03f058067 0x308600f81f82c033

def z125 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x0841188e08e20818 0x04208c470471040c

def z126 : W := mkw 0x2008160000980001 0x10040b00004c0000 0x7e0fdf6000fd8000 0x3f07efb0007ec000

def z127 : W := mkw 0x4211002094008224 0x210880104a004112 0x768ee56184158606 0xbb4772b0c20ac303

def z128 : W := mkw 0xf0fc1ffdfe994001 0xf87e0ffeff4ca000 0x51ffdfffff19e000 0x28ffefffff8cf000

def z129 : W := mkw 0x8040160940000001 0x40200b04a0000000 0x00820601c0000000 0x00410300e0000000

def z130 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x9bffdfffff080980 0xcdffefffff8404c0

def z131 : W := mkw 0x84e01fdf6a661851 0xc2700fefb5330c28 0x08411a9e4be20818 0x04208d4f25f1040c

def z132 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x540a9f7000fde000 0x2a054fb8007ef000

def z133 : W := mkw 0xc0f09ffdff00208b 0xe0784ffeff801045 0x81ffdfffff00099f 0xc0ffefffff8004cf

def z134 : W := mkw 0x0000000000000000 0x0000000000000000 0x7a0f4290000a6000 0x3d07a14800053000

def z135 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x8570990e38e41879 0x42b84c871c720c3c

def z136 : W := mkw 0x000080000100208a 0x0000400000801045 0xab5542904b0a6999 0x55aaa148258534cc

def z137 : W := mkw 0x2008000000980000 0x10040000004c0000 0x1e00000000f80000 0x0f000000007c0000

def z138 : W := mkw 0x000080000100208a 0x0000400000801045 0x81df42904f00099f 0xc0efa148278004cf

def z139 : W := mkw 0x0400000200661850 0x0200000100330c28 0xae00000000e61879 0x5700000000730c3c

def z140 : W := mkw 0xb0cc1fd940df4001 0xd8660feca06fa000 0x7effdfffc0ffe000 0x3f7fefffe07ff000

def z141 : W := mkw 0x429109a094468224 0xa14884d04a234112 0xffbffde1b4f79667 0xffdffef0da7bcb33

def z142 : W := mkw 0xc0f01ffdfe460001 0xe0780ffeff230000 0x2fffdfffffe60000 0x17ffeffffff30000

def z143 : W := mkw 0xe8fa1ffffeb81d01 0xf47d0fffff5c0e80 0x0420bd6fb0f01600 0x02105eb7d8780b00

def z144 : W := mkw 0xc0501679d6000001 0x60280b3ceb000000 0x00fbde7fc7000000 0x007def3fe3800000

def z145 : W := mkw 0x108409d000474000 0x884204e80023a000 0x6e0dd9f000e7e000 0x3706ecf80073f000

def z146 : W := mkw 0x300c000000df4000 0x18060000006fa000 0x7e0ec56000ffe000 0x3f0762b0007ff000

def z147 : W := mkw 0x8842000b40201d00 0x44210005a0100e80 0x8ef1f80fc0e01f80 0xc778fc07e0700fc0

def z148 : W := mkw 0x280a000000980500 0x14050000004c0280 0x1000200000180780 0x88001000000c03c0

def z149 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x88f13a0fc0e81f80 0xc4789d07e0740fc0

def z150 : W := mkw 0x108409d000474000 0x884204e80023a000 0x0000016000058000 0x000000b00002c000

def z151 : W := mkw 0x0000000000000000 0x0000000000000000 0x0841008008020818 0x042080400401040c

def z152 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x2524998e38e61079 0x12924cc71c73083c

def z153 : W := mkw 0x0080098000460000 0x804004c000230000 0x2e05d98000e60000 0x1702ecc000730000

def z154 : W := mkw 0x0420000628201850 0x0210000314100c28 0x8170000e38001879 0x40b800071c000c3c

def z155 : W := mkw 0x00801fd000000001 0x80400fe800000000 0x000fdff000000000 0x0007eff800000000

def z156 : W := mkw 0x0000000000000000 0x0000000000000000 0x01d000004f000000 0x00e8000027800000

def z157 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x51ffffffff118606 0xa8ffffffff88c303

def z158 : W := mkw 0x000080000100208a 0x0000400000801045 0xdadb421047086986 0xed6da108238434c3

def z159 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xfefffe9fc0fa7f80 0xff7fff4fe07d3fc0

def z160 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x05ffdffffff58000 0x02ffeffffffac000

def z161 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x0c61be0fc0f81f80 0x0630df07e07c0fc0

def z162 : W := mkw 0xc4f01ffffe661851 0xe2780fffff330c28 0xafffdfffffe61879 0x57ffeffffff30c3c

def z163 : W := mkw 0x300c000000df4000 0x18060000006fa000 0x7e00000000ffe000 0x3f000000007ff000

def z164 : W := mkw 0xea5b162bd4b89f25 0x752d8b15ea5c4f92 0xffffff6ff4fd9fe7 0xffffffb7fa7ecff3

def z165 : W := mkw 0x4211002094008224 0x210880104a004112 0x51bee561b4118606 0xa8df72b0da08c303

def z166 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x09ffdfffffea6000 0x04ffeffffff53000

def z167 : W := mkw 0x00a0098428000000 0x805004c214000000 0x0041188e08000000 0x00208c4704000000

def z168 : W := mkw 0xc2511629d4008225 0x61288b14ea004112 0xf7ffff6ff4159667 0xfbffffb7fa0acb33

def z169 : W := mkw 0x000080000100208a 0x0000400000801045 0x084102904b0a6998 0x04208148258534cc

def z170 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0xa7ffdfffff041061 0x53ffefffff820830

def z171 : W := mkw 0xf0fc9ffdffdf608b 0xf87e4ffeffefb045 0xffffdfffffffe99f 0xffffeffffffff4cf

def z172 : W := mkw 0xc0d01ff9d6000001 0xe0680ffceb000000 0x008fdff1c7000000 0x0047eff8e3800000

def z173 : W := mkw 0xc4f009affe661850 0xe27804d7ff330c28 0xaff5d98fffe61879 0x57faecc7fff30c3c

def z174 : W := mkw 0x000080000100208a 0x0000400000801045 0xfb0c00900f0a699f 0xfd860048078534cf

def z175 : W := mkw 0xe85a1679d6980501 0x742d0b3ceb4c0280 0x108a2671c7180780 0x88451338e38c03c0

def z176 : W := mkw 0x04a08984294620da 0x825044c214a3106d 0xfbdf43907f0e69ff 0xfdefa1c83f8734ff

def z177 : W := mkw 0xb0ec1fdd6adf4001 0xd8760feeb56fa000 0x08411a9e4bea6000 0x04208d4f25f53000

def z178 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xff7fdb9e38ee7879 0x7fbfedcf1c773c3c

def z179 : W := mkw 0x00801fd000000001 0x80400fe800000000 0x760fdff000158000 0x3b07eff8000ac000

def z180 : W := mkw 0x729d9ff095dfe2af 0xb94ecff84aeff157 0xfffffff1ffffffff 0xfffffff8ffffffff

def z181 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xab55588e08e20819 0x55aaac470471040c

def z182 : W := mkw 0x4211002094008224 0x210880104a004112 0xf3be6001b4001667 0xf9df3000da000b33

def z183 : W := mkw 0x04a01fd628661851 0x82500feb14330c28 0xaf7fdffe38e61879 0x57bfefff1c730c3c

def z184 : W := mkw 0x2008160000980001 0x10040b00004c0000 0x1e03de0000f80000 0x0f01ef00007c0000

def z185 : W := mkw 0x000080000100208a 0x0000400000801045 0x694d02904f0a699f 0x34a68148278534cf

def z186 : W := mkw 0x729d1ff094dfc225 0xb94e8ff84a6fe112 0xf7befd61b4f59667 0xfbdf7eb0da7acb33

def z187 : W := mkw 0xacea1f8f68fe1d51 0xd6750fc7b47f0ea8 0xaf75fd8fb8f61e79 0x57bafec7dc7b0f3c

def z188 : W := mkw 0xa8ea1fdf6ab81d01 0xd4750fefb55c0e80 0x08411a9e4be80980 0x04208d4f25f404c0

def z189 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xaf04018038e61879 0x578200c01c730c3c

def z190 : W := mkw 0xe87a162ffeb81d01 0x743d0b17ff5c0e80 0x9ff3fe0ffff81f80 0xcff9ff07fffc0fc0

def z191 : W := mkw 0x000080000100208a 0x0000400000801045 0x5000000000086186 0xa8000000000430c3

def z192 : W := mkw 0x2008160000980001 0x10040b00004c0000 0x04009c0000f00000 0x02004e0000780000

def z193 : W := mkw 0xc4f01ffdfe460051 0xe2780ffeff230028 0x21ffdfffff060079 0x10ffefffff83003c

def z194 : W := mkw 0x46310026bc209a74 0x231880135e104d3a 0xf7fee56fbc159e7f 0xfbff72b7de0acf3f

def z195 : W := mkw 0x300c000000df4000 0x18060000006fa000 0x0800000000ea6000 0x0400000000753000

def z196 : W := mkw 0x4211002094008224 0x210880104a004112 0xffbfe7f1b41ff667 0xffdff3f8da0ffb33

def z197 : W := mkw 0xacea1f8f68fe1d51 0xd6750fc7b47f0ea8 0xbff7ff8ff8fe1ff9 0xdffbffc7fc7f0ffc

def z198 : W := mkw 0x000080000100208a 0x0000400000801045 0x9ad342904b0a6998 0xcd69a148258534cc

def z199 : W := mkw 0x0000000000000000 0x0000000000000000 0xa600000000041061 0x5300000000020830

def z200 : W := mkw 0x14a409d428474050 0x8a5204ea1423a028 0x610c01f03807e079 0x308600f81c03f03c

def z201 : W := mkw 0x40b009f4be000000 0xa05804fa5f000000 0x01bec5f1bf000000 0x00df62f8df800000

def z202 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x012c9dffbf000000 0x00964effdf800000

def z203 : W := mkw 0xea5b962bd5b8bfaf 0x752dcb15eadc5fd7 0xffffffffffffffff 0xffffffffffffffff

def z204 : W := mkw 0x4010002094000000 0x200800104a000000 0x01bec561b4000000 0x00df62b0da000000

def z205 : W := mkw 0xc4f01ffffe661851 0xe2780fffff330c28 0xaf75ddefb8e61879 0x57baeef7dc730c3c

def z206 : W := mkw 0x00801fd000460001 0x80400fe800230000 0x2e0fdff000e60000 0x1707eff800730000

def z207 : W := mkw 0x0000000000000000 0x0000000000000000 0x00b2c40180000000 0x00596200c0000000

def z208 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xae41188e08e61879 0x57208c4704730c3c

def z209 : W := mkw 0xa84a160940980501 0x54250b04a04c0280 0x10f3fe0fc0180780 0x8879ff07e00c03c0

def z210 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xfffffe0fc4f81f87 0xffffff07e27c0fc3

def z211 : W := mkw 0x0000000000000000 0x0000000000000000 0x2604c10000040000 0x1302608000020000

def z212 : W := mkw 0x000080000100208a 0x0000400000801045 0x4008001007006006 0x2004000803803003

def z213 : W := mkw 0x4211002094008224 0x210880104a004112 0x610c016034058067 0x308600b01a02c033

def z214 : W := mkw 0x04a08986296638da 0x825044c314b31c6d 0xffffdb9e7fee79ff 0xffffedcf3ff73cff

def z215 : W := mkw 0x4211002094008224 0x210880104a004112 0xffffe761f41d9fe7 0xfffff3b0fa0ecff3

def z216 : W := mkw 0xe8fa1ffdfe980501 0xf47d0ffeff4c0280 0x11ffffffff180780 0x88ffffffff8c03c0

def z217 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9e413a0e40f81f80 0xcf209d07207c0fc0

def z218 : W := mkw 0xacea1f8f68fe1d51 0xd6750fc7b47f0ea8 0x9ef3ff0ff0fc1fe0 0xcf79ff87f87e0ff0

def z219 : W := mkw 0x2008160000980001 0x10040b00004c0000 0x7e0fde9000fa6000 0x3f07ef48007d3000

def z220 : W := mkw 0x0000000000000000 0x0000000000000000 0xfbdf420044080987 0xfdefa100220404c3

def z221 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x0c019ff000ffe000 0x0600cff8007ff000

def z222 : W := mkw 0x0601000200669a74 0x0300800100334d3a 0xfe00200000f79e7f 0xff001000007bcf3f

def z223 : W := mkw 0x8842000b40201d00 0x44210005a0100e80 0x96f2e40fc0101f80 0xcb797207e0080fc0

def z224 : W := mkw 0xc0f09ffdff00208b 0xe0784ffeff801045 0xfbffdfffff0a699f 0xfdffefffff8534cf

def z225 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x01fec56fff000000 0x00ff62b7ff800000

def z226 : W := mkw 0x000080000100208a 0x0000400000801045 0xffdfc7f04f1fe99f 0xffefe3f8278ff4cf

def z227 : W := mkw 0x0000000200201800 0x0000000100100c00 0x0420980e00e01000 0x02104c0700700800

def z228 : W := mkw 0xa8ea1fdf6ab81d01 0xd4750fefb55c0e80 0x9ef3fe9fcbf81f80 0xcf79ff4fe5fc0fc0

def z229 : W := mkw 0x020180000100a2ae 0x0100c00000805157 0xfe002000001fffff 0xff001000000fffff

def z230 : W := mkw 0x000080000100208a 0x0000400000801045 0x58cb02904f0a699e 0xac658148278534cf

def z231 : W := mkw 0x10841fd000474001 0x88420fe80023a000 0x600fdff00007e000 0x3007eff80003f000

def z232 : W := mkw 0x300c165000994001 0x18060b28004ca000 0x0000046000118000 0x000002300008c000

def z233 : W := mkw 0x00801fd000000001 0x80400fe800000000 0x7a0fdff0000a6000 0x3d07eff800053000

def z234 : W := mkw 0x300c000000994000 0x18060000004ca000 0x500000000019e000 0x28000000000cf000

def z235 : W := mkw 0x0000000000000000 0x0000000000000000 0x760ec56000158000 0x3b0762b0000ac000

def z236 : W := mkw 0xb0ec1fdd6adf4001 0xd8760feeb56fa000 0x7e4fdffe4bffe000 0x3f27efff25fff000

def z237 : W := mkw 0x108409d000474000 0x884204e80023a000 0x0000009000026000 0x0000004800013000

def z238 : W := mkw 0x0000000000000000 0x0000000000000000 0xfb9f4290040a6007 0xfdcfa14802053003

def z239 : W := mkw 0x80e09fdd6b00208b 0xc0704feeb5801045 0xfbdf5a9e4f0a699f 0xfdefad4f278534cf

def z240 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xa734d90e30e41061 0x539a6c8718720830

def z241 : W := mkw 0x421180209500a2ae 0x2108c0104a805157 0xf7fee561ff159fff 0xfbff72b0ff8acfff

def z242 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7fdfdff04fffe000 0x3fefeff827fff000

def z243 : W := mkw 0x000080000100208a 0x0000400000801045 0xffffc3907f0e79ff 0xffffe1c83f873cff

def z244 : W := mkw 0x421180209500a2ae 0x2108c0104a805157 0xf7bee771f71df7e7 0xfbdf73b8fb8efbf3

def z245 : W := mkw 0x300c96500199608b 0x18064b2800ccb045 0x508a06704719e186 0xa8450338238cf0c3

def z246 : W := mkw 0xea5b162bd4b89f25 0x752d8b15ea5c4f92 0x9ef3ff6ff0fd9fe0 0xcf79ffb7f87ecff0

def z247 : W := mkw 0x4211002094008224 0x210880104a004112 0xffffe5e1bc179e7f 0xfffff2f0de0bcf3f

def z248 : W := mkw 0x0000000000000000 0x0000000000000000 0xfb5f4290080a6819 0x7dafa1480405340c

def z249 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x97ffffffff101600 0xcbffffffff880b00

def z250 : W := mkw 0x0000000000000000 0x0000000000000000 0x2104010030040061 0x1082008018020030

def z251 : W := mkw 0x4211002094008224 0x210880104a004112 0x85b0a561b4159667 0xc2d852b0da0acb33

def z252 : W := mkw 0x4211002094008224 0x210880104a004112 0x00202001b0001660 0x00101000d8000b30

def z253 : W := mkw 0x280a800201b83d8a 0x1405400100dc1ec5 0xfe00200000fa7f9f 0xff001000007d3fcf

def z254 : W := mkw 0x000080000100208a 0x0000400000801045 0x0000021043086180 0x00000108218430c0

def z255 : W := mkw 0xa84a96094198258b 0x54254b04a0cc12c5 0xfbdf6691cf1a6f9f 0xfdefb348e78d37cf

def z256 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0xabffdfffff020819 0x55ffefffff81040c

def z257 : W := mkw 0xea5b162bd4b89f25 0x752d8b15ea5c4f92 0xdefbfe6fc4f99f86 0xef7dff37e27ccfc3

def z258 : W := mkw 0xf8fe1ffffeff5d01 0xfc7f0fffff7fae80 0xffffffffffffff80 0xffffffffffffffc0

def z259 : W := mkw 0x308c1fd200ff5801 0x98460fe9007fac00 0xfe7fdffe00fff800 0x7f3fefff007ffc00

def z260 : W := mkw 0x0201000000008224 0x0100800000004112 0x8000200000001667 0xc000100000000b33

def z261 : W := mkw 0x8040160940000001 0x40200b04a0000000 0x96f3fe0fc0101600 0xcb79ff07e0080b00

def z262 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x640c9df000f7e000 0x32064ef8007bf000

def z263 : W := mkw 0xd0f41ffdfe474001 0xe87a0ffeff23a000 0x61ffdfffff07e000 0x30ffefffff83f000

def z264 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xbff7ff0ff0fc1fe1 0xdffbff87f87e0ff0

def z265 : W := mkw 0x84e01f8f68661851 0xc2700fc7b4330c28 0xaff7df8ff8e61879 0x57fbefc7fc730c3c

def z266 : W := mkw 0x000080000100208a 0x0000400000801045 0x7a8f4290470a6186 0xbd47a148238530c3

def z267 : W := mkw 0x008009d000000000 0x804004e800000000 0x000c01f000000000 0x000600f800000000

def z268 : W := mkw 0x388e1fd200ff5d01 0x9c470fe9007fae80 0xfe0ffff000ffff80 0xff07fff8007fffc0

def z269 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xfedfdff040ffe980 0xff6feff8207ff4c0

def z270 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xffffd98e3ce6187f 0xffffecc71e730c3f

def z271 : W := mkw 0xeafb1ffffeb89f25 0xf57d8fffff5c4f92 0xfffffffffffd9fe7 0xfffffffffffecff3

def z272 : W := mkw 0x000080000100208a 0x0000400000801045 0x7a4f42904b0a6998 0x3d27a148258534cc

def z273 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x2945198e38e60879 0x14a28cc71c73043c

def z274 : W := mkw 0x421180209500a2ae 0x2108c0104a805157 0xf7bee5f1bf17f67f 0xfbdf72f8df8bfb3f

def z275 : W := mkw 0xc4f09fffff6638db 0xe2784fffffb31c6d 0xffffdfffffee79ff 0xffffeffffff73cff

def z276 : W := mkw 0xac6a160f68b81d51 0x56350b07b45c0ea8 0x9ff3fe0ff8f81ff9 0xcff9ff07fc7c0ffc

def z277 : W := mkw 0xa84a960b41b83d8b 0x54254b05a0dc1ec5 0xdefbfe1fc7f87f86 0xef7dff0fe3fc3fc3

def z278 : W := mkw 0x34ac1fd628ff5851 0x9a560feb147fac28 0x04209d6e30f59060 0x02104eb7187ac830

def z279 : W := mkw 0x280a160200b81d01 0x14050b01005c0e80 0x9e03fe0000f81f80 0xcf01ff00007c0fc0

def z280 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x2e25d98e30e61060 0x1712ecc718730830

def z281 : W := mkw 0x108409d000474000 0x884204e80023a000 0x7a0f43f0000fe000 0x3d07a1f80007f000

def z282 : W := mkw 0x200896000198208b 0x10044b0000cc1045 0xffdfde904ffa699f 0xffefef4827fd34cf

def z283 : W := mkw 0x14a409d628675850 0x8a5204eb1433ac28 0xef7dd9fe38e7f879 0x77beecff1c73fc3c

def z284 : W := mkw 0x721d16709499c225 0x390e8b384a4ce112 0xf7bee771b41df667 0xfbdf73b8da0efb33

def z285 : W := mkw 0x709c1ff094df4001 0xb84e0ff84a6fa000 0x7fbfdff1b4ffe000 0x3fdfeff8da7ff000

def z286 : W := mkw 0xc0500029d6000000 0x60280014eb000000 0x00800001c7000000 0x00400000e3800000

def z287 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x2e45d98e08e60818 0x1722ecc70473040c

def z288 : W := mkw 0x00a01fd428000001 0x80500fea14000000 0x017fdffe38000000 0x00bfefff1c000000

def z289 : W := mkw 0x34ac098628ff5850 0x9a5604c3147fac28 0xff75d98e38fff879 0x7fbaecc71c7ffc3c

def z290 : W := mkw 0x4010002094000000 0x200800104a000000 0xf3bec561b4000007 0xf9df62b0da000003

def z291 : W := mkw 0x4010002094000000 0x200800104a000000 0x97bee561b4101600 0xcbdf72b0da080b00

def z292 : W := mkw 0x4211002094008224 0x210880104a004112 0x762ee561b0159660 0x3b1772b0d80acb30

def z293 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xbff7fe8fc8fa1f99 0xdffbff47e47d0fcc

def z294 : W := mkw 0x0000000000000000 0x0000000000000000 0x8190000004000007 0xc0c8000002000003

def z295 : W := mkw 0x0000000000000000 0x0000000000000000 0x1082240180100600 0x88411200c0080300

def z296 : W := mkw 0x2008160000980001 0x10040b00004c0000 0x08011a0000e80000 0x04008d0000740000

def z297 : W := mkw 0xa84a960b41b83d8b 0x54254b05a0dc1ec5 0x08411a9e4bea6998 0x04208d4f25f534cc

def z298 : W := mkw 0x0000000000000000 0x0000000000000000 0x8150000008000819 0x40a800000400040c

def z299 : W := mkw 0x0000000000000000 0x0000000000000000 0x004102904b000000 0x0020814825800000

def z300 : W := mkw 0x4211002094008224 0x210880104a004112 0x96b2e561b0159660 0xcb5972b0d80acb30

def z301 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x61ffdfffff058067 0x30ffefffff82c033

def z302 : W := mkw 0xc4f01ffffe661851 0xe2780fffff330c28 0x09ffdfffffe20818 0x04ffeffffff1040c

def z303 : W := mkw 0x00a0098428000000 0x805004c214000000 0x0104018038000000 0x008200c01c000000

def z304 : W := mkw 0x320d000000dfc224 0x19068000006fe112 0xfe00200000fff667 0xff001000007ffb33

def z305 : W := mkw 0xb84e165940994501 0x5c270b2ca04ca280 0x508a2671c019e780 0xa8451338e00cf3c0

def z306 : W := mkw 0x8842800b41203d8a 0x44214005a0901ec5 0x81f0200fcf001f9f 0xc0f81007e7800fcf

def z307 : W := mkw 0xbcee1fdf68ff5d51 0xde770fefb47faea8 0xfffffffff8fffff9 0xfffffffffc7ffffc

def z308 : W := mkw 0x0000000000000000 0x0000000000000000 0xfbdf40800c02081f 0xfdefa0400601040f

def z309 : W := mkw 0xb8ce1fd940df4501 0xdc670feca06fa280 0x7e8ffff1c0ffe780 0xbf47fff8e07ff3c0

def z310 : W := mkw 0x4211002094008224 0x210880104a004112 0xe73cc16034059067 0x739e60b01a02c833

def z311 : W := mkw 0x42b109a4bc008224 0xa15884d25e004112 0xf7fffdefbc159667 0xfbfffef7de0acb33

def z312 : W := mkw 0x04208006292038da 0x0210400314901c6d 0x81f0000e7f0019ff 0xc0f800073f800cff

def z313 : W := mkw 0x000080000100208a 0x0000400000801045 0x0080000047000186 0x80400000238000c3

def z314 : W := mkw 0x8c62000f68201d50 0x46310007b4100ea8 0x81f0200ff8001ff9 0xc0f81007fc000ffc

def z315 : W := mkw 0xea5b1629d4988725 0x752d8b14ea4c4392 0xf7bee761f41d97e7 0xfbdf73b0fa0ecbf3

def z316 : W := mkw 0xa84a160940980501 0x54250b04a04c0280 0x9ad36601c0180f80 0xcd69b300e00c07c0

def z317 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x8e71da0e40e81980 0x4738ed0720740cc0

def z318 : W := mkw 0x000080000100208a 0x0000400000801045 0x004000004b000998 0x00200000258004cc

def z319 : W := mkw 0x0000000200201800 0x0000000100100c00 0x0841180e00e00800 0x04208c0700700400

def z320 : W := mkw 0xacea1f8f68fe1d51 0xd6750fc7b47f0ea8 0xaf75db8e78ee19f9 0x57baedc73c770cfc

def z321 : W := mkw 0xaa4b160b40b89f25 0x55258b05a05c4f92 0xfef3fe0fc0fd9fe7 0xff79ff07e07ecff3

def z322 : W := mkw 0x04a08986296638da 0x825044c314b31c6d 0xef7dd99e3fe6787f 0x77beeccf1ff33c3f

def z323 : W := mkw 0x4211002094008224 0x210880104a004112 0xf7b02001b4159667 0xfbd81000da0acb33

def z324 : W := mkw 0x300c165000994001 0x18060b28004ca000 0x5e0bde7000f9e000 0x2f05ef38007cf000

def z325 : W := mkw 0x40b009f4be000000 0xa05804fa5f000000 0x017dd9fe3f000000 0x00beecff1f800000

def z326 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x81ffffffff001667 0xc0ffffffff800b33

def z327 : W := mkw 0x108489d00147608a 0x884244e800a3b045 0xfbdf43f04f0fe99f 0xfdefa1f82787f4cf

def z328 : W := mkw 0x0000000000000000 0x0000000000000000 0xa314400000000001 0x518a200000000000

def z329 : W := mkw 0xa84a960b41b83d8b 0x54254b05a0dc1ec5 0xfef3fe0fc0fa7f9f 0xff79ff07e07d3fcf

def z330 : W := mkw 0x8040160940000001 0x40200b04a0000000 0x01ffde9fcf000000 0x00ffef4fe7800000

def z331 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x014d1bfe7f000000 0x00a68dff3f800000

def z332 : W := mkw 0xe85a162bd4b81d01 0x742d0b15ea5c0e80 0x9fffff6ff4f81f80 0xcfffffb7fa7c0fc0

def z333 : W := mkw 0x280a000200b81d00 0x14050001005c0e80 0x9ed3620040f81f80 0xcf69b100207c0fc0

def z334 : W := mkw 0x46310026bc209a74 0x231880135e104d3a 0x81f0200fbc001e7f 0xc0f81007de000f3f

def z335 : W := mkw 0xfadf1ffbd4ffdf25 0xfd6f8ffdea7fef92 0xfffffffff4ffffe7 0xfffffffffa7ffff3

def z336 : W := mkw 0x04a0098428460050 0x825004c214230028 0x2f05d98038e60079 0x1782ecc01c73003c

def z337 : W := mkw 0x000080000100208a 0x0000400000801045 0x000000900b026018 0x000000480581300c

def z338 : W := mkw 0x04a08984294620da 0x825044c214a3106d 0x610c01903f06607f 0x308600c81f83303f

def z339 : W := mkw 0x300c165000994001 0x18060b28004ca000 0x760ec770001de000 0x3b0763b8000ef000

def z340 : W := mkw 0xc0501629d4000001 0x60280b14ea000000 0x01ffdf6ff4000000 0x00ffefb7fa000000

def z341 : W := mkw 0xe0f81ffdfe980001 0xf07c0ffeff4c0000 0x1fffdffffff80000 0x0fffeffffffc0000

def z342 : W := mkw 0xa84a960b41b83d8b 0x54254b05a0dc1ec5 0xfbdf5a9e4fea699f 0xfdefad4f27f534cf

def z343 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x0175db9e7b000000 0x00baedcf3d800000

def z344 : W := mkw 0x4211002094008224 0x210880104a004112 0x97b2e401b4101667 0xcbd97200da080b33

def z345 : W := mkw 0x0000000000000000 0x0000000000000000 0xbbd74280480a0999 0xddeba140240504cc

def z346 : W := mkw 0xe8fa1ffffeb81d01 0xf47d0fffff5c0e80 0x05fffffffff01600 0x02fffffffff80b00

def z347 : W := mkw 0xa84a160940980501 0x54250b04a04c0280 0x96b2e601c0181780 0xcb597300e00c0bc0

def z348 : W := mkw 0x8842800b41203d8a 0x44214005a0901ec5 0xfbff629fcf0a7f9f 0xfdffb14fe7853fcf

def z349 : W := mkw 0x300c165000994001 0x18060b28004ca000 0x7a0f46f0001be000 0x3d07a378000df000

def z350 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xff3fdff030fff061 0x7f9feff8187ff830

def z351 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x760edd6000f58000 0x3b076eb0007ac000

def z352 : W := mkw 0xa84a960b41b83d8b 0x54254b05a0dc1ec5 0x9ef3fe9fcbfa7f98 0xcf79ff4fe5fd3fcc

def z353 : W := mkw 0x04a08986296638da 0x825044c314b31c6d 0xfbdf5a9e4fea699f 0xfdefad4f27f534cf

def z354 : W := mkw 0x4010002094000000 0x200800104a000000 0x00208561b0000000 0x001042b0d8000000

def z355 : W := mkw 0x4010002094000000 0x200800104a000000 0x008a046184000000 0x00450230c2000000

def z356 : W := mkw 0x20881fd000980001 0x90440fe8004c0000 0x1e0fdff000f80000 0x0f07eff8007c0000

def z357 : W := mkw 0x0420000628201850 0x0210000314100c28 0x0020000e30001060 0x0010000718000830

def z358 : W := mkw 0x40b009f4be000000 0xa05804fa5f000000 0x0000016030000000 0x000000b018000000

def z359 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xff7fddee38f79879 0x7fbfeef71c7bcc3c

def z360 : W := mkw 0x8842000b40201d00 0x44210005a0100e80 0x0020200f80001600 0x00101007c0000b00

def z361 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x04209d6fb0f58000 0x02104eb7d87ac000

def z362 : W := mkw 0x0420000628201850 0x0210000314100c28 0x0040000e08000818 0x002000070400040c

def z363 : W := mkw 0x0000000000000000 0x0000000000000000 0x610c000004000007 0x3086000002000003

def z364 : W := mkw 0x04a08986296638da 0x825044c314b31c6d 0xff75d98e38ee79ff 0xffbaecc71c773cff

def z365 : W := mkw 0x0000000000000000 0x0000000000000000 0x80b0200180001600 0xc0581000c0000b00

def z366 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xae20990e30e61879 0x57104c8718730c3c

def z367 : W := mkw 0x4211002094008224 0x210880104a004112 0xa7b4e101b4041667 0xd3da7080da020b33

def z368 : W := mkw 0x30ac1fd428df4001 0x98560fea146fa000 0x7f7fdffe38ffe000 0x3fbfefff1c7ff000

def z369 : W := mkw 0x0000000000000000 0x0000000000000000 0xabdf42904f020819 0x55efa1482781040c

def z370 : W := mkw 0x00801fd000000001 0x80400fe800000000 0x00011a9000000000 0x00008d4800000000

def z371 : W := mkw 0x34ac9fd629ff78db 0x9a564feb14ffbc6d 0xffffdffe7ffff9ff 0xffffefff3ffffcff

def z372 : W := mkw 0xc0501679d6000001 0x60280b3ceb000000 0x01df46f1cf000000 0x00efa378e7800000

def z373 : W := mkw 0xc070802dff00208a 0x60384016ff801045 0xfbff429fff0a699f 0xfdffa14fff8534cf

def z374 : W := mkw 0x0000000000000000 0x0000000000000000 0x9ef3e601c0181f80 0xcf79f300e00c0fc0

def z375 : W := mkw 0x300c165000df4001 0x18060b28006fa000 0x7e0a067000ffe000 0x3f050338007ff000

def z376 : W := mkw 0xc271002dfe008224 0x61388016ff004112 0x81f0200fff001667 0xc0f81007ff800b33

def z377 : W := mkw 0xb84e165b40b95d01 0x5c270b2da05cae80 0xdefbfe7fc0f9ff80 0xef7dff3fe07cffc0

def z378 : W := mkw 0x00801fd000000001 0x80400fe800000000 0x01dfdff04f000000 0x00efeff827800000

def z379 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x580b1ef000fbe000 0x2c058f78007df000

def z380 : W := mkw 0x300c000000df4000 0x18060000006fa000 0x0400000000f58000 0x02000000007ac000

def z381 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x05ffffffff159660 0x02ffffffff8acb30

def z382 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x700e07f0001fe000 0x380703f8000ff000

def z383 : W := mkw 0x0000000000000000 0x0000000000000000 0x9292400000000000 0xc949200000000000

def z384 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x00cb1effcf000000 0x00658f7fe7800000

def z385 : W := mkw 0xca53002bd4209f24 0x65298015ea104f92 0x81f0200ff4001fe7 0xc0f81007fa000ff3

def z386 : W := mkw 0x421180209500a2ae 0x2108c0104a805157 0x81f02001ff001fff 0xc0f81000ff800fff

def z387 : W := mkw 0x34ac1fd628ff5851 0x9a560feb147fac28 0x08411a9e08ea6818 0x04208d4f0475340c

def z388 : W := mkw 0x6a1b002294b89f24 0x350d80114a5c4f92 0xffbee561b4fd9fe7 0xffdf72b0da7ecff3

def z389 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0xf3ffdfffff000007 0xf9ffefffff800003

def z390 : W := mkw 0xc2f19ffdff00a2af 0xe178cffeff805157 0xffffffffff1fffff 0xffffffffff8fffff

def z391 : W := mkw 0x0000000000000000 0x0000000000000000 0x00d3420040000000 0x0069a10020000000

def z392 : W := mkw 0x44b009a6bc661850 0xa25804d35e330c28 0xafffddefbce61879 0x57ffeef7de730c3c

def z393 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x1e23fe0f80f81600 0x0f11ff07c07c0b00

def z394 : W := mkw 0x00a0098628201800 0x805004c314100c00 0x8f75d98e38e01800 0x47baecc71c700c00

def z395 : W := mkw 0x00a0098428000000 0x805004c214000000 0x0020990e30000000 0x00104c8718000000

def z396 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9ad35a0e40e80980 0xcd69ad07207404c0

def z397 : W := mkw 0x40300024be000000 0x201800125f000000 0x010000003f000000 0x008000001f800000

def z398 : W := mkw 0x308c09d000df4000 0x984604e8006fa000 0x7e0c01f000ffe000 0x3f0600f8007ff000

def z399 : W := mkw 0x0400000200661850 0x0200000100330c28 0x0800000000e20818 0x040000000071040c

def z400 : W := mkw 0x2caa098628fe1d50 0x965504c3147f0ea8 0xbf75f98e38fe1ff9 0xdfbafcc71c7f0ffc

def z401 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01f09d6fff000000 0x00f84eb7ff800000

def z402 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x00619ffffb000000 0x0030cffffd800000

def z403 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xafffdb9e7fe61879 0x57ffedcf3ff30c3c

def z404 : W := mkw 0xc2511679d6008225 0x61288b3ceb004112 0xf7bee771f7159667 0xfbdf73b8fb8acb33

def z405 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x1e43de0e40f80980 0x0f21ef07207c04c0

def z406 : W := mkw 0xea5b162bd4b89f25 0x752d8b15ea5c4f92 0x0420bd6fb0f59660 0x02105eb7d87acb30

def z407 : W := mkw 0xca53002bd4209f24 0x65298015ea104f92 0xf7fee56ff4159fe7 0xfbff72b7fa0acff3

def z408 : W := mkw 0xac4a160b40fe1d51 0x56250b05a07f0ea8 0xbef3fe0fc0fe1ff9 0xdf79ff07e07f0ffc

def z409 : W := mkw 0x0000000000000000 0x0000000000000000 0xf73ec56030159061 0x7b9f62b0180ac830

def z410 : W := mkw 0x280a000200b81d00 0x14050001005c0e80 0x0800000000e80980 0x04000000007404c0

def z411 : W := mkw 0x0000000000000000 0x0000000000000000 0x2104008008020019 0x108200400401000c

def z412 : W := mkw 0x80e01f8d68000001 0xc0700fc6b4000000 0x01f7df8ff8000000 0x00fbefc7fc000000

def z413 : W := mkw 0x000080000100208a 0x0000400000801045 0xfa0f4290000a699f 0xfd07a148000534cf

def z414 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xfeffff6fc0fd9f80 0xff7fffb7e07ecfc0

def z415 : W := mkw 0x0000000000000000 0x0000000000000000 0xf3df42904f000007 0xf9efa14827800003

def z416 : W := mkw 0x000080000100208a 0x0000400000801045 0xf39e421047086187 0xf9cf2108238430c3

def z417 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x7e2fdfffb0ffe000 0x3f17efffd87ff000

def z418 : W := mkw 0x4211002094008224 0x210880104a004112 0x718e2561b4158667 0xb8c712b0da0ac333

def z419 : W := mkw 0x300c96500199608b 0x18064b2800ccb045 0xfbdf46f04f1be99f 0xfdefa378278df4cf

def z420 : W := mkw 0x8040000940000000 0x40200004a0000000 0x00f0000fc0000000 0x00780007e0000000

def z421 : W := mkw 0x421180209500a2ae 0x2108c0104a805157 0x610c01f03f07e07f 0x308600f81f83f03f

def z422 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x0575d98e38e41060 0x02baecc71c720830

def z423 : W := mkw 0x729d1ff094dfc225 0xb94e8ff84a6fe112 0x7e8ffff184ffe606 0xbf47fff8c27ff303

def z424 : W := mkw 0x0000000000000000 0x0000000000000000 0x7600000000158000 0x3b000000000ac000

def z425 : W := mkw 0x84e01fdf6a661851 0xc2700fefb5330c28 0xaf75db9e7be61879 0x57baedcf3df30c3c

def z426 : W := mkw 0x0400000200661850 0x0200000100330c28 0x0400000000e41060 0x0200000000720830

def z427 : W := mkw 0x0000000000000000 0x0000000000000000 0x508a000004000006 0xa845000002000003

def z428 : W := mkw 0x0000000000000000 0x0000000000000000 0x7a000000000a6000 0x3d00000000053000

def z429 : W := mkw 0xc271002dfe008224 0x61388016ff004112 0xf7fee56fff159667 0xfbff72b7ff8acb33

def z430 : W := mkw 0xb8ce1fdb40ff5d01 0xdc670feda07fae80 0x9ef3ff6fc0fd9f80 0xcf79ffb7e07ecfc0

def z431 : W := mkw 0x0201000000008224 0x0100800000004112 0xf734e10030159667 0xfb9a7080180acb33

def z432 : W := mkw 0x0420000628201850 0x0210000314100c28 0x8f71d80e38e01879 0x47b8ec071c700c3c

def z433 : W := mkw 0x0000000000000000 0x0000000000000000 0xaf75c18038061879 0x57bae0c01c030c3c

def z434 : W := mkw 0x04008002016638da 0x0200400100b31c6d 0xfe00000000ee79ff 0xff00000000773cff

def z435 : W := mkw 0x0420000428000050 0x0210000214000028 0x0100000038000079 0x008000001c00003c

def z436 : W := mkw 0x00a0098428000000 0x805004c214000000 0xa775d98e38041061 0x53baecc71c020830

def z437 : W := mkw 0x300c160000df4001 0x18060b00006fa000 0x7e03de0000ffe000 0x3f01ef00007ff000

def z438 : W := mkw 0xf4fc1ffffeff5851 0xfa7e0fffff7fac28 0xffffdffffffff879 0x7fffeffffffffc3c

def z439 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x01df5a9e4f000000 0x00efad4f27800000

def z440 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x004fdffe4b000000 0x0027efff25800000

def z441 : W := mkw 0x00a0098428460000 0x805004c214230000 0x2f75d98e38e60000 0x17baecc71c730000

def z442 : W := mkw 0x421180209500a2ae 0x2108c0104a805157 0xfbff6291ff0a7fff 0xfdffb148ff853fff

def z443 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x08f3de0fc0e80980 0x0479ef07e07404c0

def z444 : W := mkw 0x0000000000000000 0x0000000000000000 0x0155408008000000 0x00aaa04004000000

def z445 : W := mkw 0x308c9fd001df608b 0x98464fe800efb045 0xfe0fdff000ffe99f 0xff07eff8007ff4cf

def z446 : W := mkw 0xa8ea1f8f68b81d01 0xd4750fc7b45c0e80 0x9ff7ff8ff8f81f80 0xcffbffc7fc7c0fc0

def z447 : W := mkw 0x04a08986296638da 0x825044c314b31c6d 0x08411a9e4bea6998 0x04208d4f25f534cc

def z448 : W := mkw 0xea5b162bd4b89f25 0x752d8b15ea5c4f92 0xf7befd6fb4f59667 0xfbdf7eb7da7acb33

def z449 : W := mkw 0xc070167dfe000001 0x60380b3eff000000 0x01fa067fff000000 0x00fd033fff800000

def z450 : W := mkw 0x20881f8000de0001 0x90440fc0006f0000 0x3e07df8000fe0000 0x1f03efc0007f0000

def z451 : W := mkw 0x04a0098428460050 0x825004c214230028 0x0000010030040060 0x0000008018020030

def z452 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xbff7db8e78ee19f9 0xdffbedc73c770cfc

def z453 : W := mkw 0x4211002094008224 0x210880104a004112 0xd6bae46184119606 0xeb5d7230c208cb03

def z454 : W := mkw 0x40b01ff4be000001 0xa0580ffa5f000000 0x010fdff03f000000 0x0087eff81f800000

def z455 : W := mkw 0x000080000100208a 0x0000400000801045 0xfbd000004f0a699f 0xfde80000278534cf

def z456 : W := mkw 0x308c1fd000994001 0x98460fe8004ca000 0x500fdff00019e000 0x2807eff8000cf000

def z457 : W := mkw 0x0000000000000000 0x0000000000000000 0x500a021000086000 0x2805010800043000

def z458 : W := mkw 0x04208006292038da 0x0210400314901c6d 0xfbff429e7f0a79ff 0xfdffa14f3f853cff

def z459 : W := mkw 0xa048160940980001 0x50240b04a04c0000 0x1ef3de0fc0f80000 0x0f79ef07e07c0000

def z460 : W := mkw 0x34ac1fd628ff5851 0x9a560feb147fac28 0xaf75ddee38f79879 0x57baeef71c7bcc3c

def z461 : W := mkw 0x000080000100208a 0x0000400000801045 0x09df42904f0a6998 0x04efa148278534cc

def z462 : W := mkw 0x328d1fd000dfc225 0x99468fe8006fe112 0xfe0ffff000fff667 0xff07fff8007ffb33

def z463 : W := mkw 0x8040160940000001 0x40200b04a0000000 0x00411a0e40000000 0x00208d0720000000

def z464 : W := mkw 0x0080098000460000 0x804004c000230000 0x0400990000e40000 0x02004c8000720000

def z465 : W := mkw 0xf2fd1ffdfedfc225 0xf97e8ffeff6fe112 0xfffffffffffff667 0xfffffffffffffb33

def z466 : W := mkw 0x308c9fd001df608b 0x98464fe800efb045 0xfbdf5a904fea699f 0xfdefad4827f534cf

def z467 : W := mkw 0x8842160b40201d01 0x44210b05a0100e80 0x80f3fe0fc0001f80 0xc079ff07e0000fc0

def z468 : W := mkw 0x0000000000000000 0x0000000000000000 0x1082020040080180 0x88410100200400c0

def z469 : W := mkw 0x04a0098428460050 0x825004c214230028 0x0000008008020018 0x000000400401000c

def z470 : W := mkw 0xb84e160b40ff5d01 0x5c270b05a07fae80 0xfef3fe0fc0ffff80 0xff79ff07e07fffc0

def z471 : W := mkw 0x401080209500208a 0x200840104a801045 0xfbffc7f1ff0a699f 0xfdffe3f8ff8534cf

def z472 : W := mkw 0x40b089f4bf00208a 0xa05844fa5f801045 0xfbdf43f07f0a699f 0xfdefa1f83f8534cf

def z473 : W := mkw 0x0000000000000000 0x0000000000000000 0x720e400000000000 0x3907200000000000

def z474 : W := mkw 0xc0501679d6000001 0x60280b3ceb000000 0x01bec771f7000000 0x00df63b8fb800000

def z475 : W := mkw 0x000080020120388a 0x0000400100901c45 0xffffda9e4fea799f 0xffffed4f27f53ccf

def z476 : W := mkw 0x8842000b40201d00 0x44210005a0100e80 0x0040000e40000980 0x00200007200004c0

def z477 : W := mkw 0x000080000100208a 0x0000400000801045 0x800000000000099f 0xc0000000000004cf

def z478 : W := mkw 0x4211002094008224 0x210880104a004112 0xf39e416034058067 0xf9cf20b01a02c033

def z479 : W := mkw 0x4010007096000000 0x200800384b000000 0x0008007007000000 0x0004003803800000

def z480 : W := mkw 0x0000000000000000 0x0000000000000000 0x9bdf42904f080980 0xcdefa148278404c0

def z481 : W := mkw 0xc4f01ffffe661851 0xe2780fffff330c28 0x04209d6fb0e41060 0x02104eb7d8720830

def z482 : W := mkw 0xc0509679d700208b 0x60284b3ceb801045 0x508a0671c7086186 0xa8450338e38430c3

def z483 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9e822601c0f81f80 0xcf411300e07c0fc0

def z484 : W := mkw 0x000080000100208a 0x0000400000801045 0xd1da02104f08699f 0xe8ed0108278434cf

def z485 : W := mkw 0xecfa1ffffefe1d51 0xf67d0fffff7f0ea8 0xbffffffffffe1ff9 0xdfffffffffff0ffc

def z486 : W := mkw 0x24a81f8628fe1851 0x92540fc3147f0c28 0xbf77df8e38fe1879 0x5fbbefc71c7f0c3c

def z487 : W := mkw 0x0080098000460000 0x804004c000230000 0x0801188000e20000 0x04008c4000710000

def z488 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x002fdfffb0000000 0x0017efffd8000000

def z489 : W := mkw 0x0000000000000000 0x0000000000000000 0x008a021047000000 0x0045010823800000

def z490 : W := mkw 0xe8fa1ffffeb81d01 0xf47d0fffff5c0e80 0x09ffdfffffe80980 0x04ffeffffff404c0

def z491 : W := mkw 0x00a089842900208a 0x805044c214801045 0xfbffdb9e7f0a699f 0xfdffedcf3f8534cf

def z492 : W := mkw 0x4211002094008224 0x210880104a004112 0x0100000034000067 0x008000001a000033

def z493 : W := mkw 0xb8ce1fdb40ff5d01 0xdc670feda07fae80 0x08411a9e40ea6980 0x04208d4f207534c0

def z494 : W := mkw 0x000080000100208a 0x0000400000801045 0xf3de40004f00099f 0xf9ef2000278004cf

def z495 : W := mkw 0x0420000628661850 0x0210000314330c28 0xaf70000e38e61879 0x57b800071c730c3c

def z496 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x00f3de9fcb000000 0x0079ef4fe5800000

def z497 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x84f0bc0fc0f01f80 0xc2785e07e0780fc0

def z498 : W := mkw 0x8040160940000001 0x40200b04a0000000 0x00209c0f80000000 0x00104e07c0000000

def z499 : W := mkw 0xa84a160940980501 0x54250b04a04c0280 0x0000020040080180 0x00000100200400c0

def z500 : W := mkw 0x4211002094008224 0x210880104a004112 0xa734e561b0159661 0x539a72b0d80acb30

def z501 : W := mkw 0x4211002094008224 0x210880104a004112 0x54aaa561b4159666 0xaa5552b0da0acb33

def z502 : W := mkw 0xc070162dfe000001 0x60380b16ff000000 0x01f3de0fff000000 0x00f9ef07ff800000

def z503 : W := mkw 0x0802000200201d00 0x0401000100100e80 0x8000200000001f80 0xc000100000000fc0

def z504 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z505 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x0175ddefb8000000 0x00baeef7dc000000

def z506 : W := mkw 0x04a08986296638da 0x825044c314b31c6d 0xaf75db9e7bee79f9 0x57baedcf3df73cfc

def z507 : W := mkw 0xf05c1679d6994001 0x782e0b3ceb4ca000 0x508a0671c719e000 0x28450338e38cf000

def z508 : W := mkw 0x000080000100208a 0x0000400000801045 0xf39e40900f02601f 0xf9cf20480781300f

def z509 : W := mkw 0x04008002016638da 0x0200400100b31c6d 0xffdf42904fee79ff 0xffefa14827f73cff

def z510 : W := mkw 0x300c165000994001 0x18060b28004ca000 0x0000021000086000 0x0000010800043000

def z511 : W := mkw 0x2008160000980001 0x10040b00004c0000 0x9eb3fe0180f81600 0xcf59ff00c07c0b00

def z512 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xfebffff180fff600 0xff5ffff8c07ffb00

def z513 : W := mkw 0x108489d00147608a 0x884244e800a3b045 0x610c01f00f07e01f 0x308600f80783f00f

def z514 : W := mkw 0x300c000000df4000 0x18060000006fa000 0x7e0f429000ffe000 0x3f07a148007ff000

def z515 : W := mkw 0x4211002294209a24 0x210880114a104d12 0xfffffd6fb4f59e67 0xfffffeb7da7acf33

def z516 : W := mkw 0xc0f01ffffe201801 0xe0780fffff100c00 0x8fffdfffffe01800 0x47ffeffffff00c00

def z517 : W := mkw 0x000080000100208a 0x0000400000801045 0x61df42904f02601f 0x30efa1482781300f

def z518 : W := mkw 0x0020000428000000 0x0010000214000000 0x0170000e38000000 0x00b800071c000000

def z519 : W := mkw 0x0201000000008224 0x0100800000004112 0x0400200000159660 0x02001000000acb30

def z520 : W := mkw 0x280a000200b81d00 0x14050001005c0e80 0x0400200000f01600 0x0200100000780b00

def z521 : W := mkw 0x529509f09447c224 0xa94a84f84a23e112 0xf7bee5f1b417f667 0xfbdf72f8da0bfb33

def z522 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x0000180000e00000 0x00000c0000700000

def z523 : W := mkw 0x0000000000000000 0x0000000000000000 0x010c00900f000000 0x0086004807800000

def z524 : W := mkw 0x4010002094000000 0x200800104a000000 0x010c016034000000 0x008600b01a000000

def z525 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x8971188e38e21879 0x44b88c471c710c3c

def z526 : W := mkw 0x0000000000000000 0x0000000000000000 0x8630c00000001000 0x4318600000000800

def z527 : W := mkw 0x721d002094dfc224 0x390e80104a6fe112 0xffbee561b4fff667 0xffdf72b0da7ffb33

def z528 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x080fdff000ea6000 0x0407eff800753000

def z529 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x8e71d90e30e41860 0x4738ec8718720c30

def z530 : W := mkw 0x308c9fd001df608b 0x98464fe800efb045 0x08411a904bea6998 0x04208d4825f534cc

def z531 : W := mkw 0x0000000000000000 0x0000000000000000 0x0420a40180101600 0x02105200c0080b00

def z532 : W := mkw 0x34ac1fd628ff5851 0x9a560feb147fac28 0x7e4fdffe08ffe818 0x3f27efff047ff40c

def z533 : W := mkw 0x46b109a6bc669a74 0xa35884d35e334d3a 0xef7dd9ee3ce7987f 0x77beecf71e73cc3f

def z534 : W := mkw 0x0000000000000000 0x0000000000000000 0x0420810030041060 0x0210408018020830

def z535 : W := mkw 0x0000000000000000 0x0000000000000000 0xfadf4290400a6980 0xfd6fa148200534c0

def z536 : W := mkw 0xf0dc1ff9d6df4001 0xf86e0ffceb6fa000 0x7e8fdff1c7ffe000 0x3f47eff8e3fff000

def z537 : W := mkw 0x0201000000008224 0x0100800000004112 0xf79e600004159667 0xfbcf3000020acb33

def z538 : W := mkw 0x0000000000000000 0x0000000000000000 0x600c016000058000 0x300600b00002c000

def z539 : W := mkw 0x42911ff094008225 0xa1488ff84a004112 0xf7bffff1b4159667 0xfbdffff8da0acb33

def z540 : W := mkw 0x4211002094008224 0x210880104a004112 0x0000016030058060 0x000000b01802c030

def z541 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x2e05dde000f78000 0x1702eef0007bc000

def z542 : W := mkw 0xacea1f8f68fe1d51 0xd6750fc7b47f0ea8 0x0420bd0fb0f41660 0x02105e87d87a0b30

def z543 : W := mkw 0x308c098000df4000 0x984604c0006fa000 0x7e05d98000ffe000 0x3f02ecc0007ff000

def z544 : W := mkw 0xea5b1629d4988725 0x752d8b14ea4c4392 0x508a2661c4198786 0xa8451330e20cc3c3

def z545 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x8e71fc0f80f01e00 0x4738fe07c0780f00

def z546 : W := mkw 0x008089800146208a 0x804044c000a31045 0xffdfdb904fee699f 0xffefedc827f734cf

def z547 : W := mkw 0xb8ce1fdb40ff5d01 0xdc670feda07fae80 0x9ef3fe9fc0fa7f80 0xcf79ff4fe07d3fc0

def z548 : W := mkw 0x50b409f4be474000 0xa85a04fa5f23a000 0x610c01f03f07e000 0x308600f81f83f000

def z549 : W := mkw 0x0000000000000000 0x0000000000000000 0x1602c40000100000 0x0b01620000080000

def z550 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x0420bd6fb0159660 0x02105eb7d80acb30

def z551 : W := mkw 0x0000000000000000 0x0000000000000000 0x019e400004000000 0x00cf200002000000

def z552 : W := mkw 0x0000000000460000 0x0000000000230000 0x2e00000000e60000 0x1700000000730000

def z553 : W := mkw 0x6219162094988225 0x310c8b104a4c4112 0xffbfff61b4fd9667 0xffdfffb0da7ecb33

def z554 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x8e71d88e08e21818 0x4738ec4704710c0c

def z555 : W := mkw 0x0480098200661850 0x824004c100330c28 0xae05d98000e61879 0x5702ecc000730c3c

def z556 : W := mkw 0x0080098000460000 0x804004c000230000 0x2004018000060000 0x100200c000030000

def z557 : W := mkw 0x44b009f6be661850 0xa25804fb5f330c28 0xaf7dd9fe3fe61879 0x57beecff1ff30c3c

def z558 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x680d1bf000efe000 0x34068df80077f000

def z559 : W := mkw 0x000080000100208a 0x0000400000801045 0x08000000000a6998 0x04000000000534cc

def z560 : W := mkw 0x0000000000000000 0x0000000000000000 0x7e0fc7f0001fe000 0x3f07e3f8000ff000

def z561 : W := mkw 0x46b109a4bc468274 0xa35884d25e23413a 0xf7bee5e1bc17967f 0xfbdf72f0de0bcb3f

def z562 : W := mkw 0x4211002094008224 0x210880104a004112 0xf7ffe7f1ff159667 0xfbfff3f8ff8acb33

def z563 : W := mkw 0x0000000000000000 0x0000000000000000 0xb7b6e501b0141661 0xdbdb7280d80a0b30

def z564 : W := mkw 0x300c800001df608a 0x1806400000efb045 0xffdf42904fffe99f 0xffefa14827fff4cf

def z565 : W := mkw 0xa8ca1f8b40fe1d01 0xd4650fc5a07f0e80 0xbef7ff8fc0fe1f80 0xdf7bffc7e07f0fc0

def z566 : W := mkw 0x40b009a4bc000000 0xa05804d25e000000 0x01ffddefbc000000 0x00ffeef7de000000

def z567 : W := mkw 0x280a000200b81d00 0x14050001005c0e80 0x9eb2e40180f81f80 0xcf597200c07c0fc0

def z568 : W := mkw 0x308c9fd001df608b 0x98464fe800efb045 0x7e4fdff04bffe998 0x3f27eff825fff4cc

def z569 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01bedd6fb4000000 0x00df6eb7da000000

def z570 : W := mkw 0x0080098000000000 0x804004c000000000 0x0005d98000000000 0x0002ecc000000000

def z571 : W := mkw 0x000080000100208a 0x0000400000801045 0x718e02904f0a619f 0xb8c70148278530cf

def z572 : W := mkw 0x70bc1ff4bedf4001 0xb85e0ffa5f6fa000 0x7f0fdff03fffe000 0x3f87eff81ffff000

def z573 : W := mkw 0xacea1f8f68fe1d51 0xd6750fc7b47f0ea8 0x9ef3fe8fc8fa1f98 0xcf79ff47e47d0fcc

def z574 : W := mkw 0x421180209500a2ae 0x2108c0104a805157 0xfbdf66f1cf1bef9f 0xfdefb378e78df7cf

def z575 : W := mkw 0x804096094100208b 0x40204b04a0801045 0xfbffde9fcf0a699f 0xfdffef4fe78534cf

def z576 : W := mkw 0x0000000000000000 0x0000000000000000 0x600c009000026000 0x3006004800013000

def z577 : W := mkw 0x0000000000000000 0x0000000000000000 0x80d0000040000980 0xc0680000200004c0

def z578 : W := mkw 0x0000000000000000 0x0000000000000000 0x1a03420000080000 0x0d01a10000040000

def z579 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x0020000fb0000000 0x00100007d8000000

def z580 : W := mkw 0x0000160000000001 0x00000b0000000000 0x0003de0000000000 0x0001ef0000000000

def z581 : W := mkw 0x0000000200201800 0x0000000100100c00 0xaf75d90e30e41861 0x57baec8718720c30

def z582 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x040fdff000f58000 0x0207eff8007ac000

def z583 : W := mkw 0x280a800201b83d8a 0x1405400100dc1ec5 0xffdf62904ffa7f9f 0xffefb14827fd3fcf

def z584 : W := mkw 0x8842000b40201d00 0x44210005a0100e80 0x9af3620fc0081f80 0xcd79b107e0040fc0

def z585 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xa174018e38061879 0x50ba00c71c030c3c

def z586 : W := mkw 0x000080000100208a 0x0000400000801045 0x51df42904f086186 0xa8efa148278430c3

def z587 : W := mkw 0xc8f21ffffe201d01 0xe4790fffff100e80 0x81ffffffff001f80 0xc0ffffffff800fc0

def z588 : W := mkw 0x4211002094008224 0x210880104a004112 0x61bec561b4058067 0x30df62b0da02c033

def z589 : W := mkw 0xc0f09ffdff00208b 0xe0784ffeff801045 0x09ffdfffff0a6998 0x04ffefffff8534cc

def z590 : W := mkw 0xa84a96094198258b 0x54254b04a0cc12c5 0x508a2611c7186786 0xa8451308e38c33c3

def z591 : W := mkw 0x4211002094008224 0x210880104a004112 0x05bee561b4159660 0x02df72b0da0acb30

def z592 : W := mkw 0x0201000000008224 0x0100800000004112 0x6000000000058067 0x300000000002c033

def z593 : W := mkw 0xacea9f8f69fe3ddb 0xd6754fc7b4ff1eed 0xffffff9ffffe7fff 0xffffffcfffff3fff

def z594 : W := mkw 0x8842000940000500 0x44210004a0000280 0x00802001c0000780 0x80401000e00003c0

def z595 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x0975d98e38e20818 0x04baecc71c71040c

def z596 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x0000180e00000000 0x00000c0700000000

def z597 : W := mkw 0x46b109a6bc669a74 0xa35884d35e334d3a 0xaf75fdefb8f79e79 0x57bafef7dc7bcf3c

def z598 : W := mkw 0xe85a167bd6b81d01 0x742d0b3deb5c0e80 0x9efbfe7fc7f81f80 0xcf7dff3fe3fc0fc0

def z599 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400856000158000 0x020042b0000ac000

def z600 : W := mkw 0xacea1f8f68fe1d51 0xd6750fc7b47f0ea8 0x08411a8e48ea0998 0x04208d47247504cc

def z601 : W := mkw 0xc2511679d6008225 0x61288b3ceb004112 0x508a2671c7118606 0xa8451338e388c303

def z602 : W := mkw 0x308c9fd001df608b 0x98464fe800efb045 0x7e8fdff047ffe186 0xbf47eff823fff0c3

def z603 : W := mkw 0x4211002094008224 0x210880104a004112 0x770ec56034158067 0x3b8762b01a0ac033

def z604 : W := mkw 0x0201000000008224 0x0100800000004112 0xf60ee56000159667 0xfb0772b0000acb33

def z605 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0xf7befd6fb4159667 0xfbdf7eb7da0acb33

def z606 : W := mkw 0x0400000200201850 0x0200000100100c28 0x8000000000001879 0x4000000000000c3c

def z607 : W := mkw 0xc070802dff00208a 0x60384016ff801045 0x81f0000fff00099f 0xc0f80007ff8004cf

def z608 : W := mkw 0x4010002094000000 0x200800104a000000 0x01b00001b4000000 0x00d80000da000000

def z609 : W := mkw 0x0080098200661800 0x804004c100330c00 0xae75d98e00e61800 0x573aecc700730c00

def z610 : W := mkw 0x8ce2098f68661d50 0xc67104c7b4330ea8 0xaff5f98ff8e61ff9 0xd7fafcc7fc730ffc

def z611 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7a0f5a9000ea6000 0x3d07ad4800753000

def z612 : W := mkw 0xa84a160940980501 0x54250b04a04c0280 0x1e83fe01c0f80780 0x8f41ff00e07c03c0

def z613 : W := mkw 0xb8ce1fdb40ff5d01 0xdc670feda07fae80 0x0420bd6f80f59600 0x02105eb7c07acb00

def z614 : W := mkw 0x0000000200201800 0x0000000100100c00 0x9ef3fc0f80f01e00 0xcf79fe07c0780f00

def z615 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x96b2fc0f80f01600 0xcb597e07c0780b00

def z616 : W := mkw 0x2008160000980001 0x10040b00004c0000 0x9ed3de0040f80980 0xcf69ef00207c04c0

def z617 : W := mkw 0x0000000000000000 0x0000000000000000 0x8130000030001061 0x4098000018000830

def z618 : W := mkw 0x421180209500a2ae 0x2108c0104a805157 0xffbee561b41fffff 0xffdf72b0da0fffff

def z619 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x1e03df6000fd8000 0x0f01efb0007ec000

def z620 : W := mkw 0x529509f09447c224 0xa94a84f84a23e112 0x610c01f03407e067 0x308600f81a03f033

def z621 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x0000180e00e00000 0x00000c0700700000

def z622 : W := mkw 0x0400000200661850 0x0200000100330c28 0xaf55408008e61879 0x57aaa04004730c3c

def z623 : W := mkw 0x0000000000000000 0x0000000000000000 0x000ec56000000000 0x000762b000000000

def z624 : W := mkw 0x1004005000014000 0x080200280000a000 0x400800700001e000 0x200400380000f000

def z625 : W := mkw 0x0000000000000000 0x0000000000000000 0x0134c10030000000 0x009a608018000000

def z626 : W := mkw 0x4211002094008224 0x210880104a004112 0x4008006004018006 0x200400300200c003

def z627 : W := mkw 0xc4f01ffffe661851 0xe2780fffff330c28 0x05ffdfffffe41060 0x02ffeffffff20830

def z628 : W := mkw 0x04a0098428460050 0x825004c214230028 0xa734c18038061079 0x539a60c01c03083c

def z629 : W := mkw 0xa84a960b41b83d8b 0x54254b05a0dc1ec5 0x9ff3fe0fcff81f9f 0xcff9ff07e7fc0fcf

def z630 : W := mkw 0x80e09fdd6b00208b 0xc0704feeb5801045 0x08411a9e4b0a6998 0x04208d4f258534cc

def z631 : W := mkw 0x0080098000460000 0x804004c000230000 0x7e0fdb9000ee6000 0x3f07edc800773000

def z632 : W := mkw 0x2a0b000200b89f24 0x15058001005c4f92 0xfe00200000fd9fe7 0xff001000007ecff3

def z633 : W := mkw 0xc872002ffe201d00 0x64390017ff100e80 0x81f0200fff001f80 0xc0f81007ff800fc0

def z634 : W := mkw 0x0420000628201850 0x0210000314100c28 0xa774c10e38041879 0x53ba60871c020c3c

def z635 : W := mkw 0xe8fa9fffffb83d8b 0xf47d4fffffdc1ec5 0xfffffffffffa7f9f 0xfffffffffffd3fcf

def z636 : W := mkw 0xc4f01ffffe201851 0xe2780fffff100c28 0x81ffdfffff001879 0x40ffefffff800c3c

def z637 : W := mkw 0x04a0098428460050 0x825004c214230028 0xab55418038060879 0x55aaa0c01c03043c

def z638 : W := mkw 0x0000000000000000 0x0000000000000000 0xf7bee40184101607 0xfbdf7200c2080b03

def z639 : W := mkw 0x0000000000000000 0x0000000000000000 0xf7bec10034041067 0xfbdf60801a020833

def z640 : W := mkw 0x4211002094008224 0x210880104a004112 0xf68a246184159667 0xfb451230c20acb33

def z641 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa00000000020819 0x550000000001040c

def z642 : W := mkw 0x0080098000460000 0x804004c000230000 0xaf35d98030e61061 0x579aecc018730830

def z643 : W := mkw 0x729d1ff094dfc225 0xb94e8ff84a6fe112 0x7f0fdff034ffe067 0x3f87eff81a7ff033

def z644 : W := mkw 0x8040160b40201801 0x40200b05a0100c00 0x8ef3de0fc0e01800 0x4779ef07e0700c00

def z645 : W := mkw 0x421180209500a2ae 0x2108c0104a805157 0x508a2671c719e786 0xa8451338e38cf3c3

def z646 : W := mkw 0x020180000100a2ae 0x0100c00000805157 0xffdf62904f1fffff 0xffefb148278fffff

def z647 : W := mkw 0x0080098000460000 0x804004c000230000 0xaf55d98008e60819 0x57aaecc00473040c

def z648 : W := mkw 0x0420000628201850 0x0210000314100c28 0xab75408e38021879 0x55baa0471c010c3c

def z649 : W := mkw 0x000080000100208a 0x0000400000801045 0xe1dc00904f02699f 0xf0ee0048278134cf

def z650 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x04f3fe0fc0f01600 0x0279ff07e0780b00

def z651 : W := mkw 0x000080000100208a 0x0000400000801045 0x7b0f42900f0a601f 0x3d87a1480785300f

def z652 : W := mkw 0x0000000000000000 0x0000000000000000 0x9600200000101600 0xcb00100000080b00

def z653 : W := mkw 0x000080000100208a 0x0000400000801045 0x9bd342004f08099f 0xcde9a100278404cf

def z654 : W := mkw 0x06a1098628669a74 0x835084c314334d3a 0xff75f98e38f79e7f 0xffbafcc71c7bcf3f

def z655 : W := mkw 0xa84a160940980501 0x54250b04a04c0280 0x0000240180100600 0x00001200c0080300

def z656 : W := mkw 0x0201000000008224 0x0100800000004112 0xf6b2e40180159667 0xfb597200c00acb33

def z657 : W := mkw 0x0000000000000000 0x0000000000000000 0x8a51400000000800 0x4528a00000000400

def z658 : W := mkw 0xc0f09ffdff00208b 0xe0784ffeff801045 0x61ffdfffff02601f 0x30ffefffff81300f

def z659 : W := mkw 0x44b009f4be460050 0xa25804fa5f230028 0x210c01f03f060079 0x108600f81f83003c

def z660 : W := mkw 0x04a0098628201850 0x825004c314100c28 0x8175d98e38001879 0x40baecc71c000c3c

def z661 : W := mkw 0x42b109f4be008224 0xa15884fa5f004112 0xf7bee5f1bf159667 0xfbdf72f8df8acb33

def z662 : W := mkw 0xea5b162bd4b89f25 0x752d8b15ea5c4f92 0x9ff3fe0ff4f81fe7 0xcff9ff07fa7c0ff3

def z663 : W := mkw 0x4010002094000000 0x200800104a000000 0x01ffc7f1ff000000 0x00ffe3f8ff800000

def z664 : W := mkw 0x4010002094000000 0x200800104a000000 0xa7bec561b4041061 0x53df62b0da020830

def z665 : W := mkw 0x40b009f4be000000 0xa05804fa5f000000 0x01df43f07f000000 0x00efa1f83f800000

def z666 : W := mkw 0x4211002094008224 0x210880104a004112 0x0080200184000606 0x80401000c2000303

def z667 : W := mkw 0x2c0a000200fe1d50 0x16050001007f0ea8 0xbe00200000fe1ff9 0xdf001000007f0ffc

def z668 : W := mkw 0x721d16709499c225 0x390e8b384a4ce112 0x508a26718419e606 0xa8451338c20cf303

def z669 : W := mkw 0x00a0098428000000 0x805004c214000000 0xab75d98e38020819 0x55baecc71c01040c

def z670 : W := mkw 0x00801fd000000001 0x80400fe800000000 0x00009d6000000000 0x00004eb000000000

def z671 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x1e03de9000fa6000 0x0f01ef48007d3000

def z672 : W := mkw 0xa84a000b40b81d00 0x54250005a05c0e80 0x9ef0200fc0f81f80 0xcf781007e07c0fc0

def z673 : W := mkw 0x1004000000474000 0x080200000023a000 0x600000000007e000 0x300000000003f000

def z674 : W := mkw 0xc0f09ffdff00208b 0xe0784ffeff801045 0x51ffdfffff086186 0xa8ffefffff8430c3

def z675 : W := mkw 0x0080098000460000 0x804004c000230000 0x7e0fdde000f78000 0x3f07eef0007bc000

def z676 : W := mkw 0x000080000100208a 0x0000400000801045 0xfa4102904b0a699f 0xfd208148258534cf

def z677 : W := mkw 0x421180209500a2ae 0x2108c0104a805157 0xfbdf43f07f0fe9ff 0xfdefa1f83f87f4ff

def z678 : W := mkw 0x46b109a6bc669a74 0xa35884d35e334d3a 0xaff5f98fbce61e7f 0xd7fafcc7de730f3f

def z679 : W := mkw 0x0000000200201800 0x0000000100100c00 0xaf75d88e08e21819 0x57baec4704710c0c

def z680 : W := mkw 0xc470002ffe201850 0x62380017ff100c28 0x81f0000fff001879 0x40f80007ff800c3c

def z681 : W := mkw 0x4611002294669a74 0x230880114a334d3a 0xffbee561b4f79e7f 0xffdf72b0da7bcf3f

def z682 : W := mkw 0x04a0098428460050 0x825004c214230028 0x2175d98e38060079 0x10baecc71c03003c

def z683 : W := mkw 0x0400000000460050 0x0200000000230028 0x2000000000060079 0x100000000003003c

def z684 : W := mkw 0x34ac1fd628ff5851 0x9a560feb147fac28 0xaf75db9e38ee7879 0x57baedcf1c773c3c

def z685 : W := mkw 0x000080000100208a 0x0000400000801045 0x010000000f00001f 0x008000000780000f

def z686 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x90f2260fc0181f80 0xc8791307e00c0fc0

def z687 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7e011a9000ffe000 0x3f008d48007ff000

def z688 : W := mkw 0xb8ce1fdb40ff5d01 0xdc670feda07fae80 0x7e2fffff80fff600 0x3f17ffffc07ffb00

def z689 : W := mkw 0xc0501679d6000001 0x60280b3ceb000000 0x0000046180000000 0x00000230c0000000

def z690 : W := mkw 0x4010002094000000 0x200800104a000000 0x77bec561b4158000 0x3bdf62b0da0ac000

def z691 : W := mkw 0x0000000000000000 0x0000000000000000 0xf79ec56004158007 0xfbcf62b0020ac003

def z692 : W := mkw 0x000080000100208a 0x0000400000801045 0xfad34200400a699f 0xfd69a100200534cf

def z693 : W := mkw 0x40901ff094000001 0xa0480ff84a000000 0x01bfdff1b4000000 0x00dfeff8da000000

def z694 : W := mkw 0x0000000200201800 0x0000000100100c00 0x8e00000000e01800 0x4700000000700c00

def z695 : W := mkw 0x0000000000000000 0x0000000000000000 0x9a00000000080980 0xcd000000000404c0

def z696 : W := mkw 0x4211002094008224 0x210880104a004112 0xf39e646184118607 0xf9cf3230c208c303

def z697 : W := mkw 0x0000000200201800 0x0000000100100c00 0x8070000e00001800 0x4038000700000c00

def z698 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x0000180e00e00000 0x00000c0700700000

def z699 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x018e07f1ff000000 0x00c703f8ff800000

def z700 : W := mkw 0x0000000000000000 0x0000000000000000 0x0841020040080980 0x04208100200404c0

def z701 : W := mkw 0x0000000000000000 0x0000000000000000 0x0e01d80000e00000 0x0700ec0000700000

def z702 : W := mkw 0x46b109a4bc468274 0xa35884d25e23413a 0x610c01e03c07807f 0x308600f01e03c03f

def z703 : W := mkw 0x0000000000000000 0x0000000000000000 0x0071d80e00000000 0x0038ec0700000000

def z704 : W := mkw 0x108409d000474000 0x884204e80023a000 0x760ec5f00017e000 0x3b0762f8000bf000

def z705 : W := mkw 0x0000000200201800 0x0000000100100c00 0x9ef3da0e40e81980 0xcf79ed0720740cc0

def z706 : W := mkw 0x340c000200ff5850 0x1a060001007fac28 0xfe00000000fff879 0x7f000000007ffc3c

def z707 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xaf7fdb9e38e61879 0x57bfedcf1c730c3c

def z708 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x81f0000fff000007 0xc0f80007ff800003

def z709 : W := mkw 0xc0f09ffdff00208b 0xe0784ffeff801045 0xfa209d6fb00a699f 0xfd104eb7d80534cf

def z710 : W := mkw 0xf8fe1ffdfe994501 0xfc7f0ffeff4ca280 0x51ffffffff19e780 0xa8ffffffff8cf3c0

def z711 : W := mkw 0x308c098000df4000 0x984604c0006fa000 0x7e0fdde000ffe000 0x3f07eef0007ff000

def z712 : W := mkw 0x10841fd000474001 0x88420fe80023a000 0x6e0fdff000e7e000 0x3707eff80073f000

def z713 : W := mkw 0x00a0098428460000 0x805004c214230000 0x2e45d98e08e60000 0x1722ecc704730000

def z714 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7f5fdff008ffe000 0x3fafeff8047ff000

def z715 : W := mkw 0x40b009f4be000000 0xa05804fa5f000000 0x01ffdbfe7f000000 0x00ffedff3f800000

def z716 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xff75d98e38ee7879 0x7fbaecc71c773c3c

def z717 : W := mkw 0xc271002dfe008224 0x61388016ff004112 0x61fc016fff058067 0x30fe00b7ff82c033

def z718 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xfe9fdff000ffe000 0xff4feff8007ff000

def z719 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7e2ffff180fff600 0x3f17fff8c07ffb00

def z720 : W := mkw 0xc271002dfe008224 0x61388016ff004112 0x01f0000fff000067 0x00f80007ff800033

def z721 : W := mkw 0x04008002016638da 0x0200400100b31c6d 0x0800000000ea6998 0x04000000007534cc

def z722 : W := mkw 0x00a0098428000000 0x805004c214000000 0xf7ffdb9e7f041067 0xfbffedcf3f820833

def z723 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xffbffff184fff607 0xffdffff8c27ffb03

def z724 : W := mkw 0xb0ec1fdd6a994001 0xd8760feeb54ca000 0x504b1efe4b19e000 0x28258f7f258cf000

def z725 : W := mkw 0xf2fd1ffdfedfc225 0xf97e8ffeff6fe112 0x7fffffffffffe606 0xbffffffffffff303

def z726 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7e4fdff04bffe000 0x3f27eff825fff000

def z727 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xae25d98e30e61879 0x5712ecc718730c3c

def z728 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0xffffdfffffffe819 0x7fffeffffffff40c

def z729 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7e4fdff008ffe818 0x3f27eff8047ff40c

def z730 : W := mkw 0xb0ec1fdd6adf4001 0xd8760feeb56fa000 0x7bdf5a9e4fea6000 0x3defad4f27f53000

def z731 : W := mkw 0xf2fd1ffdfedfc225 0xf97e8ffeff6fe112 0x05fffffffff59660 0x02fffffffffacb30

def z732 : W := mkw 0x300c160000df4001 0x18060b00006fa000 0x7e0fdf6000ffe000 0x3f07efb0007ff000

def z733 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xff75d98e38e6187f 0xffbaecc71c730c3f

def z734 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x9ad35a9e4b080980 0xcd69ad4f258404c0

def z735 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x01fc009fff000000 0x00fe004fff800000

def z736 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xffdfdff00cffe81f 0xffefeff8067ff40f

def z737 : W := mkw 0x34ac1fd428df4051 0x9a560fea146fa028 0x7e0fdff008ffe018 0x3f07eff8047ff00c

def z738 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xffffdb8e7cee19ff 0xffffedc73e770cff

def z739 : W := mkw 0x8040000940000000 0x40200004a0000000 0x01f0000fcf000000 0x00f80007e7800000

def z740 : W := mkw 0xc070162dfe000001 0x60380b16ff000000 0x01f2060fff000000 0x00f90307ff800000

def z741 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xbef7fe8fc0fa1f80 0xdf7bff47e07d0fc0

def z742 : W := mkw 0xacea1f8d68de0551 0xd6750fc6b46f02a8 0x31862781f81e07f9 0x98c313c0fc0f03fc

def z743 : W := mkw 0x42b109f4be008224 0xa15884fa5f004112 0xf7fffdffbf159667 0xfbfffeffdf8acb33

def z744 : W := mkw 0xb0cc1fd942df4001 0xd8660feca16fa000 0x7e0fdff043ffe000 0x3f07eff821fff000

def z745 : W := mkw 0x280a800201b83d8a 0x1405400100dc1ec5 0x9e00200000f81f9f 0xcf001000007c0fcf

def z746 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xfffffe9fc8fa7f99 0xffffff4fe47d3fcc

def z747 : W := mkw 0x000080000100208a 0x0000400000801045 0xfbd102904f0a699f 0xfde88148278534cf

def z748 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x012fdfffbf000000 0x0097efffdf800000

def z749 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x00ffdfffcb000000 0x007fefffe5800000

def z750 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xa774d90e38e41879 0x53ba6c871c720c3c

def z751 : W := mkw 0x30ac1fd428df4001 0x98560fea146fa000 0xff7fdffe38ffe819 0x7fbfefff1c7ff40c

def z752 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01fb1effff000000 0x00fd8f7fff800000

def z753 : W := mkw 0xc4f01ffdfe460051 0xe2780ffeff230028 0xabffdfffff060879 0x55ffefffff83043c

def z754 : W := mkw 0xd0f41ffdfe474001 0xe87a0ffeff23a000 0x6fffdfffffe7e000 0x37ffeffffff3f000

def z755 : W := mkw 0x380e800201ff7d8a 0x1c07400100ffbec5 0xfe00200000ffff9f 0xff001000007fffcf

def z756 : W := mkw 0x00a0098428000000 0x805004c214000000 0x0175db9e7b000000 0x00baedcf3d800000

def z757 : W := mkw 0x0400000200661850 0x0200000100330c28 0xaf75d90e30e61879 0x57baec8718730c3c

def z758 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x08411a9e4b020818 0x04208d4f2581040c

def z759 : W := mkw 0x000080000100208a 0x0000400000801045 0x094102904f0a699f 0x04a08148278534cf

def z760 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xaf34d90e30e61879 0x579a6c8718730c3c

def z761 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x9bf3420fff080980 0xcdf9a107ff8404c0

def z762 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0xbbffdfffff0a0999 0xddffefffff8504cc

def z763 : W := mkw 0x68ba09f6beb81d00 0xb45d04fb5f5c0e80 0x9f0c21f03ff81f80 0xcf8610f81ffc0fc0

def z764 : W := mkw 0x30ac1fd428df4001 0x98560fea146fa000 0x7fffdffe7fffe000 0x3fffefff3ffff000

def z765 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xab75588e38e21879 0x55baac471c710c3c

def z766 : W := mkw 0x8040160940000001 0x40200b04a0000000 0xf7fffe9fcf101607 0xfbffff4fe7880b03

def z767 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x0460990e38e41878 0x02304c871c720c3c

def z768 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0xfbffdfffff0a6007 0xfdffefffff853003

def z769 : W := mkw 0xb0cc1fd940df4001 0xd8660feca06fa000 0x7fffdfffcfffe000 0x3fffefffe7fff000

def z770 : W := mkw 0x000080000100208a 0x0000400000801045 0xf1de02904f0a699f 0xf8ef0148278534cf

def z771 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x764fdffe4b158000 0x3b27efff258ac000

def z772 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x0140000e7f000000 0x00a000073f800000

def z773 : W := mkw 0x729d1ff094dfc225 0xb94e8ff84a6fe112 0x89b13a91b4ea7667 0xc4d89d48da753b33

def z774 : W := mkw 0xea5b162bd4b89f25 0x752d8b15ea5c4f92 0x694d1b6e74ed89e7 0x34a68db73a76c4f3

def z775 : W := mkw 0xc2511679d6008225 0x61288b3ceb004112 0xf7ffff7ff7159667 0xfbffffbffb8acb33

def z776 : W := mkw 0xe8fa1ffdfe980501 0xf47d0ffeff4c0280 0x97ffffffff181780 0xcbffffffff8c0bc0

def z777 : W := mkw 0xc070162dfe000001 0x60380b16ff000000 0x01f11a0fff000000 0x00f88d07ff800000

def z778 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x05ffdfffff041060 0x02ffefffff820830

def z779 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x96f2fc0fc0f01f80 0xcb797e07e0780fc0

def z780 : W := mkw 0x421180209500a2ae 0x2108c0104a805157 0x0c61a7f1fb1ffff8 0x0630d3f8fd8ffffc

def z781 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7e0edd6000ffe000 0x3f076eb0007ff000

def z782 : W := mkw 0xf07c002dfedf4000 0x783e0016ff6fa000 0x7ff0000fffffe000 0x3ff80007fffff000

def z783 : W := mkw 0x04a009d62a661850 0x825004eb15330c28 0xaf75d99e3be61879 0x57baeccf1df30c3c

def z784 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x00d35a9e4b000000 0x0069ad4f25800000

def z785 : W := mkw 0x4211002094008224 0x210880104a004112 0xffffe7f1bc1ffe7f 0xfffff3f8de0fff3f

def z786 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x04009f7000fde000 0x02004fb8007ef000

def z787 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x0c20990e30e61878 0x06104c8718730c3c

def z788 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x0861188e38e21878 0x04308c471c710c3c

def z789 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x00611a9ffb000000 0x00308d4ffd800000

def z790 : W := mkw 0x000080000100208a 0x0000400000801045 0xfbff6291cf0a7f9f 0xfdffb148e7853fcf

def z791 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x7f2fdfffbfffe000 0x3f97efffdffff000

def z792 : W := mkw 0x308c09d000df4000 0x984604e8006fa000 0x7e0f43f000ffe000 0x3f07a1f8007ff000

def z793 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0xd1ffffffff119667 0xe8ffffffff88cb33

def z794 : W := mkw 0xb0ec1fdd6adf4001 0xd8760feeb56fa000 0x7f7fdffe7bffe000 0x3fbfefff3dfff000

def z795 : W := mkw 0x000080000100208a 0x0000400000801045 0xfbdf43f04f0fe99f 0xfdefa1f82787f4cf

def z796 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x5c0b9ff000ffe000 0x2e05cff8007ff000

def z797 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0xffffffffff1d9fe7 0xffffffffff8ecff3

def z798 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xffffdb9e7fe6187f 0xffffedcf3ff30c3f

def z799 : W := mkw 0x4211002094008224 0x210880104a004112 0x0520a561b4159667 0x029052b0da0acb33

def z800 : W := mkw 0x308c09d000df4000 0x984604e8006fa000 0x680c01f000efe000 0x340600f80077f000

def z801 : W := mkw 0x300c000000df4000 0x18060000006fa000 0x7e0fc7f000ffe000 0x3f07e3f8007ff000

def z802 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x8ef1fc0fc0f01f80 0xc778fe07e0780fc0

def z803 : W := mkw 0xb0ec1fdd6adf4001 0xd8760feeb56fa000 0x7fdfdffe4fffe000 0x3fefefff27fff000

def z804 : W := mkw 0xc271002dfe008224 0x61388016ff004112 0x01f0200fff000606 0x80f81007ff800303

def z805 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0xb7ffffffff141661 0xdbffffffff8a0b30

def z806 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x81f0000fff000819 0x40f80007ff80040c

def z807 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x61ffdfffff058000 0x30ffefffff82c000

def z808 : W := mkw 0x04008002016638da 0x0200400100b31c6d 0xae00000000ee79f9 0x5700000000773cfc

def z809 : W := mkw 0xc070167dfe000001 0x60380b3eff000000 0x00ca067fcf000000 0x0065033fe7800000

def z810 : W := mkw 0xc070167dfe000001 0x60380b3eff000000 0x01f0021fff000000 0x00f8010fff800000

def z811 : W := mkw 0xc450167bd6661851 0x62280b3deb330c28 0xae8a0671c7e61879 0x57450338e3f30c3c

def z812 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01f3de9fff000000 0x00f9ef4fff800000

def z813 : W := mkw 0x04a0098628201850 0x825004c314100c28 0x8f75d98e38e01879 0x47baecc71c700c3c

def z814 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7e8fdff004ffe006 0xbf47eff8027ff003

def z815 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7e019ff000ffe000 0x3f00cff8007ff000

def z816 : W := mkw 0x00a0098428000000 0x805004c214000000 0x01df5a9e4f000000 0x00efad4f27800000

def z817 : W := mkw 0x30ac1fd428df4001 0x98560fea146fa000 0x7e4fdffe08ffe000 0x3f27efff047ff000

def z818 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x760edf7000fde000 0x3b076fb8007ef000

def z819 : W := mkw 0xd0f41ffdfe474001 0xe87a0ffeff23a000 0x01ffdfffff058000 0x00ffefffff82c000

def z820 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x00a09d6ff7000000 0x00504eb7fb800000

def z821 : W := mkw 0xe0f81ffdfe980001 0xf07c0ffeff4c0000 0x7fffdffffffd8000 0x3fffeffffffec000

def z822 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x01ffdb9e7f000000 0x00ffedcf3f800000

def z823 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x85ffffffff159667 0xc2ffffffff8acb33

def z824 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x08411a9e4b0a6000 0x04208d4f25853000

def z825 : W := mkw 0x342c165628b95851 0x1a160b2b145cac28 0xd17a067e3819f879 0x68bd033f1c0cfc3c

def z826 : W := mkw 0xf0fc1ffdfe994001 0xf87e0ffeff4ca000 0x77ffdfffff1de000 0x3bffefffff8ef000

def z827 : W := mkw 0x300c165000994001 0x18060b28004ca000 0x7e0fdf7000fde000 0x3f07efb8007ef000

def z828 : W := mkw 0xa0e81fdd6a980001 0xd0740feeb54c0000 0x1e43de9e4bf80000 0x0f21ef4f25fc0000

def z829 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x77ffdffffff58000 0x3bffeffffffac000

def z830 : W := mkw 0x40b009f4be000000 0xa05804fa5f000000 0x017c01fe3f000000 0x00be00ff1f800000

def z831 : W := mkw 0x300c000000df4000 0x18060000006fa000 0x7e00856000ffe000 0x3f0042b0007ff000

def z832 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x1fffdffffffd8000 0x0fffeffffffec000

def z833 : W := mkw 0x4211002094008224 0x210880104a004112 0x04a0a561b4159666 0x825052b0da0acb33

def z834 : W := mkw 0x98c609db40675d00 0xcc6304eda033ae80 0xe0fc21ffc007ff80 0xf07e10ffe003ffc0

def z835 : W := mkw 0x0080098000460000 0x804004c000230000 0x7e0fdff000ffe000 0x3f07eff8007ff000

def z836 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x7bffdfffffea6000 0x3dffeffffff53000

def z837 : W := mkw 0x40b009f4be000000 0xa05804fa5f000000 0x014d19fe3f000000 0x00a68cff1f800000

def z838 : W := mkw 0x000080000100208a 0x0000400000801045 0x7b4f42904f0a699f 0x3da7a148278534cf

def z839 : W := mkw 0x42b109f4be008224 0xa15884fa5f004112 0xe77dd9fe3f059067 0x73beecff1f82c833

def z840 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xdefbfe6fc0f99f80 0xef7dff37e07ccfc0

def z841 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xffdfdff04fffe007 0xffefeff827fff003

def z842 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xaf75db9e7be61879 0x57baedcf3df30c3c

def z843 : W := mkw 0x300c165000df4001 0x18060b28006fa000 0x540a067000fde000 0x2a050338007ef000

def z844 : W := mkw 0x4211002094008224 0x210880104a004112 0xf78e2561b4159667 0xfbc712b0da0acb33

def z845 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0xf3ffdfffff058067 0xf9ffefffff82c033

def z846 : W := mkw 0x000080000100208a 0x0000400000801045 0x69df42904f0a699f 0x34efa148278534cf

def z847 : W := mkw 0x308c09d000df4000 0x984604e8006fa000 0x7e0ec5f000ffe000 0x3f0762f8007ff000

def z848 : W := mkw 0xc0f01ffdfe460001 0xe0780ffeff230000 0x7fffdfffffee6000 0x3fffeffffff73000

def z849 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7e4fdff040ffe980 0x3f27eff8207ff4c0

def z850 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01209d6fbf000000 0x00904eb7df800000

def z851 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xaf45198e38e61879 0x57a28cc71c730c3c

def z852 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xaf75db8e78ee19f9 0x57baedc73c770cfc

def z853 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x81ffffffff001600 0xc0ffffffff800b00

def z854 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x00f11a9fcb000000 0x00788d4fe5800000

def z855 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x00fbdeffcf000000 0x007def7fe7800000

def z856 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xffdfdff044ffe987 0xffefeff8227ff4c3

def z857 : W := mkw 0xb0ec1fdd6adf4001 0xd8760feeb56fa000 0x7effdfffcbffe000 0x3f7fefffe5fff000

def z858 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x00c0000fcf000000 0x00600007e7800000

def z859 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x00209f7ff3000000 0x00104fbff9800000

def z860 : W := mkw 0x46b109a6bc669a74 0xa35884d35e334d3a 0x58cb3cef8cf38e1e 0xac659e77c679c70f

def z861 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x11ffffffff100600 0x88ffffffff880300

def z862 : W := mkw 0x4211002094008224 0x210880104a004112 0xf7fee561bc159e7f 0xfbff72b0de0acf3f

def z863 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x55ffdffffffde000 0x2affeffffffef000

def z864 : W := mkw 0x4211002094008224 0x210880104a004112 0xf7bee771b41df667 0xfbdf73b8da0efb33

def z865 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x2fffdfffffee6000 0x17ffeffffff73000

def z866 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xaf7fddee38e61879 0x57bfeef71c730c3c

def z867 : W := mkw 0x80e01f8d68000001 0xc0700fc6b4000000 0x01ffdf9fff000000 0x00ffefcfff800000

def z868 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x0120000fbf000000 0x00900007df800000

def z869 : W := mkw 0xc070167dfe000001 0x60380b3eff000000 0x01fbde7fff000000 0x00fdef3fff800000

def z870 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xfffffe9fcffa7f80 0xffffff4fe7fd3fc0

def z871 : W := mkw 0x82e11fdd6a008225 0xc1708feeb5004112 0xf6413a9e4b159667 0xfb209d4f258acb33

def z872 : W := mkw 0x04008002016638da 0x0200400100b31c6d 0xffbec10034ee79ff 0xffdf60801a773cff

def z873 : W := mkw 0x300c165000df4001 0x18060b28006fa000 0x7e0ec77000ffe000 0x3f0763b8007ff000

def z874 : W := mkw 0xf4fc1ffdfedf4051 0xfa7e0ffeff6fa028 0x7fffdfffffffe079 0x3fffeffffffff03c

def z875 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01fc9dffff000000 0x00fe4effff800000

def z876 : W := mkw 0x4211002094008224 0x210880104a004112 0x6420a561b0159667 0x321052b0d80acb33

def z877 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0xf7fefd6fff159667 0xfbff7eb7ff8acb33

def z878 : W := mkw 0x14a409d628675850 0x8a5204eb1433ac28 0xe17c01fe3807f879 0x70be00ff1c03fc3c

def z879 : W := mkw 0x30ac1fd428df4001 0x98560fea146fa000 0xff7fdffe38fff061 0x7fbfefff1c7ff830

def z880 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x01ffc7ffff000000 0x00ffe3ffff800000

def z881 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9ff3fe0fc4f81f87 0xcff9ff07e27c0fc3

def z882 : W := mkw 0xc070167dfe000001 0x60380b3eff000000 0x00aa067ff7000000 0x0055033ffb800000

def z883 : W := mkw 0x00a089842900208a 0x805044c214801045 0xfb75d98e380a699f 0xfdbaecc71c0534cf

def z884 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x0fffdfffffe00000 0x07ffeffffff00000

def z885 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x65ffffffff159667 0x32ffffffff8acb33

def z886 : W := mkw 0x8040160940000001 0x40200b04a0000000 0x00411a9e4b000000 0x00208d4f25800000

def z887 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7f3fdff030ffe000 0x3f9feff8187ff000

def z888 : W := mkw 0xc0f009adfe000000 0xe07804d6ff000000 0x01ffdb9fff000000 0x00ffedcfff800000

def z889 : W := mkw 0xb0cc1fd940df4001 0xd8660feca06fa000 0xfeffdfffc0ffe980 0xff7fefffe07ff4c0

def z890 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xbf77db8e38ee1879 0x5fbbedc71c770c3c

def z891 : W := mkw 0x0802800201203d8a 0x0401400100901ec5 0x8000200000001f9f 0xc000100000000fcf

def z892 : W := mkw 0xc0500029d6000000 0x60280014eb000000 0x00f0000fc7000000 0x00780007e3800000

def z893 : W := mkw 0x8842000b40201d00 0x44210005a0100e80 0x9ef3fc0fc0f01f80 0xcf79fe07e0780fc0

def z894 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0xfffffffffffff600 0xfffffffffffffb00

def z895 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x652cbdffbf159667 0x32965effdf8acb33

def z896 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x0071da9e4b000000 0x0038ed4f25800000

def z897 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x98f33e0fc0f81f80 0xcc799f07e07c0fc0

def z898 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x08c13a0fc0e80f80 0x84609d07e07407c0

def z899 : W := mkw 0x308c1fd000994001 0x98460fe8004ca000 0x5e0fdff000f9e000 0x2f07eff8007cf000

def z900 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x0c009d6000ffe000 0x06004eb0007ff000

def z901 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7f0fdff030ffe061 0x3f87eff8187ff030

def z902 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0xab555a9e4b020819 0x55aaad4f2581040c

def z903 : W := mkw 0xa84a960b41b83d8b 0x54254b05a0dc1ec5 0x652cbc9f8ff2761f 0x32965e4fc7f93b0f

def z904 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x55ffffffff159666 0xaaffffffff8acb33

def z905 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0xf7ffdfffff158007 0xfbffefffff8ac003

def z906 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x0cf3fe0fc0f81f80 0x0679ff07e07c0fc0

def z907 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0xffffffffff1ff667 0xffffffffff8ffb33

def z908 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x85f0bd6fff159667 0xc2f85eb7ff8acb33

def z909 : W := mkw 0xc2511629d4008225 0x61288b14ea004112 0xf7ffffffff159667 0xfbffffffff8acb33

def z910 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0xe7ffdfffff059067 0x73ffefffff82c833

def z911 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0xa775db9e7b041061 0x53baedcf3d820830

def z912 : W := mkw 0x4211002094008224 0x210880104a004112 0x5420a561b0159666 0xaa1052b0d80acb33

def z913 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x81ffdfffff001061 0x40ffefffff800830

def z914 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xaff5d98e3ce6187f 0xd7faecc71e730c3f

def z915 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x77ffdfffff158067 0x3bffefffff8ac033

def z916 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x8ef1fa0fc0e81f80 0xc778fd07e0740fc0

def z917 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x05ffffffff101600 0x02ffffffff880b00

def z918 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9e71fc0f80f81f80 0xcf38fe07c07c0fc0

def z919 : W := mkw 0x8060000d6a000000 0x40300006b5000000 0x00f0000fcb000000 0x00780007e5800000

def z920 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7e03df6000ffe000 0x3f01efb0007ff000

def z921 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x016d9fffff000000 0x00b6cfffff800000

def z922 : W := mkw 0x4211002094008224 0x210880104a004112 0x772ee561b4159667 0x3b9772b0da0acb33

def z923 : W := mkw 0xac4a160b40b81d51 0x56250b05a05c0ea8 0x9ef3fe0fc0f81ff9 0xcf79ff07e07c0ffc

def z924 : W := mkw 0x4211002094008224 0x210880104a004112 0x8420a561b0159667 0xc21052b0d80acb33

def z925 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x08011ef000fbe000 0x04008f78007df000

def z926 : W := mkw 0x46b189a4bd46a2fe 0xa358c4d25ea3517f 0x610c01f03f07e07f 0x308600f81f83f03f

def z927 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0xfbffdfffff02081f 0xfdffefffff81040f

def z928 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x7bff429fff0a6000 0x3dffa14fff853000

def z929 : W := mkw 0x4211002094008224 0x210880104a004112 0xffbffd61b4f59667 0xffdffeb0da7acb33

def z930 : W := mkw 0x000080000100208a 0x0000400000801045 0xfbdf46f04f1be99f 0xfdefa378278df4cf

def z931 : W := mkw 0xc0f009fdfe000000 0xe07804feff000000 0x014c01fe7f000000 0x00a600ff3f800000

def z932 : W := mkw 0xb84e165b40b95d01 0x5c270b2da05cae80 0xfefffeffc0fbff80 0xff7fff7fe07dffc0

def z933 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9ec33e0fc0f81f80 0xcf619f07e07c0fc0

def z934 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x81f0200fff001600 0xc0f81007ff800b00

def z935 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x64009d6000f7e000 0x32004eb0007bf000

def z936 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0xffffdffffffff061 0x7fffeffffffff830

def z937 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xffdfdff048ffe999 0xffefeff8247ff4cc

def z938 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xffffdb9e7fee7879 0x7fffedcf3ff73c3c

def z939 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x18f3fe0fc0f80f80 0x8c79ff07e07c07c0

def z940 : W := mkw 0x4211002094008224 0x210880104a004112 0x76aee561b4159666 0xbb5772b0da0acb33

def z941 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x01f0856fff000000 0x00f842b7ff800000

def z942 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x2575d98e38e61079 0x12baecc71c73083c

def z943 : W := mkw 0x804096094100208b 0x40204b04a0801045 0xfaf3de0fc00a699f 0xfd79ef07e00534cf

def z944 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xfe0ffff000fff600 0xff07fff8007ffb00

def z945 : W := mkw 0x300c165000df4001 0x18060b28006fa000 0x7e00046000ffe000 0x3f000230007ff000

def z946 : W := mkw 0x04008002016638da 0x0200400100b31c6d 0xae00000000e619ff 0xd700000000730cff

def z947 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x41ffdfffff018006 0x20ffefffff80c003

def z948 : W := mkw 0x90e41fdd6a474001 0xc8720feeb523a000 0x00411a9e4b026000 0x00208d4f25813000

def z949 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7a0f5ef000fbe000 0x3d07af78007df000

def z950 : W := mkw 0x30ac1fd428df4001 0x98560fea146fa000 0x7e2fdffe30ffe000 0x3f17efff187ff000

def z951 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xff7fdff038fff879 0x7fbfeff81c7ffc3c

def z952 : W := mkw 0x000080000100208a 0x0000400000801045 0xfbff42907f0a79ff 0xfdffa1483f853cff

def z953 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x48091af000ebe000 0x24048d780075f000

def z954 : W := mkw 0x348c1fd000df4051 0x9a460fe8006fa028 0x7e0fdff000ffe079 0x3f07eff8007ff03c

def z955 : W := mkw 0xe078162dfe980001 0x703c0b16ff4c0000 0x1ff3de0ffff80000 0x0ff9ef07fffc0000

def z956 : W := mkw 0xc0f009adfe000000 0xe07804d6ff000000 0x01f0990fff000000 0x00f84c87ff800000

def z957 : W := mkw 0x8040165942000001 0x40200b2ca1000000 0x00f3de1fc3000000 0x0079ef0fe1800000

def z958 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x09ffdfffff080980 0x04ffefffff8404c0

def z959 : W := mkw 0x34ac1fd428df4051 0x9a560fea146fa028 0xff3fdff038fff079 0x7f9feff81c7ff83c

def z960 : W := mkw 0x4211002094008224 0x210880104a004112 0xffbee561b41d9fe7 0xffdf72b0da0ecff3

def z961 : W := mkw 0x40b009a4bc000000 0xa05804d25e000000 0x01ffdfffff000000 0x00ffefffff800000

def z962 : W := mkw 0xd0f41ffdfe474001 0xe87a0ffeff23a000 0x7bffdfffff0fe000 0x3dffefffff87f000

def z963 : W := mkw 0xc4f009adfe460050 0xe27804d6ff230028 0x21f4018fff060079 0x10fa00c7ff83003c

def z964 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xaf7dd99e3fe61879 0x57beeccf1ff30c3c

def z965 : W := mkw 0x8040000940000000 0x40200004a0000000 0x01ff429fcf000000 0x00ffa14fe7800000

def z966 : W := mkw 0x0400000200661850 0x0200000100330c28 0xafdf42904fe61879 0x57efa14827f30c3c

def z967 : W := mkw 0x4211002094008224 0x210880104a004112 0xf7fffd6fb4159667 0xfbfffeb7da0acb33

def z968 : W := mkw 0xd2f51ffdfe47c225 0xe97a8ffeff23e112 0xf7ffffffff17f667 0xfbffffffff8bfb33

def z969 : W := mkw 0x4211002094008224 0x210880104a004112 0xd6bae561b4159666 0xeb5d72b0da0acb33

def z970 : W := mkw 0x308c9fd001df608b 0x98464fe800efb045 0x85d09d604ff5899f 0xc2e84eb027fac4cf

def z971 : W := mkw 0xa8ea1fdd6a980501 0xd4750feeb54c0280 0x00411a9e4b080180 0x00208d4f258400c0

def z972 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x77ffffffff158606 0xbbffffffff8ac303

def z973 : W := mkw 0xb0ec1fdd6adf4001 0xd8760feeb56fa000 0x7e0fdffe00ffe000 0x3f07efff007ff000

def z974 : W := mkw 0x4211002094008224 0x210880104a004112 0xf7ffe761f4159667 0xfbfff3b0fa0acb33

def z975 : W := mkw 0x280a960201b83d8b 0x14054b0100dc1ec5 0xfe0ffe9000fa7f9f 0xff07ff48007d3fcf

def z976 : W := mkw 0x8060000d6a000000 0x40300006b5000000 0x01df429e4f000000 0x00efa14f27800000

def z977 : W := mkw 0x4211002094008224 0x210880104a004112 0xffffe7f1ff179e7f 0xfffff3f8ff8bcf3f

def z978 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x5e0bdf7000fde000 0x2f05efb8007ef000

def z979 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x01ffffffff001660 0x00ffffffff800b30

def z980 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x0dffdfffffffe000 0x06ffeffffffff000

def z981 : W := mkw 0x80e01fdd6a460001 0xc0700feeb5230000 0x08411a9e4be20000 0x04208d4f25f10000

def z982 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0xfbffdfffff0a6819 0x7dffefffff85340c

def z983 : W := mkw 0xe0f81ffdfe980001 0xf07c0ffeff4c0000 0x9ffffffffff81600 0xcffffffffffc0b00

def z984 : W := mkw 0x2a0b800201b8bfae 0x1505c00100dc5fd7 0xfe00200000ffffff 0xff001000007fffff

def z985 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xa734d98e38e61079 0x539a6cc71c73083c

def z986 : W := mkw 0x84e01fdd6a460051 0xc2700feeb5230028 0x21451b9e7b060079 0x10a28dcf3d83003c

def z987 : W := mkw 0x8842000b40201d00 0x44210005a0100e80 0x9ef3fa0fc0e81f80 0xcf79fd07e0740fc0

def z988 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x59ffdffffffbe000 0x2cffeffffffdf000

def z989 : W := mkw 0x8060160d6a000001 0x40300b06b5000000 0x00411a0e4b000000 0x00208d0725800000

def z990 : W := mkw 0xc0f009fdfe000000 0xe07804feff000000 0x01ff43ffff000000 0x00ffa1ffff800000

def z991 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7e0a9f7000ffe000 0x3f054fb8007ff000

def z992 : W := mkw 0x0000000200201800 0x0000000100100c00 0x9ef3fe0fc0f81f80 0xcf79ff07e07c0fc0

def z993 : W := mkw 0xc8f21ffdfe000501 0xe4790ffeff000280 0x01ffffffff000780 0x80ffffffff8003c0

def z994 : W := mkw 0xb84e160b40b95d01 0x5c270b05a05cae80 0xdef3fe0fc0f9ff80 0xef79ff07e07cffc0

def z995 : W := mkw 0x04a009d628661850 0x825004eb14330c28 0xaf7dd9fe38e61879 0x57beecff1c730c3c

def z996 : W := mkw 0x280a000200b81d00 0x14050001005c0e80 0x9ef3fc0f80f81f80 0xcf79fe07c07c0fc0

def z997 : W := mkw 0xe8fa1ffdfe980501 0xf47d0ffeff4c0280 0x01ffffffff100600 0x00ffffffff880300

def z998 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x0c20bc0f80f81f80 0x06105e07c07c0fc0

def z999 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01f5ddefff000000 0x00faeef7ff800000

def z1000 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xfefffe0fc0f81f80 0xff7fff07e07c0fc0

def z1001 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x1ec3fe0fc0f80f80 0x8f61ff07e07c07c0

def z1002 : W := mkw 0x000080000100208a 0x0000400000801045 0xffffc2904f0a799f 0xffffe14827853ccf

def z1003 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x81f0000fff001061 0x40f80007ff800830

def z1004 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7e7fdffe00ffe000 0x3f3fefff007ff000

def z1005 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x09f11a9fffea6000 0x04f88d4ffff53000

def z1006 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xaf70990e38e61879 0x57b84c871c730c3c

def z1007 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x44089d7000f5e000 0x22044eb8007af000

def z1008 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x01fe400fff000000 0x00ff2007ff800000

def z1009 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xae61998e38e61879 0x5730ccc71c730c3c

def z1010 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x8420990e30e41879 0x42104c8718720c3c

def z1011 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x1ea3fe0fc0f81780 0x8f51ff07e07c0bc0

def z1012 : W := mkw 0x14a409d628675850 0x8a5204eb1433ac28 0xaf75d9ee38e79879 0x57baecf71c73cc3c

def z1013 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x65ffdffffff7e000 0x32ffeffffffbf000

def z1014 : W := mkw 0xc0f01ffdfe460001 0xe0780ffeff230000 0xafffdfffffe60819 0x57ffeffffff3040c

def z1015 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xab55598e38e60879 0x55aaacc71c73043c

def z1016 : W := mkw 0x388e1fd000df4501 0x9c470fe8006fa280 0x7e0ffff000ffe780 0xbf07fff8007ff3c0

def z1017 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x01f5408fff000000 0x00faa047ff800000

def z1018 : W := mkw 0x04a08986296638da 0x825044c314b31c6d 0x54aa9b1e77ec71e6 0xaa554d8f3bf638f3

def z1019 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x004b1efe4b000000 0x00258f7f25800000

def z1020 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x10823e0fc0f80780 0x88411f07e07c03c0

def z1021 : W := mkw 0x34ac1fd428df4051 0x9a560fea146fa028 0xff5fdff038ffe879 0x7fafeff81c7ff43c

def z1022 : W := mkw 0x4211002094008224 0x210880104a004112 0xffffe7f1ff1ff667 0xfffff3f8ff8ffb33

def z1023 : W := mkw 0xf2fd1ffdfedfc225 0xf97e8ffeff6fe112 0x7ffffffffffff660 0x3ffffffffffffb30

def z1024 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xbf75d98e38ee19f9 0xdfbaecc71c770cfc

def z1025 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xffbfdff034fff067 0xffdfeff81a7ff833

def z1026 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01fedd6fff000000 0x00ff6eb7ff800000

def z1027 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0xffffdfffffffe980 0xffffeffffffff4c0

def z1028 : W := mkw 0xf8fe1ffdfedf4501 0xfc7f0ffeff6fa280 0x7fffffffffffe780 0xbffffffffffff3c0

def z1029 : W := mkw 0x04a0098428460050 0x825004c214230028 0x2f75d98e38e60079 0x17baecc71c73003c

def z1030 : W := mkw 0x000080000100208a 0x0000400000801045 0xffdf42904f1fe99f 0xffefa148278ff4cf

def z1031 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xffffff0ff4fc1fe7 0xffffff87fa7e0ff3

def z1032 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xaf75ddee38f79879 0x57baeef71c7bcc3c

def z1033 : W := mkw 0x14a409d628675850 0x8a5204eb1433ac28 0xaf75d99e38e67879 0x57baeccf1c733c3c

def z1034 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xff7fd98e38e61879 0x7fbfecc71c730c3c

def z1035 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x0040180e4b000000 0x00200c0725800000

def z1036 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9e61be0fc0f81f80 0xcf30df07e07c0fc0

def z1037 : W := mkw 0xa84a165b42b81d01 0x54250b2da15c0e80 0x9ef3fe1fc3f81f80 0xcf79ff0fe1fc0fc0

def z1038 : W := mkw 0x340c800201ff78da 0x1a06400100ffbc6d 0xfe00000000fff9ff 0xff000000007ffcff

def z1039 : W := mkw 0x4211002094008224 0x210880104a004112 0xf62ee561b0159667 0xfb1772b0d80acb33

def z1040 : W := mkw 0xc2f109fdfe008224 0xe17884feff004112 0xe1fc21ffff059667 0xf0fe10ffff82cb33

def z1041 : W := mkw 0x4211002094008224 0x210880104a004112 0xf7bee771f7159667 0xfbdf73b8fb8acb33

def z1042 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0xf7ffdfffff159061 0x7bffefffff8ac830

def z1043 : W := mkw 0xb0ec1fdd6a994001 0xd8760feeb54ca000 0x00411a9e4b086000 0x00208d4f25843000

def z1044 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0xffffffffff179e7f 0xffffffffff8bcf3f

def z1045 : W := mkw 0x300c165000994001 0x18060b28004ca000 0x7e0fdef000fbe000 0x3f07ef78007df000

def z1046 : W := mkw 0xb0ec1fdd6adf4001 0xd8760feeb56fa000 0x00411a9e4be00000 0x00208d4f25f00000

def z1047 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9ff3fe0ff0f81fe1 0xcff9ff07f87c0ff0

def z1048 : W := mkw 0x40300024be000000 0x201800125f000000 0x0170000e3f000000 0x00b800071f800000

def z1049 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xfe0fdff000ffe980 0xff07eff8007ff4c0

def z1050 : W := mkw 0xc271167dfe008225 0x61388b3eff004112 0xd1fa267fff119667 0xe8fd133fff88cb33

def z1051 : W := mkw 0x4211002094008224 0x210880104a004112 0x55bee561b4159666 0xaadf72b0da0acb33

def z1052 : W := mkw 0xc0d01ff9d6000001 0xe0680ffceb000000 0x00ffdfffc7000000 0x007fefffe3800000

def z1053 : W := mkw 0xb0ec1fdd6adf4001 0xd8760feeb56fa000 0x7e411a9e4bffe000 0x3f208d4f25fff000

def z1054 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x73ffdfffff000000 0x39ffefffff800000

def z1055 : W := mkw 0xc070162dfe000001 0x60380b16ff000000 0x01ffde9fff000000 0x00ffef4fff800000

def z1056 : W := mkw 0xc0501629d4000001 0x60280b14ea000000 0x01ffdfffff000000 0x00ffefffff800000

def z1057 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x0420be0fc0f81780 0x02105f07e07c0bc0

def z1058 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x1bffdfffff080000 0x0dffefffff840000

def z1059 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xffffddee3cf7987f 0xffffeef71e7bcc3f

def z1060 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x08011bf000efe000 0x04008df80077f000

def z1061 : W := mkw 0xc6f11ffdfe468275 0xe3788ffeff23413a 0xf7ffffffff17967f 0xfbffffffff8bcb3f

def z1062 : W := mkw 0xc2f109fdfe008224 0xe17884feff004112 0xf7fee5ffff159667 0xfbff72ffff8acb33

def z1063 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x0000189e0b000000 0x00000c4f05800000

def z1064 : W := mkw 0xc0501679d6000001 0x60280b3ceb000000 0x01ffdf7ff7000000 0x00ffefbffb800000

def z1065 : W := mkw 0x4211002094008224 0x210880104a004112 0xf6aaa561b4159667 0xfb5552b0da0acb33

def z1066 : W := mkw 0x4211002094008224 0x210880104a004112 0x85bee561b4159667 0xc2df72b0da0acb33

def z1067 : W := mkw 0xc0f009fdfe000000 0xe07804feff000000 0x01f0016fff000000 0x00f800b7ff800000

def z1068 : W := mkw 0x40b009f4be000000 0xa05804fa5f000000 0x012c99fe3f000000 0x00964cff1f800000

def z1069 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x08613a0fc0e81f80 0x04309d07e0740fc0

def z1070 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x97ffffffff101667 0xcbffffffff880b33

def z1071 : W := mkw 0xb0ec1fdd6adf4001 0xd8760feeb56fa000 0x1ef3de9fcbfa6000 0x0f79ef4fe5fd3000

def z1072 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9ef3ff0ff0fc1fe0 0xcf79ff87f87e0ff0

def z1073 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9ef0bc0fc0f81f80 0xcf785e07e07c0fc0

def z1074 : W := mkw 0x0420000628201850 0x0210000314100c28 0xaf75d90e38e41879 0x57baec871c720c3c

def z1075 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xaff5f98fb8e61e79 0xd7fafcc7dc730f3c

def z1076 : W := mkw 0xc271002dfe008224 0x61388016ff004112 0x01f0200fff001660 0x00f81007ff800b30

def z1077 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0xa3ffdfffff000001 0x51ffefffff800000

def z1078 : W := mkw 0x4211002094008224 0x210880104a004112 0xf7fee561ff159667 0xfbff72b0ff8acb33

def z1079 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x01451b9e7b000000 0x00a28dcf3d800000

def z1080 : W := mkw 0xc0f01ffdfe460001 0xe0780ffeff230000 0xafffdfffffe61061 0x57ffeffffff30830

def z1081 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x01f4c10fff000000 0x00fa6087ff800000

def z1082 : W := mkw 0xb0ec1fdd6adf4001 0xd8760feeb56fa000 0x04009d6e00f58000 0x02004eb7007ac000

def z1083 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x27ffdfffff040000 0x13ffefffff820000

def z1084 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0xf7beff7ff7159667 0xfbdf7fbffb8acb33

def z1085 : W := mkw 0xb0cc1fd940df4001 0xd8660feca06fa000 0x7e2fdfff80ffe000 0x3f17efffc07ff000

def z1086 : W := mkw 0xc872002dfe000500 0x64390016ff000280 0x01f0200fff000780 0x80f81007ff8003c0

def z1087 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x97f2e40fff101600 0xcbf97207ff880b00

def z1088 : W := mkw 0xf0dc1ff9d6df4001 0xf86e0ffceb6fa000 0x7effdfffc7ffe000 0x3f7fefffe3fff000

def z1089 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7a0f5bf000efe000 0x3d07adf80077f000

def z1090 : W := mkw 0x30ac1fd42adf4001 0x98560fea156fa000 0x7e0fdff00bffe000 0x3f07eff805fff000

def z1091 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x54aa9f7ff7fde000 0x2a554fbffbfef000

def z1092 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0xf3ffffffff118607 0xf9ffffffff88c303

def z1093 : W := mkw 0xc2f11ffdfe468225 0xe1788ffeff234112 0xfffffffffff79667 0xfffffffffffbcb33

def z1094 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01f19fffff000000 0x00f8cfffff800000

def z1095 : W := mkw 0xc4f01ffdfe000051 0xe2780ffeff000028 0x01ffdfffff000079 0x00ffefffff80003c

def z1096 : W := mkw 0x300c165000994001 0x18060b28004ca000 0x5e0a067000f9e000 0x2f050338007cf000

def z1097 : W := mkw 0x280a800201b83d8a 0x1405400100dc1ec5 0xde00200000f87f86 0xef001000007c3fc3

def z1098 : W := mkw 0xa84a165b40b81d01 0x54250b2da05c0e80 0x9efbfe7fc0f81f80 0xcf7dff3fe07c0fc0

def z1099 : W := mkw 0x000080000100208a 0x0000400000801045 0xfbffc3907f0a699f 0xfdffe1c83f8534cf

def z1100 : W := mkw 0xb0ec1fdd6adf4001 0xd8760feeb56fa000 0x2f75db9e7bee6000 0x17baedcf3df73000

def z1101 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xff1fdff000ffe001 0x7f8feff8007ff000

def z1102 : W := mkw 0x308c09d000df4000 0x984604e8006fa000 0x7e00016000ffe000 0x3f0000b0007ff000

def z1103 : W := mkw 0x280a800201b83d8a 0x1405400100dc1ec5 0xfa00000000ea699f 0xfd000000007534cf

def z1104 : W := mkw 0x280a800201b83d8a 0x1405400100dc1ec5 0x9e00200000fa7f98 0xcf001000007d3fcc

def z1105 : W := mkw 0x04808982016638da 0x824044c100b31c6d 0xfe0fdb9000ee79ff 0xff07edc800773cff

def z1106 : W := mkw 0xb0ec1fdd6adf4001 0xd8760feeb56fa000 0x04419ffe4bf58000 0x0220cfff25fac000

def z1107 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7e0e07f000ffe000 0x3f0703f8007ff000

def z1108 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x61ffdfffff000007 0x30ffefffff800003

def z1109 : W := mkw 0x00a0098428000000 0x805004c214000000 0x01f5d98e7f000000 0x00faecc73f800000

def z1110 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0xf7ffffffff159600 0xfbffffffff8acb00

def z1111 : W := mkw 0xe0f81ffdfe980001 0xf07c0ffeff4c0000 0x05ffdffffff00000 0x02ffeffffff80000

def z1112 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x01f1029fff000000 0x00f8814fff800000

def z1113 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xfe0fdff000ffe819 0x7f07eff8007ff40c

def z1114 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x600c19f000e7e000 0x30060cf80073f000

def z1115 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x61ffdfffff026000 0x30ffefffff813000

def z1116 : W := mkw 0x4211002094008224 0x210880104a004112 0xffbfe5e1b4179667 0xffdff2f0da0bcb33

def z1117 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01fa9f7fff000000 0x00fd4fbfff800000

def z1118 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x00419ffe4b000000 0x0020cfff25800000

def z1119 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x014fdffe7f000000 0x00a7efff3f800000

def z1120 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x09ffdfffff0a6000 0x04ffefffff853000

def z1121 : W := mkw 0xd4f41ffdfe474051 0xea7a0ffeff23a028 0x61ffdfffff07e079 0x30ffefffff83f03c

def z1122 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x0420998e38e61078 0x02104cc71c73083c

def z1123 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xfef3fe0fc0fa7f80 0xff79ff07e07d3fc0

def z1124 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xa975198e38e61879 0x54ba8cc71c730c3c

def z1125 : W := mkw 0xd0f41ffdfe474001 0xe87a0ffeff23a000 0x01ffdfffff026000 0x00ffefffff813000

def z1126 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x694d1bfe7fefe000 0x34a68dff3ff7f000

def z1127 : W := mkw 0xa048160940980001 0x50240b04a04c0000 0x1e43de0e40f80000 0x0f21ef07207c0000

def z1128 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x01fa021fff000000 0x00fd010fff800000

def z1129 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7e8fdff040ffe180 0xbf47eff8207ff0c0

def z1130 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x8170180e38e01879 0x40b80c071c700c3c

def z1131 : W := mkw 0xe8fa1ffdfe980501 0xf47d0ffeff4c0280 0x1ffffffffff80780 0x8ffffffffffc03c0

def z1132 : W := mkw 0x000080000100208a 0x0000400000801045 0xfb8e02904f0a699f 0xfdc70148278534cf

def z1133 : W := mkw 0x0000000200201800 0x0000000100100c00 0xaf75d98e38e61879 0x57baecc71c730c3c

def z1134 : W := mkw 0xc271002dfe008224 0x61388016ff004112 0x05f0a56fff159660 0x02f852b7ff8acb30

def z1135 : W := mkw 0x80e0098d6a000000 0xc07004c6b5000000 0x0041188e4b000000 0x00208c4725800000

def z1136 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01ae9fffff000000 0x00d74fffff800000

def z1137 : W := mkw 0xc0501679d6000001 0x60280b3ceb000000 0x00aa9e7fc7000000 0x00554f3fe3800000

def z1138 : W := mkw 0x4211002094008224 0x210880104a004112 0x65bee561b4159667 0x32df72b0da0acb33

def z1139 : W := mkw 0x44b009f6be661850 0xa25804fb5f330c28 0xaf0c01f03fe61879 0x578600f81ff30c3c

def z1140 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7e2fdff030fff060 0x3f17eff8187ff830

def z1141 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xbff7ff8ff8fe1ff9 0xdffbffc7fc7f0ffc

def z1142 : W := mkw 0xc070162dfe000001 0x60380b16ff000000 0x01f09c0fff000000 0x00f84e07ff800000

def z1143 : W := mkw 0xe87a162dfe980501 0x743d0b16ff4c0280 0x11f2260fff180780 0x88f91307ff8c03c0

def z1144 : W := mkw 0x108409d000474000 0x884204e80023a000 0x6e0c01f000e7e000 0x370600f80073f000

def z1145 : W := mkw 0x40b009a4be000000 0xa05804d25f000000 0x0175d98e3f000000 0x00baecc71f800000

def z1146 : W := mkw 0x300c165000df4001 0x18060b28006fa000 0x7e0bde7000ffe000 0x3f05ef38007ff000

def z1147 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x00289d7fb7000000 0x00144ebfdb800000

def z1148 : W := mkw 0x10a409d42a474000 0x885204ea1523a000 0x600c01f00b07e000 0x300600f80583f000

def z1149 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x88f3fe0fc0e81f80 0xc479ff07e0740fc0

def z1150 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x0841198e38e60878 0x04208cc71c73043c

def z1151 : W := mkw 0x000080000100208a 0x0000400000801045 0xffdf62904f1a7f9f 0xffefb148278d3fcf

def z1152 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x014d1a9e4f000000 0x00a68d4f27800000

def z1153 : W := mkw 0x0400000200201850 0x0200000100100c28 0x8130000030001879 0x4098000018000c3c

def z1154 : W := mkw 0x4211002094008224 0x210880104a004112 0x75aea561b4159667 0xbad752b0da0acb33

def z1155 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xaff7db8e78e61879 0x57fbedc73c730c3c

def z1156 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x54009d6000fde000 0x2a004eb0007ef000

def z1157 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x0175dffffb000000 0x00baeffffd800000

def z1158 : W := mkw 0x8040160940000001 0x40200b04a0000000 0x00fbde1fc7000000 0x007def0fe3800000

def z1159 : W := mkw 0x0420000628201850 0x0210000314100c28 0xaf75d88e38e21879 0x57baec471c710c3c

def z1160 : W := mkw 0xc2f109adfe008224 0xe17884d6ff004112 0xf7fffdefff159667 0xfbfffef7ff8acb33

def z1161 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xae71d90e30e61879 0x5738ec8718730c3c

def z1162 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xfffffe9fcff81f87 0xffffff4fe7fc0fc3

def z1163 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x96b2fe0fc0f81780 0xcb597f07e07c0bc0

def z1164 : W := mkw 0x2c0a800201fe3dda 0x1605400100ff1eed 0xfe00200000fe7fff 0xff001000007f3fff

def z1165 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x84f3fe0fc0f01f80 0xc279ff07e0780fc0

def z1166 : W := mkw 0x90e41fdd6a474001 0xc8720feeb523a000 0x604d1bfe4b07e000 0x30268dff2583f000

def z1167 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x0d75d98e38e61878 0x06baecc71c730c3c

def z1168 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xbef3fe0fc0fc1fe1 0xdf79ff07e07e0ff0

def z1169 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x0043de9e4b000000 0x0021ef4f25800000

def z1170 : W := mkw 0xc4f01ffdfe460051 0xe2780ffeff230028 0xa7ffdfffff061079 0x53ffefffff83083c

def z1171 : W := mkw 0xc070167dfe000001 0x60380b3eff000000 0x01ff46ffff000000 0x00ffa37fff800000

def z1172 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7f0fdff004ffe007 0x3f87eff8027ff003

def z1173 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9af37a0fc0e81f80 0xcd79bd07e0740fc0

def z1174 : W := mkw 0x000080020120388a 0x0000400100901c45 0xfe00000000ea799f 0xff00000000753ccf

def z1175 : W := mkw 0x000080000100208a 0x0000400000801045 0xfbffc691cf0a699f 0xfdffe348e78534cf

def z1176 : W := mkw 0xc0501679d6000001 0x60280b3ceb000000 0x00cb1e7fc7000000 0x00658f3fe3800000

def z1177 : W := mkw 0xb8ce1fd940df4501 0xdc670feca06fa280 0xfedffff1c0ffef80 0xff6ffff8e07ff7c0

def z1178 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01ff5a9fff000000 0x00ffad4fff800000

def z1179 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x01ffdfffff058060 0x00ffefffff82c030

def z1180 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xaff7dd8fb8e61879 0x57fbeec7dc730c3c

def z1181 : W := mkw 0x14a409d628675850 0x8a5204eb1433ac28 0xff7fddfe38f7f879 0x7fbfeeff1c7bfc3c

def z1182 : W := mkw 0x4211002094008224 0x210880104a004112 0xf1be2561b4159667 0xf8df12b0da0acb33

def z1183 : W := mkw 0x8842000b40201d00 0x44210005a0100e80 0x84f0b80fc0e01f80 0xc2785c07e0700fc0

def z1184 : W := mkw 0xb8ce1fd940df4501 0xdc670feca06fa280 0xfebffff1c0fff780 0xff5ffff8e07ffbc0

def z1185 : W := mkw 0xc470002dfe000050 0x62380016ff000028 0x01f0000fff000079 0x00f80007ff80003c

def z1186 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x8f71d90e38e41879 0x47b8ec871c720c3c

def z1187 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xafffd98e3ce61879 0x57ffecc71e730c3c

def z1188 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x0c0fdff000ffe000 0x0607eff8007ff000

def z1189 : W := mkw 0x280a800201b83d8a 0x1405400100dc1ec5 0xffbee40184fa7f9f 0xffdf7200c27d3fcf

def z1190 : W := mkw 0xb84e165b40b95d01 0x5c270b2da05cae80 0xd0fa267fc019ff80 0xe87d133fe00cffc0

def z1191 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x14f3fe0fc0f81780 0x8a79ff07e07c0bc0

def z1192 : W := mkw 0x0020000428000000 0x0010000214000000 0x01ff429e7f000000 0x00ffa14f3f800000

def z1193 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xa574998e38e61879 0x52ba4cc71c730c3c

def z1194 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x580fdff000fbe000 0x2c07eff8007df000

def z1195 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x71ffdfffff1fe000 0x38ffefffff8ff000

def z1196 : W := mkw 0x34ac1fd428df4051 0x9a560fea146fa028 0x7e0fdff030ffe060 0x3f07eff8187ff030

def z1197 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x7a4f5a9e4b0a6000 0x3d27ad4f25853000

def z1198 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x2f25d98e38e61079 0x1792ecc71c73083c

def z1199 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x8bffdfffff000800 0x45ffefffff800400

def z1200 : W := mkw 0x8040160940000001 0x40200b04a0000000 0x01df5a9e4f000000 0x00efad4f27800000

def z1201 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x5e0bdef000fbe000 0x2f05ef78007df000

def z1202 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x2e05dff000ffe000 0x1702eff8007ff000

def z1203 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xffffff6fc4fd9f87 0xffffffb7e27ecfc3

def z1204 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xff75d98e38f79879 0x7fbaecc71c7bcc3c

def z1205 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7e8ffff180ffe600 0xbf47fff8c07ff300

def z1206 : W := mkw 0xd0f409fdfe474000 0xe87a04feff23a000 0x61fc01ffff07e000 0x30fe00ffff83f000

def z1207 : W := mkw 0x4211002094008224 0x210880104a004112 0xffffe7f1f41fffe7 0xfffff3f8fa0ffff3

def z1208 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9e23fe0f80f81f80 0xcf11ff07c07c0fc0

def z1209 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x51ffdfffff118000 0x28ffefffff88c000

def z1210 : W := mkw 0xa84a000b40b81d00 0x54250005a05c0e80 0x9ef1f80fc0f81f80 0xcf78fc07e07c0fc0

def z1211 : W := mkw 0xc4f01ffdfe460051 0xe2780ffeff230028 0x01ffdfffff020018 0x00ffefffff81000c

def z1212 : W := mkw 0x50b409f4be474000 0xa85a04fa5f23a000 0x6f7dd9fe3fe7e000 0x37beecff1ff3f000

def z1213 : W := mkw 0x000080000100208a 0x0000400000801045 0xffffe7f1cf1fff9f 0xfffff3f8e78fffcf

def z1214 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9ff3fe0fc8f81f99 0xcff9ff07e47c0fcc

def z1215 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0xafffdfffff061879 0x57ffefffff830c3c

def z1216 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xbfffdb9e7fee19f9 0xdfffedcf3ff70cfc

def z1217 : W := mkw 0x060180020166bafe 0x0300c00100b35d7f 0xfe00200000ffffff 0xff001000007fffff

def z1218 : W := mkw 0xf0fc1ffdfe994001 0xf87e0ffeff4ca000 0x01ffdfffff118000 0x00ffefffff88c000

def z1219 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x58cb1effcffbe000 0x2c658f7fe7fdf000

def z1220 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xfffffdefb8f79e79 0xfffffef7dc7bcf3c

def z1221 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x00001a1e43000000 0x00000d0f21800000

def z1222 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x00619e9fcb000000 0x0030cf4fe5800000

def z1223 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xffdfdff04fffe980 0xffefeff827fff4c0

def z1224 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x6e0ddbf000efe000 0x3706edf80077f000

def z1225 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9efbfe1fc7f81f80 0xcf7dff0fe3fc0fc0

def z1226 : W := mkw 0xb0cc1fd940df4001 0xd8660feca06fa000 0xfeffffffc0fff600 0xff7fffffe07ffb00

def z1227 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x05ffdfffff158000 0x02ffefffff8ac000

def z1228 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01bedf7ff7000000 0x00df6fbffb800000

def z1229 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x77ffffffff159660 0x3bffffffff8acb30

def z1230 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x640fdff000f7e000 0x3207eff8007bf000

def z1231 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9ea2be0fc0f81f80 0xcf515f07e07c0fc0

def z1232 : W := mkw 0xc0f01ffdfe460001 0xe0780ffeff230000 0x09ffdfffffe20000 0x04ffeffffff10000

def z1233 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x004f5a9e4b000000 0x0027ad4f25800000

def z1234 : W := mkw 0xc0f009fdfe000000 0xe07804feff000000 0x01fdd9ffff000000 0x00feecffff800000

def z1235 : W := mkw 0xc2511679d6008225 0x61288b3ceb004112 0xd6fbfe7fc7119606 0xeb7dff3fe388cb03

def z1236 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9ef3ff6fc0fd9f80 0xcf79ffb7e07ecfc0

def z1237 : W := mkw 0xe0f81ffdfe980001 0xf07c0ffeff4c0000 0x7fffdffffffa6000 0x3fffeffffffd3000

def z1238 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01f3df6fff000000 0x00f9efb7ff800000

def z1239 : W := mkw 0xc070167dfe000001 0x60380b3eff000000 0x01f0046fff000000 0x00f80237ff800000

def z1240 : W := mkw 0x300c165000df4001 0x18060b28006fa000 0x7e0f46f000ffe000 0x3f07a378007ff000

def z1241 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x010c19fe3f000000 0x00860cff1f800000

def z1242 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9eb2fc0f80f81f80 0xcf597e07c07c0fc0

def z1243 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7f9fdff004ffe000 0x3fcfeff8027ff000

def z1244 : W := mkw 0xb4ec1fdf6aff5851 0xda760fefb57fac28 0xff7fdffe7bfff879 0x7fbfefff3dfffc3c

def z1245 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x8575d98e38e41879 0x42baecc71c720c3c

def z1246 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x00c31e9fcb000000 0x00618f4fe5800000

def z1247 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x1fffdffffffa6000 0x0fffeffffffd3000

def z1248 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0xa7ffffffff159661 0x53ffffffff8acb30

def z1249 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01f0180fff000000 0x00f80c07ff800000

def z1250 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xffffff6ff0fd9fe1 0xffffffb7f87ecff0

def z1251 : W := mkw 0xc0f009adfe000000 0xe07804d6ff000000 0x01f4018fff000000 0x00fa00c7ff800000

def z1252 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x09ffdfffff020818 0x04ffefffff81040c

def z1253 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x21ffdfffff020019 0x10ffefffff81000c

def z1254 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x01f3420fff000000 0x00f9a107ff800000

def z1255 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7f0fdff008ffe019 0x3f87eff8047ff00c

def z1256 : W := mkw 0x04008002012038da 0x0200400100901c6d 0x80000000000019ff 0xc000000000000cff

def z1257 : W := mkw 0xb8ce1fd940df4501 0xdc670feca06fa280 0x7e0ffff180ffe600 0x3f07fff8c07ff300

def z1258 : W := mkw 0x42b109a4bc008224 0xa15884d25e004112 0xf7ffffffff159667 0xfbffffffff8acb33

def z1259 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x00411effcb000000 0x00208f7fe5800000

def z1260 : W := mkw 0x4211002094008224 0x210880104a004112 0xf7fee561f4159fe7 0xfbff72b0fa0acff3

def z1261 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x00411bfe7b000000 0x00208dff3d800000

def z1262 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x00209dffbb000000 0x00104effdd800000

def z1263 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x1ce3be0fc0f81f80 0x8e71df07e07c0fc0

def z1264 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x8f71d88e38e21879 0x47b8ec471c710c3c

def z1265 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x7f4fdffe7fffe000 0x3fa7efff3ffff000

def z1266 : W := mkw 0xc0f009adfe460000 0xe07804d6ff230000 0x2ff5d98fffe60000 0x17faecc7fff30000

def z1267 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xfffffd8fbcf61e7f 0xfffffec7de7b0f3f

def z1268 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x017ddbfe7f000000 0x00beedff3f800000

def z1269 : W := mkw 0x300c000000df4000 0x18060000006fa000 0x7e0c016000ffe000 0x3f0600b0007ff000

def z1270 : W := mkw 0x8040160940000001 0x40200b04a0000000 0x00f3de9fcb000000 0x0079ef4fe5800000

def z1271 : W := mkw 0x300c000000df4000 0x18060000006fa000 0x7e0a046000ffe000 0x3f050230007ff000

def z1272 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9efffe9fc0f81f80 0xcf7fff4fe07c0fc0

def z1273 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x69ffdfffffefe000 0x34ffeffffff7f000

def z1274 : W := mkw 0xeafb1ffdfe988725 0xf57d8ffeff4c4392 0xf7ffffffff1d97e7 0xfbffffffff8ecbf3

def z1275 : W := mkw 0xc4f01ffdfe460051 0xe2780ffeff230028 0x01ffdfffff040060 0x00ffefffff820030

def z1276 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x0461bffffb159660 0x0230dffffd8acb30

def z1277 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9ff7ff0ff0f81f80 0xcffbff87f87c0fc0

def z1278 : W := mkw 0x000080000100208a 0x0000400000801045 0x819000000400099f 0xc0c80000020004cf

def z1279 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xaff5d98e78e619f9 0xd7faecc73c730cfc

def z1280 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xffdfdff04fffe819 0x7fefeff827fff40c

def z1281 : W := mkw 0x0802800201203d8a 0x0401400100901ec5 0xfa002000000a7f9f 0xfd00100000053fcf

def z1282 : W := mkw 0x4211002094008224 0x210880104a004112 0xe73ce561b4159667 0x739e72b0da0acb33

def z1283 : W := mkw 0x46318026bd20bafe 0x2318c0135e905d7f 0x81f0200fff001fff 0xc0f81007ff800fff

def z1284 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x2f45d98e38e60879 0x17a2ecc71c73043c

def z1285 : W := mkw 0x00a0098428460000 0x805004c214230000 0x7fffdb9e7fee6000 0x3fffedcf3ff73000

def z1286 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x11ffdfffff080180 0x88ffefffff8400c0

def z1287 : W := mkw 0x4211002094008224 0x210880104a004112 0xd5baa561b4159667 0xeadd52b0da0acb33

def z1288 : W := mkw 0xe0f81ffdfe980001 0xf07c0ffeff4c0000 0x11ffdfffff180000 0x08ffefffff8c0000

def z1289 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xbffffe9fcffa1f99 0xdfffff4fe7fd0fcc

def z1290 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01cf1fffff000000 0x00e78fffff800000

def z1291 : W := mkw 0xb0ec1fdd68df4001 0xd8760feeb46fa000 0x7fffdffff8ffe000 0x3fffeffffc7ff000

def z1292 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x1e63fe0fc0f81f80 0x0f31ff07e07c0fc0

def z1293 : W := mkw 0x4211002094008224 0x210880104a004112 0xf72ca561b4159667 0xfb9652b0da0acb33

def z1294 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x004d1bfe4b000000 0x00268dff25800000

def z1295 : W := mkw 0xc0501679d6000001 0x60280b3ceb000000 0x00fa067fc7000000 0x007d033fe3800000

def z1296 : W := mkw 0x4211002094008224 0x210880104a004112 0xf7bee5f1b417f667 0xfbdf72f8da0bfb33

def z1297 : W := mkw 0xc0501679d6000001 0x60280b3ceb000000 0x01ffdeffcf000000 0x00ffef7fe7800000

def z1298 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x81ffdfffff000980 0xc0ffefffff8004c0

def z1299 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x1e03dff000ffe000 0x0f01eff8007ff000

def z1300 : W := mkw 0xc0f009adfe000000 0xe07804d6ff000000 0x01ffddefff000000 0x00ffeef7ff800000

def z1301 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x01fc016fff000000 0x00fe00b7ff800000

def z1302 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0xa7f4c10fff041061 0x53fa6087ff820830

def z1303 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0xabf5408fff020819 0x55faa047ff81040c

def z1304 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xbff7d98e38e61879 0xdffbecc71c730c3c

def z1305 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x81f13a9fff001667 0xc0f89d4fff800b33

def z1306 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x017dddffbf000000 0x00beeeffdf800000

def z1307 : W := mkw 0x00a009d42a000000 0x805004ea15000000 0x0041189e0b000000 0x00208c4f05800000

def z1308 : W := mkw 0x000080000100208a 0x0000400000801045 0xfbdf6691cf1a6f9f 0xfdefb348e78d37cf

def z1309 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9ef3fe9fcbf81f80 0xcf79ff4fe5fc0fc0

def z1310 : W := mkw 0x4211002094008224 0x210880104a004112 0xf7bee761f41d97e7 0xfbdf73b0fa0ecbf3

def z1311 : W := mkw 0xeafb1ffdfe988725 0xf57d8ffeff4c4392 0x51ffffffff198786 0xa8ffffffff8cc3c3

def z1312 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x04a0bc0fc0f01780 0x82505e07e0780bc0

def z1313 : W := mkw 0x308c09d000df4000 0x984604e8006fa000 0x7e0dd9f000ffe000 0x3f06ecf8007ff000

def z1314 : W := mkw 0x70bc1ff4bedf4001 0xb85e0ffa5f6fa000 0x7f7fdffe3fffe000 0x3fbfefff1ffff000

def z1315 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x04009df000f7e000 0x02004ef8007bf000

def z1316 : W := mkw 0x0000000000000000 0x0000000000000000 0x7a4f42904b0a6000 0x3d27a14825853000

def z1317 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x21ffdfffff040061 0x10ffefffff820030

def z1318 : W := mkw 0x0020000428000000 0x0010000214000000 0x01f0000e7f000000 0x00f800073f800000

def z1319 : W := mkw 0x000080000100208a 0x0000400000801045 0x89df42904f0a699f 0xc4efa148278534cf

def z1320 : W := mkw 0xc0f009fdfe000000 0xe07804feff000000 0x01fec5ffff000000 0x00ff62ffff800000

def z1321 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0xf3df5a9e4f000007 0xf9efad4f27800003

def z1322 : W := mkw 0xc271162dfe008225 0x61388b16ff004112 0xf7ffff6fff159667 0xfbffffb7ff8acb33

def z1323 : W := mkw 0x000080000100208a 0x0000400000801045 0xfb4d02904f0a699f 0xfda68148278534cf

def z1324 : W := mkw 0x4211002094008224 0x210880104a004112 0x97b2e561b4159667 0xcbd972b0da0acb33

def z1325 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0xe1ffffffff059667 0xf0ffffffff82cb33

def z1326 : W := mkw 0xc271162dfe008225 0x61388b16ff004112 0x97f3fe0fff101667 0xcbf9ff07ff880b33

def z1327 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xfe3fdff000fff000 0x7f1feff8007ff800

def z1328 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7e8fdff047ffe000 0x3f47eff823fff000

def z1329 : W := mkw 0xb8ce1fd940df4501 0xdc670feca06fa280 0x7e0fdff040ffe180 0x3f07eff8207ff0c0

def z1330 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x71ffffffff158667 0xb8ffffffff8ac333

def z1331 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x680fdff000efe000 0x3407eff80077f000

def z1332 : W := mkw 0x000080000100208a 0x0000400000801045 0xe9dd02904f0a699f 0xf4ee8148278534cf

def z1333 : W := mkw 0x000080000100208a 0x0000400000801045 0xfbdf43907f0e69ff 0xfdefa1c83f8734ff

def z1334 : W := mkw 0x80e0098d6a000000 0xc07004c6b5000000 0x0175d98e7b000000 0x00baecc73d800000

def z1335 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x96f3fe9fcb101600 0xcb79ff4fe5880b00

def z1336 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01411a9e7f000000 0x00a08d4f3f800000

def z1337 : W := mkw 0x8040160940000001 0x40200b04a0000000 0x01f3de0fcf000000 0x00f9ef07e7800000

def z1338 : W := mkw 0x388e9fd201ff7d8b 0x9c474fe900ffbec5 0xfe0ffff000ffff9f 0xff07fff8007fffcf

def z1339 : W := mkw 0xf2fd1ffdfe99c225 0xf97e8ffeff4ce112 0xf7ffffffff1df667 0xfbffffffff8efb33

def z1340 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9ffffe0fc4f81f80 0xcfffff07e27c0fc0

def z1341 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x017fdffe7b000000 0x00bfefff3d800000

def z1342 : W := mkw 0xf2fd1ffdfedfc225 0xf97e8ffeff6fe112 0xf7fffffffff59667 0xfbfffffffffacb33

def z1343 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x760eddf000f7e000 0x3b076ef8007bf000

def z1344 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xfffffe9fc4fa7f87 0xffffff4fe27d3fc3

def z1345 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xfe0fdff000fff061 0x7f07eff8007ff830

def z1346 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x01f2c40fff000000 0x00f96207ff800000

def z1347 : W := mkw 0x4211002094008224 0x210880104a004112 0xf7bee5e1bc17967f 0xfbdf72f0de0bcb3f

def z1348 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x2104198e38e60079 0x10820cc71c73003c

def z1349 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xfefffff1c0ffff80 0xff7ffff8e07fffc0

def z1350 : W := mkw 0xc271167dfe008225 0x61388b3eff004112 0xf7fee77fff159667 0xfbff73bfff8acb33

def z1351 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xaf75fd8fb8f61e79 0x57bafec7dc7b0f3c

def z1352 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0xd7ffffffff119606 0xebffffffff88cb03

def z1353 : W := mkw 0x0000000000000000 0x0000000000000000 0x01ffda9e4f000000 0x00ffed4f27800000

def z1354 : W := mkw 0x8040165942000001 0x40200b2ca1000000 0x00411a1e43000000 0x00208d0f21800000

def z1355 : W := mkw 0x000080000100208a 0x0000400000801045 0xffffc7f07f1ff9ff 0xffffe3f83f8ffcff

def z1356 : W := mkw 0x300c165000df4001 0x18060b28006fa000 0x580a067000fbe000 0x2c050338007df000

def z1357 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x7fffdfffff1fe000 0x3fffefffff8ff000

def z1358 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x9fffffffff181f80 0xcfffffffff8c0fc0

def z1359 : W := mkw 0xb84e165b40b95d01 0x5c270b2da05cae80 0x9ef3fe1fc0f87f80 0xcf79ff0fe07c3fc0

def z1360 : W := mkw 0x000080000100208a 0x0000400000801045 0x59df42904f0a699e 0xacefa148278534cf

def z1361 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x2e65d98e38e61878 0x1732ecc71c730c3c

def z1362 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0xf7befdffbf159667 0xfbdf7effdf8acb33

def z1363 : W := mkw 0xa048160940980001 0x50240b04a04c0000 0x7fffde9fcffa6000 0x3fffef4fe7fd3000

def z1364 : W := mkw 0x000080000100208a 0x0000400000801045 0xffdf42904f0e79ff 0xffefa14827873cff

def z1365 : W := mkw 0x000080000100208a 0x0000400000801045 0xeb5d42904f0a699f 0x75aea148278534cf

def z1366 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xaff5d98e7fe61879 0x57faecc73ff30c3c

def z1367 : W := mkw 0x000080000100208a 0x0000400000801045 0xabd542904f0a699f 0xd5eaa148278534cf

def z1368 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7e0d1bf000ffe000 0x3f068df8007ff000

def z1369 : W := mkw 0xd0f41ffdfe474001 0xe87a0ffeff23a000 0x77ffdfffff17e000 0x3bffefffff8bf000

def z1370 : W := mkw 0xb0ec9fdd6bdf608b 0xd8764feeb5efb045 0xffdfdffe4fffe99f 0xffefefff27fff4cf

def z1371 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7e0b1ef000ffe000 0x3f058f78007ff000

def z1372 : W := mkw 0x84e01fdd6a460051 0xc2700feeb5230028 0x00411a9e4b020018 0x00208d4f2581000c

def z1373 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xbff7fe0fc0f81f81 0xdffbff07e07c0fc0

def z1374 : W := mkw 0xb8ce1fd940df4501 0xdc670feca06fa280 0x7effffffc0ffe780 0xbf7fffffe07ff3c0

def z1375 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xaf75db9e38ee7879 0x57baedcf1c773c3c

def z1376 : W := mkw 0xc4f01ffdfe460051 0xe2780ffeff230028 0x2fffdfffffe60079 0x17ffeffffff3003c

def z1377 : W := mkw 0x4211002094008224 0x210880104a004112 0xffffe7e1fc1f9fff 0xfffff3f0fe0fcfff

def z1378 : W := mkw 0xb84e165b40b95d01 0x5c270b2da05cae80 0x9ef3fe6fc0f99f80 0xcf79ff37e07ccfc0

def z1379 : W := mkw 0x000080000100208a 0x0000400000801045 0xdadb42904f0a699e 0xed6da148278534cf

def z1380 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9effff6fc0f81f80 0xcf7fffb7e07c0fc0

def z1381 : W := mkw 0x0802000200201d00 0x0401000100100e80 0x80b0200180001f80 0xc0581000c0000fc0

def z1382 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0xf7ffdfffff041067 0xfbffefffff820833

def z1383 : W := mkw 0x4211002094008224 0x210880104a004112 0xf6b2e561b0159667 0xfb5972b0d80acb33

def z1384 : W := mkw 0x04008002016638da 0x0200400100b31c6d 0xfa00000000ea699f 0xfd000000007534cf

def z1385 : W := mkw 0xf2fd1ffdfe99c225 0xf97e8ffeff4ce112 0x51ffffffff19e606 0xa8ffffffff8cf303

def z1386 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9ef3fe9fc0fa7f80 0xcf79ff4fe07d3fc0

def z1387 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x81f0000fff000980 0xc0f80007ff8004c0

def z1388 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xfe5fdff000ffe800 0x7f2feff8007ff400

def z1389 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x2d65998e38e61879 0x16b2ccc71c730c3c

def z1390 : W := mkw 0x4211002094008224 0x210880104a004112 0xf7bee5f1bf159667 0xfbdf72f8df8acb33

def z1391 : W := mkw 0x0420000628661850 0x0210000314330c28 0xaf71d80e38e61879 0x57b8ec071c730c3c

def z1392 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xffbffff1b0fff661 0xffdffff8d87ffb30

def z1393 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xbef7ff0fc0fc1f80 0xdf7bff87e07e0fc0

def z1394 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x8420bc0f80f01f80 0xc2105e07c0780fc0

def z1395 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x6e0dddf000f7e000 0x3706eef8007bf000

def z1396 : W := mkw 0x40b009f4be000000 0xa05804fa5f000000 0x01ffddffbf000000 0x00ffeeffdf800000

def z1397 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x93ffdfffff000000 0xc9ffefffff800000

def z1398 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xffffdb9e3cee787f 0xffffedcf1e773c3f

def z1399 : W := mkw 0xb8ee1fdf6aff5d01 0xdc770fefb57fae80 0xfeffffffcbffff80 0xff7fffffe5ffffc0

def z1400 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x00cb1a9e4f000000 0x00658d4f27800000

def z1401 : W := mkw 0xd0f41ffdfe014001 0xe87a0ffeff00a000 0x41ffdfffff01e000 0x20ffefffff80f000

def z1402 : W := mkw 0xea5b9629d598a7af 0x752dcb14eacc53d7 0x508a2671c719e786 0xa8451338e38cf3c3

def z1403 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x01ffffffff118600 0x00ffffffff88c300

def z1404 : W := mkw 0x000080000100208a 0x0000400000801045 0xfbdfc7f04f0a699f 0xfdefe3f8278534cf

def z1405 : W := mkw 0xb0cc1fd940df4001 0xd8660feca06fa000 0x7e4fdffe40ffe000 0x3f27efff207ff000

def z1406 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x94f2be0fc0f81f80 0xca795f07e07c0fc0

def z1407 : W := mkw 0x4211002094008224 0x210880104a004112 0xf7bfe7f1b4159667 0xfbdff3f8da0acb33

def z1408 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01fe07ffff000000 0x00ff03ffff800000

def z1409 : W := mkw 0xc271002dfe008224 0x61388016ff004112 0xf7f0200fff159667 0xfbf81007ff8acb33

def z1410 : W := mkw 0x4211002094008224 0x210880104a004112 0xffffe7f1ff1d9fe7 0xfffff3f8ff8ecff3

def z1411 : W := mkw 0x0420000628201850 0x0210000314100c28 0x8971180e38e01879 0x44b88c071c700c3c

def z1412 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9ff3fe0fcff81f80 0xcff9ff07e7fc0fc0

def z1413 : W := mkw 0xf05c1679d6994001 0x782e0b3ceb4ca000 0x5efbde7fc7f9e000 0x2f7def3fe3fcf000

def z1414 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xbef3fe0fc0fa1f99 0xdf79ff07e07d0fcc

def z1415 : W := mkw 0xe8fa1ffdfe980501 0xf47d0ffeff4c0280 0x01ffdfffff080180 0x00ffefffff8400c0

def z1416 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x00eb9fffff000000 0x0075cfffff800000

def z1417 : W := mkw 0x280a000200b81d00 0x14050001005c0e80 0x9fdf62904ff81f80 0xcfefb14827fc0fc0

def z1418 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x01711a9e7b000000 0x00b88d4f3d800000

def z1419 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x1420bc0f80f81780 0x8a105e07c07c0bc0

def z1420 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x00619b9e7b000000 0x0030cdcf3d800000

def z1421 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x01dfdffe4f000000 0x00efefff27800000

def z1422 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x51ffdfffff000006 0xa8ffefffff800003

def z1423 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xaf24998e38e61879 0x57924cc71c730c3c

def z1424 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x8cf1be0fc0f81f80 0xc678df07e07c0fc0

def z1425 : W := mkw 0xe0f81ffdfe980001 0xf07c0ffeff4c0000 0x9fffdffffff80980 0xcfffeffffffc04c0

def z1426 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x2975d98e38e60879 0x14baecc71c73043c

def z1427 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x54aabf7ff7159666 0xaa555fbffb8acb33

def z1428 : W := mkw 0xc0f01fadfe000001 0xe0780fd6ff000000 0x01f7df8fff000000 0x00fbefc7ff800000

def z1429 : W := mkw 0xc0501629d6000001 0x60280b14eb000000 0x00f3de0fc7000000 0x0079ef07e3800000

def z1430 : W := mkw 0x0ca2098628661d50 0x865104c314330ea8 0xaf75f98e38e61ff9 0xd7bafcc71c730ffc

def z1431 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x540fdff000fde000 0x2a07eff8007ef000

def z1432 : W := mkw 0x4211002094008224 0x210880104a004112 0xffbee561b4179e7f 0xffdf72b0da0bcf3f

def z1433 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x08413e0fc0f80f80 0x04209f07e07c07c0

def z1434 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xfef3fe0fc0f81f87 0xff79ff07e07c0fc3

def z1435 : W := mkw 0xc0f01ffdfe460001 0xe0780ffeff230000 0x21ffdfffff060000 0x10ffefffff830000

def z1436 : W := mkw 0xc2f109adfe008224 0xe17884d6ff004112 0xa7f5f98fff041667 0xd3fafcc7ff820b33

def z1437 : W := mkw 0xc0f009fdfe000000 0xe07804feff000000 0x01f0009fff000000 0x00f8004fff800000

def z1438 : W := mkw 0xe8fa1ffdfe980501 0xf47d0ffeff4c0280 0x9bffffffff180f80 0xcdffffffff8c07c0

def z1439 : W := mkw 0xc271002dfe008224 0x61388016ff004112 0x51fa246fff118606 0xa8fd1237ff88c303

def z1440 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01fd1bffff000000 0x00fe8dffff800000

def z1441 : W := mkw 0x00a009d42a000000 0x805004ea15000000 0x0175d99e3b000000 0x00baeccf1d800000

def z1442 : W := mkw 0x4211002094008224 0x210880104a004112 0xf7ffe5e1bc159667 0xfbfff2f0de0acb33

def z1443 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x05f09d6ffff58000 0x02f84eb7fffac000

def z1444 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x01555a9e4b000000 0x00aaad4f25800000

def z1445 : W := mkw 0x6a1b802295b8bfae 0x350dc0114adc5fd7 0xffbee561b4ffffff 0xffdf72b0da7fffff

def z1446 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x0045db9e4b000000 0x0022edcf25800000

def z1447 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x00a0000ff7000000 0x00500007fb800000

def z1448 : W := mkw 0x8060000d6a000000 0x40300006b5000000 0x0041029e4b000000 0x0020814f25800000

def z1449 : W := mkw 0x000080000100208a 0x0000400000801045 0x7acf42904f0a699e 0xbd67a148278534cf

def z1450 : W := mkw 0x108409d000474000 0x884204e80023a000 0x7e0fdbf000efe000 0x3f07edf80077f000

def z1451 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x008a1e7fc7000000 0x00450f3fe3800000

def z1452 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x87ffdfffff001000 0x43ffefffff800800

def z1453 : W := mkw 0xe2f91ffdfe988225 0xf17c8ffeff4c4112 0xfffffffffffd9667 0xfffffffffffecb33

def z1454 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x8e71fe0fc0f81f80 0x4738ff07e07c0fc0

def z1455 : W := mkw 0xc271002dfe008224 0x61388016ff004112 0xf3ff629fff001667 0xf9ffb14fff800b33

def z1456 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9ff7fe8fc8f81f80 0xcffbff47e47c0fc0

def z1457 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x17ffdfffff100000 0x0bffefffff880000

def z1458 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7edfdff040ffe000 0x3f6feff8207ff000

def z1459 : W := mkw 0xf07c167dfe994001 0x783e0b3eff4ca000 0x51fa067fff19e000 0x28fd033fff8cf000

def z1460 : W := mkw 0xf0fc1ffdfe994001 0xf87e0ffeff4ca000 0x7bffdfffff1be000 0x3dffefffff8df000

def z1461 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x500a1e7000f9e000 0x28050f38007cf000

def z1462 : W := mkw 0x4211002094008224 0x210880104a004112 0xffbee561b41ff667 0xffdf72b0da0ffb33

def z1463 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xfffffe8fccfa1f9f 0xffffff47e67d0fcf

def z1464 : W := mkw 0xa8ea1fdd6a980501 0xd4750feeb54c0280 0x10c33e9fcb180780 0x88619f4fe58c03c0

def z1465 : W := mkw 0xc070162dfe000001 0x60380b16ff000000 0x01ffdf6fff000000 0x00ffefb7ff800000

def z1466 : W := mkw 0x8060165d6a000001 0x40300b2eb5000000 0x0040021e4b000000 0x0020010f25800000

def z1467 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x51ffdfffff086000 0x28ffefffff843000

def z1468 : W := mkw 0x108409d000474000 0x884204e80023a000 0x640c99f000e7e000 0x32064cf80073f000

def z1469 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x006fdffffb000000 0x0037effffd800000

def z1470 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0xffffdfffffffe007 0xffffeffffffff003

def z1471 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x80f0380fc0e01f80 0xc0781c07e0700fc0

def z1472 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xbff7ff8ff8fe1ff9 0xdffbffc7fc7f0ffc

def z1473 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x780f1ff000ffe000 0x3c078ff8007ff000

def z1474 : W := mkw 0xc070007dfe000000 0x6038003eff000000 0x01f8007fff000000 0x00fc003fff800000

def z1475 : W := mkw 0x280a800201b83d8a 0x1405400100dc1ec5 0x0800000000ea6998 0x04000000007534cc

def z1476 : W := mkw 0x0420000628201850 0x0210000314100c28 0x8570980e38e01879 0x42b84c071c700c3c

def z1477 : W := mkw 0xc0f01ffdfe460001 0xe0780ffeff230000 0x7fffdffffff78000 0x3fffeffffffbc000

def z1478 : W := mkw 0x4211002094008224 0x210880104a004112 0x4428a561b4159666 0x221452b0da0acb33

def z1479 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x00cfdfffcf000000 0x0067efffe7800000

def z1480 : W := mkw 0xe85a167bd6b81d01 0x742d0b3deb5c0e80 0x9e8a2671c7f81f80 0xcf451338e3fc0fc0

def z1481 : W := mkw 0x80e01fdd6a460001 0xc0700feeb5230000 0x2e45db9e4be60000 0x1722edcf25f30000

def z1482 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01f5db9fff000000 0x00faedcfff800000

def z1483 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xbf75f98e38f61e79 0xdfbafcc71c7b0f3c

def z1484 : W := mkw 0x8060000d6a000000 0x40300006b5000000 0x0170000e7b000000 0x00b800073d800000

def z1485 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x0460bc0fc0f01f80 0x02305e07e0780fc0

def z1486 : W := mkw 0xf0fc1ffdfe994001 0xf87e0ffeff4ca000 0x01ffdfffff086000 0x00ffefffff843000

def z1487 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x2fffdffffff78000 0x17ffeffffffbc000

def z1488 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x01ffdfffffe00000 0x00ffeffffff00000

def z1489 : W := mkw 0x14a409d628675850 0x8a5204eb1433ac28 0xff7fdbfe38eff879 0x7fbfedff1c77fc3c

def z1490 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x00491afe4f000000 0x00248d7f27800000

def z1491 : W := mkw 0x8060160d6a000001 0x40300b06b5000000 0x00f3de0fcb000000 0x0079ef07e5800000

def z1492 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xef7dd9ee38e79879 0x77beecf71c73cc3c

def z1493 : W := mkw 0xc070167dfe000001 0x60380b3eff000000 0x01fec77fff000000 0x00ff63bfff800000

def z1494 : W := mkw 0x4211002094008224 0x210880104a004112 0xe5bca561b4159667 0xf2de52b0da0acb33

def z1495 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0xf7ffffffff101607 0xfbffffffff880b03

def z1496 : W := mkw 0x000080000100208a 0x0000400000801045 0xffdfc3904f0e699f 0xffefe1c8278734cf

def z1497 : W := mkw 0x461180229566bafe 0x2308c0114ab35d7f 0xffbee561b4ffffff 0xffdf72b0da7fffff

def z1498 : W := mkw 0xc0f01ffdfe460001 0xe0780ffeff230000 0x05ffdfffffe40000 0x02ffeffffff20000

def z1499 : W := mkw 0xc0f009fdfe000000 0xe07804feff000000 0x012c01ffbf000000 0x009600ffdf800000

def z1500 : W := mkw 0x000080000100208a 0x0000400000801045 0xffdfc6904f1a699f 0xffefe348278d34cf

def z1501 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x7e6fdffffbffe000 0x3f37effffdfff000

def z1502 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01beddffbf000000 0x00df6effdf800000

def z1503 : W := mkw 0x108409d000474000 0x884204e80023a000 0x680d19f000e7e000 0x34068cf80073f000

def z1504 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9ef3fe8fc8fa1f98 0xcf79ff47e47d0fcc

def z1505 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xff7fdffe38fff879 0x7fbfefff1c7ffc3c

def z1506 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x7ecfdfffcfffe000 0x3f67efffe7fff000

def z1507 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xef7dd99e38e67879 0x77beeccf1c733c3c

def z1508 : W := mkw 0x000080000100208a 0x0000400000801045 0x484902904f0a699e 0x24248148278534cf

def z1509 : W := mkw 0x300c005000df4000 0x18060028006fa000 0x7e08007000ffe000 0x3f040038007ff000

def z1510 : W := mkw 0x000080000100208a 0x0000400000801045 0xd9db02904f0a699f 0xeced8148278534cf

def z1511 : W := mkw 0x000080000100208a 0x0000400000801045 0x08c102904f0a699e 0x84608148278534cf

def z1512 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x0520990e38e41079 0x02904c871c72083c

def z1513 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x00fbdf7ff7000000 0x007defbffb800000

def z1514 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x652c9dffbff7e000 0x32964effdffbf000

def z1515 : W := mkw 0x4211002094008224 0x210880104a004112 0xffffe561b4159e67 0xfffff2b0da0acf33

def z1516 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7f0fdff00fffe000 0x3f87eff807fff000

def z1517 : W := mkw 0xf0fc1ffdfe994001 0xf87e0ffeff4ca000 0x5fffdffffff9e000 0x2fffeffffffcf000

def z1518 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xdefbfe0fc4f81f86 0xef7dff07e27c0fc3

def z1519 : W := mkw 0x80c01fd940000001 0xc0600feca0000000 0x01ffdfffcf000000 0x00ffefffe7800000

def z1520 : W := mkw 0xa84a160940980501 0x54250b04a04c0280 0x1ef3fe0fc0f80780 0x8f79ff07e07c03c0

def z1521 : W := mkw 0xc0f009adfe000000 0xe07804d6ff000000 0x01f1188fff000000 0x00f88c47ff800000

def z1522 : W := mkw 0x000080000100208a 0x0000400000801045 0xfbffda9e4f0a699f 0xfdffed4f278534cf

def z1523 : W := mkw 0x14a4098628675850 0x8a5204c31433ac28 0xef75d98e38e7f879 0x77baecc71c73fc3c

def z1524 : W := mkw 0x34ac1fd428df4051 0x9a560fea146fa028 0x7f7fdffe38ffe079 0x3fbfefff1c7ff03c

def z1525 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9ad37e0fc0f80f80 0xcd69bf07e07c07c0

def z1526 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7e05dde000ffe000 0x3f02eef0007ff000

def z1527 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x00afdffff7000000 0x0057effffb800000

def z1528 : W := mkw 0x4211002094008224 0x210880104a004112 0xa7b4e561b4159667 0xd3da72b0da0acb33

def z1529 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x01fa046fff000000 0x00fd0237ff800000

def z1530 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0xfbffdfffff080987 0xfdffefffff8404c3

def z1531 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xef7dd98e3ce6187f 0x77beecc71e730c3f

def z1532 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x0c619ffffbffe000 0x0630cffffdfff000

def z1533 : W := mkw 0x04008002012038da 0x0200400100901c6d 0xfa000000000a79ff 0xfd00000000053cff

def z1534 : W := mkw 0x000080000100208a 0x0000400000801045 0x9bd342904f0a699f 0xcde9a148278534cf

def z1535 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0xfbffdfffff0a6980 0xfdffefffff8534c0

def z1536 : W := mkw 0xb04c165942994001 0x58260b2ca14ca000 0x500a06704319e000 0x28050338218cf000

def z1537 : W := mkw 0x00a0098428000000 0x805004c214000000 0x00411a9e4b000000 0x00208d4f25800000

def z1538 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x00609d6ffb000000 0x00304eb7fd800000

def z1539 : W := mkw 0x300c165000994001 0x18060b28004ca000 0x540a9e7000f9e000 0x2a054f38007cf000

def z1540 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x614d1bfe7f058067 0x30a68dff3f82c033

def z1541 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x81ffdfffff000007 0xc0ffefffff800003

def z1542 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x8e71d98e38e61878 0x4738ecc71c730c3c

def z1543 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x740e9ff000ffe000 0x3a074ff8007ff000

def z1544 : W := mkw 0xc6f11ffdfe468275 0xe3788ffeff23413a 0x61ffdfffff07807f 0x30ffefffff83c03f

def z1545 : W := mkw 0xb84e165b40b95d01 0x5c270b2da05cae80 0xfeffff7fc0fdff80 0xff7fffbfe07effc0

def z1546 : W := mkw 0x8842000b40201d00 0x44210005a0100e80 0x88f1380fc0e01f80 0xc4789c07e0700fc0

def z1547 : W := mkw 0xe0f81ffdfede0001 0xf07c0ffeff6f0000 0x3fffdffffffe0000 0x1fffefffffff0000

def z1548 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xaf71188e38e61879 0x57b88c471c730c3c

def z1549 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0xf3ffffffff001667 0xf9ffffffff800b33

def z1550 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x0060000ffb000000 0x00300007fd800000

def z1551 : W := mkw 0x8060000d6a000000 0x40300006b5000000 0x01d0000e4f000000 0x00e8000727800000

def z1552 : W := mkw 0x2008160000980001 0x10040b00004c0000 0x7e0fdff000ffe000 0x3f07eff8007ff000

def z1553 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x08411a9e4b080980 0x04208d4f258404c0

def z1554 : W := mkw 0xf0fc1ffdfedf4001 0xf87e0ffeff6fa000 0x7eafdffff7ffe000 0x3f57effffbfff000

def z1555 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x01ffdfffff000067 0x00ffefffff800033

def z1556 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x97ffffffff159660 0xcbffffffff8acb30

def z1557 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0x9ef13a0fc0f81f80 0xcf789d07e07c0fc0

def z1558 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x77fec56fff158000 0x3bff62b7ff8ac000

def z1559 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x01f7df9ffb000000 0x00fbefcffd800000

def z1560 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0xfe0fdff000ffe007 0xff07eff8007ff003

def z1561 : W := mkw 0x4211002094008224 0x210880104a004112 0xffbfe761b41d9667 0xffdff3b0da0ecb33

def z1562 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7ebfdff180ffe000 0x3f5feff8c07ff000

def z1563 : W := mkw 0x00a01fd428000001 0x80500fea14000000 0x01ffdffe7f000000 0x00ffefff3f800000

def z1564 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x8d71998e38e61879 0x46b8ccc71c730c3c

def z1565 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xbf77dd8e38f61879 0x5fbbeec71c7b0c3c

def z1566 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xfeffffffc0ffff80 0xff7fffffe07fffc0

def z1567 : W := mkw 0x000080000100208a 0x0000400000801045 0xffdfda904fea699f 0xffefed4827f534cf

def z1568 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0xa7ffffffff041667 0xd3ffffffff820b33

def z1569 : W := mkw 0x300c165000994001 0x18060b28004ca000 0x580b1e7000f9e000 0x2c058f38007cf000

def z1570 : W := mkw 0x04008002016638da 0x0200400100b31c6d 0xee00000000e6787f 0x7700000000733c3f

def z1571 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x50cb3effcf118606 0xa8659f7fe788c303

def z1572 : W := mkw 0xd2f51ffdfe47c225 0xe97a8ffeff23e112 0x61ffdfffff07e067 0x30ffefffff83f033

def z1573 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x2bffdfffff020000 0x15ffefffff810000

def z1574 : W := mkw 0x348c9fd201ff78db 0x9a464fe900ffbc6d 0xfe0fdff000fff9ff 0xff07eff8007ffcff

def z1575 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x00c11a9fcf000000 0x00608d4fe7800000

def z1576 : W := mkw 0xb0cc1fd940df4001 0xd8660feca06fa000 0x7e8fdff1c0ffe000 0x3f47eff8e07ff000

def z1577 : W := mkw 0xca53802bd520bfae 0x6529c015ea905fd7 0x81f0200fff001fff 0xc0f81007ff800fff

def z1578 : W := mkw 0x000080000100208a 0x0000400000801045 0x79cf02904f0a699f 0xbce78148278534cf

def z1579 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x8975d98e38e21879 0x44baecc71c710c3c

def z1580 : W := mkw 0xf2fd1ffdfedfc225 0xf97e8ffeff6fe112 0x7fffdfffffffe067 0x3fffeffffffff033

def z1581 : W := mkw 0xe0f81ffdfe980001 0xf07c0ffeff4c0000 0x09ffdfffffe80000 0x04ffeffffff40000

def z1582 : W := mkw 0x00a0098428000000 0x805004c214000000 0x017dd99e3f000000 0x00beeccf1f800000

def z1583 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x7e0c9df000ffe000 0x3f064ef8007ff000

def z1584 : W := mkw 0x30ac1fd428df4001 0x98560fea146fa000 0x7f0fdff038ffe000 0x3f87eff81c7ff000

def z1585 : W := mkw 0x80e009dd6a000000 0xc07004eeb5000000 0x0040009e4b000000 0x0020004f25800000

def z1586 : W := mkw 0x4211002094008224 0x210880104a004112 0xf734e561b0159667 0xfb9a72b0d80acb33

def z1587 : W := mkw 0x308c1fd000df4001 0x98460fe8006fa000 0x6c0d9ff000ffe000 0x3606cff8007ff000

def z1588 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0xf3fe400fff000007 0xf9ff2007ff800003

def z1589 : W := mkw 0x000080000100208a 0x0000400000801045 0xfacb02904f0a699f 0xfd658148278534cf

def z1590 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x2420990e30e61079 0x12104c871873083c

def z1591 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xdefbfe1fc0f87f80 0xef7dff0fe07c3fc0

def z1592 : W := mkw 0x308c09d000df4000 0x984604e8006fa000 0x640c01f000f7e000 0x320600f8007bf000

def z1593 : W := mkw 0xc070002dfe000000 0x60380016ff000000 0x01f1d80fff000000 0x00f8ec07ff800000

def z1594 : W := mkw 0x000080000100208a 0x0000400000801045 0xffffe791ff1e7fff 0xfffff3c8ff8f3fff

def z1595 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x01d11a9e4f000000 0x00e88d4f27800000

def z1596 : W := mkw 0x8842160b40201d01 0x44210b05a0100e80 0x8ef3fe0fc0e01f80 0xc779ff07e0700fc0

def z1597 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01df5effcf000000 0x00efaf7fe7800000

def z1598 : W := mkw 0x04a0098628661850 0x825004c314330c28 0x0941188e38e20879 0x04a08c471c71043c

def z1599 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x01df5bfe7f000000 0x00efadff3f800000

def z1600 : W := mkw 0xa0e81fdd6a980001 0xd0740feeb54c0000 0x08411a9e4be80000 0x04208d4f25f40000

def z1601 : W := mkw 0xc271002dfe008224 0x61388016ff004112 0xf7ffe7ffff159667 0xfbfff3ffff8acb33

def z1602 : W := mkw 0xc2f11ffdfe008225 0xe1788ffeff004112 0x01ffffffff000606 0x80ffffffff800303

def z1603 : W := mkw 0x108409d000474000 0x884204e80023a000 0x7e0fddf000f7e000 0x3f07eef8007bf000

def z1604 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x81ffdfffff000819 0x40ffefffff80040c

def z1605 : W := mkw 0x4211002094008224 0x210880104a004112 0xf7b0a561b4159667 0xfbd852b0da0acb33

def z1606 : W := mkw 0x40b01ff4be000001 0xa0580ffa5f000000 0x017fdffe3f000000 0x00bfefff1f800000

def z1607 : W := mkw 0x04a0098628661850 0x825004c314330c28 0xffffdb9e78ee79f9 0xffffedcf3c773cfc

def z1608 : W := mkw 0xc0f01ffdfe000001 0xe0780ffeff000000 0x00f3dffffb000000 0x0079effffd800000

def z1609 : W := mkw 0xa84a160b40b81d01 0x54250b05a05c0e80 0xfef3fe0fc0fd9f80 0xff79ff07e07ecfc0

def z1610 : W := mkw 0x80e01fdd6a000001 0xc0700feeb5000000 0x01ffde9fcf000000 0x00ffef4fe7800000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z9,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z10,z8]),(0,[z1,z2,z3,z4,z5,z11,z8]),(0,[z1,z2,z3,z4,z4,z5,z12])],[],[(0,[z1,z2,z3,z4,z5,z13,z14]),(0,[z1,z3,z15,z4,z16,z5,z8]),(0,[z17,z1,z2,z3,z4,z5,z12]),(0,[z1,z2,z18,z3,z4,z5,z8])],[(0,[z19,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z20,z3,z4,z5,z21]),(0,[z1,z2,z3,z4,z5,z8,z22]),(0,[z17,z1,z2,z3,z4,z23,z8]),(0,[z24,z1,z2,z3,z4,z25,z8]),(0,[z1,z2,z3,z4,z26,z5,z8]),(0,[z1,z2,z3,z4,z5,z27,z8]),(0,[z1,z2,z3,z4,z5,z12,z28])],[(0,[z29,z1,z2,z3,z4,z30,z5])],[],[(0,[z1,z2,z3,z4,z31,z5,z8]),(0,[z1,z2,z3,z32,z33,z5,z8])],[(0,[z34,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z35,z4,z5,z8])],[(0,[z36,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z37,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z38]),(0,[z1,z2,z3,z4,z5,z6,z39])],[(0,[z1,z2,z3,z40,z4,z5,z8]),(0,[z1,z2,z3,z4,z41,z5,z8]),(0,[z1,z2,z3,z4,z42,z5,z8]),(1,[z1,z2,z43,z4,z5,z28]),(0,[z1,z44,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z45,z5,z8]),(0,[z1,z46,z2,z3,z4,z5,z8])],[(0,[z47,z1,z2,z3,z48,z5,z8]),(0,[z49,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z50,z4,z51,z5,z8]),(0,[z1,z52,z2,z3,z4,z5,z8])],[(1,[z1,z2,z53,z4,z5,z8]),(0,[z1,z2,z54,z4,z5,z8,z28]),(0,[z55,z1,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z56,z8]),(0,[z57,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z20,z3,z4,z5,z28]),(0,[z34,z1,z58,z3,z4,z5,z8]),(0,[z47,z1,z2,z3,z4,z59,z8]),(0,[z1,z2,z3,z4,z60,z5,z8]),(0,[z1,z2,z3,z61,z4,z5,z8]),(0,[z62,z1,z2,z3,z4,z5,z8])],[(0,[z63,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z64])],[],[(1,[z1,z2,z3,z4,z5,z65]),(0,[z1,z66,z2,z3,z67,z5,z8]),(0,[z68,z1,z2,z3,z4,z5,z8])],[(0,[z1,z69,z2,z3,z4,z30,z5]),(0,[z1,z2,z3,z70,z4,z5,z8]),(0,[z1,z2,z4,z5,z71,z8,z28])],[(0,[z1,z2,z3,z4,z30,z5,z14]),(0,[z1,z2,z3,z4,z72,z5,z8]),(0,[z1,z2,z3,z4,z5,z6,z6])],[(0,[z1,z2,z3,z4,z5,z73,z12]),(0,[z1,z2,z3,z4,z5,z8,z74]),(0,[z1,z75,z2,z3,z4,z5,z8])],[(0,[z47,z2,z3,z4,z5,z73,z8]),(0,[z76,z1,z2,z77,z4,z5,z8]),(1,[z1,z78,z3,z4,z5,z8]),(0,[z1,z66,z2,z3,z4,z5,z8])],[(0,[z79,z1,z2,z3,z4,z5,z8])],[(0,[z80,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z59,z5,z12]),(0,[z1,z2,z81,z15,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z82,z8])],[(0,[z1,z2,z83,z3,z4,z5,z8]),(0,[z1,z84,z2,z3,z4,z5,z8])],[(0,[z34,z1,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z32,z16,z5,z8]),(1,[z1,z2,z15,z4,z5,z28]),(0,[z85,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z86,z71,z8]),(0,[z1,z2,z3,z4,z5,z12,z39]),(0,[z1,z2,z3,z87,z4,z5,z8])],[(0,[z1,z2,z88,z3,z4,z5,z8]),(1,[z1,z2,z3,z67,z5,z12]),(1,[z1,z2,z3,z4,z5,z89]),(0,[z1,z2,z3,z90,z4,z5,z8])],[(0,[z91,z1,z2,z3,z4,z5,z8]),(0,[z24,z1,z2,z3,z4,z30,z5]),(0,[z92,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z93,z4,z5,z8]),(0,[z1,z2,z3,z4,z94,z5,z12])],[(0,[z95,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z8,z96]),(0,[z1,z2,z3,z97,z4,z5,z8])],[(0,[z1,z2,z3,z4,z25,z59,z8]),(0,[z1,z2,z3,z98,z4,z5,z8])]],
   [[(0,[z1,z99,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z12])],[(0,[z1,z2,z3,z4,z5,z8,z100]),(0,[z1,z2,z3,z4,z67,z30,z5]),(1,[z1,z2,z3,z32,z5,z12]),(0,[z1,z2,z3,z4,z5,z101,z8]),(0,[z1,z2,z3,z4,z102,z5,z8]),(0,[z1,z103,z2,z104,z4,z5,z8]),(0,[z1,z2,z105,z4,z25,z5,z8]),(1,[z1,z66,z2,z3,z30,z5])],[(0,[z1,z2,z3,z106,z4,z5,z8]),(0,[z1,z2,z3,z4,z107,z5,z8]),(0,[z62,z1,z2,z3,z4,z5,z28])],[(0,[z0,z1,z2,z3,z4,z5,z28]),(1,[z1,z2,z3,z108,z5,z8])],[(0,[z109,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z110,z30,z5])],[(0,[z1,z2,z111,z3,z4,z73,z8]),(0,[z1,z2,z112,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z51,z5,z8]),(0,[z29,z1,z2,z3,z4,z5,z12]),(0,[z1,z66,z2,z3,z30,z5,z8]),(0,[z1,z2,z3,z4,z4,z30,z5])],[(0,[z113,z2,z20,z3,z4,z5,z8]),(0,[z76,z1,z114,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z115,z5])],[(0,[z1,z2,z116,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z117,z8]),(0,[z1,z2,z3,z4,z72,z5,z28]),(0,[z1,z2,z3,z4,z118,z5,z8])],[(0,[z119,z1,z2,z3,z4,z120,z8]),(0,[z1,z121,z2,z3,z4,z5,z8]),(0,[z113,z1,z2,z20,z4,z5,z8]),(0,[z76,z1,z2,z3,z108,z5,z8]),(0,[z122,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z123,z3,z4,z5,z8]),(0,[z1,z2,z81,z4,z5,z71,z8]),(0,[z1,z2,z3,z4,z124,z5,z8])],[(0,[z17,z1,z125,z3,z4,z5,z8]),(0,[z1,z125,z2,z3,z4,z30,z5]),(0,[z1,z66,z2,z3,z4,z5,z28]),(0,[z1,z2,z126,z3,z4,z5,z8]),(0,[z1,z2,z111,z3,z4,z94,z8])],[(0,[z1,z2,z3,z127,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z128]),(0,[z1,z2,z3,z4,z129,z5,z8]),(1,[z1,z2,z4,z5,z71,z28])],[(0,[z47,z1,z2,z3,z4,z5,z130]),(0,[z76,z1,z2,z3,z4,z5,z14]),(0,[z1,z2,z3,z4,z131,z5,z8])],[(0,[z1,z2,z3,z4,z16,z5,z8])],[(0,[z119,z1,z2,z132,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z133]),(0,[z1,z2,z3,z87,z4,z5,z28])],[(0,[z134,z1,z135,z3,z4,z5,z8]),(0,[z136,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z137,z3,z4,z5,z8]),(0,[z138,z1,z2,z3,z4,z5,z8])],[(0,[z1,z114,z139,z3,z4,z5,z8]),(1,[z1,z2,z4,z5,z140,z8])]],
   [[(0,[z1,z2,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z141,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z142]),(0,[z1,z125,z2,z3,z16,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z143])],[],[(0,[z1,z2,z3,z50,z67,z5,z8]),(0,[z1,z2,z3,z4,z5,z144,z8]),(0,[z1,z2,z145,z4,z72,z5,z8]),(0,[z1,z2,z146,z3,z4,z5,z8])],[(0,[z1,z69,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z32,z4,z5,z12]),(0,[z55,z1,z2,z3,z4,z30,z5]),(1,[z1,z2,z3,z4,z147,z8]),(0,[z1,z2,z148,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z149,z5,z8]),(0,[z1,z2,z3,z4,z30,z30,z5])],[(0,[z1,z2,z150,z3,z4,z5,z8]),(1,[z17,z1,z3,z16,z5,z8])],[(0,[z151,z1,z2,z3,z4,z5,z8]),(0,[z47,z1,z152,z3,z4,z5,z8]),(0,[z1,z153,z154,z3,z4,z5,z8]),(0,[z1,z155,z2,z3,z4,z30,z5])],[(0,[z1,z2,z3,z50,z4,z5,z8]),(1,[z1,z2,z3,z4,z149,z8])],[(0,[z55,z1,z2,z3,z4,z94,z5]),(0,[z1,z2,z3,z4,z51,z5,z28])],[(0,[z156,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z157]),(0,[z158,z1,z2,z3,z4,z5,z8])],[(0,[z134,z1,z2,z3,z4,z159,z8]),(1,[z1,z2,z3,z4,z5,z160]),(0,[z1,z155,z2,z4,z5,z8,z28])],[(1,[z1,z2,z146,z4,z5,z8]),(0,[z1,z2,z3,z87,z4,z8,z39])],[(1,[z1,z2,z3,z4,z161,z8]),(0,[z34,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z48,z4,z5,z8]),(0,[z1,z114,z2,z3,z4,z5,z162])],[(0,[z1,z2,z163,z20,z4,z5,z8]),(0,[z1,z2,z3,z67,z5,z8,z164]),(0,[z24,z1,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z165,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z166]),(0,[z1,z167,z2,z3,z4,z30,z5]),(0,[z1,z2,z3,z4,z5,z8,z168])],[(0,[z169,z2,z3,z4,z5,z73,z8])],[(0,[z1,z2,z15,z4,z51,z5,z8]),(0,[z17,z1,z2,z3,z4,z5,z170]),(0,[z1,z2,z3,z4,z16,z5,z28]),(0,[z1,z2,z3,z4,z72,z8,z164])],[(0,[z1,z2,z3,z4,z5,z8,z171]),(1,[z34,z2,z3,z67,z5,z8]),(0,[z1,z2,z3,z4,z5,z172,z8])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z173]),(0,[z174,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z175])],[(0,[z1,z2,z43,z54,z4,z5,z8]),(0,[z1,z2,z176,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z177,z8])],[(0,[z134,z1,z178,z3,z4,z5,z8]),(0,[z47,z1,z2,z3,z4,z73,z8]),(0,[z1,z2,z4,z51,z5,z71,z8]),(0,[z1,z179,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z180,z5,z8]),(0,[z1,z181,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z30,z59,z5]),(0,[z1,z155,z2,z163,z4,z5,z8]),(1,[z1,z2,z3,z4,z30,z5])],[(0,[z1,z2,z178,z3,z4,z5,z8]),(0,[z1,z2,z3,z182,z4,z5,z8]),(0,[z1,z2,z183,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z162]),(1,[z1,z2,z184,z4,z71,z8]),(0,[z185,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z186,z5,z8]),(0,[z1,z2,z3,z4,z72,z5,z6])],[(0,[z1,z125,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z50,z4,z5,z28])],[(0,[z1,z2,z3,z4,z5,z187,z8]),(0,[z76,z1,z2,z3,z4,z30,z5]),(0,[z1,z66,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z188,z8])],[],[(1,[z1,z121,z2,z3,z4,z5]),(0,[z1,z2,z81,z3,z4,z5,z166]),(0,[z1,z189,z2,z3,z4,z5,z8])],[(0,[z1,z2,z54,z4,z51,z5,z8]),(0,[z76,z1,z2,z3,z4,z94,z5]),(0,[z1,z2,z3,z87,z4,z5,z6]),(0,[z1,z2,z111,z3,z87,z4,z8])],[(0,[z1,z2,z3,z4,z30,z72,z5]),(0,[z1,z2,z3,z4,z5,z8,z190])],[(0,[z191,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z192,z3,z4,z5,z8]),(0,[z1,z154,z3,z4,z72,z5,z8]),(0,[z1,z103,z2,z3,z4,z5,z193])]],
   [[(0,[z1,z2,z3,z4,z67,z5,z8]),(0,[z55,z1,z139,z2,z3,z4,z5]),(0,[z1,z153,z2,z43,z4,z5,z8]),(0,[z1,z2,z3,z4,z194,z5,z8]),(0,[z1,z2,z3,z4,z5,z13,z8]),(0,[z1,z2,z3,z4,z94,z5,z13]),(0,[z1,z2,z195,z3,z4,z5,z12])],[(1,[z1,z2,z3,z196,z5,z8]),(0,[z1,z2,z3,z4,z25,z73,z8]),(0,[z1,z2,z3,z4,z197,z8,z164]),(0,[z198,z1,z2,z3,z4,z5,z8])],[(0,[z199,z1,z2,z3,z4,z5,z8]),(0,[z1,z139,z3,z4,z5,z13,z8]),(0,[z1,z2,z3,z4,z30,z5,z12])],[(0,[z1,z2,z200,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z177,z28]),(0,[z1,z2,z3,z201,z4,z5,z8])],[(0,[z1,z2,z81,z3,z51,z5,z8]),(0,[z1,z2,z81,z3,z4,z30,z5]),(0,[z1,z155,z2,z3,z4,z5,z12])],[(0,[z1,z2,z3,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z14,z12])],[(0,[z47,z1,z2,z3,z4,z5,z202]),(0,[z17,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z4,z5,z6,z28])],[(0,[z1,z2,z3,z32,z51,z5,z8]),(0,[z1,z2,z3,z32,z4,z30,z5]),(0,[z1,z2,z3,z4,z51,z5,z6])],[(0,[z1,z2,z3,z4,z5,z8,z203]),(0,[z1,z2,z3,z204,z5,z8,z12])],[(0,[z1,z69,z125,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z205]),(0,[z1,z206,z2,z3,z4,z5,z8]),(0,[z207,z1,z2,z3,z4,z5,z8]),(0,[z1,z208,z2,z3,z4,z5,z8])],[(0,[z169,z2,z3,z32,z4,z5,z8])],[(1,[z1,z2,z3,z4,z5,z170]),(0,[z1,z2,z3,z4,z209,z5,z8])],[(1,[z1,z2,z3,z4,z210,z8]),(0,[z1,z2,z3,z4,z5,z202,z8])],[(0,[z211,z1,z2,z3,z4,z5,z8])],[(0,[z212,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z16,z5,z6]),(0,[z1,z2,z3,z213,z86,z5,z8])],[(0,[z1,z153,z2,z15,z4,z5,z8])]],
   [[(0,[z119,z0,z2,z3,z4,z5,z8]),(0,[z1,z125,z214,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z215,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z216]),(0,[z1,z2,z3,z4,z217,z5,z8])],[],[(0,[z1,z2,z3,z4,z5,z159,z8]),(0,[z55,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z218,z8]),(0,[z1,z2,z219,z3,z4,z5,z8]),(0,[z220,z1,z2,z3,z4,z5,z8])],[(1,[z1,z2,z221,z4,z5,z8])],[(1,[z1,z2,z3,z4,z23,z8]),(0,[z1,z2,z222,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z223,z5,z8])],[(1,[z76,z2,z3,z4,z5,z224]),(0,[z76,z1,z139,z2,z3,z4,z5]),(0,[z1,z154,z3,z4,z16,z5,z8]),(1,[z1,z2,z3,z4,z5,z225])],[(1,[z169,z2,z3,z32,z5,z8]),(0,[z1,z153,z2,z105,z4,z5,z8]),(0,[z1,z226,z2,z3,z4,z5,z8]),(0,[z1,z2,z105,z184,z4,z5,z8]),(0,[z1,z2,z3,z3,z4,z5,z28])],[(0,[z169,z0,z2,z3,z4,z5,z8]),(0,[z227,z1,z2,z3,z4,z5,z8]),(0,[z76,z1,z2,z3,z4,z5,z12]),(0,[z17,z1,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z50,z4,z5,z6]),(0,[z1,z2,z3,z4,z30,z5,z228])],[(0,[z1,z229,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z73,z8]),(0,[z1,z2,z43,z4,z25,z5,z8]),(0,[z230,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z231,z3,z4,z5,z8])],[(0,[z156,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z232,z3,z4,z5,z8]),(0,[z1,z233,z2,z3,z4,z5,z8]),(0,[z1,z2,z234,z3,z4,z5,z8]),(0,[z17,z230,z2,z3,z4,z5,z8]),(0,[z1,z103,z2,z3,z4,z25,z8]),(0,[z235,z1,z2,z3,z4,z149,z8])],[(0,[z1,z2,z3,z4,z59,z5,z8]),(0,[z1,z2,z3,z4,z5,z12,z38])],[(2,[z1,z2,z4,z5,z236])],[(0,[z1,z153,z2,z4,z5,z71,z8]),(0,[z1,z2,z237,z3,z4,z5,z8])],[(0,[z76,z1,z2,z3,z4,z117,z8]),(0,[z238,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z30,z239,z5])]],
   [[(0,[z1,z2,z3,z4,z94,z5,z8])],[(0,[z1,z240,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z30,z5,z12])],[(0,[z1,z2,z3,z4,z241,z5,z8]),(0,[z1,z2,z3,z242,z4,z5,z8]),(0,[z1,z243,z2,z3,z4,z5,z8]),(0,[z1,z2,z145,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z228,z8])],[(1,[z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z244,z5,z8]),(0,[z1,z2,z245,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z246]),(0,[z1,z2,z81,z3,z4,z5,z12])],[(0,[z1,z2,z3,z4,z247,z5,z8]),(0,[z55,z1,z2,z3,z4,z5,z28]),(0,[z248,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z144])],[(0,[z1,z2,z3,z4,z196,z5,z8]),(1,[z1,z2,z70,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z249])],[(0,[z250,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z81,z3,z4,z5,z225])],[(1,[z1,z2,z3,z251,z5,z8]),(0,[z1,z2,z3,z252,z4,z5,z8])],[(0,[z134,z1,z2,z54,z4,z5,z8]),(0,[z113,z2,z3,z4,z67,z5,z8]),(0,[z1,z2,z3,z4,z161,z5,z8]),(0,[z1,z2,z253,z3,z4,z5,z8]),(0,[z29,z1,z2,z3,z4,z5,z8])],[(0,[z254,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z255,z8])],[(0,[z1,z2,z3,z4,z5,z8,z256]),(1,[z1,z2,z3,z4,z5,z21]),(0,[z1,z2,z3,z4,z5,z8,z257]),(0,[z1,z3,z4,z5,z13,z8,z162]),(1,[z1,z2,z81,z50,z5,z8]),(0,[z1,z2,z3,z4,z5,z28,z258])],[(0,[z1,z2,z3,z4,z5,z73,z28])],[(0,[z1,z2,z3,z259,z4,z5,z8]),(0,[z1,z260,z2,z3,z4,z5,z8])],[(0,[z235,z1,z2,z4,z5,z8,z28])],[(0,[z1,z103,z69,z3,z4,z5,z8]),(0,[z1,z152,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z261,z5,z12])],[(1,[z1,z2,z262,z4,z5,z8]),(1,[z1,z2,z3,z215,z5,z8]),(1,[z1,z2,z3,z4,z5,z263])]],
   [[(0,[z1,z2,z3,z4,z5,z264,z8]),(0,[z1,z2,z3,z4,z265,z5,z8])],[(0,[z266,z1,z2,z3,z4,z5,z8]),(0,[z1,z267,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z268,z4,z5,z8])],[(0,[z1,z2,z3,z4,z67,z5,z6]),(0,[z47,z1,z2,z269,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z13,z6]),(0,[z1,z2,z3,z4,z94,z5,z28]),(0,[z1,z2,z146,z4,z30,z5,z8])],[(0,[z1,z103,z2,z3,z4,z30,z5])],[(1,[z1,z270,z3,z4,z5,z8]),(0,[z1,z3,z4,z72,z5,z197,z8]),(0,[z1,z2,z3,z4,z5,z8,z271]),(0,[z1,z2,z3,z213,z4,z30,z5])],[(0,[z1,z2,z3,z4,z30,z5,z13]),(0,[z1,z2,z105,z4,z5,z8,z28]),(1,[z1,z2,z3,z4,z5,z28]),(1,[z1,z2,z163,z4,z5,z6])],[(0,[z1,z69,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z32,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z197,z8]),(1,[z1,z2,z145,z4,z5,z8]),(0,[z272,z1,z2,z3,z4,z5,z8]),(0,[z1,z273,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z274,z5,z8]),(0,[z1,z2,z3,z4,z59,z86,z8]),(0,[z1,z2,z3,z4,z5,z224,z12]),(0,[z1,z2,z3,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z8,z275]),(0,[z1,z2,z3,z251,z4,z5,z8]),(0,[z95,z1,z2,z3,z4,z59,z8]),(0,[z1,z2,z3,z4,z5,z276,z8]),(0,[z17,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z277,z8]),(0,[z1,z2,z3,z278,z4,z5,z8])],[(0,[z29,z1,z2,z3,z4,z5,z28]),(0,[z1,z2,z279,z3,z4,z5,z8])],[(0,[z1,z280,z2,z3,z4,z5,z8]),(0,[z1,z2,z281,z3,z4,z5,z8]),(0,[z1,z2,z282,z3,z4,z5,z8]),(0,[z1,z2,z283,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z130]),(0,[z1,z2,z3,z4,z284,z5,z8])],[(0,[z1,z2,z3,z4,z5,z14,z39])],[(0,[z1,z260,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z285,z5,z8]),(0,[z1,z2,z4,z30,z5,z236,z8])],[(0,[z24,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z5,z286,z8]),(0,[z1,z287,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z64,z8])],[(0,[z1,z288,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z289,z4,z5,z8])],[(0,[z1,z2,z3,z290,z4,z5,z8])],[(1,[z1,z2,z3,z247,z5,z8]),(0,[z29,z1,z2,z3,z4,z86,z8]),(0,[z1,z2,z3,z291,z4,z5,z8])],[(0,[z55,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z30,z5,z164])],[(0,[z119,z1,z69,z3,z4,z5,z8]),(0,[z1,z2,z3,z292,z4,z5,z8])],[(1,[z1,z2,z3,z4,z293,z8]),(0,[z1,z2,z3,z4,z5,z21,z8]),(0,[z1,z2,z3,z4,z110,z5,z8])],[(0,[z294,z1,z2,z3,z4,z5,z8]),(1,[z113,z2,z20,z4,z5,z8]),(0,[z1,z2,z3,z4,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z6,z162])],[(0,[z1,z69,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z32,z4,z5,z28]),(0,[z295,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z197,z28]),(1,[z63,z2,z3,z4,z5,z8]),(0,[z235,z1,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z94,z5,z39])],[],[(0,[z1,z153,z2,z3,z4,z30,z5]),(0,[z24,z1,z103,z3,z4,z5,z8]),(0,[z1,z2,z296,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z30,z5,z71])],[(0,[z1,z2,z3,z4,z5,z73,z6]),(0,[z1,z2,z3,z4,z5,z297,z8]),(0,[z1,z125,z2,z3,z4,z5,z8]),(0,[z1,z114,z3,z4,z5,z8,z162]),(1,[z29,z1,z2,z3,z8,z164])],[(0,[z298,z1,z2,z3,z4,z5,z8]),(0,[z299,z1,z2,z3,z4,z30,z5])],[(0,[z1,z2,z3,z67,z51,z5,z8])],[],[(0,[z1,z2,z3,z300,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z6,z190]),(0,[z1,z2,z3,z4,z5,z8,z301])]],
   [[(0,[z1,z2,z3,z4,z72,z5,z216]),(0,[z1,z2,z105,z3,z4,z5,z12])],[(0,[z1,z2,z3,z4,z5,z8,z302]),(0,[z24,z1,z2,z3,z4,z5,z28]),(0,[z1,z303,z2,z3,z4,z5,z8]),(0,[z29,z1,z2,z3,z4,z8,z164])],[(0,[z1,z103,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z304,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z305,z8]),(0,[z1,z2,z3,z4,z94,z5,z6]),(0,[z1,z2,z111,z3,z4,z30,z5])],[(0,[z1,z2,z195,z3,z4,z5,z8]),(0,[z1,z2,z3,z213,z4,z5,z12])],[(0,[z1,z2,z3,z67,z16,z5,z8]),(0,[z1,z2,z3,z4,z306,z5,z8]),(0,[z1,z2,z3,z4,z5,z307,z8]),(0,[z308,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z4,z72,z5,z309,z8]),(0,[z1,z2,z3,z310,z4,z5,z8])],[(0,[z1,z2,z3,z4,z67,z5,z28]),(0,[z1,z2,z3,z4,z5,z13,z28]),(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z30,z5,z8])],[(0,[z1,z2,z3,z4,z311,z5,z8])],[(0,[z1,z2,z3,z4,z5,z309,z8]),(0,[z1,z2,z3,z4,z5,z162,z28]),(0,[z1,z2,z3,z4,z5,z12,z162]),(0,[z1,z2,z81,z50,z4,z5,z8]),(0,[z1,z155,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z14,z8])],[(0,[z1,z312,z2,z3,z4,z5,z8]),(0,[z313,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z314,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z315]),(1,[z1,z2,z50,z4,z5,z28])],[(0,[z1,z2,z3,z4,z316,z5,z8]),(0,[z1,z2,z3,z4,z317,z5,z8]),(0,[z29,z1,z2,z3,z4,z5,z6])],[(0,[z24,z1,z2,z3,z4,z71,z8])],[(0,[z119,z1,z2,z3,z4,z5,z65]),(0,[z1,z2,z105,z3,z4,z25,z8])],[(0,[z1,z2,z3,z4,z23,z5,z8]),(0,[z1,z125,z2,z3,z4,z5,z28])],[(0,[z318,z1,z2,z3,z4,z5,z8]),(0,[z1,z167,z2,z3,z4,z5,z8])],[(0,[z319,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z320,z8]),(0,[z1,z2,z3,z4,z5,z321,z8])]],
   [[(0,[z1,z2,z322,z3,z4,z5,z8]),(0,[z1,z2,z3,z323,z4,z5,z8])],[(0,[z113,z1,z2,z54,z4,z5,z8]),(0,[z1,z2,z3,z4,z72,z59,z8])],[(1,[z1,z2,z324,z4,z5,z8]),(1,[z1,z2,z3,z325,z4,z5])],[(0,[z1,z103,z2,z3,z4,z5,z144]),(0,[z1,z2,z3,z4,z5,z8,z326]),(0,[z1,z2,z327,z3,z4,z5,z8])],[(0,[z328,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z329,z8])],[(0,[z1,z2,z3,z4,z330,z5,z8])],[(0,[z1,z2,z3,z4,z30,z5,z28]),(0,[z1,z2,z3,z4,z5,z331,z8]),(0,[z1,z2,z3,z4,z5,z8,z332])],[(0,[z1,z69,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z32,z4,z5,z6]),(0,[z1,z2,z333,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z334,z5,z8]),(0,[z1,z2,z3,z4,z5,z197,z6]),(0,[z1,z2,z3,z4,z5,z8,z335]),(0,[z1,z336,z2,z3,z4,z5,z8])],[(0,[z119,z1,z2,z3,z4,z5,z12]),(0,[z1,z69,z3,z15,z4,z5,z8]),(0,[z95,z2,z3,z4,z67,z5,z8]),(0,[z1,z153,z2,z3,z4,z5,z12]),(0,[z1,z125,z3,z33,z4,z5,z8]),(0,[z1,z155,z2,z3,z4,z5,z28])],[(0,[z337,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z14,z28]),(0,[z1,z2,z324,z3,z4,z5,z8])],[(0,[z1,z2,z338,z3,z4,z5,z8]),(0,[z169,z113,z2,z3,z4,z5,z8]),(0,[z76,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z339,z3,z4,z5,z8]),(0,[z235,z1,z2,z4,z51,z5,z8]),(0,[z1,z2,z3,z4,z5,z340,z8])],[(0,[z1,z2,z3,z4,z5,z8,z224]),(0,[z235,z1,z2,z3,z51,z5,z8]),(0,[z235,z1,z2,z3,z4,z30,z5]),(1,[z1,z2,z3,z4,z5,z341]),(0,[z1,z2,z279,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z342,z8])],[(0,[z1,z139,z69,z3,z4,z5,z8]),(1,[z1,z58,z3,z4,z5,z8]),(0,[z1,z2,z262,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z343,z5]),(0,[z1,z2,z3,z344,z4,z5,z8])],[],[(0,[z47,z1,z2,z3,z4,z30,z5]),(0,[z345,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z47,z95,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z346]),(0,[z1,z2,z3,z4,z347,z5,z8])],[(0,[z169,z1,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z59,z5,z28]),(0,[z24,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z348,z5,z8]),(0,[z1,z2,z111,z3,z4,z5,z12])],[(0,[z69,z2,z214,z3,z4,z5,z8]),(0,[z1,z2,z349,z3,z4,z5,z8]),(0,[z24,z1,z3,z15,z4,z5,z8]),(0,[z1,z2,z3,z350,z4,z5,z8]),(0,[z1,z139,z2,z3,z4,z30,z5]),(0,[z1,z2,z3,z4,z5,z286,z6])],[(0,[z1,z2,z3,z4,z120,z5,z8]),(0,[z119,z2,z214,z3,z4,z5,z8]),(0,[z1,z2,z351,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z352,z8]),(0,[z17,z1,z2,z350,z4,z5,z8]),(0,[z1,z2,z353,z3,z4,z5,z8])],[(0,[z1,z2,z3,z354,z4,z5,z8]),(0,[z1,z2,z3,z355,z4,z5,z8]),(0,[z1,z2,z105,z3,z4,z30,z5]),(1,[z185,z2,z3,z4,z5,z8]),(0,[z1,z2,z356,z3,z4,z5,z8])],[(0,[z1,z357,z2,z3,z4,z5,z8]),(0,[z1,z2,z163,z54,z4,z5,z8]),(0,[z1,z2,z3,z54,z4,z5,z12]),(0,[z1,z2,z3,z358,z4,z5,z8]),(1,[z1,z359,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z360,z5,z8]),(0,[z1,z2,z3,z4,z73,z71,z8]),(0,[z1,z2,z81,z3,z4,z5,z8])],[(0,[z1,z154,z2,z105,z4,z5,z8]),(0,[z1,z3,z4,z16,z5,z197,z8])],[(0,[z1,z2,z214,z3,z4,z30,z5]),(0,[z1,z103,z125,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z361])],[(0,[z29,z185,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z6,z224]),(0,[z1,z362,z2,z3,z4,z5,z8])],[(0,[z169,z2,z214,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z59,z71,z8]),(1,[z230,z2,z3,z4,z5,z8]),(0,[z235,z1,z2,z163,z4,z5,z8])],[(0,[z363,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z364,z3,z4,z5,z8]),(0,[z365,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z86,z73,z8]),(0,[z1,z366,z2,z3,z4,z5,z8]),(0,[z76,z1,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z367,z4,z5,z8]),(0,[z1,z125,z2,z3,z4,z5,z6]),(0,[z1,z114,z2,z368,z4,z5,z8]),(0,[z235,z1,z2,z81,z4,z5,z8]),(0,[z1,z2,z3,z4,z30,z5,z39])],[(0,[z1,z2,z3,z4,z59,z8,z39]),(0,[z1,z125,z3,z15,z4,z5,z8]),(0,[z369,z1,z2,z3,z4,z5,z8]),(0,[z1,z370,z2,z3,z4,z30,z5])],[(0,[z1,z2,z3,z371,z4,z5,z8])]],
   [[],[(0,[z0,z69,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z372,z8]),(0,[z1,z2,z3,z4,z5,z6,z373])],[(0,[z374,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z375,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z71,z8,z164]),(0,[z1,z2,z3,z4,z5,z39,z28]),(0,[z1,z2,z3,z4,z5,z376,z12]),(0,[z1,z2,z3,z4,z94,z8,z39])],[(0,[z1,z2,z3,z4,z73,z8,z164]),(1,[z1,z2,z242,z4,z5,z8]),(0,[z1,z2,z105,z163,z4,z5,z8])],[(1,[z1,z2,z3,z4,z377,z8])],[(0,[z1,z378,z2,z3,z4,z5,z8]),(0,[z95,z2,z3,z4,z59,z5,z8]),(0,[z1,z2,z379,z3,z4,z5,z8]),(0,[z1,z2,z105,z81,z4,z5,z8])],[(0,[z134,z113,z2,z3,z4,z5,z8]),(0,[z1,z2,z380,z3,z4,z5,z8]),(0,[z34,z2,z3,z4,z67,z5,z8]),(1,[z1,z2,z3,z4,z5,z381]),(0,[z1,z2,z382,z3,z4,z5,z8]),(0,[z1,z2,z78,z3,z4,z5,z8])],[(0,[z383,z1,z2,z3,z4,z5,z8]),(0,[z17,z1,z2,z3,z4,z5,z384]),(0,[z1,z2,z3,z4,z30,z5,z6])],[(0,[z1,z2,z3,z4,z59,z8,z164]),(0,[z1,z2,z81,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z8,z385])],[(0,[z1,z155,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z386,z5,z8]),(0,[z1,z2,z253,z3,z4,z5,z73]),(0,[z1,z2,z3,z387,z4,z5,z8])],[(0,[z1,z2,z3,z4,z388,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z389]),(0,[z1,z2,z3,z4,z5,z8,z390]),(0,[z29,z1,z2,z3,z213,z5,z8])],[(0,[z119,z1,z2,z3,z4,z30,z5]),(0,[z391,z1,z2,z3,z4,z5,z8]),(1,[z55,z2,z3,z4,z5,z14]),(0,[z1,z2,z3,z4,z392,z5,z8])],[(0,[z0,z2,z3,z4,z67,z5,z8]),(0,[z1,z2,z3,z4,z393,z5,z8]),(0,[z47,z1,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z28,z28]),(0,[z1,z394,z2,z3,z4,z5,z8])],[(0,[z1,z395,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z396,z5,z8]),(0,[z1,z2,z3,z397,z4,z5,z8]),(0,[z1,z2,z398,z3,z4,z5,z8])]],
   [[(1,[z1,z2,z350,z4,z5,z8]),(0,[z1,z399,z2,z3,z4,z5,z12]),(0,[z1,z2,z400,z3,z4,z5,z8])],[(1,[z1,z2,z3,z4,z5,z401]),(0,[z1,z2,z3,z4,z5,z402,z8]),(1,[z95,z2,z3,z4,z59,z8]),(0,[z1,z2,z3,z4,z59,z5,z6]),(1,[z1,z403,z3,z4,z5,z8]),(0,[z1,z139,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z8,z404]),(0,[z1,z2,z3,z4,z405,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z406])],[(0,[z1,z2,z3,z4,z5,z8,z407])],[(0,[z1,z2,z3,z4,z5,z408,z8])],[(0,[z409,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z410,z3,z4,z5,z12])],[(0,[z411,z1,z2,z3,z4,z5,z8]),(0,[z169,z1,z2,z3,z4,z30,z5]),(0,[z1,z2,z3,z4,z412,z5,z8]),(0,[z413,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z12,z271]),(0,[z1,z2,z3,z4,z5,z8,z376])],[(0,[z169,z95,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z414,z8])],[(0,[z1,z2,z214,z3,z4,z5,z12]),(0,[z1,z2,z77,z3,z4,z5,z8]),(0,[z415,z1,z2,z3,z4,z5,z12])],[(0,[z1,z2,z184,z43,z4,z5,z8]),(0,[z1,z2,z43,z3,z4,z5,z12]),(0,[z416,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z54,z4,z30,z5]),(0,[z1,z2,z3,z32,z4,z5,z381]),(0,[z1,z2,z3,z4,z5,z8,z417]),(0,[z1,z2,z3,z418,z4,z5,z8])],[(1,[z119,z214,z3,z4,z5,z8]),(0,[z1,z2,z3,z32,z213,z5,z8]),(0,[z1,z2,z419,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z86,z197,z8]),(0,[z1,z139,z2,z3,z87,z4,z5]),(0,[z1,z2,z3,z4,z420,z5,z8])],[(0,[z119,z1,z2,z53,z4,z5,z8]),(0,[z1,z2,z3,z4,z421,z5,z8]),(0,[z1,z422,z2,z3,z4,z5,z8]),(0,[z235,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z81,z3,z50,z5,z8])],[(0,[z169,z2,z3,z54,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z224,z28]),(0,[z1,z2,z3,z4,z423,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z193]),(0,[z424,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z425,z5,z8])],[(0,[z1,z426,z2,z3,z4,z5,z8]),(0,[z76,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z25,z5,z12])],[(0,[z1,z2,z3,z32,z50,z5,z8])],[(0,[z427,z1,z2,z3,z4,z5,z8]),(0,[z428,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z429])]],
   [[(0,[z1,z2,z3,z4,z5,z430,z8]),(0,[z1,z431,z2,z3,z4,z5,z8]),(1,[z235,z1,z2,z51,z5,z8]),(0,[z1,z432,z105,z3,z4,z5,z8])],[(0,[z433,z1,z2,z3,z4,z5,z8]),(0,[z1,z103,z2,z324,z4,z5,z8]),(0,[z1,z114,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z236,z8])],[(0,[z1,z434,z2,z214,z3,z4,z5]),(0,[z1,z2,z3,z213,z67,z5,z8]),(0,[z1,z435,z2,z3,z4,z5,z8]),(0,[z1,z2,z43,z3,z4,z5,z128]),(0,[z1,z436,z2,z3,z4,z5,z12]),(0,[z1,z2,z437,z3,z4,z5,z8])],[(0,[z1,z154,z2,z43,z4,z5,z8]),(0,[z1,z2,z105,z3,z4,z5,z8])],[(1,[z1,z2,z3,z4,z5,z384]),(0,[z1,z2,z111,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z28,z438])],[(0,[z1,z154,z69,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z439,z5]),(0,[z1,z103,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z11])],[(0,[z1,z214,z3,z15,z4,z5,z8]),(0,[z1,z121,z2,z214,z3,z4,z5]),(0,[z1,z2,z3,z4,z440,z5,z8]),(0,[z1,z441,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z213,z4,z5,z8]),(0,[z1,z66,z2,z3,z204,z5,z8])],[(0,[z1,z2,z184,z15,z4,z5,z8]),(0,[z1,z2,z3,z4,z442,z5,z8]),(0,[z1,z2,z3,z4,z443,z5,z8])],[(0,[z1,z2,z81,z3,z4,z5,z6])],[(0,[z444,z1,z2,z3,z4,z5,z8]),(0,[z1,z139,z214,z3,z4,z5,z8])],[(0,[z47,z1,z2,z3,z215,z5,z8]),(0,[z1,z2,z3,z4,z147,z5,z8])],[(0,[z1,z2,z3,z445,z4,z5,z8]),(0,[z1,z2,z43,z3,z4,z147,z8]),(0,[z1,z2,z3,z4,z5,z446,z8]),(0,[z1,z2,z3,z204,z4,z30,z5])],[(0,[z1,z2,z447,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z448]),(1,[z1,z2,z3,z4,z5,z449]),(0,[z1,z2,z450,z3,z4,z5,z8])],[(0,[z1,z103,z214,z3,z4,z5,z8]),(0,[z1,z451,z2,z3,z4,z5,z8]),(1,[z1,z452,z3,z4,z5,z8]),(0,[z95,z1,z2,z3,z4,z73,z8]),(0,[z235,z1,z2,z3,z4,z5,z28])],[(0,[z1,z2,z3,z453,z4,z5,z8])],[(1,[z1,z2,z3,z4,z5,z96]),(0,[z1,z2,z105,z3,z4,z5,z263]),(0,[z1,z2,z3,z454,z4,z5,z8]),(1,[z1,z2,z3,z204,z5,z12])]],
   [[(0,[z134,z1,z2,z3,z4,z30,z5]),(0,[z455,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z4,z94,z5,z140,z8])],[(0,[z1,z2,z3,z4,z30,z5,z197]),(0,[z1,z2,z456,z3,z4,z5,z8])],[(0,[z457,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z100]),(1,[z1,z2,z20,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z224,z39]),(0,[z1,z2,z3,z87,z4,z5,z224]),(0,[z1,z154,z2,z15,z4,z5,z8]),(0,[z1,z458,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z459,z5,z8])],[(0,[z1,z2,z163,z43,z4,z5,z8])],[(0,[z1,z2,z3,z460,z4,z5,z8]),(0,[z461,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z105,z3,z4,z5,z28]),(0,[z1,z2,z3,z462,z4,z5,z8])],[(0,[z1,z2,z105,z4,z51,z5,z8]),(0,[z1,z2,z184,z4,z5,z71,z8]),(1,[z1,z2,z3,z4,z5,z236]),(0,[z1,z2,z3,z4,z463,z30,z5])],[(0,[z1,z464,z2,z3,z4,z5,z8]),(0,[z134,z2,z3,z54,z4,z5,z8]),(0,[z1,z103,z2,z3,z4,z5,z28])],[(0,[z1,z2,z3,z32,z4,z439,z5]),(1,[z1,z2,z4,z5,z309,z8]),(0,[z1,z2,z3,z4,z5,z8,z465]),(0,[z1,z441,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z213,z4,z5,z28])],[(0,[z1,z2,z3,z466,z4,z5,z8]),(1,[z1,z155,z2,z4,z5,z28]),(0,[z1,z2,z3,z4,z467,z5,z8])],[(0,[z468,z1,z2,z3,z4,z5,z8]),(0,[z1,z469,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z470,z8]),(0,[z1,z2,z3,z471,z4,z5,z8])],[(0,[z1,z2,z3,z472,z4,z5,z8])],[(0,[z473,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z73,z8,z39]),(0,[z1,z2,z3,z4,z5,z117,z8]),(0,[z1,z153,z2,z3,z4,z5,z8]),(0,[z1,z2,z43,z3,z4,z30,z5]),(0,[z1,z2,z3,z4,z5,z474,z8]),(0,[z1,z475,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z476,z5,z8])],[(0,[z477,z1,z2,z3,z4,z5,z8]),(0,[z17,z1,z3,z4,z16,z5,z8]),(0,[z1,z2,z111,z3,z87,z4,z5])],[(0,[z299,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z478,z4,z5,z8]),(0,[z1,z2,z3,z479,z4,z5,z8]),(0,[z480,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z34,z1,z2,z3,z4,z5,z389]),(0,[z169,z1,z2,z3,z67,z5,z8]),(0,[z1,z2,z43,z4,z5,z8,z28]),(0,[z235,z63,z2,z3,z4,z5,z8])],[(0,[z1,z2,z132,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z142]),(0,[z1,z154,z2,z4,z5,z71,z8]),(0,[z1,z2,z3,z4,z5,z8,z481]),(0,[z1,z2,z3,z397,z4,z5,z6]),(0,[z1,z2,z3,z213,z4,z86,z8])],[(0,[z1,z2,z3,z4,z5,z482,z8]),(0,[z1,z2,z163,z15,z4,z5,z8]),(0,[z1,z2,z3,z4,z483,z5,z8])],[(0,[z484,z1,z2,z3,z4,z5,z8])],[(0,[z119,z1,z214,z3,z4,z5,z8]),(0,[z169,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z485]),(0,[z1,z139,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z459,z5,z28]),(0,[z1,z2,z3,z4,z261,z5,z8]),(0,[z1,z2,z111,z3,z4,z5,z8])],[(0,[z169,z1,z2,z3,z32,z5,z8]),(0,[z1,z114,z2,z3,z4,z30,z5]),(0,[z1,z2,z486,z3,z4,z5,z8]),(0,[z29,z99,z2,z3,z4,z5,z8])],[],[(0,[z1,z487,z2,z3,z4,z5,z8]),(0,[z413,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z54,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z488,z8]),(0,[z1,z2,z3,z4,z330,z5,z73]),(0,[z29,z1,z2,z3,z4,z5,z249])],[(0,[z489,z1,z2,z3,z4,z5,z8]),(0,[z1,z154,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z384,z8]),(0,[z1,z139,z2,z3,z4,z5,z39])],[(0,[z1,z2,z184,z3,z4,z25,z8]),(0,[z1,z2,z3,z4,z5,z8,z490]),(0,[z1,z2,z3,z204,z4,z5,z12])],[(0,[z76,z1,z2,z242,z4,z5,z8]),(1,[z1,z432,z3,z4,z5,z8])],[(0,[z1,z491,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z492,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z493,z8]),(0,[z1,z2,z3,z4,z420,z5,z6])],[(0,[z1,z2,z43,z81,z4,z5,z8]),(0,[z235,z1,z2,z3,z4,z5,z6]),(0,[z494,z1,z2,z3,z4,z5,z8])],[(0,[z2,z214,z3,z4,z67,z5,z8]),(0,[z1,z153,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z30,z25,z5]),(0,[z1,z495,z2,z3,z4,z5,z8])],[(0,[z134,z1,z2,z3,z4,z5,z12]),(0,[z477,z1,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z213,z4,z8,z164]),(1,[z1,z2,z3,z4,z496,z5])]],
   [[],[(0,[z1,z2,z3,z33,z4,z30,z5]),(0,[z1,z2,z163,z4,z5,z71,z8])],[(0,[z1,z2,z3,z4,z5,z401,z8])],[(1,[z1,z2,z3,z4,z497,z8]),(1,[z1,z154,z43,z4,z5,z8])],[(0,[z1,z2,z3,z4,z498,z5,z8]),(0,[z1,z2,z3,z4,z499,z5,z8]),(0,[z1,z2,z3,z4,z94,z5,z162])],[(0,[z1,z2,z105,z3,z4,z5,z6])],[(0,[z1,z2,z3,z500,z4,z5,z8]),(0,[z1,z2,z3,z4,z72,z73,z8]),(0,[z1,z2,z111,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z12,z465])],[(0,[z1,z2,z43,z3,z4,z5,z89]),(0,[z1,z103,z2,z3,z4,z5,z6]),(1,[z1,z2,z375,z4,z5,z8])],[(1,[z1,z2,z3,z501,z5,z8]),(0,[z1,z2,z3,z4,z5,z502,z8]),(0,[z1,z2,z503,z3,z4,z5,z8]),(0,[z1,z2,z3,z213,z4,z5,z6]),(0,[z504,z1,z2,z3,z4,z30,z5])],[(0,[z1,z2,z3,z4,z5,z505,z8]),(0,[z1,z2,z3,z4,z497,z5,z8]),(0,[z1,z2,z506,z3,z4,z5,z8]),(0,[z76,z1,z403,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z507]),(0,[z508,z1,z2,z3,z4,z5,z8])],[(0,[z1,z509,z2,z3,z4,z5,z8])],[],[(0,[z119,z1,z2,z3,z247,z5,z8]),(0,[z1,z2,z510,z3,z4,z5,z8]),(0,[z1,z2,z511,z3,z4,z5,z8]),(0,[z1,z2,z3,z512,z4,z5,z8])],[(0,[z1,z135,z2,z3,z4,z5,z8]),(0,[z1,z2,z513,z3,z4,z5,z8]),(0,[z1,z2,z514,z3,z4,z5,z8])],[],[(0,[z119,z1,z2,z3,z4,z293,z8]),(1,[z1,z135,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z515,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z516]),(0,[z1,z432,z2,z3,z4,z5,z8]),(0,[z517,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z518,z2,z3,z4,z5,z8]),(1,[z24,z1,z3,z4,z197,z8])],[(0,[z47,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z2,z3,z4,z5,z8]),(0,[z1,z519,z2,z3,z4,z5,z8]),(0,[z1,z2,z520,z3,z4,z5,z8]),(0,[z1,z2,z184,z3,z4,z30,z5]),(0,[z1,z2,z3,z4,z521,z5,z8])],[(0,[z134,z1,z2,z3,z251,z5,z8]),(0,[z1,z399,z2,z3,z4,z5,z8])],[(0,[z1,z2,z522,z3,z4,z5,z8]),(0,[z1,z139,z2,z3,z4,z5,z8])],[(0,[z523,z1,z2,z3,z4,z5,z8]),(0,[z1,z3,z33,z4,z16,z5,z8]),(0,[z1,z2,z3,z524,z4,z5,z8])],[(0,[z1,z2,z3,z15,z4,z30,z5]),(1,[z1,z525,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z28,z171])],[(0,[z526,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z410,z3,z4,z5,z8])],[(0,[z34,z1,z2,z3,z4,z5,z402]),(0,[z1,z2,z3,z4,z439,z5,z8]),(0,[z1,z2,z3,z4,z30,z5,z236])],[(0,[z1,z2,z3,z4,z527,z5,z8]),(0,[z1,z2,z528,z3,z4,z5,z8])],[(0,[z1,z2,z214,z3,z4,z5,z8]),(0,[z1,z529,z2,z3,z4,z5,z8]),(0,[z415,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z530,z4,z5,z8]),(0,[z531,z1,z2,z3,z4,z5,z8]),(0,[z17,z1,z2,z3,z4,z264,z8]),(0,[z1,z2,z3,z532,z4,z5,z8]),(0,[z1,z2,z3,z4,z533,z5,z8])],[(0,[z534,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z111,z3,z4,z5,z39])],[(0,[z1,z69,z3,z4,z16,z5,z8]),(0,[z47,z1,z2,z262,z4,z5,z8]),(1,[z1,z2,z3,z4,z42,z8]),(0,[z1,z154,z2,z3,z4,z30,z5]),(0,[z1,z114,z2,z3,z87,z4,z5]),(0,[z235,z1,z359,z3,z4,z5,z8]),(0,[z1,z525,z2,z3,z4,z5,z8]),(0,[z535,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z12,z390]),(0,[z1,z2,z398,z4,z94,z5,z8])],[(0,[z2,z3,z4,z59,z5,z73,z8]),(0,[z1,z153,z2,z3,z4,z5,z6]),(1,[z1,z139,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z8,z536])],[(0,[z2,z3,z32,z4,z67,z5,z8]),(0,[z1,z537,z2,z3,z4,z5,z8]),(0,[z1,z153,z3,z15,z4,z5,z8]),(0,[z1,z154,z125,z3,z4,z5,z8]),(0,[z538,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z177]),(0,[z1,z2,z3,z4,z5,z8,z12])]],
   [[(0,[z1,z2,z3,z33,z4,z5,z12]),(0,[z1,z370,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z25,z5,z8]),(0,[z1,z2,z3,z4,z539,z5,z8]),(0,[z1,z2,z3,z4,z5,z6,z429])],[(0,[z1,z2,z3,z4,z5,z210,z8]),(0,[z1,z2,z3,z540,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z216])],[(0,[z1,z2,z541,z3,z4,z5,z8]),(0,[z76,z1,z2,z3,z4,z42,z8]),(0,[z1,z2,z3,z4,z5,z542,z8]),(0,[z1,z2,z543,z3,z4,z5,z8]),(0,[z1,z2,z184,z3,z4,z5,z64]),(1,[z1,z273,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z544])],[(0,[z1,z2,z270,z3,z4,z5,z8]),(0,[z47,z1,z2,z3,z4,z5,z28]),(0,[z55,z1,z2,z111,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z507,z28])],[(0,[z1,z2,z3,z4,z545,z5,z8]),(0,[z1,z546,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z547,z8]),(1,[z1,z2,z105,z4,z25,z8])],[(0,[z17,z243,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z548,z5,z8]),(0,[z1,z436,z2,z3,z4,z5,z8])],[(0,[z169,z1,z2,z3,z4,z5,z6]),(0,[z1,z139,z2,z3,z4,z5,z28]),(0,[z549,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z111,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z550,z12])],[(0,[z551,z1,z2,z3,z4,z5,z8]),(0,[z552,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z553,z5,z8]),(0,[z29,z1,z273,z3,z4,z5,z8]),(0,[z1,z554,z2,z3,z4,z5,z8]),(0,[z504,z1,z2,z3,z4,z5,z12])],[(0,[z1,z555,z2,z3,z4,z5,z8])],[(0,[z55,z1,z2,z3,z4,z5,z224]),(0,[z1,z556,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z128]),(0,[z1,z2,z3,z4,z557,z5,z8])],[(0,[z1,z2,z3,z54,z4,z5,z6]),(0,[z1,z2,z3,z4,z30,z5,z73]),(1,[z1,z2,z3,z4,z5,z502])],[(0,[z1,z2,z558,z3,z4,z5,z8])],[(0,[z1,z2,z214,z3,z4,z5,z28]),(1,[z1,z2,z398,z4,z5,z8])],[(0,[z1,z2,z163,z4,z5,z6,z8]),(0,[z1,z2,z163,z3,z4,z30,z5]),(0,[z559,z1,z2,z3,z4,z5,z12])],[(0,[z1,z2,z43,z4,z51,z5,z8])],[(0,[z119,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z134,z1,z2,z3,z196,z5,z8])],[(0,[z1,z2,z20,z15,z4,z5,z8]),(0,[z560,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z343,z5,z8]),(0,[z1,z2,z3,z4,z561,z5,z8]),(0,[z1,z2,z184,z3,z4,z5,z12])],[(0,[z1,z2,z105,z3,z4,z71,z8]),(0,[z1,z2,z3,z4,z25,z5,z28]),(0,[z1,z2,z3,z4,z5,z164,z28]),(1,[z1,z2,z4,z5,z236,z8])],[(0,[z1,z2,z3,z4,z562,z5,z8]),(0,[z1,z2,z3,z4,z5,z6,z14]),(0,[z235,z1,z2,z3,z50,z5,z8]),(1,[z99,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z65,z8]),(0,[z563,z1,z2,z3,z4,z5,z8]),(0,[z1,z103,z2,z3,z4,z71,z8])],[(0,[z1,z2,z3,z15,z4,z5,z12]),(0,[z1,z2,z4,z5,z6,z8,z28]),(0,[z1,z2,z564,z3,z4,z5,z8])],[(0,[z2,z3,z4,z5,z14,z8,z224]),(0,[z1,z2,z3,z4,z5,z565,z8]),(0,[z1,z2,z3,z566,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z249])],[(0,[z0,z1,z69,z3,z4,z5,z8]),(1,[z226,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z50,z4,z5,z326]),(0,[z1,z2,z3,z4,z548,z5,z28]),(0,[z1,z2,z567,z3,z4,z30,z5])],[(0,[z113,z1,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z8,z160]),(0,[z1,z2,z3,z4,z5,z5,z8]),(0,[z1,z2,z3,z33,z4,z5,z157]),(0,[z1,z2,z3,z4,z51,z5,z465])],[(0,[z1,z2,z3,z568,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z569,z8]),(0,[z1,z2,z15,z4,z25,z5,z8]),(0,[z1,z2,z3,z4,z30,z5,z162])],[(0,[z1,z570,z2,z3,z4,z5,z8])],[(1,[z1,z2,z3,z4,z5,z256]),(0,[z1,z2,z3,z4,z5,z8,z166]),(0,[z1,z2,z3,z4,z25,z86,z8])],[(0,[z1,z2,z3,z4,z5,z14,z162]),(0,[z571,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z572,z5,z8])],[(0,[z1,z2,z3,z4,z5,z573,z8]),(0,[z235,z1,z2,z3,z4,z414,z8])],[]],
   [[(0,[z1,z2,z20,z4,z5,z71,z8]),(0,[z1,z2,z3,z4,z574,z5,z8])],[(0,[z119,z1,z2,z3,z4,z5,z28])],[(1,[z243,z2,z3,z4,z5,z8]),(0,[z1,z518,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z575,z5,z8])],[(0,[z576,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z269,z4,z5,z8]),(0,[z47,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z71,z12]),(0,[z1,z2,z3,z30,z5,z8,z12])],[(0,[z577,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z550])],[(0,[z578,z1,z2,z3,z4,z5,z8]),(0,[z1,z139,z2,z3,z4,z5,z6])],[(1,[z1,z103,z3,z4,z72,z8]),(0,[z1,z114,z2,z3,z4,z5,z13])],[],[(0,[z1,z2,z3,z4,z5,z579,z8]),(0,[z169,z1,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z25,z8,z164]),(0,[z1,z2,z3,z4,z86,z5,z12])],[],[(0,[z580,z1,z2,z3,z4,z5,z8]),(0,[z581,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z214,z3,z4,z5,z6]),(0,[z1,z2,z582,z3,z4,z5,z8]),(0,[z1,z154,z2,z3,z4,z5,z8]),(0,[z1,z114,z2,z3,z4,z5,z39]),(0,[z1,z2,z163,z3,z4,z5,z12])],[(0,[z1,z2,z3,z54,z4,z5,z28]),(1,[z1,z2,z3,z4,z5,z130]),(0,[z235,z1,z2,z3,z4,z5,z11]),(0,[z1,z2,z3,z204,z4,z5,z8]),(1,[z1,z2,z3,z4,z94,z39])],[(0,[z1,z2,z583,z3,z4,z5,z8]),(1,[z1,z2,z111,z3,z87,z4])],[(0,[z1,z2,z3,z4,z584,z5,z8]),(0,[z1,z585,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z105,z20,z4,z5,z8]),(0,[z586,z1,z2,z3,z4,z5,z8]),(0,[z1,z105,z283,z3,z4,z5,z8])],[(0,[z1,z2,z3,z32,z5,z8,z12]),(0,[z1,z2,z3,z4,z5,z8,z587]),(0,[z1,z2,z3,z588,z4,z5,z8])],[(0,[z134,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z589]),(0,[z1,z2,z3,z4,z5,z590,z8]),(0,[z76,z55,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z562,z5,z8]),(0,[z1,z2,z3,z591,z4,z5,z8]),(0,[z1,z2,z3,z4,z25,z5,z6])],[(0,[z34,z1,z2,z3,z4,z5,z12]),(0,[z1,z592,z2,z3,z4,z5,z8])],[(0,[z1,z154,z214,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z593,z8]),(0,[z1,z2,z3,z4,z594,z5,z8]),(1,[z235,z1,z2,z4,z5,z28]),(0,[z1,z595,z2,z3,z4,z5,z8])],[],[],[(1,[z1,z152,z3,z4,z5,z8]),(0,[z235,z1,z2,z3,z4,z5,z96]),(0,[z1,z2,z3,z4,z596,z30,z5])],[(0,[z1,z2,z3,z4,z597,z5,z8]),(0,[z47,z1,z452,z3,z4,z5,z8]),(0,[z24,z1,z2,z3,z4,z72,z8]),(0,[z1,z2,z3,z4,z5,z8,z598]),(0,[z1,z2,z3,z4,z463,z5,z8])],[(0,[z599,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z600,z8])],[(0,[z1,z214,z3,z4,z16,z5,z8]),(0,[z95,z1,z2,z3,z4,z30,z5]),(0,[z1,z2,z3,z4,z5,z13,z224]),(0,[z1,z2,z3,z4,z5,z8,z170]),(0,[z24,z1,z2,z3,z4,z197,z8]),(0,[z1,z555,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z8,z601])],[(0,[z1,z2,z3,z4,z5,z293,z8]),(0,[z0,z1,z2,z3,z4,z5,z12])],[(0,[z1,z2,z3,z602,z4,z5,z8]),(0,[z113,z1,z2,z3,z4,z30,z5])],[(1,[z1,z2,z3,z4,z159,z8]),(0,[z1,z2,z3,z603,z4,z5,z8]),(0,[z1,z2,z503,z3,z4,z5,z28])],[(0,[z1,z2,z43,z3,z4,z5,z8]),(0,[z1,z604,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z72,z5,z12]),(0,[z1,z2,z3,z204,z4,z5,z28])]],
   [[(0,[z1,z2,z3,z4,z5,z8,z605]),(1,[z1,z2,z3,z4,z5,z301]),(0,[z1,z2,z3,z4,z30,z86,z5])],[(0,[z119,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z104,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z164])],[(0,[z1,z606,z2,z3,z4,z5,z8])],[(0,[z1,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z258])],[(0,[z134,z1,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z607,z8]),(0,[z1,z2,z359,z3,z4,z5,z8])],[(1,[z1,z2,z253,z3,z4,z5]),(1,[z1,z125,z3,z33,z5,z8]),(0,[z1,z2,z3,z87,z4,z5,z12])],[(1,[z1,z178,z3,z4,z5,z8]),(0,[z1,z2,z3,z608,z4,z5,z8]),(0,[z1,z609,z2,z3,z4,z5,z8])],[(0,[z55,z2,z3,z4,z5,z14,z8]),(0,[z1,z114,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z610,z5,z8]),(0,[z1,z2,z3,z86,z5,z8,z164])],[],[],[(0,[z1,z58,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z115,z30,z5])],[(1,[z1,z2,z54,z4,z5,z28]),(0,[z1,z2,z611,z3,z4,z5,z8]),(0,[z1,z2,z3,z87,z4,z5,z14])],[(0,[z1,z2,z20,z3,z4,z30,z5]),(0,[z1,z2,z3,z4,z30,z5,z224]),(0,[z1,z2,z3,z4,z612,z5,z8]),(0,[z1,z2,z3,z4,z5,z613,z8])],[(0,[z614,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z325,z4,z72,z5]),(1,[z1,z2,z512,z4,z5,z8])],[(0,[z34,z1,z2,z3,z4,z161,z8]),(0,[z1,z2,z3,z4,z5,z224,z162])],[(1,[z1,z2,z3,z4,z120,z8]),(0,[z1,z2,z3,z33,z67,z5,z8]),(0,[z1,z2,z3,z4,z615,z5,z8]),(1,[z1,z114,z3,z4,z5,z162])]],
   [[(0,[z1,z2,z20,z4,z5,z8,z28]),(0,[z1,z2,z221,z3,z4,z5,z8]),(0,[z1,z2,z43,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z6,z12])],[],[(0,[z1,z2,z616,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z8]),(0,[z29,z1,z2,z512,z4,z5,z8])],[(1,[z1,z2,z3,z48,z5,z8]),(0,[z617,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z33,z4,z5,z8])],[(1,[z1,z2,z132,z4,z5,z8]),(0,[z1,z2,z3,z4,z618,z5,z8]),(1,[z1,z2,z3,z4,z5,z326]),(0,[z1,z606,z2,z3,z4,z5,z28])],[(0,[z1,z2,z3,z4,z73,z197,z8]),(0,[z1,z153,z2,z3,z4,z5,z449]),(0,[z17,z1,z2,z3,z33,z5,z8]),(0,[z1,z103,z3,z4,z72,z5,z8])],[(0,[z1,z2,z619,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z16,z5,z12]),(0,[z1,z2,z3,z4,z620,z5,z8])],[(0,[z1,z621,z2,z3,z4,z5,z8]),(0,[z1,z69,z3,z4,z5,z197,z8]),(0,[z34,z1,z2,z3,z4,z30,z5])],[(1,[z1,z2,z3,z4,z5,z202]),(0,[z1,z2,z3,z50,z4,z440,z5])],[(0,[z95,z1,z2,z3,z4,z5,z12]),(0,[z1,z622,z2,z3,z4,z5,z8]),(0,[z1,z114,z2,z3,z4,z5,z28]),(0,[z623,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z4,z30,z5,z236])],[(0,[z504,z1,z2,z3,z4,z5,z8]),(0,[z1,z69,z3,z4,z5,z8,z162]),(0,[z1,z2,z3,z4,z59,z197,z8]),(0,[z1,z2,z3,z4,z5,z8,z157])],[(0,[z1,z2,z624,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z264,z8]),(0,[z1,z2,z3,z368,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z579,z6]),(0,[z1,z46,z2,z3,z4,z30,z5])],[(0,[z76,z1,z2,z111,z3,z4,z5]),(0,[z1,z2,z43,z3,z4,z377,z8]),(0,[z1,z52,z2,z3,z4,z30,z5])],[(0,[z134,z1,z2,z3,z4,z5,z401]),(0,[z29,z1,z2,z3,z4,z5,z331])],[(0,[z1,z154,z2,z3,z4,z5,z6]),(0,[z625,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z263])],[(0,[z0,z1,z2,z3,z4,z30,z5]),(1,[z1,z2,z104,z4,z5,z8]),(0,[z1,z2,z3,z204,z4,z5,z6])]],
   [[(0,[z1,z2,z403,z3,z4,z5,z8]),(0,[z1,z2,z3,z626,z4,z5,z8]),(0,[z24,z1,z3,z4,z5,z197,z8]),(0,[z1,z2,z163,z50,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z12,z12])],[(0,[z1,z2,z3,z4,z5,z8,z627]),(0,[z1,z628,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z629,z8]),(0,[z76,z1,z2,z3,z4,z5,z224]),(0,[z1,z2,z3,z4,z630,z5,z8]),(0,[z1,z2,z3,z213,z4,z496,z5])],[(0,[z1,z631,z2,z3,z4,z5,z8]),(0,[z1,z2,z632,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z633])],[(0,[z134,z1,z2,z3,z4,z5,z6]),(0,[z1,z634,z2,z3,z4,z5,z8]),(0,[z1,z2,z184,z3,z4,z5,z8])],[(0,[z1,z2,z3,z33,z4,z5,z28]),(0,[z29,z1,z2,z3,z5,z8,z164]),(0,[z1,z66,z2,z3,z4,z30,z5])],[(0,[z1,z2,z3,z4,z596,z5,z8]),(1,[z1,z2,z3,z4,z5,z465])],[(0,[z1,z2,z3,z4,z5,z8,z635])],[(0,[z1,z2,z3,z15,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z636])],[(0,[z1,z637,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z87,z4,z30,z5])],[(0,[z638,z1,z2,z3,z4,z5,z8]),(0,[z1,z153,z2,z3,z4,z5,z142])],[(0,[z639,z1,z2,z3,z4,z5,z8]),(0,[z113,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z20,z3,z4,z5,z12]),(0,[z1,z2,z3,z108,z4,z5,z8]),(0,[z1,z2,z3,z640,z4,z5,z8]),(0,[z1,z2,z4,z25,z5,z71,z8])],[(0,[z1,z103,z3,z4,z16,z5,z8]),(0,[z1,z125,z3,z4,z5,z197,z8]),(0,[z504,z1,z2,z3,z4,z5,z28]),(0,[z1,z179,z2,z3,z4,z5,z12])],[(0,[z641,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z87,z4,z94,z5])],[(0,[z235,z1,z525,z3,z4,z5,z8]),(0,[z1,z642,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z643,z5,z8])],[(0,[z34,z1,z2,z3,z4,z210,z8]),(0,[z1,z2,z3,z4,z30,z425,z5])]],
   [[(0,[z1,z2,z43,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z644,z5,z8]),(0,[z1,z604,z2,z3,z4,z5,z6])],[(0,[z76,z2,z3,z4,z5,z8,z224])],[(0,[z1,z2,z3,z4,z645,z5,z8]),(0,[z1,z646,z2,z3,z4,z5,z8])],[(0,[z1,z647,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z32,z5,z8,z164]),(0,[z1,z2,z3,z4,z51,z30,z5])],[(0,[z1,z648,z2,z3,z4,z5,z8])],[],[(0,[z2,z3,z54,z4,z67,z5,z8]),(0,[z1,z2,z184,z3,z4,z5,z28])],[(0,[z1,z2,z3,z4,z5,z225,z8]),(0,[z649,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z71,z8])],[(1,[z1,z434,z2,z3,z4,z5]),(1,[z47,z2,z3,z4,z73,z8]),(0,[z1,z2,z3,z4,z650,z5,z8]),(0,[z1,z154,z43,z3,z4,z5,z8]),(0,[z24,z1,z154,z3,z4,z5,z8]),(0,[z651,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z608,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z377,z8]),(0,[z1,z114,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z115,z5,z8]),(0,[z652,z1,z2,z3,z4,z5,z8])],[(0,[z2,z20,z3,z54,z4,z5,z8]),(0,[z76,z1,z2,z3,z562,z5,z8]),(0,[z1,z2,z3,z15,z4,z5,z28]),(0,[z1,z2,z3,z4,z16,z30,z5]),(0,[z653,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z39])],[],[(0,[z1,z2,z452,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z86,z5,z8])],[(0,[z113,z1,z2,z3,z4,z5,z28]),(1,[z1,z2,z3,z4,z5,z389]),(0,[z1,z2,z15,z4,z5,z8,z28]),(0,[z1,z2,z654,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z655,z5,z8]),(0,[z134,z1,z2,z3,z4,z5,z100])],[(0,[z17,z1,z2,z379,z4,z5,z8]),(0,[z1,z2,z163,z3,z4,z5,z8]),(0,[z1,z656,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z184,z3,z4,z71,z8]),(0,[z1,z2,z3,z213,z4,z5,z301]),(0,[z1,z2,z146,z3,z4,z30,z5])],[(0,[z119,z1,z2,z3,z501,z5,z8]),(0,[z657,z1,z2,z3,z4,z5,z8]),(0,[z1,z154,z2,z3,z4,z5,z28])],[(0,[z34,z1,z2,z3,z67,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z658])],[(0,[z1,z2,z3,z4,z659,z5,z8]),(0,[z1,z660,z2,z3,z4,z5,z8])],[(0,[z1,z2,z20,z3,z4,z5,z160]),(1,[z1,z2,z269,z4,z5,z8]),(0,[z1,z2,z3,z50,z4,z30,z5]),(0,[z1,z66,z2,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z661,z5,z8])],[(0,[z1,z2,z3,z33,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z8,z662]),(1,[z1,z2,z3,z4,z5,z376])],[(0,[z34,z1,z2,z3,z32,z5,z8]),(0,[z1,z2,z3,z4,z5,z361,z28])],[(0,[z34,z1,z2,z70,z4,z5,z8]),(0,[z1,z2,z3,z663,z4,z5,z8]),(0,[z1,z2,z3,z664,z4,z5,z8]),(0,[z1,z2,z111,z3,z4,z5,z162]),(1,[z1,z2,z146,z4,z30,z5])],[(0,[z1,z2,z3,z665,z4,z5,z8]),(0,[z1,z2,z3,z666,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z71,z28]),(0,[z1,z2,z567,z3,z4,z5,z8])],[(0,[z1,z2,z105,z3,z4,z5,z502])],[(0,[z1,z2,z667,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z414,z8]),(0,[z1,z2,z3,z4,z668,z5,z8])],[(0,[z1,z2,z81,z54,z4,z5,z8]),(1,[z1,z283,z3,z4,z5,z8]),(0,[z504,z1,z2,z3,z4,z5,z6])],[(0,[z55,z1,z114,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z5,z193])],[(0,[z0,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z20,z4,z51,z5,z8]),(0,[z1,z669,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z86,z5,z28]),(0,[z1,z2,z3,z4,z5,z140,z8])],[(0,[z1,z670,z2,z3,z4,z5,z8]),(1,[z1,z2,z77,z4,z5,z8]),(0,[z235,z226,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z54,z15,z4,z5,z8]),(0,[z1,z2,z50,z4,z5,z8,z28]),(1,[z1,z2,z3,z4,z5,z429]),(0,[z1,z2,z671,z3,z4,z5,z8])],[(0,[z1,z2,z163,z3,z4,z5,z28])],[(0,[z55,z1,z2,z3,z4,z5,z14]),(0,[z1,z2,z3,z4,z5,z89,z8]),(0,[z1,z2,z3,z4,z51,z5,z12]),(0,[z1,z2,z3,z4,z672,z5,z8]),(0,[z1,z2,z3,z4,z5,z6,z164])],[(0,[z1,z2,z673,z3,z4,z5,z8])],[(0,[z1,z214,z3,z4,z5,z197,z8]),(0,[z1,z2,z3,z4,z5,z8,z674])],[(0,[z1,z66,z2,z3,z32,z5,z8]),(1,[z1,z2,z3,z4,z440,z5]),(0,[z1,z2,z3,z4,z124,z5,z12])],[(0,[z0,z1,z214,z3,z4,z5,z8]),(0,[z1,z675,z2,z3,z4,z5,z8]),(0,[z1,z2,z184,z3,z4,z5,z6]),(0,[z676,z1,z2,z3,z4,z5,z8])],[(0,[z1,z214,z3,z4,z5,z8,z162]),(0,[z34,z1,z270,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z677,z5,z8])],[(1,[z134,z2,z54,z4,z5,z8]),(0,[z1,z2,z3,z4,z51,z115,z5])],[(0,[z1,z2,z3,z4,z678,z5,z8]),(0,[z29,z1,z78,z3,z4,z5,z8])],[(0,[z2,z3,z4,z67,z5,z73,z8]),(0,[z679,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z15,z4,z5,z6]),(0,[z1,z125,z2,z3,z33,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z680]),(0,[z1,z2,z3,z4,z681,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z341]),(1,[z1,z2,z3,z4,z5,z331]),(0,[z1,z682,z2,z3,z4,z5,z8])],[(1,[z1,z2,z379,z4,z5,z8])],[(0,[z113,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z33,z4,z343,z5]),(0,[z1,z683,z2,z3,z4,z5,z8])],[(0,[z1,z103,z2,z3,z4,z72,z8]),(0,[z1,z2,z3,z684,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z373,z8])],[(0,[z134,z1,z2,z3,z4,z497,z8]),(0,[z1,z2,z54,z4,z5,z71,z8])]],
   [[(0,[z685,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z20,z81,z4,z5,z8]),(0,[z1,z103,z2,z3,z4,z197,z8]),(1,[z1,z2,z105,z4,z5,z28]),(0,[z1,z2,z3,z4,z496,z5,z8]),(0,[z57,z1,z2,z3,z4,z30,z5])],[(0,[z1,z434,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z686,z5,z8])],[(0,[z1,z2,z3,z4,z5,z12,z164]),(0,[z1,z2,z687,z3,z4,z5,z8])],[(0,[z559,z1,z2,z3,z4,z5,z8]),(0,[z1,z43,z3,z15,z4,z5,z8]),(0,[z1,z2,z3,z50,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z6,z8])],[(0,[z17,z1,z2,z3,z4,z30,z5]),(0,[z1,z2,z3,z325,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z601,z12]),(0,[z1,z2,z3,z4,z239,z5,z8])],[(1,[z1,z2,z3,z4,z5,z402])],[(0,[z1,z2,z3,z4,z5,z688,z8]),(0,[z1,z2,z3,z4,z5,z449,z8])],[(0,[z1,z2,z3,z4,z5,z689,z8]),(0,[z1,z2,z3,z4,z5,z8,z28]),(0,[z1,z2,z3,z690,z4,z5,z8])],[(0,[z691,z1,z2,z3,z4,z5,z8]),(0,[z1,z139,z2,z3,z4,z5,z162]),(0,[z692,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z693,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z71,z6])],[],[(1,[z1,z366,z3,z4,z5,z8]),(0,[z17,z1,z2,z3,z16,z5,z8]),(0,[z1,z2,z3,z4,z115,z5,z6])],[(0,[z95,z1,z2,z3,z4,z5,z8]),(0,[z1,z3,z15,z4,z72,z5,z8]),(0,[z694,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z558,z4,z5,z8])],[(0,[z1,z2,z3,z4,z72,z86,z8]),(0,[z1,z2,z184,z3,z4,z5,z341])],[(0,[z695,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z86,z5,z6])],[(0,[z134,z1,z2,z20,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z173])]],
   [[(0,[z1,z2,z3,z696,z4,z5,z8]),(0,[z76,z1,z366,z3,z4,z5,z8]),(1,[z1,z153,z15,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z197,z12])],[(0,[z1,z2,z3,z53,z4,z5,z8]),(0,[z1,z2,z163,z3,z4,z5,z6]),(0,[z29,z1,z2,z558,z4,z5,z8])],[(0,[z697,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z698,z5,z8]),(0,[z1,z2,z111,z3,z4,z59,z8]),(0,[z1,z2,z3,z4,z5,z699,z8])],[(0,[z119,z1,z2,z3,z4,z5,z256]),(0,[z700,z1,z2,z3,z4,z5,z8]),(0,[z701,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z381]),(0,[z1,z2,z3,z4,z5,z6,z28])],[],[(0,[z1,z2,z3,z501,z4,z5,z8])],[(0,[z1,z2,z3,z4,z702,z5,z8]),(0,[z1,z114,z2,z375,z4,z5,z8])],[(0,[z1,z2,z105,z54,z4,z5,z8]),(0,[z1,z2,z3,z690,z4,z5,z28])],[(0,[z34,z1,z2,z221,z4,z5,z8]),(0,[z1,z2,z3,z67,z5,z8,z12]),(0,[z703,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z43,z20,z4,z5,z8])],[(0,[z34,z169,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z330,z5]),(1,[z1,z2,z368,z4,z5,z8])],[(0,[z1,z2,z3,z4,z67,z5,z12]),(0,[z1,z2,z3,z4,z5,z8,z438]),(0,[z1,z2,z3,z4,z5,z13,z12]),(0,[z1,z2,z704,z3,z4,z5,z8])],[(0,[z1,z2,z20,z3,z4,z5,z8]),(0,[z95,z1,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z94,z30,z5])],[(0,[z705,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z706,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z28,z465])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z707,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z708]),(0,[z2,z3,z4,z5,z8,z709]),(1,[z243,z3,z16,z5,z8]),(0,[z1,z66,z2,z3,z5,z177]),(0,[z1,z2,z4,z30,z5,z140])],[(0,[z1,z2,z3,z4,z5,z710]),(0,[z1,z2,z711,z4,z30,z5]),(0,[z1,z2,z398,z4,z30,z5])],[(0,[z701,z1,z15,z4,z5,z8]),(0,[z1,z2,z712,z4,z5,z8]),(0,[z92,z1,z2,z51,z5,z8]),(0,[z1,z713,z2,z4,z5,z236])],[(0,[z1,z2,z714,z4,z5,z8]),(0,[z1,z2,z3,z715,z4,z5]),(0,[z638,z2,z3,z67,z5,z8])],[(0,[z1,z716,z3,z4,z5,z8]),(0,[z47,z2,z3,z4,z73,z202]),(0,[z1,z2,z4,z16,z5,z236]),(0,[z235,z1,z525,z4,z5,z28]),(0,[z1,z2,z50,z4,z5,z177]),(0,[z1,z2,z3,z4,z5,z717])],[(0,[z1,z2,z718,z4,z5,z8]),(0,[z1,z2,z4,z285,z5,z6])],[(0,[z691,z1,z2,z51,z5,z8]),(0,[z2,z54,z4,z5,z361,z28]),(0,[z1,z2,z719,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z720]),(0,[z1,z399,z3,z4,z5,z601])],[(0,[z1,z721,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z497,z8]),(0,[z1,z2,z3,z196,z5,z100]),(0,[z691,z2,z3,z67,z5,z8]),(0,[z1,z647,z15,z4,z5,z8]),(0,[z1,z154,z43,z4,z5,z8]),(0,[z1,z2,z350,z4,z5,z8]),(0,[z1,z2,z323,z4,z5,z28])],[(0,[z1,z403,z3,z4,z5,z8]),(0,[z1,z722,z2,z3,z4,z5]),(0,[z95,z2,z3,z4,z59,z8]),(0,[z1,z152,z3,z4,z5,z12]),(0,[z1,z2,z723,z4,z5,z8]),(0,[z1,z2,z111,z3,z4,z330]),(0,[z1,z2,z3,z4,z5,z724]),(0,[z1,z2,z3,z4,z5,z725]),(0,[z63,z2,z3,z4,z5,z96]),(0,[z1,z2,z30,z5,z236,z12]),(0,[z1,z2,z726,z4,z30,z5])],[(0,[z214,z3,z67,z16,z5,z8]),(0,[z1,z2,z3,z562,z5,z14]),(0,[z1,z727,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z728]),(0,[z1,z2,z729,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z730]),(0,[z1,z441,z3,z4,z5,z162]),(0,[z1,z2,z3,z4,z5,z731]),(0,[z1,z2,z732,z4,z5,z8])],[(0,[z1,z69,z3,z4,z5,z256]),(0,[z1,z733,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z734,z5]),(0,[z1,z2,z3,z4,z5,z735]),(0,[z1,z154,z382,z4,z5,z8]),(0,[z1,z432,z3,z4,z5,z263])],[(0,[z1,z2,z3,z501,z5,z8]),(0,[z1,z2,z242,z4,z5,z28]),(0,[z679,z1,z3,z4,z197,z8]),(0,[z1,z2,z736,z4,z5,z8]),(0,[z1,z2,z737,z4,z5,z8]),(0,[z226,z2,z3,z51,z5,z8]),(0,[z226,z2,z3,z4,z30,z5]),(0,[z1,z738,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z739,z5]),(0,[z1,z2,z514,z4,z5,z6]),(0,[z1,z2,z3,z4,z377,z28]),(0,[z1,z2,z3,z4,z5,z740]),(0,[z1,z2,z3,z4,z414,z8])],[(0,[z1,z2,z3,z4,z741,z8]),(0,[z1,z2,z3,z4,z159,z12]),(0,[z1,z3,z4,z72,z742,z8]),(0,[z1,z2,z3,z4,z743,z5]),(0,[z1,z2,z50,z4,z5,z236]),(0,[z1,z2,z163,z4,z5,z502])],[(0,[z1,z2,z53,z4,z120,z8]),(0,[z1,z546,z15,z4,z5,z8]),(0,[z1,z2,z4,z334,z5,z28]),(0,[z235,z1,z2,z4,z5,z166]),(0,[z1,z2,z81,z4,z5,z236]),(0,[z1,z2,z4,z30,z5,z744])]],
   [[(0,[z1,z2,z745,z3,z4,z5]),(0,[z1,z2,z269,z4,z5,z202]),(0,[z1,z2,z3,z4,z746,z8]),(0,[z226,z2,z4,z5,z8,z28])],[(0,[z119,z214,z3,z4,z5,z8]),(0,[z1,z2,z43,z4,z5,z465]),(0,[z1,z2,z359,z4,z5,z28]),(0,[z747,z2,z3,z4,z5,z8])],[(0,[z639,z2,z3,z67,z5,z8]),(0,[z1,z2,z3,z4,z5,z748]),(0,[z1,z2,z3,z4,z749,z5])],[(0,[z1,z2,z3,z4,z120,z65]),(0,[z1,z750,z3,z4,z5,z8]),(0,[z531,z1,z2,z3,z8,z164]),(0,[z1,z452,z3,z4,z5,z6]),(0,[z1,z2,z751,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z752]),(0,[z29,z1,z2,z3,z6,z164])],[(0,[z1,z2,z54,z4,z5,z128]),(0,[z1,z2,z3,z4,z5,z753]),(0,[z76,z2,z3,z4,z42,z224]),(0,[z24,z1,z3,z4,z197,z8]),(0,[z1,z2,z3,z4,z5,z754]),(0,[z1,z2,z344,z4,z5,z28]),(0,[z1,z2,z3,z539,z30,z5]),(0,[z29,z1,z273,z3,z8,z164])],[(0,[z1,z2,z3,z755,z4,z5]),(0,[z1,z78,z512,z4,z5,z8])],[(0,[z1,z756,z2,z3,z4,z5]),(0,[z24,z1,z3,z4,z276,z8]),(0,[z1,z125,z3,z33,z5,z12]),(0,[z1,z273,z3,z4,z5,z12]),(0,[z1,z757,z3,z4,z30,z5])],[(0,[z1,z178,z3,z4,z5,z12]),(0,[z1,z135,z3,z251,z5,z8]),(0,[z243,z2,z3,z4,z30,z5]),(0,[z235,z1,z2,z51,z5,z8])],[(0,[z1,z2,z132,z4,z5,z65]),(0,[z1,z2,z3,z4,z758,z5]),(0,[z759,z2,z3,z4,z5,z8]),(0,[z1,z2,z105,z4,z25,z12])],[(0,[z1,z2,z3,z4,z497,z28]),(0,[z1,z760,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z761]),(0,[z1,z154,z43,z4,z5,z28]),(0,[z243,z125,z3,z4,z5,z8]),(0,[z1,z2,z350,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z762]),(0,[z1,z2,z4,z5,z177,z236]),(0,[z1,z66,z2,z146,z30,z5]),(1,[z1,z2,z3,z4,z763])],[(1,[z1,z2,z764,z4,z5]),(0,[z1,z765,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z766,z5]),(0,[z95,z2,z3,z4,z59,z28]),(0,[z1,z403,z3,z4,z5,z28]),(0,[z1,z767,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z768]),(0,[z504,z1,z2,z4,z5,z236])],[(0,[z1,z2,z3,z4,z30,z161]),(1,[z1,z2,z4,z5,z769]),(0,[z770,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z384]),(0,[z226,z2,z163,z4,z5,z8]),(0,[z235,z1,z2,z4,z149,z28]),(0,[z1,z2,z3,z4,z771,z5]),(0,[z1,z2,z512,z4,z5,z772])],[(0,[z1,z2,z3,z4,z439,z5]),(0,[z433,z1,z3,z16,z5,z8]),(0,[z230,z2,z350,z4,z5,z8]),(0,[z1,z226,z2,z51,z5,z8]),(0,[z1,z2,z3,z4,z5,z11]),(0,[z1,z2,z773,z51,z5,z8]),(0,[z1,z2,z3,z8,z774,z164])],[(0,[z1,z2,z619,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z775]),(0,[z226,z2,z81,z4,z5,z8]),(0,[z185,z2,z3,z4,z5,z6])],[(0,[z1,z2,z53,z4,z5,z256]),(0,[z1,z2,z3,z501,z5,z28]),(0,[z243,z2,z3,z16,z5,z8]),(0,[z1,z2,z3,z4,z5,z776]),(0,[z1,z2,z4,z5,z309,z6]),(0,[z1,z2,z512,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z777])],[(0,[z1,z2,z3,z4,z5,z778]),(0,[z1,z2,z3,z4,z779,z8]),(1,[z2,z3,z780,z5,z8]),(0,[z1,z2,z781,z4,z5,z8]),(0,[z1,z15,z4,z686,z5,z8]),(0,[z1,z2,z3,z4,z414,z28]),(0,[z1,z155,z2,z4,z5,z782]),(0,[z1,z783,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z120,z12]),(1,[z2,z70,z67,z5,z8]),(0,[z1,z2,z3,z4,z784,z5]),(0,[z1,z2,z3,z785,z5,z8]),(0,[z1,z2,z15,z4,z5,z465]),(0,[z1,z2,z786,z4,z5,z8]),(0,[z1,z2,z104,z4,z5,z193]),(0,[z1,z2,z145,z4,z5,z740]),(0,[z92,z1,z2,z3,z8,z164]),(0,[z1,z787,z3,z4,z5,z8]),(0,[z1,z2,z398,z4,z5,z12])],[(0,[z1,z788,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z789]),(0,[z1,z2,z3,z4,z42,z8]),(0,[z790,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z251,z159,z8]),(0,[z1,z2,z4,z59,z71,z28]),(0,[z235,z1,z359,z4,z5,z28])],[(0,[z119,z214,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z449]),(0,[z1,z2,z3,z4,z5,z177]),(0,[z29,z1,z2,z3,z12,z164])],[(0,[z1,z152,z3,z215,z5,z8]),(0,[z1,z2,z3,z48,z5,z12]),(0,[z1,z2,z3,z4,z5,z791]),(0,[z1,z2,z792,z4,z5,z8]),(0,[z55,z2,z3,z4,z5,z550]),(0,[z1,z2,z3,z4,z5,z793]),(0,[z1,z2,z367,z4,z5,z28]),(0,[z1,z2,z4,z5,z662,z28]),(0,[z1,z283,z184,z4,z5,z8])],[(0,[z409,z1,z3,z16,z5,z8]),(0,[z1,z2,z3,z4,z5,z794]),(0,[z1,z2,z3,z4,z5,z216]),(0,[z795,z2,z3,z4,z5,z8]),(0,[z1,z2,z4,z5,z236,z164])],[(0,[z1,z2,z796,z4,z5,z8]),(0,[z151,z214,z3,z4,z5,z8]),(0,[z1,z2,z54,z4,z5,z166]),(0,[z1,z2,z3,z4,z5,z797]),(0,[z24,z1,z3,z4,z197,z28]),(0,[z1,z2,z3,z4,z5,z96]),(0,[z1,z2,z3,z204,z5,z12]),(0,[z1,z798,z3,z4,z5,z12])],[(0,[z2,z3,z70,z67,z5,z8]),(0,[z34,z1,z2,z4,z5,z236]),(0,[z308,z2,z3,z67,z5,z8]),(0,[z1,z2,z3,z562,z30,z5]),(0,[z1,z2,z4,z5,z680,z28]),(0,[z1,z2,z3,z799,z5,z8]),(0,[z1,z2,z800,z4,z5,z8]),(0,[z1,z2,z801,z4,z30,z5])],[(0,[z1,z2,z3,z4,z802,z8]),(0,[z1,z2,z3,z4,z5,z803]),(0,[z1,z2,z3,z300,z5,z12]),(0,[z1,z2,z3,z4,z5,z804]),(0,[z1,z2,z105,z4,z5,z465])],[(0,[z1,z2,z20,z4,z5,z28]),(0,[z95,z1,z2,z4,z5,z236]),(0,[z1,z2,z3,z4,z5,z805]),(0,[z235,z1,z2,z51,z5,z28])],[(0,[z1,z2,z3,z4,z5,z806]),(0,[z1,z139,z3,z4,z5,z601]),(0,[z1,z2,z3,z4,z5,z807]),(0,[z1,z179,z2,z4,z5,z465]),(0,[z1,z2,z3,z4,z763,z39])],[(0,[z1,z178,z3,z251,z5,z8]),(0,[z1,z808,z2,z3,z4,z5]),(0,[z1,z366,z77,z4,z5,z8]),(0,[z1,z2,z3,z562,z94,z5]),(0,[z226,z2,z3,z4,z5,z12]),(0,[z1,z359,z3,z4,z5,z11]),(0,[z1,z2,z3,z4,z5,z809]),(0,[z1,z2,z4,z5,z236,z71])],[(0,[z1,z152,z3,z4,z30,z5]),(0,[z1,z2,z242,z4,z5,z6]),(0,[z1,z2,z3,z4,z264,z12]),(0,[z1,z2,z3,z4,z5,z810]),(0,[z1,z3,z4,z5,z811,z162]),(0,[z1,z2,z3,z4,z5,z812]),(0,[z1,z813,z3,z4,z5,z8]),(0,[z1,z2,z4,z5,z173,z28])],[(0,[z1,z2,z814,z4,z5,z8]),(0,[z76,z2,z3,z4,z239,z5]),(0,[z1,z145,z15,z4,z5,z8]),(0,[z1,z2,z3,z4,z377,z6]),(0,[z1,z2,z3,z4,z5,z236])],[(0,[z1,z2,z815,z4,z5,z8]),(0,[z243,z2,z3,z4,z5,z170]),(0,[z1,z816,z2,z3,z4,z5]),(0,[z1,z2,z817,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z811]),(0,[z1,z2,z3,z4,z5,z502])],[(0,[z1,z2,z818,z4,z5,z8]),(0,[z1,z2,z3,z501,z293,z8]),(0,[z1,z2,z3,z4,z5,z819]),(1,[z270,z3,z67,z5,z8]),(0,[z415,z2,z3,z4,z5,z224]),(0,[z1,z2,z3,z4,z30,z264]),(0,[z1,z2,z4,z5,z71,z465]),(0,[z1,z2,z3,z4,z94,z228])]],
   [[(0,[z1,z2,z111,z3,z4,z117]),(0,[z1,z2,z3,z4,z5,z820]),(0,[z230,z2,z3,z4,z5,z384]),(0,[z1,z2,z3,z4,z5,z821]),(0,[z1,z2,z3,z90,z30,z5])],[(0,[z1,z2,z3,z4,z822,z5]),(0,[z1,z2,z3,z4,z5,z823]),(0,[z1,z2,z3,z4,z824,z5]),(0,[z1,z2,z4,z386,z5,z28]),(0,[z1,z2,z825,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z826])],[(0,[z1,z2,z3,z4,z497,z401]),(0,[z1,z2,z827,z4,z5,z8]),(0,[z1,z2,z3,z4,z828,z5]),(0,[z1,z99,z2,z3,z8,z164])],[(0,[z308,z214,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z829]),(0,[z1,z2,z3,z4,z42,z28]),(0,[z1,z2,z200,z4,z5,z28]),(0,[z1,z2,z3,z830,z4,z5])],[(0,[z1,z135,z3,z196,z5,z8]),(0,[z1,z2,z831,z4,z439,z5]),(0,[z1,z336,z15,z4,z5,z8]),(0,[z1,z2,z105,z4,z25,z263])],[(0,[z1,z2,z3,z4,z5,z832]),(0,[z1,z2,z3,z4,z117,z224]),(0,[z1,z2,z3,z833,z5,z8]),(0,[z24,z1,z2,z4,z71,z28]),(0,[z1,z359,z3,z4,z5,z96]),(0,[z1,z2,z4,z834,z71,z8])],[(0,[z1,z835,z2,z4,z5,z8]),(0,[z1,z2,z3,z4,z30,z210]),(0,[z1,z2,z3,z4,z5,z836]),(0,[z1,z2,z3,z837,z4,z5]),(0,[z838,z2,z3,z4,z5,z8]),(0,[z1,z2,z397,z4,z5,z28]),(0,[z1,z604,z2,z4,z5,z28])],[(0,[z99,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z839,z5]),(0,[z1,z105,z283,z4,z25,z8])],[(0,[z1,z2,z351,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z142]),(0,[z1,z2,z3,z4,z840,z8]),(0,[z243,z2,z3,z4,z23,z8]),(0,[z1,z2,z145,z4,z5,z216]),(0,[z1,z2,z558,z4,z5,z331])],[(0,[z1,z2,z3,z4,z497,z6]),(0,[z1,z154,z43,z4,z5,z6]),(0,[z1,z2,z350,z4,z5,z6]),(0,[z29,z1,z2,z512,z8,z164]),(0,[z1,z2,z841,z4,z5,z8]),(0,[z1,z842,z3,z4,z30,z5])],[(0,[z1,z69,z3,z4,z5,z193]),(0,[z95,z2,z3,z4,z59,z6]),(0,[z1,z403,z3,z4,z5,z6]),(0,[z1,z2,z843,z4,z5,z8]),(0,[z1,z125,z3,z33,z30,z5]),(0,[z1,z2,z3,z844,z5,z8]),(0,[z1,z2,z3,z4,z5,z249]),(0,[z1,z2,z397,z4,z5,z140])],[(0,[z1,z178,z3,z4,z30,z5])],[(0,[z1,z2,z3,z4,z5,z845]),(0,[z235,z1,z2,z773,z5,z8]),(0,[z846,z2,z3,z4,z5,z8]),(0,[z1,z2,z847,z4,z30,z5])],[(0,[z1,z2,z3,z4,z5,z848]),(0,[z1,z2,z849,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z850]),(0,[z1,z851,z3,z4,z5,z8])],[(0,[z1,z2,z3,z501,z5,z6]),(0,[z1,z852,z3,z4,z5,z8]),(0,[z1,z2,z4,z5,z307,z28]),(0,[z1,z2,z3,z4,z5,z853]),(0,[z1,z2,z3,z4,z854,z5]),(0,[z1,z370,z2,z4,z5,z236])],[(0,[z1,z2,z3,z196,z159,z8]),(0,[z47,z2,z253,z3,z4,z73]),(0,[z1,z2,z3,z4,z5,z855]),(0,[z1,z3,z4,z515,z197,z8]),(0,[z63,z525,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z414,z6]),(0,[z1,z2,z856,z4,z5,z8]),(0,[z1,z2,z111,z3,z4,z124])]],
   [[(0,[z95,z2,z3,z4,z615,z8]),(0,[z1,z154,z3,z4,z147,z8]),(0,[z17,z1,z3,z16,z264,z8]),(0,[z1,z2,z4,z496,z5,z857])],[(0,[z374,z1,z2,z3,z8,z164]),(0,[z1,z2,z350,z4,z5,z858]),(0,[z1,z2,z3,z4,z5,z859]),(0,[z1,z125,z3,z860,z5,z8]),(0,[z1,z2,z3,z4,z5,z861])],[(0,[z1,z2,z3,z862,z5,z8]),(0,[z1,z2,z3,z215,z59,z8]),(0,[z1,z432,z3,z4,z5,z8]),(0,[z581,z1,z3,z4,z197,z8]),(0,[z1,z283,z4,z5,z8,z28]),(0,[z1,z2,z512,z4,z30,z5])],[(0,[z1,z2,z132,z4,z5,z863]),(0,[z119,z214,z3,z4,z5,z6]),(0,[z1,z2,z3,z864,z5,z8]),(0,[z1,z2,z333,z3,z87,z4]),(0,[z1,z2,z3,z4,z5,z865]),(0,[z1,z866,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z867,z5]),(0,[z1,z2,z3,z4,z5,z868]),(0,[z1,z2,z3,z618,z5,z12]),(0,[z1,z2,z3,z4,z5,z869]),(0,[z1,z2,z511,z4,z71,z8]),(0,[z1,z2,z3,z4,z870,z8]),(1,[z1,z2,z3,z871,z5])],[(0,[z1,z872,z2,z3,z4,z5]),(0,[z1,z2,z32,z50,z5,z28]),(0,[z1,z2,z350,z4,z5,z384]),(0,[z1,z2,z873,z4,z5,z8]),(0,[z1,z2,z104,z4,z5,z874]),(0,[z1,z757,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z763,z8])],[(0,[z2,z3,z32,z67,z5,z12]),(0,[z1,z2,z3,z562,z5,z12]),(0,[z480,z2,z3,z4,z5,z224]),(0,[z24,z1,z3,z4,z197,z6]),(0,[z1,z2,z3,z4,z496,z5])],[(0,[z1,z214,z3,z4,z5,z256]),(0,[z1,z2,z3,z4,z5,z875]),(0,[z1,z2,z4,z5,z430,z28]),(0,[z29,z1,z2,z3,z8,z774]),(0,[z1,z2,z3,z876,z5,z8])],[(0,[z1,z178,z3,z196,z5,z8]),(0,[z1,z2,z3,z4,z5,z877]),(0,[z1,z2,z3,z48,z30,z5]),(0,[z1,z2,z3,z4,z330,z39]),(0,[z1,z2,z878,z4,z5,z8]),(0,[z1,z2,z3,z50,z5,z177]),(0,[z1,z2,z3,z4,z8,z774]),(0,[z1,z2,z879,z4,z5,z12]),(0,[z1,z2,z4,z94,z5,z236])],[(0,[z1,z2,z132,z4,z30,z5]),(0,[z1,z2,z3,z4,z5,z880]),(0,[z47,z2,z3,z4,z73,z12]),(0,[z76,z2,z3,z562,z5,z224]),(0,[z235,z1,z2,z51,z5,z6]),(0,[z99,z2,z3,z4,z5,z28])],[(1,[z214,z3,z247,z5,z8]),(0,[z1,z2,z3,z4,z881,z8]),(1,[z2,z3,z67,z210,z8]),(0,[z1,z2,z3,z4,z209,z39]),(0,[z1,z2,z4,z5,z228,z236])],[(0,[z1,z2,z3,z4,z5,z882]),(0,[z1,z883,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z884]),(0,[z1,z2,z4,z309,z8,z164])],[(0,[z1,z2,z3,z48,z5,z885]),(0,[z1,z2,z3,z4,z886,z5]),(0,[z1,z2,z887,z4,z5,z8]),(0,[z1,z103,z3,z4,z72,z144])],[(0,[z1,z2,z3,z4,z5,z888]),(0,[z1,z2,z3,z562,z117,z8]),(0,[z1,z2,z3,z4,z30,z42]),(0,[z1,z2,z4,z5,z889,z8])],[(0,[z1,z890,z3,z4,z5,z8]),(0,[z1,z2,z375,z4,z5,z8]),(0,[z226,z2,z4,z51,z5,z8]),(0,[z1,z2,z4,z442,z5,z28])],[(0,[z1,z69,z104,z4,z5,z8]),(0,[z1,z2,z891,z3,z4,z5]),(0,[z1,z2,z104,z4,z5,z892])]],
   [[(0,[z1,z2,z3,z247,z120,z8]),(0,[z2,z3,z4,z67,z210,z8]),(0,[z1,z2,z3,z4,z893,z8]),(0,[z1,z2,z4,z86,z309,z8]),(0,[z1,z2,z3,z4,z5,z894])],[(0,[z1,z69,z2,z4,z5,z236]),(0,[z1,z2,z3,z4,z5,z895])],[(0,[z1,z2,z3,z630,z5,z12]),(0,[z1,z2,z445,z4,z5,z28]),(0,[z1,z125,z3,z4,z264,z8]),(0,[z1,z2,z3,z4,z896,z5]),(0,[z1,z2,z3,z4,z94,z598]),(0,[z99,z2,z3,z4,z86,z8]),(0,[z1,z2,z3,z30,z5,z168]),(0,[z1,z2,z111,z3,z87,z4])],[(0,[z138,z2,z20,z4,z5,z8]),(0,[z1,z2,z3,z4,z42,z6]),(0,[z1,z2,z3,z4,z897,z8]),(0,[z1,z2,z3,z4,z898,z8]),(0,[z24,z1,z3,z4,z30,z197]),(0,[z1,z2,z899,z4,z5,z8]),(0,[z1,z2,z195,z4,z5,z376]),(0,[z1,z2,z900,z4,z5,z8]),(0,[z1,z2,z4,z94,z140,z39])],[(0,[z0,z2,z3,z67,z5,z12]),(0,[z1,z2,z901,z4,z5,z8]),(0,[z1,z2,z104,z4,z30,z5]),(0,[z1,z432,z3,z4,z5,z28])],[(0,[z1,z2,z3,z4,z902,z5]),(0,[z1,z2,z269,z4,z5,z12]),(1,[z2,z3,z4,z903,z8]),(0,[z24,z1,z104,z4,z5,z8])],[(0,[z1,z135,z3,z4,z5,z8]),(0,[z1,z2,z3,z501,z5,z904]),(0,[z1,z2,z3,z596,z5,z12]),(0,[z29,z1,z2,z3,z30,z164])],[(0,[z2,z3,z32,z780,z5,z8]),(0,[z24,z1,z2,z4,z5,z236])],[(0,[z1,z3,z860,z16,z5,z8]),(0,[z1,z2,z382,z4,z25,z8])],[(0,[z1,z2,z32,z4,z5,z803]),(0,[z1,z2,z3,z418,z5,z12]),(0,[z1,z2,z4,z5,z236,z13])],[(0,[z1,z2,z245,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z905]),(0,[z1,z2,z3,z4,z906,z8]),(0,[z1,z2,z4,z25,z834,z8])],[(0,[z1,z152,z3,z4,z5,z8]),(0,[z1,z2,z3,z196,z5,z907]),(0,[z1,z2,z460,z4,z5,z28]),(0,[z1,z153,z825,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z908]),(0,[z1,z2,z3,z115,z5,z429]),(0,[z1,z2,z462,z4,z5,z28]),(0,[z1,z2,z356,z4,z5,z28]),(0,[z1,z436,z3,z4,z5,z38])],[(0,[z1,z2,z262,z4,z5,z130]),(0,[z1,z2,z3,z215,z5,z130]),(0,[z1,z2,z3,z4,z5,z909]),(0,[z1,z525,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z910]),(0,[z1,z283,z3,z4,z5,z12])],[(0,[z1,z2,z3,z4,z911,z5]),(0,[z1,z2,z4,z5,z197,z236]),(0,[z1,z103,z145,z4,z72,z8]),(0,[z1,z2,z3,z912,z5,z8]),(0,[z1,z432,z3,z4,z71,z8]),(0,[z1,z2,z4,z5,z236,z39])],[(0,[z1,z2,z3,z247,z5,z256]),(0,[z1,z2,z281,z4,z25,z8]),(0,[z1,z2,z3,z4,z5,z913]),(0,[z1,z114,z3,z4,z5,z173]),(0,[z1,z359,z3,z4,z414,z8])]],
   [[(0,[z1,z914,z3,z4,z5,z8]),(0,[z1,z2,z3,z67,z5,z301]),(0,[z1,z2,z4,z73,z71,z28]),(0,[z1,z2,z77,z4,z5,z12]),(0,[z1,z2,z375,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z915]),(0,[z99,z2,z3,z4,z8,z164])],[(0,[z1,z2,z3,z4,z159,z8]),(0,[z1,z2,z3,z4,z916,z8])],[(0,[z1,z2,z3,z4,z293,z256]),(0,[z1,z181,z3,z33,z5,z8]),(0,[z1,z2,z3,z4,z5,z917]),(0,[z1,z669,z3,z4,z5,z162])],[(0,[z1,z2,z3,z4,z918,z8]),(0,[z1,z2,z20,z4,z5,z100]),(0,[z1,z2,z77,z108,z5,z8]),(0,[z122,z1,z2,z4,z5,z28]),(0,[z1,z2,z4,z459,z71,z8]),(0,[z1,z2,z3,z4,z919,z5]),(0,[z1,z78,z3,z4,z5,z331])],[(0,[z1,z2,z920,z4,z5,z8]),(1,[z1,z2,z4,z834,z8]),(0,[z1,z2,z3,z4,z5,z301])],[(0,[z248,z214,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z921]),(0,[z1,z2,z3,z32,z5,z301]),(0,[z1,z15,z4,z72,z5,z28]),(0,[z1,z139,z3,z4,z5,z13])],[(0,[z1,z2,z3,z922,z5,z8]),(0,[z1,z2,z3,z4,z923,z8]),(0,[z1,z189,z3,z4,z5,z13]),(0,[z1,z2,z3,z924,z5,z8])],[(0,[z1,z152,z262,z4,z5,z8]),(0,[z55,z2,z583,z3,z4,z5]),(0,[z1,z2,z3,z4,z264,z170])],[(0,[z1,z2,z132,z4,z5,z12]),(0,[z1,z2,z925,z4,z5,z8]),(0,[z1,z135,z3,z4,z5,z28]),(0,[z2,z3,z4,z780,z5,z8]),(0,[z1,z403,z242,z4,z5,z8]),(0,[z1,z2,z111,z3,z4,z329]),(0,[z1,z154,z43,z4,z377,z8]),(0,[z1,z2,z3,z204,z871,z5]),(0,[z1,z2,z3,z4,z261,z271])],[(0,[z1,z2,z371,z4,z5,z28]),(0,[z1,z2,z3,z4,z926,z8]),(0,[z134,z2,z54,z4,z5,z12]),(0,[z1,z2,z54,z4,z5,z263]),(0,[z1,z2,z3,z4,z161,z389]),(0,[z1,z2,z253,z3,z4,z5]),(0,[z19,z2,z3,z4,z5,z14]),(0,[z1,z273,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z927]),(0,[z1,z103,z3,z325,z4,z72]),(0,[z1,z2,z368,z4,z5,z286]),(0,[z99,z2,z3,z4,z5,z6])],[(0,[z1,z178,z3,z4,z5,z8]),(0,[z1,z2,z20,z4,z5,z928]),(0,[z1,z491,z3,z4,z5,z162])],[(0,[z1,z2,z4,z67,z5,z236]),(1,[z1,z359,z4,z5,z28]),(0,[z1,z2,z105,z4,z25,z8]),(0,[z1,z2,z847,z4,z5,z8])],[(0,[z1,z2,z3,z929,z5,z8]),(0,[z930,z2,z3,z4,z5,z8])],[(0,[z34,z2,z3,z67,z5,z389]),(0,[z1,z152,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z931])],[(0,[z169,z2,z3,z300,z5,z8]),(0,[z1,z15,z4,z141,z5,z8]),(0,[z1,z2,z3,z860,z5,z8]),(0,[z1,z103,z2,z4,z71,z28]),(0,[z1,z2,z368,z4,z30,z5]),(0,[z1,z46,z3,z4,z5,z13]),(0,[z1,z2,z4,z110,z5,z236])],[(0,[z1,z2,z3,z4,z932,z8]),(0,[z1,z525,z3,z4,z5,z28]),(0,[z1,z2,z4,z4,z5,z236])]],
   [[(0,[z1,z2,z15,z4,z5,z160]),(0,[z480,z2,z3,z4,z73,z8]),(0,[z1,z2,z3,z4,z933,z8]),(0,[z1,z2,z3,z4,z5,z934]),(0,[z1,z2,z935,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z936]),(0,[z1,z125,z3,z33,z5,z157]),(0,[z1,z103,z4,z72,z309,z8]),(0,[z1,z2,z512,z4,z5,z8])],[(0,[z1,z2,z937,z4,z5,z8]),(0,[z1,z938,z3,z4,z5,z8]),(0,[z1,z2,z3,z87,z4,z763])],[(0,[z1,z2,z3,z4,z120,z8]),(0,[z1,z2,z3,z4,z159,z28]),(0,[z2,z3,z4,z59,z903,z8]),(0,[z1,z2,z15,z4,z5,z166]),(0,[z1,z2,z3,z4,z939,z8]),(0,[z1,z2,z711,z4,z5,z8]),(0,[z1,z2,z104,z4,z5,z12]),(0,[z1,z2,z398,z4,z5,z8])],[(0,[z1,z2,z3,z940,z5,z8]),(0,[z1,z2,z3,z4,z5,z941]),(0,[z1,z2,z3,z215,z73,z8]),(0,[z1,z942,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z943,z5]),(0,[z1,z432,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z782,z28]),(0,[z1,z78,z558,z4,z5,z8]),(0,[z1,z2,z944,z4,z5,z8])],[(0,[z1,z2,z945,z4,z5,z8]),(0,[z1,z946,z2,z3,z4,z5]),(0,[z24,z1,z3,z4,z307,z8]),(0,[z1,z2,z3,z4,z5,z947]),(0,[z1,z2,z325,z4,z5,z309]),(0,[z1,z2,z4,z459,z71,z28])],[(0,[z1,z2,z3,z4,z948,z5]),(0,[z1,z2,z3,z871,z5,z12])],[(0,[z1,z2,z949,z4,z5,z8]),(0,[z1,z2,z950,z4,z5,z8]),(0,[z1,z2,z3,z48,z5,z8]),(0,[z1,z2,z951,z4,z5,z8]),(0,[z651,z2,z3,z4,z59,z8]),(0,[z952,z2,z3,z4,z5,z8]),(0,[z1,z2,z953,z4,z5,z8]),(0,[z1,z2,z954,z4,z5,z8]),(0,[z1,z2,z3,z5,z177,z465]),(0,[z1,z2,z3,z4,z5,z955])],[(0,[z1,z2,z3,z4,z5,z956]),(0,[z1,z2,z20,z4,z377,z8]),(0,[z1,z2,z105,z4,z5,z160]),(0,[z1,z2,z3,z4,z957,z5]),(0,[z1,z2,z3,z924,z5,z28]),(0,[z1,z2,z3,z4,z923,z28])],[(0,[z1,z2,z3,z4,z5,z958]),(0,[z1,z2,z3,z32,z5,z326]),(0,[z1,z2,z269,z4,z30,z5]),(0,[z1,z2,z4,z5,z236,z8]),(0,[z156,z2,z3,z4,z5,z373]),(0,[z1,z2,z959,z4,z5,z8]),(0,[z57,z1,z2,z4,z5,z236])],[(0,[z1,z2,z726,z4,z5,z8]),(0,[z1,z2,z3,z960,z5,z8])],[(0,[z1,z2,z3,z961,z4,z5]),(0,[z1,z2,z616,z4,z71,z8]),(0,[z1,z2,z3,z4,z5,z962]),(0,[z1,z2,z105,z4,z5,z166]),(0,[z1,z273,z3,z4,z5,z28])],[(0,[z1,z178,z3,z4,z5,z28]),(0,[z1,z366,z3,z4,z5,z12]),(0,[z1,z15,z4,z16,z5,z28]),(0,[z1,z2,z3,z4,z5,z963]),(0,[z1,z2,z3,z640,z30,z5]),(0,[z1,z2,z4,z5,z376,z28])],[(0,[z1,z2,z3,z4,z5,z907]),(0,[z599,z1,z2,z4,z5,z28]),(0,[z1,z964,z3,z4,z5,z8]),(0,[z1,z153,z2,z4,z377,z8]),(0,[z1,z43,z825,z4,z5,z8]),(0,[z1,z2,z105,z4,z25,z28]),(0,[z1,z2,z3,z4,z965,z5]),(0,[z1,z2,z4,z30,z5,z236])],[(0,[z1,z2,z54,z196,z5,z8]),(0,[z226,z2,z3,z4,z5,z8]),(0,[z1,z966,z2,z3,z4,z5])],[(0,[z1,z670,z2,z4,z5,z28]),(0,[z1,z366,z3,z108,z5,z8]),(0,[z1,z2,z3,z4,z60,z39]),(0,[z1,z2,z4,z5,z6,z417]),(0,[z1,z2,z3,z4,z264,z8]),(0,[z1,z2,z456,z4,z5,z28]),(0,[z1,z2,z4,z5,z502,z28])]],
   [[(0,[z1,z675,z2,z4,z5,z28]),(0,[z1,z2,z3,z967,z5,z8]),(0,[z1,z2,z375,z4,z5,z6]),(0,[z1,z283,z4,z51,z5,z8]),(0,[z1,z2,z3,z4,z5,z968])],[(0,[z1,z2,z3,z969,z5,z8]),(0,[z1,z135,z3,z4,z5,z401]),(0,[z113,z2,z970,z4,z5,z8]),(0,[z1,z2,z242,z4,z42,z8]),(0,[z1,z153,z15,z4,z5,z12]),(0,[z17,z1,z379,z16,z5,z8]),(0,[z1,z2,z3,z4,z5,z971]),(0,[z1,z283,z3,z4,z30,z5])],[(0,[z1,z2,z3,z4,z5,z256]),(0,[z1,z2,z3,z4,z5,z972]),(0,[z1,z2,z4,z5,z71,z166])],[(0,[z119,z214,z3,z501,z5,z8]),(0,[z1,z2,z4,z5,z973,z8]),(0,[z1,z2,z262,z48,z5,z8]),(0,[z1,z2,z3,z974,z5,z8]),(0,[z1,z2,z975,z3,z4,z5]),(0,[z1,z366,z3,z4,z117,z8])],[(0,[z1,z2,z4,z5,z73,z236]),(0,[z1,z2,z77,z4,z30,z5]),(0,[z1,z2,z104,z4,z5,z144]),(0,[z1,z2,z3,z4,z976,z5]),(0,[z1,z938,z3,z4,z5,z28]),(0,[z29,z99,z2,z3,z8,z164])],[(0,[z1,z2,z3,z4,z120,z28]),(0,[z1,z2,z3,z977,z5,z8]),(1,[z1,z2,z773,z5,z8]),(0,[z1,z2,z3,z51,z5,z429]),(0,[z1,z606,z3,z4,z5,z507]),(0,[z1,z2,z398,z4,z5,z28])],[(0,[z1,z2,z978,z4,z5,z8]),(0,[z92,z1,z2,z4,z5,z28])],[(0,[z1,z2,z3,z4,z5,z979]),(0,[z1,z2,z221,z4,z5,z980]),(0,[z1,z2,z4,z59,z5,z236]),(0,[z1,z2,z3,z4,z981,z5]),(0,[z1,z2,z3,z4,z5,z982]),(0,[z1,z2,z3,z4,z5,z983]),(0,[z1,z2,z105,z4,z834,z8]),(0,[z1,z2,z3,z291,z5,z12]),(0,[z1,z66,z2,z4,z5,z236])],[(0,[z1,z69,z15,z4,z5,z28]),(0,[z1,z135,z3,z4,z5,z6]),(0,[z1,z2,z70,z4,z5,z402]),(0,[z1,z2,z984,z3,z4,z5]),(0,[z1,z985,z3,z4,z5,z8]),(0,[z1,z2,z3,z215,z5,z202]),(0,[z1,z2,z3,z4,z986,z5]),(1,[z1,z3,z4,z5,z811])],[(0,[z243,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z987,z8]),(0,[z270,z3,z4,z67,z5,z8]),(0,[z1,z2,z3,z48,z5,z28]),(0,[z1,z2,z3,z4,z5,z988])],[(0,[z691,z1,z2,z4,z5,z28]),(0,[z1,z2,z3,z4,z210,z389]),(0,[z1,z103,z324,z4,z72,z8]),(0,[z1,z2,z3,z681,z5,z12]),(0,[z235,z1,z2,z51,z414,z8]),(0,[z1,z2,z3,z4,z989,z5]),(0,[z1,z2,z163,z4,z5,z376])],[(0,[z1,z2,z3,z4,z5,z990]),(0,[z1,z2,z3,z32,z5,z465]),(0,[z47,z1,z2,z4,z5,z236]),(0,[z1,z2,z4,z5,z236,z28]),(0,[z185,z2,z3,z4,z5,z249])],[(0,[z1,z2,z991,z4,z5,z8]),(0,[z1,z2,z3,z4,z159,z401]),(0,[z1,z2,z111,z3,z4,z659]),(0,[z1,z2,z81,z4,z5,z376]),(0,[z1,z2,z512,z4,z86,z8])],[(0,[z992,z1,z2,z3,z4,z8]),(0,[z134,z2,z54,z4,z30,z5]),(0,[z169,z1,z2,z4,z5,z236]),(0,[z1,z152,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z993]),(0,[z1,z2,z3,z4,z994,z8]),(0,[z1,z2,z4,z5,z794,z8]),(0,[z1,z2,z368,z4,z5,z12]),(0,[z226,z359,z3,z4,z5,z8]),(0,[z1,z995,z3,z4,z5,z8]),(0,[z1,z2,z996,z3,z4,z30])],[(0,[z1,z2,z3,z4,z30,z293]),(0,[z1,z2,z3,z4,z5,z997]),(0,[z24,z1,z15,z4,z5,z28]),(0,[z1,z103,z3,z4,z72,z8]),(0,[z1,z3,z4,z5,z8,z811]),(0,[z1,z2,z3,z4,z998,z12])],[(0,[z1,z2,z232,z4,z5,z28]),(0,[z1,z403,z3,z4,z42,z8]),(0,[z1,z525,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z414,z11])]],
   [[(0,[z1,z2,z3,z4,z5,z999]),(0,[z1,z2,z3,z4,z1000,z8]),(0,[z1,z2,z111,z242,z4,z5]),(0,[z1,z2,z3,z4,z1001,z8]),(0,[z1002,z2,z3,z4,z5,z8]),(0,[z226,z2,z3,z4,z5,z28]),(0,[z1,z2,z4,z440,z5,z28]),(0,[z1,z283,z163,z4,z5,z8]),(0,[z1,z2,z437,z4,z5,z6])],[(0,[z1,z2,z3,z4,z161,z402]),(0,[z1,z2,z379,z4,z30,z5]),(0,[z1,z2,z3,z4,z264,z28]),(0,[z1,z2,z3,z4,z5,z1003]),(0,[z1,z2,z1004,z4,z5,z8]),(0,[z235,z1,z2,z4,z5,z1005]),(0,[z62,z2,z3,z4,z5,z171])],[(0,[z1,z1006,z3,z4,z5,z8]),(0,[z1,z114,z403,z3,z4,z5]),(0,[z1,z2,z532,z4,z5,z28]),(0,[z1,z2,z1007,z4,z5,z8]),(0,[z1,z283,z81,z4,z5,z8]),(0,[z415,z2,z3,z4,z5,z390])],[(0,[z1,z2,z3,z500,z5,z12]),(0,[z1,z2,z3,z4,z159,z6]),(0,[z1,z2,z221,z4,z5,z1008]),(0,[z1,z1009,z3,z4,z5,z8]),(0,[z1,z154,z145,z4,z5,z8]),(0,[z1,z1010,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z1011,z8]),(0,[z1,z1012,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z130]),(0,[z1,z2,z3,z4,z5,z1013]),(0,[z230,z2,z3,z4,z264,z8]),(0,[z1,z2,z3,z239,z5,z12]),(0,[z1,z2,z3,z4,z94,z39])],[(0,[z1,z178,z3,z4,z5,z401]),(0,[z34,z2,z3,z67,z5,z402]),(0,[z560,z1,z2,z51,z5,z8]),(0,[z1,z2,z3,z4,z330,z117]),(0,[z1,z66,z2,z30,z5,z236])],[(0,[z1,z121,z2,z764,z4,z5]),(0,[z1,z2,z3,z4,z497,z100]),(0,[z1,z2,z3,z4,z5,z1014]),(0,[z1,z2,z3,z4,z5,z980]),(0,[z1,z1015,z3,z4,z5,z8]),(0,[z1,z2,z1016,z4,z5,z8]),(0,[z1,z114,z3,z4,z5,z811])],[(0,[z1,z2,z3,z4,z5,z1017]),(0,[z2,z1018,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1019,z5]),(0,[z1,z436,z3,z4,z5,z162])],[(0,[z1,z2,z132,z247,z5,z8]),(0,[z1,z2,z3,z4,z1020,z8]),(0,[z1,z2,z1021,z4,z5,z8]),(0,[z1,z2,z3,z1022,z5,z8]),(0,[z1,z2,z3,z661,z30,z5])],[(0,[z1,z2,z3,z562,z5,z8]),(0,[z1,z2,z801,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1023]),(0,[z1,z1024,z3,z4,z5,z8]),(0,[z1,z125,z104,z4,z5,z8]),(0,[z1,z2,z3,z4,z414,z96]),(0,[z235,z1,z2,z51,z5,z11]),(0,[z1,z2,z163,z4,z440,z5]),(0,[z1,z2,z3,z4,z870,z28])],[(0,[z1,z2,z1025,z4,z5,z8]),(0,[z17,z1,z3,z860,z5,z8])],[(0,[z1,z2,z132,z4,z293,z8]),(0,[z1,z2,z3,z4,z5,z1026]),(0,[z243,z2,z3,z4,z5,z28]),(0,[z1,z125,z2,z4,z5,z236]),(0,[z235,z1,z2,z4,z5,z28]),(0,[z1,z273,z3,z4,z5,z6]),(0,[z99,z2,z3,z213,z5,z8]),(0,[z1,z2,z879,z4,z5,z8])],[(0,[z1,z178,z3,z4,z5,z6]),(0,[z47,z2,z3,z4,z73,z8]),(0,[z1,z2,z269,z4,z5,z1027]),(0,[z1,z103,z3,z4,z347,z8]),(0,[z1,z525,z3,z4,z5,z11])],[(0,[z1,z2,z105,z4,z25,z6]),(0,[z29,z1,z2,z558,z8,z164])],[(0,[z1,z154,z339,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z1028]),(0,[z1,z1029,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z20,z4,z5,z177]),(0,[z1,z2,z262,z4,z5,z1013]),(0,[z1,z366,z3,z4,z30,z5]),(0,[z1,z103,z3,z4,z72,z28]),(0,[z1,z226,z2,z4,z5,z28]),(0,[z1030,z2,z3,z4,z5,z8]),(0,[z413,z2,z3,z4,z5,z579])],[(0,[z1,z2,z3,z4,z1031,z8]),(0,[z2,z54,z4,z67,z5,z28]),(0,[z1,z1032,z3,z4,z5,z8]),(0,[z1,z2,z32,z4,z5,z236]),(0,[z1,z1033,z3,z4,z5,z8]),(0,[z1,z2,z558,z4,z30,z5])],[(0,[z1,z135,z3,z4,z5,z100]),(0,[z1,z1034,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1035,z5]),(0,[z1,z2,z3,z4,z5,z1008]),(0,[z1,z2,z3,z32,z5,z389]),(0,[z1,z2,z3,z4,z1036,z8])],[(0,[z1,z2,z70,z4,z5,z389]),(0,[z1,z2,z3,z4,z1037,z8]),(0,[z226,z2,z3,z50,z5,z8]),(0,[z235,z1,z2,z51,z5,z96]),(0,[z1,z2,z296,z4,z71,z8]),(0,[z1,z2,z3,z588,z5,z12])],[(0,[z1,z2,z3,z1038,z4,z5]),(0,[z1,z2,z43,z4,z5,z160]),(0,[z29,z1,z2,z3,z331,z164])],[(0,[z1,z2,z3,z4,z120,z6]),(0,[z169,z2,z54,z4,z5,z28]),(0,[z1,z2,z3,z1039,z5,z8]),(0,[z2,z3,z67,z5,z73,z12]),(0,[z1,z153,z15,z4,z30,z5]),(0,[z1,z1010,z3,z4,z5,z28]),(0,[z1,z2,z398,z4,z5,z6])],[(0,[z76,z2,z77,z4,z5,z224]),(0,[z1,z525,z3,z4,z5,z96]),(0,[z1,z2,z3,z4,z5,z1040]),(0,[z1,z2,z111,z4,z5,z236])],[(0,[z113,z2,z3,z67,z5,z12]),(0,[z1,z2,z43,z4,z5,z166])],[(0,[z1,z2,z3,z1041,z5,z8]),(0,[z1,z2,z269,z4,z5,z8]),(0,[z47,z2,z262,z4,z73,z8]),(0,[z47,z2,z3,z215,z73,z8]),(0,[z1,z2,z3,z4,z5,z1042]),(0,[z1,z2,z3,z4,z5,z1043]),(0,[z1,z2,z105,z4,z223,z8]),(0,[z1,z78,z3,z4,z5,z12])],[(0,[z1,z2,z3,z247,z5,z1044]),(0,[z1,z2,z3,z48,z5,z6]),(0,[z1,z441,z15,z4,z5,z8]),(0,[z29,z1,z2,z4,z5,z236])],[(0,[z1,z2,z1045,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1046]),(0,[z1,z2,z20,z4,z5,z236]),(0,[z1,z2,z77,z4,z117,z8]),(0,[z1,z2,z3,z4,z1047,z8]),(0,[z1,z2,z1048,z4,z5,z309]),(0,[z1,z2,z3,z1022,z5,z28])],[(0,[z1,z842,z3,z4,z5,z8]),(0,[z1,z2,z3,z32,z5,z376]),(0,[z1,z2,z1049,z4,z5,z8]),(0,[z1,z2,z3,z562,z5,z28]),(0,[z2,z3,z4,z5,z709,z224]),(0,[z1,z2,z105,z4,z686,z8]),(0,[z1,z2,z4,z5,z236,z6])],[(0,[z1,z125,z3,z33,z5,z8]),(0,[z1,z103,z3,z4,z305,z8])],[(0,[z1,z2,z3,z4,z5,z1050])],[(0,[z1,z2,z3,z1051,z5,z8]),(0,[z415,z2,z3,z67,z5,z12]),(0,[z1,z2,z3,z4,z5,z1052]),(0,[z1,z2,z50,z4,z5,z465])],[(0,[z1,z2,z3,z4,z5,z1053])]],
   [[(0,[z1,z2,z3,z4,z5,z1054]),(0,[z1,z2,z3,z4,z5,z1055]),(0,[z1,z2,z3,z4,z5,z1056]),(0,[z1,z2,z568,z4,z5,z28]),(0,[z1,z283,z3,z4,z5,z8]),(0,[z1,z2,z43,z4,z147,z28]),(0,[z1,z2,z379,z4,z5,z12]),(0,[z226,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z264,z6]),(0,[z1,z2,z3,z4,z1057,z8]),(0,[z1,z155,z2,z4,z5,z236]),(0,[z1,z1029,z3,z4,z5,z28])],[(0,[z369,z214,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1058]),(0,[z1,z2,z54,z4,z5,z28]),(0,[z1,z1059,z3,z4,z5,z8]),(0,[z1,z270,z3,z4,z5,z389]),(0,[z1,z2,z3,z4,z210,z402]),(0,[z1,z2,z1060,z4,z5,z8]),(0,[z1,z2,z379,z4,z23,z8]),(0,[z1,z2,z3,z4,z5,z1061]),(0,[z1,z2,z3,z4,z5,z1062])],[(0,[z1,z2,z3,z215,z1063,z5]),(0,[z1,z2,z3,z4,z5,z1064])],[(0,[z2,z54,z4,z196,z5,z8]),(0,[z1,z2,z269,z215,z5,z8]),(0,[z1,z2,z111,z3,z562,z5]),(0,[z1,z2,z3,z108,z5,z12])],[(0,[z1,z2,z3,z1065,z5,z8]),(0,[z1,z2,z3,z32,z5,z429]),(0,[z1,z2,z543,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z857])],[(0,[z119,z214,z3,z4,z5,z256]),(0,[z1,z2,z3,z1066,z5,z8]),(0,[z134,z1,z2,z4,z5,z236]),(0,[z461,z2,z3,z32,z5,z8]),(0,[z47,z2,z3,z4,z330,z73]),(0,[z1,z2,z3,z4,z5,z1067]),(0,[z1,z2,z242,z562,z5,z8]),(0,[z1,z114,z3,z4,z5,z162]),(0,[z1,z2,z492,z4,z5,z28])],[(0,[z2,z214,z3,z67,z5,z12]),(0,[z1,z2,z3,z1068,z4,z5]),(0,[z1,z2,z3,z4,z1069,z8]),(0,[z1,z2,z3,z67,z5,z326]),(0,[z1,z2,z3,z4,z5,z1070]),(0,[z1,z2,z3,z4,z5,z1071])],[(0,[z1,z2,z3,z4,z1072,z8]),(0,[z1,z2,z3,z4,z1073,z8]),(0,[z1,z1074,z3,z4,z5,z8]),(0,[z1,z1075,z3,z4,z5,z8])],[(0,[z1,z214,z3,z4,z5,z193]),(0,[z1,z2,z3,z4,z5,z1076]),(0,[z1,z2,z219,z4,z71,z8]),(0,[z409,z1,z2,z51,z5,z8])],[(0,[z1,z2,z3,z4,z5,z1077]),(0,[z1,z2,z3,z1078,z5,z8]),(0,[z1,z2,z77,z4,z5,z21]),(0,[z1,z2,z221,z4,z5,z402]),(0,[z1,z114,z2,z3,z4,z117]),(0,[z76,z2,z3,z4,z5,z709]),(0,[z1,z2,z3,z4,z1079,z5]),(0,[z1,z2,z4,z5,z309,z216]),(0,[z1,z2,z3,z4,z5,z1080]),(0,[z1,z267,z2,z4,z5,z28]),(0,[z185,z273,z3,z4,z5,z8])],[(0,[z1,z2,z132,z4,z5,z8]),(0,[z1,z2,z3,z108,z117,z8]),(0,[z1,z441,z15,z4,z5,z28]),(0,[z243,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z326])],[(0,[z134,z2,z54,z4,z5,z8]),(0,[z1,z2,z513,z4,z5,z28]),(0,[z68,z2,z3,z4,z59,z8]),(1,[z2,z3,z4,z5,z709]),(0,[z1,z2,z379,z4,z5,z1081]),(0,[z1,z283,z3,z4,z5,z263]),(0,[z1,z798,z3,z4,z5,z8]),(0,[z1,z2,z4,z5,z1082,z236])],[(0,[z433,z214,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z30,z497]),(0,[z1,z2,z3,z4,z5,z1083]),(0,[z1,z2,z4,z51,z5,z376])],[(0,[z1,z2,z54,z4,z377,z8]),(0,[z535,z2,z54,z4,z5,z8]),(0,[z1,z2,z3,z4,z117,z14]),(0,[z1,z125,z3,z33,z5,z28])],[(0,[z1,z69,z53,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1084]),(0,[z1,z2,z3,z4,z5,z202]),(0,[z1,z2,z4,z5,z1085,z8]),(0,[z1,z2,z3,z1048,z4,z5]),(0,[z1,z2,z3,z4,z5,z1086]),(0,[z1,z2,z3,z4,z5,z1087]),(0,[z1,z2,z3,z4,z5,z331])]],
   [[(0,[z134,z2,z54,z251,z5,z8]),(0,[z1,z2,z4,z5,z579,z28]),(0,[z1,z452,z3,z4,z59,z8]),(0,[z1,z2,z3,z4,z5,z1088]),(0,[z1,z103,z3,z4,z72,z6]),(0,[z1,z2,z368,z4,z5,z13]),(0,[z235,z1,z2,z50,z5,z28]),(0,[z1,z2,z558,z4,z5,z12]),(0,[z1,z2,z4,z5,z140,z12]),(0,[z1,z167,z3,z4,z425,z5])],[(0,[z1,z2,z1089,z4,z5,z8]),(0,[z1,z2,z1090,z4,z30,z5])],[(0,[z1,z2,z3,z4,z5,z1091]),(0,[z1,z2,z3,z4,z5,z1092]),(0,[z1,z2,z4,z5,z71,z160]),(0,[z76,z366,z3,z4,z5,z224]),(0,[z1,z2,z3,z4,z5,z1093]),(0,[z1,z2,z81,z50,z5,z326]),(0,[z1,z283,z3,z4,z5,z28]),(0,[z185,z2,z512,z4,z5,z8]),(0,[z299,z2,z3,z4,z239,z5])],[(0,[z1,z135,z3,z4,z497,z8]),(0,[z1,z2,z3,z196,z1035,z5])],[(0,[z1,z2,z53,z4,z30,z5]),(0,[z1,z2,z3,z4,z5,z1094]),(0,[z1,z2,z3,z4,z5,z1095]),(0,[z1,z2,z3,z4,z147,z12]),(0,[z1,z2,z4,z425,z5,z236]),(0,[z1,z2,z1096,z4,z5,z8])],[(0,[z1,z2,z1097,z3,z4,z5]),(0,[z1,z139,z3,z4,z5,z372]),(0,[z1,z2,z3,z4,z1098,z8]),(0,[z1099,z2,z3,z4,z5,z8]),(0,[z17,z1,z3,z16,z5,z12]),(0,[z1,z2,z3,z4,z5,z1100])],[(0,[z1,z2,z1101,z4,z5,z8]),(0,[z1,z2,z1102,z4,z330,z5]),(0,[z1,z2,z104,z4,z5,z8]),(0,[z1,z2,z81,z344,z5,z8]),(0,[z1,z2,z512,z4,z5,z28]),(0,[z1,z2,z1103,z3,z4,z5])],[(0,[z1,z2,z1104,z3,z4,z5]),(0,[z243,z2,z3,z4,z5,z384]),(0,[z1,z2,z3,z4,z149,z12])],[(0,[z1,z1105,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1106]),(0,[z1,z2,z3,z4,z30,z23]),(1,[z1,z3,z860,z5,z8]),(0,[z1,z2,z1107,z4,z5,z8]),(0,[z1,z2,z184,z4,z71,z64])],[(0,[z1,z2,z3,z4,z5,z402]),(0,[z1,z2,z3,z4,z5,z1108]),(0,[z1,z2,z3,z67,z5,z465]),(0,[z535,z2,z3,z4,z73,z8]),(0,[z1,z2,z3,z871,z5,z8])],[(0,[z1,z1109,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1110])],[(0,[z0,z2,z3,z247,z5,z8]),(0,[z1,z2,z3,z4,z5,z1111]),(0,[z1,z2,z3,z4,z5,z1112]),(0,[z1,z2,z262,z4,z5,z202]),(0,[z1,z2,z3,z562,z5,z6]),(0,[z1,z2,z146,z4,z5,z12])],[(0,[z1,z2,z3,z4,z5,z1044]),(0,[z1,z2,z3,z4,z161,z12]),(0,[z1,z78,z3,z4,z30,z5]),(0,[z29,z1,z2,z3,z249,z164])],[(0,[z1,z2,z132,z4,z5,z28]),(0,[z1,z2,z1113,z4,z5,z8]),(0,[z1,z2,z1114,z4,z5,z8]),(0,[z1,z2,z582,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z465]),(0,[z1,z2,z567,z3,z87,z4])],[(0,[z1,z214,z104,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1115]),(1,[z1,z825,z4,z5,z8]),(0,[z1,z2,z3,z4,z147,z128]),(0,[z1,z2,z213,z4,z5,z236])],[(0,[z1,z2,z3,z1116,z5,z8]),(0,[z1,z2,z3,z4,z5,z1117]),(0,[z1,z366,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1118,z5]),(0,[z55,z509,z2,z3,z4,z5]),(0,[z1,z3,z33,z860,z5,z8]),(0,[z1,z2,z3,z4,z5,z1119])]],
   [[(0,[z1,z2,z3,z4,z5,z1120]),(0,[z34,z2,z3,z67,z5,z12]),(0,[z1,z2,z3,z4,z5,z1121]),(0,[z1,z525,z3,z4,z414,z8]),(0,[z1,z432,z105,z4,z25,z8])],[(0,[z1,z2,z146,z4,z115,z5])],[(0,[z95,z2,z3,z67,z5,z12]),(0,[z1,z125,z15,z4,z5,z28]),(0,[z1,z1122,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z1123,z8]),(0,[z1,z2,z4,z377,z8,z28]),(0,[z1,z103,z2,z4,z5,z236]),(0,[z1,z1124,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1125]),(0,[z1,z105,z283,z4,z5,z28])],[(0,[z55,z1,z2,z4,z5,z140]),(0,[z1,z153,z15,z4,z5,z8]),(0,[z1,z2,z4,z5,z6,z536]),(0,[z1,z2,z4,z572,z5,z6])],[(0,[z1,z2,z221,z4,z5,z389]),(0,[z1,z2,z419,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z1126]),(0,[z1,z2,z4,z1127,z5,z236])],[(0,[z1,z2,z53,z4,z5,z65]),(0,[z1,z2,z214,z4,z5,z236]),(0,[z1,z2,z3,z4,z5,z1128]),(0,[z1,z2,z1129,z4,z5,z8]),(0,[z1,z1130,z3,z4,z5,z8]),(0,[z1,z233,z2,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z1131]),(0,[z1132,z2,z3,z4,z5,z8]),(0,[z1,z139,z3,z4,z5,z811]),(0,[z1,z432,z3,z4,z5,z502])],[(0,[z1,z2,z764,z4,z5,z8]),(0,[z1133,z1,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1134]),(0,[z345,z2,z3,z4,z73,z8]),(0,[z1,z2,z3,z4,z1135,z5]),(0,[z1,z2,z184,z4,z71,z12]),(0,[z1,z2,z3,z323,z30,z5]),(0,[z1,z2,z3,z1039,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1136]),(0,[z2,z3,z54,z67,z5,z12]),(0,[z1,z2,z3,z108,z30,z5]),(0,[z1,z2,z104,z4,z5,z28])],[(0,[z1,z2,z3,z4,z5,z1137]),(0,[z1,z2,z368,z87,z4,z5])],[(0,[z1,z270,z3,z4,z5,z402]),(0,[z1,z2,z269,z4,z5,z6]),(0,[z1,z2,z3,z1138,z5,z8]),(0,[z1,z2,z3,z4,z1139,z5])],[(0,[z1,z2,z1140,z4,z5,z8]),(0,[z1,z2,z3,z4,z1141,z8]),(0,[z1,z452,z3,z4,z5,z130]),(0,[z1,z2,z3,z4,z5,z1142]),(0,[z1,z2,z4,z5,z607,z28]),(0,[z1,z2,z3,z4,z5,z1143]),(0,[z1,z2,z3,z131,z5,z12]),(0,[z1,z2,z1144,z4,z5,z8]),(0,[z1,z2,z3,z1145,z4,z5])],[(0,[z1,z121,z2,z945,z4,z5]),(0,[z586,z69,z3,z4,z5,z8]),(0,[z113,z2,z3,z196,z5,z8]),(0,[z2,z54,z67,z51,z5,z8]),(0,[z413,z2,z3,z4,z5,z14]),(0,[z1,z518,z3,z4,z5,z173])],[(0,[z134,z2,z54,z196,z5,z8]),(0,[z1,z2,z3,z4,z30,z117]),(0,[z1,z2,z1146,z4,z5,z8]),(0,[z1,z2,z608,z4,z5,z28]),(0,[z1,z2,z512,z4,z8,z164]),(0,[z1,z2,z3,z4,z763,z94])],[(0,[z1,z2,z20,z4,z159,z8]),(0,[z1,z2,z3,z4,z30,z159]),(0,[z1,z2,z350,z4,z5,z936]),(0,[z1,z125,z3,z33,z5,z6]),(0,[z1,z2,z3,z4,z5,z1147]),(0,[z1,z2,z1148,z4,z5,z236])],[(0,[z1,z434,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z1149,z8])]],
   [[(0,[z1,z2,z3,z67,z5,z389]),(0,[z1,z2,z3,z4,z330,z5]),(0,[z1,z1150,z3,z4,z5,z8]),(0,[z1,z2,z368,z4,z5,z8]),(0,[z1,z2,z163,z4,z5,z89]),(0,[z1,z2,z3,z4,z5,z892]),(0,[z1151,z2,z3,z4,z5,z8])],[(0,[z1,z121,z139,z3,z4,z5]),(0,[z7,z2,z54,z4,z5,z8]),(0,[z1,z2,z3,z4,z1152,z5]),(0,[z1,z366,z3,z4,z5,z28]),(0,[z1,z2,z242,z4,z5,z224]),(0,[z1,z2,z3,z4,z94,z117]),(0,[z1,z114,z3,z4,z557,z5]),(0,[z235,z226,z2,z51,z5,z8]),(0,[z1,z2,z3,z4,z998,z8]),(0,[z1,z1153,z2,z4,z5,z236])],[(0,[z1,z2,z3,z1154,z5,z8]),(0,[z1,z1155,z3,z4,z5,z8]),(0,[z1,z2,z1156,z4,z5,z8]),(0,[z1,z283,z3,z4,z5,z6])],[(0,[z1,z2,z53,z4,z5,z12]),(0,[z1,z2,z184,z4,z834,z8]),(0,[z1,z2,z4,z5,z613,z28])],[(0,[z1,z2,z3,z4,z5,z1157]),(0,[z1,z2,z3,z4,z1158,z5]),(0,[z1,z2,z3,z4,z5,z389]),(0,[z1,z260,z2,z3,z5,z177])],[(0,[z1,z2,z3,z501,z120,z8]),(0,[z1,z1159,z3,z4,z5,z8])],[(0,[z1,z154,z349,z4,z5,z8]),(0,[z2,z3,z4,z903,z73,z8]),(0,[z76,z1,z2,z4,z5,z140]),(0,[z1,z153,z15,z4,z5,z28]),(0,[z1,z2,z81,z367,z5,z8]),(0,[z1,z2,z4,z25,z377,z8]),(0,[z79,z1,z2,z4,z5,z28]),(0,[z1,z2,z512,z4,z5,z6])],[(0,[z1,z178,z20,z4,z5,z8]),(0,[z1,z2,z70,z4,z30,z5]),(0,[z1,z153,z283,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1160])],[(0,[z1,z1018,z3,z4,z5,z8]),(0,[z1,z1161,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1162,z12])],[(0,[z1,z2,z3,z4,z1163,z8]),(0,[z1,z2,z1164,z3,z4,z5]),(0,[z1,z2,z3,z251,z30,z5]),(0,[z1,z2,z3,z4,z1165,z8]),(0,[z1,z2,z3,z67,z5,z376]),(0,[z1,z403,z111,z3,z4,z5]),(0,[z17,z1,z3,z16,z30,z5]),(0,[z1,z2,z3,z4,z1166,z5])],[(0,[z119,z214,z3,z4,z120,z8]),(0,[z1,z2,z3,z4,z1063,z5]),(0,[z1,z2,z4,z5,z236,z162])],[(0,[z1,z58,z3,z4,z5,z389]),(0,[z34,z2,z3,z67,z161,z8]),(0,[z1,z1167,z3,z4,z5,z8]),(0,[z55,z2,z3,z4,z5,z709]),(0,[z1,z2,z379,z4,z5,z170]),(0,[z1,z2,z4,z553,z71,z8])],[(0,[z1,z2,z54,z4,z5,z100]),(0,[z1,z2,z350,z4,z264,z8]),(0,[z1,z2,z3,z1078,z5,z6])],[(0,[z1,z2,z132,z4,z5,z6]),(0,[z1,z2,z3,z4,z210,z12]),(0,[z700,z2,z3,z4,z73,z8]),(0,[z1,z622,z3,z4,z5,z13]),(0,[z1,z2,z4,z612,z71,z8]),(0,[z1,z2,z3,z4,z1168,z8]),(0,[z1,z2,z3,z4,z5,z376]),(0,[z1,z2,z3,z4,z1169,z5]),(0,[z1,z2,z3,z4,z5,z1170])],[(0,[z1,z2,z3,z4,z5,z1171]),(0,[z134,z2,z54,z4,z5,z6]),(0,[z238,z2,z54,z4,z5,z8]),(0,[z1,z2,z1172,z4,z5,z8])],[(0,[z1,z2,z3,z4,z1173,z8]),(0,[z1,z403,z3,z4,z5,z224]),(0,[z1,z2,z146,z4,z30,z5])]],
   [[(0,[z1,z2,z3,z4,z159,z100]),(0,[z1,z2,z43,z4,z5,z28]),(0,[z1,z2,z324,z4,z5,z193]),(0,[z1,z139,z3,z4,z5,z175]),(0,[z1,z2,z1090,z4,z5,z8])],[(0,[z1,z2,z3,z215,z30,z5]),(0,[z47,z2,z3,z4,z73,z28]),(0,[z76,z2,z3,z4,z575,z5]),(0,[z1,z1174,z2,z3,z4,z5]),(0,[z226,z2,z3,z4,z414,z8]),(0,[z1,z2,z3,z5,z177,z12]),(0,[z1175,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1176])],[(0,[z1,z2,z4,z5,z1177,z8]),(0,[z1,z2,z3,z4,z5,z1178]),(0,[z1,z2,z3,z4,z5,z1179]),(0,[z95,z2,z3,z215,z5,z8]),(0,[z1,z452,z3,z4,z73,z8]),(0,[z1,z153,z2,z4,z5,z236]),(0,[z1,z2,z368,z4,z5,z28]),(0,[z1,z2,z704,z4,z25,z8]),(0,[z1,z1180,z3,z4,z5,z8])],[(0,[z1,z2,z3,z67,z5,z429]),(0,[z1,z1181,z3,z4,z5,z8])],[(0,[z1,z2,z3,z501,z5,z256]),(0,[z34,z2,z3,z67,z30,z5]),(0,[z17,z1,z2,z4,z5,z236]),(0,[z1,z2,z3,z4,z5,z193]),(0,[z1,z2,z382,z4,z5,z28])],[(0,[z1,z2,z3,z1182,z5,z8]),(0,[z1,z2,z3,z4,z5,z64])],[(0,[z1,z2,z3,z4,z1183,z8]),(0,[z1,z2,z77,z4,z5,z8]),(0,[z243,z2,z350,z4,z5,z8]),(0,[z1,z2,z3,z4,z23,z12]),(0,[z1,z2,z4,z5,z1184,z8]),(0,[z1,z125,z3,z33,z343,z5]),(0,[z1,z2,z3,z4,z5,z1185])],[(0,[z1,z2,z3,z4,z5,z65]),(0,[z1,z1186,z3,z4,z5,z8]),(0,[z1,z1187,z3,z4,z5,z8]),(0,[z1,z2,z1188,z4,z5,z8]),(0,[z1,z2,z1189,z3,z4,z5]),(0,[z1,z2,z4,z5,z1190,z8]),(0,[z1,z2,z3,z30,z5,z404]),(0,[z1,z2,z3,z4,z5,z429])],[(0,[z1,z2,z3,z4,z1191,z8]),(0,[z1,z1192,z2,z3,z4,z5]),(0,[z1,z2,z104,z4,z5,z6])],[(0,[z1,z178,z3,z4,z5,z100]),(0,[z1,z1193,z3,z4,z5,z8])],[(0,[z220,z2,z3,z4,z73,z8]),(0,[z76,z2,z3,z108,z5,z224]),(0,[z1,z139,z2,z3,z4,z117]),(0,[z1,z2,z1194,z4,z5,z8]),(0,[z1,z2,z126,z4,z5,z28]),(0,[z1,z2,z3,z5,z188,z12])],[(0,[z1,z2,z281,z4,z5,z28]),(0,[z1,z2,z3,z4,z117,z12]),(0,[z563,z1,z3,z16,z5,z8]),(0,[z1,z78,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1195]),(0,[z1,z2,z105,z4,z5,z341]),(0,[z1,z2,z4,z548,z71,z28])],[(0,[z1,z2,z1196,z4,z5,z8]),(0,[z1,z2,z3,z4,z1197,z5]),(0,[z1,z1198,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z440,z5])],[(0,[z1,z2,z3,z4,z5,z1199]),(0,[z1,z2,z4,z5,z803,z8]),(0,[z1,z2,z269,z4,z5,z28]),(0,[z24,z1,z3,z4,z742,z8]),(1,[z99,z2,z3,z8,z164]),(0,[z1,z2,z3,z4,z1200,z5])],[(0,[z47,z2,z3,z4,z30,z73]),(0,[z76,z2,z3,z4,z117,z224]),(0,[z1,z2,z1201,z4,z5,z8]),(0,[z1,z44,z2,z4,z5,z28])],[(0,[z1,z2,z1202,z4,z5,z8]),(0,[z1,z2,z15,z4,z5,z28]),(0,[z1,z2,z105,z4,z25,z502])]],
   [[(0,[z1,z69,z3,z247,z5,z8]),(0,[z1,z121,z403,z3,z4,z5]),(0,[z1,z2,z3,z4,z1203,z8]),(0,[z1,z2,z3,z67,z5,z12]),(0,[z1,z2,z3,z4,z264,z384]),(0,[z17,z1,z3,z16,z5,z170]),(0,[z226,z2,z3,z4,z5,z11]),(0,[z623,z1,z2,z4,z5,z28]),(0,[z1,z1204,z3,z4,z5,z8])],[(0,[z415,z2,z3,z67,z5,z8]),(0,[z1,z452,z3,z48,z5,z8]),(0,[z1,z366,z3,z4,z5,z6]),(0,[z1,z2,z1205,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1206]),(0,[z1,z2,z3,z1207,z5,z8])],[(1,[z1,z2,z4,z377,z28])],[(0,[z1,z69,z3,z4,z293,z8]),(0,[z1,z2,z3,z4,z1208,z8]),(0,[z1,z2,z379,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1209]),(0,[z1,z2,z624,z4,z5,z28]),(0,[z1,z2,z3,z4,z147,z89]),(0,[z1,z2,z81,z50,z440,z5])],[(0,[z1,z2,z3,z4,z59,z216]),(0,[z1,z2,z126,z4,z71,z8])],[(0,[z1,z2,z3,z247,z30,z5]),(0,[z1,z2,z3,z32,z5,z12]),(0,[z1,z2,z3,z4,z1210,z8]),(0,[z1,z2,z3,z4,z5,z1211]),(0,[z1,z2,z3,z4,z1212,z5]),(0,[z1213,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z30,z5,z429]),(0,[z1,z66,z2,z3,z30,z5]),(0,[z1,z2,z3,z4,z763,z5])],[(0,[z1,z2,z3,z4,z1214,z8]),(0,[z1,z2,z3,z196,z30,z5]),(0,[z1,z2,z70,z4,z5,z12]),(0,[z1,z452,z3,z4,z5,z202]),(0,[z1,z153,z15,z4,z5,z6]),(0,[z99,z273,z3,z4,z5,z8])],[(0,[z1,z214,z15,z4,z5,z28]),(0,[z1,z2,z3,z108,z5,z8]),(0,[z1,z2,z3,z4,z5,z1215]),(0,[z1,z403,z3,z562,z5,z8]),(0,[z1,z2,z105,z4,z5,z28]),(0,[z1,z2,z398,z4,z5,z502]),(0,[z1,z1216,z3,z4,z5,z8])],[(0,[z1,z2,z1217,z3,z4,z5]),(0,[z1,z2,z541,z4,z5,z28]),(0,[z1,z2,z3,z251,z5,z12]),(0,[z1,z2,z77,z4,z5,z28]),(0,[z1,z43,z15,z4,z5,z28]),(0,[z1,z2,z368,z4,z5,z39])],[(0,[z119,z1,z2,z4,z5,z236]),(0,[z1,z2,z3,z4,z5,z1218]),(0,[z1,z179,z2,z4,z5,z28]),(0,[z1,z273,z3,z4,z5,z249])],[(0,[z17,z1,z3,z16,z23,z8]),(0,[z1,z2,z3,z4,z5,z1219]),(0,[z226,z2,z3,z4,z5,z96]),(0,[z1,z1220,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z1221,z5]),(0,[z1,z2,z4,z439,z5,z803]),(0,[z1,z2,z3,z4,z1222,z5]),(0,[z1,z2,z1223,z4,z5,z8])],[(0,[z34,z2,z3,z67,z210,z8]),(0,[z1,z114,z3,z4,z425,z5]),(0,[z1,z2,z4,z5,z236,z236])],[(0,[z2,z3,z54,z196,z5,z8]),(0,[z1,z475,z3,z4,z197,z8]),(0,[z1,z78,z3,z4,z5,z28])],[(0,[z62,z2,z3,z4,z5,z224]),(0,[z1,z2,z3,z4,z5,z128]),(0,[z1,z2,z1224,z4,z5,z8]),(0,[z235,z1,z2,z4,z414,z28]),(0,[z1,z2,z4,z5,z71,z28])],[(0,[z1,z2,z3,z4,z1225,z8]),(0,[z1,z825,z15,z4,z5,z8]),(0,[z1,z2,z279,z3,z397,z4]),(0,[z1,z2,z4,z5,z1226,z12])]],
   [[(0,[z1,z2,z3,z4,z5,z1227]),(0,[z1,z2,z262,z4,z5,z12]),(0,[z1,z2,z3,z215,z5,z12]),(0,[z1,z154,z4,z5,z305,z8]),(0,[z1,z2,z4,z5,z377,z28]),(0,[z185,z2,z3,z4,z5,z331])],[(0,[z134,z2,z54,z4,z5,z28]),(0,[z2,z3,z780,z67,z5,z8]),(0,[z47,z2,z3,z4,z73,z6]),(0,[z1,z2,z4,z440,z5,z236]),(0,[z57,z2,z3,z4,z596,z5])],[(0,[z1,z2,z3,z4,z5,z1228]),(0,[z1,z2,z368,z4,z5,z6]),(0,[z235,z1,z2,z4,z5,z177]),(0,[z1,z2,z283,z4,z5,z28])],[(0,[z1,z2,z53,z247,z5,z8]),(0,[z1,z2,z3,z4,z5,z1229]),(0,[z2,z270,z3,z67,z5,z8]),(0,[z1,z58,z3,z4,z5,z402]),(0,[z24,z1,z2,z4,z309,z8]),(0,[z1,z2,z558,z4,z5,z8]),(0,[z1,z2,z4,z5,z140,z8])],[(0,[z34,z2,z221,z67,z5,z8]),(0,[z1,z2,z1230,z4,z5,z8])],[(0,[z1,z2,z3,z4,z1231,z8]),(0,[z1,z270,z3,z4,z5,z12]),(0,[z1,z139,z403,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1232]),(0,[z1,z2,z379,z4,z5,z28]),(0,[z1,z585,z2,z4,z71,z8])],[(0,[z1,z2,z602,z4,z5,z28]),(0,[z1,z2,z3,z251,z1233,z5]),(0,[z2,z3,z4,z5,z14,z709]),(0,[z1,z2,z3,z4,z5,z1234]),(0,[z1,z2,z3,z4,z5,z1235]),(1,[z1,z2,z4,z5,z782]),(0,[z1,z78,z3,z4,z86,z8])],[(0,[z1,z2,z3,z247,z5,z65]),(0,[z1,z2,z3,z4,z1236,z8]),(0,[z1,z2,z3,z4,z5,z1237]),(0,[z1,z2,z3,z4,z147,z8]),(0,[z1,z2,z145,z4,z5,z12])],[(0,[z1,z2,z3,z4,z5,z1238]),(0,[z230,z2,z379,z4,z5,z8]),(0,[z17,z1,z3,z16,z5,z8])],[(0,[z119,z434,z214,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1239]),(0,[z1,z2,z1240,z4,z5,z8]),(0,[z1,z2,z221,z4,z30,z5]),(0,[z560,z1,z2,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z1241]),(0,[z1,z2,z3,z4,z1242,z8]),(0,[z95,z2,z3,z4,z903,z8]),(0,[z1,z2,z3,z108,z5,z28]),(0,[z1,z2,z3,z4,z5,z874]),(0,[z1,z103,z3,z4,z72,z216]),(0,[z1,z2,z410,z3,z4,z124])],[(0,[z1,z2,z3,z4,z293,z65]),(0,[z1,z178,z3,z4,z497,z8]),(0,[z1,z2,z1243,z4,z5,z8]),(0,[z1,z114,z2,z242,z4,z5]),(0,[z1,z2,z3,z4,z30,z377]),(0,[z1,z2,z3,z4,z149,z8]),(0,[z99,z2,z3,z4,z5,z249]),(0,[z1,z2,z4,z5,z236,z1244])],[(0,[z1,z1245,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z498,z39])],[(0,[z169,z2,z3,z500,z5,z8]),(0,[z169,z2,z3,z32,z30,z5]),(0,[z1,z2,z3,z4,z1246,z5]),(0,[z1,z2,z3,z4,z30,z149]),(0,[z235,z1,z2,z4,z5,z236]),(0,[z1,z2,z3,z50,z5,z429]),(0,[z1,z2,z3,z4,z5,z1247]),(0,[z1,z2,z146,z30,z5,z12])],[(0,[z1,z2,z3,z4,z5,z1248]),(0,[z1,z135,z3,z4,z159,z8]),(0,[z1,z2,z3,z4,z5,z160]),(0,[z1,z2,z970,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1249]),(0,[z1,z2,z3,z32,z5,z157]),(1,[z1,z2,z4,z5,z803]),(0,[z1,z2,z3,z4,z1250,z8])],[(0,[z1,z2,z324,z4,z5,z1251]),(0,[z1,z2,z146,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z1252]),(0,[z1,z2,z3,z4,z5,z1253]),(0,[z1,z2,z3,z4,z5,z1254])]],
   [[(0,[z1,z2,z3,z562,z42,z8]),(0,[z1,z2,z666,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z166])],[(0,[z1,z2,z1255,z4,z5,z8]),(0,[z1,z1256,z2,z3,z4,z5]),(0,[z1,z2,z4,z5,z1257,z8]),(0,[z1,z2,z3,z4,z1258,z5]),(0,[z1,z2,z70,z4,z161,z8]),(0,[z1,z2,z567,z4,z5,z236])],[(0,[z1,z2,z3,z4,z5,z863]),(0,[z1,z2,z3,z4,z5,z1259]),(0,[z1,z2,z3,z241,z5,z12]),(0,[z1,z2,z3,z4,z5,z1251]),(0,[z235,z226,z2,z4,z5,z28])],[(0,[z1,z2,z3,z244,z5,z12]),(0,[z1,z2,z3,z1260,z5,z8]),(0,[z34,z2,z3,z67,z5,z8]),(0,[z1,z2,z3,z4,z5,z1261]),(0,[z1,z2,z105,z4,z71,z28]),(0,[z1,z2,z4,z5,z633,z28]),(0,[z1,z2,z3,z4,z5,z1262])],[(0,[z1,z2,z3,z4,z1263,z8]),(0,[z1,z2,z3,z247,z5,z12]),(0,[z1,z121,z3,z4,z5,z162]),(0,[z34,z2,z3,z780,z5,z8]),(0,[z1,z1264,z3,z4,z5,z8]),(0,[z1,z78,z3,z4,z8,z164]),(0,[z1,z2,z3,z4,z5,z1265])],[(0,[z1,z2,z3,z764,z4,z5]),(0,[z1,z2,z3,z196,z5,z12]),(0,[z34,z2,z70,z67,z5,z8]),(0,[z1,z2,z3,z663,z5,z12]),(0,[z95,z2,z3,z4,z30,z59]),(0,[z1,z2,z43,z4,z5,z1266]),(0,[z1,z2,z50,z5,z177,z8]),(0,[z1,z2,z4,z5,z140,z28]),(0,[z1,z2,z558,z4,z5,z28])],[(0,[z47,z452,z3,z4,z73,z8]),(0,[z1,z1267,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z769]),(0,[z1,z675,z15,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1268]),(0,[z1,z2,z3,z4,z30,z414]),(0,[z1,z2,z1269,z4,z5,z8])],[(0,[z1,z2,z3,z4,z293,z12]),(0,[z1,z2,z3,z4,z1270,z5]),(0,[z1,z2,z43,z4,z5,z341]),(0,[z1,z2,z1271,z4,z5,z8]),(0,[z1,z114,z375,z4,z5,z162]),(0,[z1,z2,z81,z50,z5,z166]),(0,[z1,z167,z2,z4,z5,z236])],[(0,[z1,z2,z3,z4,z30,z5]),(0,[z1,z2,z3,z4,z1272,z8]),(0,[z1,z2,z77,z4,z5,z6]),(0,[z1,z2,z3,z4,z94,z190])],[(0,[z1,z2,z54,z4,z5,z177]),(0,[z1,z2,z4,z5,z89,z28]),(0,[z63,z2,z3,z4,z5,z12]),(0,[z1,z2,z558,z4,z5,z1273])],[(0,[z134,z2,z54,z4,z5,z401]),(0,[z17,z1,z3,z16,z5,z28]),(0,[z1,z682,z3,z4,z5,z162]),(1,[z226,z2,z51,z5,z8]),(0,[z1,z2,z184,z4,z71,z8])],[(0,[z1,z2,z3,z247,z1221,z5]),(0,[z158,z69,z3,z4,z5,z8]),(0,[z1,z2,z262,z4,z5,z1254]),(0,[z1,z2,z3,z4,z5,z1274]),(0,[z235,z1,z2,z527,z5,z8])],[(0,[z1,z2,z3,z4,z5,z1275]),(0,[z1,z2,z3,z4,z5,z1276]),(0,[z1,z2,z3,z4,z5,z885]),(0,[z57,z2,z3,z4,z5,z14]),(0,[z1,z2,z3,z4,z1277,z8]),(0,[z1,z2,z3,z4,z149,z28]),(0,[z1278,z1,z2,z4,z5,z236])],[(0,[z1,z2,z132,z501,z5,z8]),(0,[z2,z20,z54,z4,z5,z28]),(0,[z62,z2,z54,z4,z5,z8]),(0,[z1,z1279,z3,z4,z5,z8]),(0,[z1,z283,z20,z4,z5,z8]),(0,[z1,z2,z1280,z4,z5,z8]),(0,[z1,z78,z3,z4,z5,z6])],[(0,[z2,z214,z3,z247,z5,z8]),(0,[z1,z2,z242,z4,z5,z579]),(0,[z1,z2,z1281,z3,z4,z5])],[(0,[z1,z2,z3,z1282,z5,z8]),(0,[z1,z366,z242,z4,z5,z8]),(0,[z1,z2,z81,z773,z5,z8]),(0,[z1,z2,z81,z50,z30,z5])]],
   [[(0,[z1,z2,z4,z1283,z5,z8]),(0,[z1,z270,z3,z4,z161,z8]),(0,[z1,z2,z3,z4,z59,z130]),(0,[z1,z114,z2,z4,z5,z236]),(0,[z1,z2,z4,z5,z1005,z28]),(0,[z1,z2,z4,z678,z5,z28]),(0,[z1,z1284,z3,z4,z5,z8]),(0,[z1,z2,z146,z4,z5,z28])],[(0,[z1,z1285,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1286]),(0,[z1,z178,z3,z4,z159,z8]),(0,[z1,z2,z3,z4,z23,z170])],[(0,[z1,z2,z3,z1287,z5,z8]),(0,[z119,z214,z132,z4,z5,z8]),(0,[z1,z452,z269,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1288]),(0,[z1,z2,z3,z4,z1289,z8]),(0,[z1,z2,z3,z165,z5,z12]),(0,[z1,z2,z528,z4,z5,z28])],[(0,[z1,z2,z54,z4,z5,z236]),(0,[z1,z2,z3,z4,z5,z1290])],[(0,[z34,z270,z3,z67,z5,z8]),(0,[z1,z2,z262,z4,z30,z5]),(0,[z1,z2,z4,z5,z1291,z8]),(0,[z1,z2,z4,z5,z309,z1028])],[(0,[z34,z2,z3,z67,z5,z28]),(0,[z1,z243,z3,z16,z5,z8]),(0,[z1,z2,z379,z4,z5,z6]),(0,[z1,z2,z4,z5,z373,z28]),(0,[z1,z2,z3,z4,z1208,z6])],[(0,[z1,z2,z53,z4,z5,z8]),(0,[z1,z2,z192,z4,z71,z8]),(0,[z136,z2,z3,z32,z5,z8]),(0,[z1,z2,z3,z4,z73,z216]),(0,[z1,z2,z15,z4,z5,z341]),(0,[z1,z3,z4,z16,z264,z8]),(0,[z1,z2,z4,z5,z140,z13]),(0,[z1,z2,z3,z690,z5,z465])],[(0,[z1,z2,z3,z4,z1292,z8]),(0,[z1,z2,z3,z1293,z5,z8]),(0,[z1,z2,z3,z274,z5,z12]),(0,[z1,z2,z3,z311,z30,z5]),(0,[z1,z2,z50,z5,z177,z28]),(0,[z1,z2,z3,z4,z1294,z5]),(0,[z1,z2,z3,z4,z5,z1295])],[(0,[z1,z2,z3,z1296,z5,z8]),(0,[z1,z2,z221,z4,z5,z12])],[(0,[z1,z2,z3,z4,z5,z1297]),(0,[z134,z2,z970,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1298]),(0,[z1,z270,z3,z4,z30,z5]),(0,[z1,z2,z1299,z4,z5,z8]),(0,[z1,z2,z4,z5,z769,z8]),(0,[z1,z2,z3,z108,z5,z6])],[(0,[z639,z1,z3,z16,z5,z8]),(0,[z1,z2,z4,z5,z73,z769]),(0,[z1,z2,z3,z4,z5,z1300]),(0,[z1,z2,z4,z5,z744,z8]),(0,[z1,z2,z3,z4,z5,z1301])],[(0,[z169,z2,z3,z32,z5,z12]),(0,[z1,z2,z3,z4,z5,z1302]),(0,[z1,z2,z145,z4,z30,z5]),(0,[z1,z359,z4,z5,z8,z28]),(0,[z1,z2,z3,z4,z1162,z8]),(0,[z1,z2,z4,z5,z140,z39])],[(0,[z1,z2,z3,z4,z5,z1303]),(0,[z1,z2,z3,z67,z210,z8]),(0,[z1,z2,z184,z4,z71,z28])],[(0,[z1,z1304,z3,z4,z5,z8]),(0,[z198,z2,z3,z32,z5,z8]),(0,[z1,z2,z1102,z4,z5,z8]),(0,[z1,z2,z4,z5,z688,z28]),(0,[z409,z1,z2,z4,z5,z28]),(0,[z230,z2,z3,z4,z30,z5]),(0,[z1,z2,z3,z4,z5,z1305])],[(0,[z1,z214,z53,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1306]),(0,[z1,z2,z163,z4,z5,z21]),(0,[z1,z2,z4,z73,z309,z8]),(0,[z1,z114,z2,z3,z562,z5]),(0,[z1,z1307,z2,z3,z4,z5]),(0,[z1,z2,z111,z3,z4,z548])],[(0,[z62,z2,z54,z4,z5,z28]),(1,[z2,z3,z215,z73,z8]),(0,[z1,z2,z3,z4,z5,z170]),(0,[z63,z2,z3,z4,z149,z8])]],
   [[(0,[z1,z2,z3,z48,z784,z5]),(0,[z243,z3,z4,z16,z5,z8])],[(0,[z113,z2,z20,z4,z5,z160]),(0,[z1,z2,z3,z32,z210,z8]),(0,[z1,z350,z4,z16,z5,z8]),(0,[z1308,z2,z3,z4,z5,z8]),(0,[z226,z525,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z30,z1309])],[(0,[z1,z2,z70,z4,z210,z8])],[(0,[z1,z2,z3,z1310,z5,z8]),(0,[z2,z970,z54,z4,z5,z8]),(0,[z1,z2,z4,z59,z309,z8]),(0,[z1,z2,z3,z4,z5,z89]),(0,[z1,z2,z324,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z1311])],[(0,[z1,z2,z3,z292,z5,z12]),(0,[z1,z2,z3,z4,z1312,z8]),(0,[z1,z2,z50,z4,z5,z166]),(0,[z1,z2,z3,z4,z5,z772]),(0,[z1,z2,z3,z4,z30,z1037])],[(0,[z2,z3,z4,z215,z73,z8]),(0,[z1,z2,z1313,z4,z5,z8]),(0,[z1,z2,z3,z4,z1314,z5]),(0,[z1,z2,z4,z5,z71,z341]),(0,[z1,z2,z558,z4,z5,z6]),(0,[z1,z2,z4,z5,z140,z6]),(0,[z1,z2,z1315,z4,z5,z8]),(0,[z1,z2,z204,z4,z5,z236]),(0,[z1316,z1,z2,z4,z5,z236])],[(0,[z1,z2,z3,z4,z30,z120]),(0,[z1,z2,z3,z4,z5,z1317])],[(0,[z1,z2,z3,z4,z5,z12]),(0,[z1,z1318,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z903,z8])],[(0,[z1,z2,z53,z4,z5,z28]),(0,[z294,z2,z3,z67,z5,z8]),(0,[z1319,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1320])],[(1,[z2,z54,z196,z5,z8]),(0,[z1,z2,z3,z4,z1321,z5]),(0,[z1,z2,z3,z4,z147,z6]),(0,[z1,z2,z3,z4,z23,z8]),(0,[z1,z2,z3,z4,z5,z1322]),(0,[z1323,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z1324,z5,z8]),(0,[z1,z2,z20,z4,z5,z465]),(0,[z1,z2,z3,z32,z1321,z5]),(0,[z76,z2,z3,z4,z5,z224]),(0,[z17,z1,z3,z16,z5,z6]),(0,[z1,z2,z3,z4,z5,z225]),(0,[z235,z1,z2,z51,z5,z465])],[(0,[z134,z2,z54,z4,z5,z100]),(0,[z1,z648,z43,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1325]),(0,[z1,z2,z3,z4,z5,z1326]),(0,[z1,z2,z704,z4,z5,z28])],[(0,[z1,z3,z4,z5,z13,z811]),(0,[z1,z2,z3,z4,z149,z6]),(0,[z185,z78,z3,z4,z5,z8]),(0,[z1,z2,z3,z5,z8,z774])],[(0,[z1,z2,z1327,z4,z5,z8]),(0,[z63,z2,z3,z4,z30,z5]),(0,[z1,z2,z3,z4,z115,z5])],[(0,[z1,z2,z1328,z4,z5,z8]),(0,[z1,z58,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z117,z8]),(0,[z1,z2,z4,z5,z1329,z8]),(0,[z1,z2,z3,z4,z5,z1330]),(0,[z1,z2,z81,z50,z5,z12]),(0,[z1,z2,z1331,z4,z5,z8])],[(0,[z1,z2,z3,z4,z30,z147]),(0,[z1,z2,z324,z4,z25,z8]),(0,[z1332,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z105,z4,z5,z142]),(0,[z1333,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1334,z5]),(0,[z29,z1,z2,z3,z164,z28]),(0,[z1,z2,z146,z4,z5,z6]),(0,[z1,z2,z3,z4,z1335,z5]),(0,[z1,z2,z4,z463,z5,z236])],[(0,[z1,z270,z3,z4,z210,z8]),(0,[z76,z2,z3,z4,z5,z373]),(0,[z55,z1,z2,z4,z5,z236]),(0,[z1,z2,z43,z4,z377,z28]),(0,[z1,z431,z2,z3,z30,z5]),(0,[z1,z2,z81,z50,z5,z225]),(0,[z1,z2,z3,z4,z5,z1336]),(0,[z99,z2,z512,z4,z5,z8])],[(0,[z1,z2,z3,z4,z1337,z5]),(0,[z1,z2,z3,z1338,z4,z5]),(0,[z1,z2,z3,z4,z5,z1339]),(0,[z235,z63,z2,z51,z5,z8])],[(0,[z1,z2,z221,z4,z161,z8]),(0,[z1,z2,z3,z4,z1340,z8]),(0,[z1,z2,z3,z4,z1341,z5]),(0,[z1,z2,z3,z4,z5,z1081])],[(0,[z1,z2,z3,z4,z5,z1342]),(0,[z1,z2,z3,z780,z5,z8]),(0,[z1,z2,z1343,z4,z5,z8]),(0,[z1,z3,z825,z4,z5,z8]),(0,[z1,z2,z324,z4,z5,z144]),(0,[z1,z2,z3,z4,z1344,z8]),(0,[z1,z2,z512,z4,z5,z249]),(0,[z1,z2,z3,z4,z463,z228])],[(0,[z1,z2,z3,z4,z1233,z5]),(0,[z1,z2,z70,z67,z5,z8]),(0,[z34,z2,z3,z67,z5,z6]),(0,[z1,z152,z3,z4,z5,z130]),(0,[z1,z2,z1345,z4,z5,z8]),(0,[z185,z2,z3,z4,z5,z12]),(0,[z1,z2,z558,z4,z5,z1346]),(0,[z1,z2,z3,z30,z5,z12])],[(0,[z494,z2,z20,z4,z5,z8]),(0,[z1,z359,z3,z4,z5,z12])],[(0,[z1,z2,z3,z1347,z5,z8]),(0,[z1,z1348,z3,z4,z5,z8]),(0,[z1,z2,z1349,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1350]),(0,[z1,z125,z3,z453,z5,z8]),(1,[z1,z2,z4,z414,z28])],[(0,[z1,z2,z4,z5,z10,z28]),(0,[z1,z1351,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z144]),(0,[z1,z2,z3,z4,z5,z1352]),(0,[z1,z2,z4,z5,z11,z28])],[(0,[z1,z2,z53,z4,z293,z8]),(0,[z1,z2,z70,z4,z5,z8]),(0,[z1,z270,z221,z4,z5,z8])],[(0,[z1,z2,z70,z32,z5,z8]),(0,[z1,z139,z2,z242,z4,z5]),(0,[z1,z154,z825,z4,z5,z8]),(0,[z1353,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z1354,z5]),(0,[z1,z2,z111,z3,z4,z763])],[(0,[z1,z2,z3,z4,z120,z256]),(0,[z1,z2,z3,z251,z5,z8]),(0,[z1,z2,z3,z67,z5,z157]),(0,[z1355,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z23,z28]),(0,[z1,z2,z4,z25,z5,z236]),(0,[z1,z2,z1356,z4,z5,z12])],[(0,[z1,z2,z3,z4,z5,z1357]),(0,[z1,z2,z3,z4,z5,z1358]),(0,[z230,z2,z3,z4,z5,z12]),(0,[z1,z2,z184,z4,z71,z6]),(0,[z1,z2,z4,z5,z27,z28])],[(0,[z1,z153,z15,z4,z5,z449]),(0,[z1,z2,z3,z4,z1359,z8]),(0,[z1360,z2,z3,z4,z5,z8]),(1,[z1,z2,z4,z5,z794])],[(0,[z1,z1361,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1362]),(0,[z1,z2,z3,z4,z1363,z5]),(0,[z230,z2,z3,z4,z23,z8]),(0,[z1364,z2,z3,z4,z5,z8]),(0,[z1365,z2,z3,z4,z5,z8]),(0,[z1,z2,z183,z4,z5,z28]),(0,[z1,z2,z4,z5,z8,z782]),(0,[z1,z2,z608,z4,z5,z236])],[(0,[z1,z1366,z3,z4,z5,z8]),(0,[z2,z3,z4,z5,z903,z8]),(0,[z1367,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z157]),(0,[z1,z2,z1368,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1369]),(0,[z1,z2,z4,z5,z236,z1370])]],
   [[(0,[z227,z1,z3,z4,z197,z8]),(0,[z1,z2,z3,z4,z117,z28]),(0,[z1,z2,z4,z5,z236,z224]),(0,[z1,z2,z1371,z4,z5,z8]),(0,[z1,z2,z3,z4,z1372,z5])],[(0,[z1,z2,z3,z4,z1373,z8]),(0,[z1,z2,z37,z4,z5,z28]),(0,[z1,z2,z4,z5,z1374,z8])],[(0,[z1,z1375,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z161,z8]),(0,[z2,z3,z67,z73,z8,z164]),(0,[z17,z230,z3,z16,z5,z8]),(0,[z1,z2,z3,z4,z5,z1376])],[(0,[z1,z2,z40,z4,z5,z28]),(0,[z1,z2,z3,z215,z5,z8]),(0,[z76,z1,z2,z4,z5,z236]),(0,[z1,z2,z33,z4,z5,z794]),(0,[z1,z2,z3,z1377,z5,z8]),(0,[z1,z2,z690,z50,z5,z28]),(0,[z1,z2,z3,z4,z5,z263])],[(0,[z1,z270,z3,z67,z5,z8]),(0,[z1,z403,z77,z4,z5,z8]),(0,[z1,z2,z242,z4,z5,z12]),(0,[z1,z2,z4,z343,z5,z794]),(0,[z99,z2,z3,z5,z8,z164]),(0,[z185,z2,z558,z4,z5,z8])],[(0,[z1,z2,z3,z4,z1378,z8]),(0,[z1,z2,z3,z4,z377,z12]),(0,[z1379,z2,z3,z4,z5,z8]),(0,[z1,z2,z4,z5,z414,z28]),(1,[z1,z2,z4,z5,z236])],[(0,[z701,z1,z2,z4,z71,z8]),(0,[z1,z2,z3,z4,z1380,z8]),(0,[z1,z2,z4,z5,z56,z28]),(0,[z1,z66,z2,z3,z871,z5])],[(0,[z1,z2,z54,z4,z159,z8]),(0,[z1,z2,z242,z108,z5,z8]),(0,[z24,z1,z154,z4,z71,z8]),(0,[z1,z2,z324,z4,z30,z5])],[(0,[z1,z2,z53,z4,z5,z6]),(0,[z1,z270,z3,z4,z5,z8]),(0,[z319,z1,z3,z4,z197,z8]),(0,[z1,z2,z1381,z4,z5,z236])],[(0,[z1,z2,z3,z4,z5,z1382]),(0,[z1,z270,z3,z32,z5,z8]),(0,[z1,z58,z3,z4,z161,z8]),(0,[z2,z70,z4,z67,z5,z8]),(0,[z272,z2,z3,z32,z5,z8]),(0,[z1,z537,z2,z3,z30,z5]),(0,[z1,z2,z163,z4,z5,z6])],[(0,[z1,z270,z70,z4,z5,z8]),(0,[z1,z2,z3,z1383,z5,z8]),(0,[z1,z2,z242,z4,z5,z14]),(0,[z1,z2,z145,z4,z5,z8]),(0,[z1,z1384,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1385]),(0,[z1,z2,z512,z4,z5,z894])],[(0,[z1,z2,z3,z4,z1386,z8]),(0,[z1,z2,z70,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z1387]),(0,[z1,z2,z242,z4,z117,z8]),(0,[z1,z2,z33,z4,z5,z236]),(1,[z226,z2,z4,z5,z28])],[(0,[z1,z2,z1388,z4,z5,z8]),(0,[z134,z2,z54,z4,z497,z8]),(0,[z1,z2,z3,z4,z147,z28]),(0,[z1,z359,z3,z4,z149,z8]),(1,[z1,z283,z4,z5,z28]),(0,[z1,z432,z105,z4,z5,z28])],[(0,[z1,z2,z3,z251,z5,z28]),(0,[z34,z58,z3,z67,z5,z8]),(0,[z1,z1389,z3,z4,z5,z8]),(0,[z1,z2,z3,z1390,z5,z8]),(0,[z1,z1391,z3,z4,z5,z8]),(0,[z1,z2,z3,z690,z5,z12]),(0,[z1,z2,z398,z4,z94,z39])],[(0,[z119,z214,z3,z4,z5,z65]),(0,[z243,z2,z3,z4,z264,z8]),(0,[z1,z2,z3,z4,z742,z8]),(0,[z1,z2,z1392,z4,z5,z8])],[(0,[z1,z2,z262,z215,z5,z8]),(0,[z1,z2,z3,z4,z1393,z8]),(0,[z1,z2,z3,z4,z377,z128]),(0,[z1,z2,z184,z4,z377,z8]),(0,[z1,z2,z3,z4,z834,z8])]],
   [[(0,[z534,z1,z3,z16,z5,z8]),(0,[z1,z178,z54,z4,z5,z8]),(0,[z1,z2,z3,z4,z1394,z8])],[(0,[z1,z2,z1395,z4,z5,z8]),(0,[z1,z2,z3,z48,z5,z130]),(0,[z1,z2,z43,z4,z5,z236]),(0,[z1,z2,z3,z1396,z4,z5]),(0,[z1,z2,z1271,z4,z343,z5]),(0,[z1,z2,z50,z773,z5,z8])],[(0,[z1,z103,z3,z4,z316,z8]),(0,[z1,z58,z3,z4,z30,z5]),(0,[z1,z2,z3,z4,z5,z1397]),(0,[z95,z2,z3,z4,z59,z12]),(0,[z1,z153,z15,z4,z5,z142]),(0,[z1,z2,z3,z87,z4,z483]),(0,[z1,z2,z4,z86,z71,z28])],[(0,[z1,z121,z2,z3,z4,z5]),(0,[z1,z1398,z3,z4,z5,z8]),(0,[z1,z2,z184,z4,z71,z341]),(0,[z1,z2,z4,z5,z236,z1399])],[(0,[z1,z2,z221,z4,z210,z8]),(0,[z363,z2,z3,z67,z5,z8]),(0,[z1,z2,z3,z4,z161,z28])],[(0,[z1,z2,z3,z4,z1400,z5]),(0,[z1,z2,z3,z215,z5,z28]),(0,[z1,z403,z3,z108,z5,z8])],[(0,[z169,z2,z3,z4,z210,z8]),(0,[z1,z2,z15,z4,z5,z177]),(0,[z1,z2,z3,z4,z5,z1401]),(0,[z1,z2,z87,z4,z5,z140])],[(0,[z1,z2,z3,z247,z5,z8]),(0,[z1,z3,z4,z5,z8,z1402])],[(0,[z1,z2,z3,z4,z5,z1403]),(0,[z1,z2,z3,z196,z5,z8]),(0,[z134,z135,z54,z4,z5,z8]),(0,[z1,z2,z150,z4,z5,z28]),(0,[z1,z403,z3,z4,z5,z14]),(0,[z1404,z2,z3,z4,z5,z8]),(0,[z1,z604,z2,z3,z30,z5]),(0,[z1,z2,z4,z30,z5,z1405])],[(0,[z1,z2,z3,z4,z1406,z8]),(0,[z1,z2,z3,z1407,z5,z8]),(0,[z692,z2,z3,z4,z5,z14]),(0,[z1,z2,z3,z4,z5,z1408]),(0,[z1,z103,z3,z4,z742,z8]),(0,[z1,z2,z4,z30,z5,z309]),(0,[z1,z2,z3,z4,z5,z1409]),(0,[z1,z2,z279,z3,z87,z4]),(0,[z185,z2,z3,z4,z30,z5]),(0,[z1,z2,z3,z1410,z5,z8])],[(0,[z1,z2,z3,z4,z293,z8]),(0,[z1,z270,z3,z4,z5,z28]),(0,[z1,z359,z3,z4,z30,z5])],[(0,[z119,z214,z3,z4,z5,z12]),(0,[z427,z2,z3,z67,z5,z8]),(0,[z113,z2,z20,z4,z5,z8]),(0,[z1,z152,z3,z48,z5,z8]),(0,[z47,z2,z3,z4,z903,z8]),(0,[z1,z2,z3,z4,z23,z6]),(0,[z1,z2,z4,z5,z177,z71]),(0,[z1,z2,z163,z4,z5,z782]),(0,[z1,z1411,z3,z4,z5,z8])],[(0,[z63,z2,z3,z4,z5,z8]),(0,[z374,z2,z3,z4,z73,z8]),(0,[z1,z2,z43,z4,z5,z142]),(0,[z1,z2,z145,z4,z5,z28])],[(0,[z1,z2,z3,z4,z1412,z8]),(0,[z517,z2,z3,z4,z59,z8]),(0,[z1,z2,z77,z4,z42,z8]),(0,[z1,z2,z3,z4,z5,z1413]),(0,[z1,z2,z4,z5,z6,z28])],[(0,[z1,z2,z3,z4,z1414,z8]),(0,[z1,z2,z3,z4,z5,z1415]),(0,[z1,z2,z4,z118,z5,z28]),(0,[z1,z2,z105,z4,z5,z177]),(0,[z1,z441,z3,z4,z5,z438])],[(0,[z1,z2,z3,z4,z5,z1416]),(0,[z1,z214,z3,z247,z5,z8]),(0,[z1,z2,z1417,z3,z4,z5]),(0,[z1,z2,z3,z4,z1418,z5]),(0,[z1,z2,z3,z4,z1419,z8])]],
   [[(0,[z1,z2,z3,z4,z1420,z5]),(0,[z1,z2,z3,z4,z1421,z5]),(0,[z85,z2,z20,z4,z5,z8]),(0,[z1,z152,z3,z4,z5,z202]),(0,[z1,z2,z3,z562,z5,z224]),(0,[z1,z2,z3,z4,z117,z6]),(0,[z1,z2,z15,z4,z5,z236]),(0,[z235,z1,z525,z51,z5,z8]),(1,[z1,z2,z50,z5,z177])],[(0,[z1,z2,z3,z4,z5,z1422]),(0,[z1,z1423,z3,z4,z5,z8]),(0,[z1,z15,z4,z5,z507,z28])],[(0,[z1,z214,z3,z4,z293,z8]),(0,[z1,z2,z3,z4,z1424,z8]),(0,[z1,z2,z3,z4,z5,z1425]),(0,[z113,z2,z20,z4,z5,z21]),(0,[z76,z491,z2,z3,z4,z5]),(0,[z1,z2,z4,z5,z1266,z28]),(0,[z559,z2,z3,z4,z5,z550]),(0,[z1,z2,z3,z4,z30,z1242])],[(0,[z1,z2,z3,z4,z210,z8]),(0,[z1,z273,z512,z4,z5,z8]),(0,[z1,z1426,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z1427]),(0,[z1,z2,z3,z4,z5,z1428]),(0,[z1,z2,z379,z4,z5,z384]),(0,[z1,z206,z2,z4,z5,z28])],[(0,[z1,z2,z3,z4,z5,z1429]),(0,[z17,z1,z350,z16,z5,z8]),(0,[z1,z1430,z3,z4,z5,z8]),(0,[z1,z2,z3,z608,z5,z429])],[(0,[z1,z2,z1431,z4,z5,z8]),(0,[z1,z2,z3,z1432,z5,z8]),(0,[z1,z2,z3,z251,z5,z401])],[(0,[z1,z2,z3,z4,z1433,z8]),(0,[z1,z2,z3,z4,z1434,z8]),(0,[z1,z2,z269,z4,z59,z8]),(0,[z1,z2,z4,z330,z5,z769]),(0,[z55,z2,z3,z4,z5,z361]),(0,[z1,z2,z3,z4,z5,z1435]),(0,[z1,z634,z43,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1436]),(0,[z1,z2,z339,z4,z5,z28]),(0,[z1,z283,z3,z4,z5,z502]),(0,[z1,z2,z3,z4,z5,z1437])],[(0,[z1,z2,z3,z4,z5,z1438]),(0,[z1,z2,z242,z4,z30,z5]),(0,[z1,z2,z3,z4,z5,z1439]),(0,[z1,z2,z105,z4,z5,z236])],[(0,[z1,z2,z3,z247,z5,z28]),(0,[z1,z2,z50,z67,z5,z28]),(0,[z1,z2,z3,z108,z439,z5]),(0,[z1,z359,z163,z4,z5,z8]),(0,[z1,z2,z3,z4,z871,z5])],[(0,[z1,z2,z3,z196,z5,z28]),(0,[z113,z2,z351,z4,z5,z8]),(0,[z1,z58,z3,z4,z210,z8]),(0,[z169,z2,z3,z780,z5,z8]),(0,[z1,z637,z3,z4,z72,z8]),(0,[z1,z660,z43,z4,z5,z8]),(0,[z1,z2,z996,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z1440]),(0,[z1,z1441,z2,z3,z4,z5])],[(0,[z1,z2,z3,z1442,z5,z8]),(0,[z345,z214,z3,z4,z5,z8]),(0,[z1,z2,z214,z764,z4,z5]),(0,[z1,z2,z221,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1443]),(0,[z1,z2,z20,z4,z5,z128]),(0,[z1,z2,z70,z4,z5,z6]),(0,[z1,z2,z15,z4,z5,z142]),(0,[z1,z359,z81,z4,z5,z8]),(0,[z1,z2,z3,z388,z5,z12])],[(0,[z1,z2,z3,z4,z1444,z5]),(0,[z1,z2,z3,z4,z293,z28]),(0,[z1,z2,z242,z4,z94,z5])],[(0,[z1,z2,z3,z251,z5,z6]),(0,[z1,z2,z3,z4,z1445,z5]),(0,[z1,z2,z3,z4,z1446,z5]),(0,[z1,z3,z15,z4,z147,z8]),(0,[z1,z2,z50,z4,z5,z28])],[(0,[z169,z2,z3,z32,z5,z8]),(0,[z1,z452,z3,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z1027]),(0,[z1,z2,z3,z108,z42,z8]),(0,[z63,z2,z3,z4,z5,z28]),(0,[z1,z273,z3,z4,z5,z331])],[(0,[z169,z2,z70,z4,z5,z8]),(0,[z17,z243,z3,z16,z5,z8]),(0,[z1,z103,z2,z4,z309,z8]),(0,[z1,z2,z4,z773,z5,z8]),(0,[z1,z2,z1269,z4,z496,z5]),(0,[z1,z2,z4,z5,z857,z8])]],
   [[(0,[z1,z2,z53,z4,z5,z1447]),(0,[z1,z464,z15,z4,z5,z8]),(0,[z1,z2,z3,z4,z1448,z5]),(0,[z1,z3,z4,z860,z5,z8]),(0,[z1,z2,z3,z773,z5,z8]),(0,[z1,z2,z3,z4,z575,z39])],[(0,[z369,z2,z3,z4,z5,z224]),(0,[z1,z1366,z3,z4,z5,z6]),(0,[z1,z555,z3,z4,z5,z286]),(0,[z1,z2,z800,z4,z5,z12])],[(0,[z1449,z2,z3,z4,z5,z8])],[(0,[z1,z2,z1450,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1451]),(0,[z1,z2,z3,z354,z5,z12]),(0,[z1,z2,z3,z4,z5,z1452])],[(0,[z1,z2,z132,z4,z120,z8]),(0,[z1,z2,z4,z5,z928,z28]),(0,[z1,z2,z3,z4,z161,z6]),(0,[z1,z3,z4,z5,z742,z8]),(0,[z1,z2,z368,z4,z5,z162]),(0,[z1,z2,z3,z4,z5,z1453])],[(0,[z1,z2,z3,z4,z1454,z8]),(0,[z1,z2,z3,z4,z5,z1455]),(0,[z1,z2,z3,z4,z210,z28]),(0,[z1,z2,z3,z4,z1309,z8]),(0,[z1,z2,z269,z4,z5,z868]),(0,[z1,z2,z3,z215,z5,z6]),(0,[z1,z2,z350,z4,z30,z5])],[(0,[z1,z2,z3,z4,z1456,z8]),(0,[z47,z2,z3,z4,z73,z130]),(0,[z1,z403,z3,z4,z30,z5]),(0,[z1,z2,z3,z30,z5,z605]),(0,[z1,z2,z324,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1457]),(0,[z1,z46,z3,z4,z110,z5])],[(0,[z1,z2,z3,z1321,z5,z12]),(0,[z1,z2,z1458,z4,z5,z8]),(0,[z1,z487,z15,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1459]),(0,[z1,z2,z200,z4,z25,z8]),(0,[z230,z2,z3,z4,z5,z170]),(0,[z1,z125,z350,z4,z5,z8]),(0,[z235,z1,z2,z51,z149,z8]),(0,[z1,z1430,z3,z4,z5,z28]),(0,[z1,z2,z3,z30,z871,z5])],[(0,[z1,z2,z3,z4,z5,z1460]),(0,[z2,z20,z970,z4,z5,z8]),(0,[z1,z2,z1461,z4,z5,z8]),(0,[z1,z2,z3,z591,z5,z12]),(0,[z1,z2,z163,z4,z377,z8]),(0,[z99,z78,z3,z4,z5,z8])],[(0,[z1,z2,z3,z1462,z5,z8]),(0,[z1,z366,z3,z4,z42,z8]),(0,[z17,z1,z3,z16,z5,z384]),(0,[z1,z2,z4,z5,z309,z12]),(0,[z1,z2,z213,z4,z5,z857]),(0,[z1,z52,z2,z567,z3,z4])],[(0,[z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z247,z293,z8]),(0,[z1,z2,z3,z501,z30,z5]),(0,[z119,z1018,z3,z4,z5,z8]),(0,[z1,z270,z3,z4,z5,z6]),(0,[z1,z403,z3,z4,z94,z5]),(0,[z1,z2,z4,z5,z71,z142]),(0,[z1,z2,z81,z4,z377,z8]),(0,[z1,z104,z4,z72,z5,z8]),(0,[z1,z2,z4,z5,z385,z28])],[],[(0,[z1,z2,z182,z4,z5,z28]),(0,[z1,z2,z3,z48,z5,z202]),(0,[z1,z2,z3,z4,z1463,z8]),(0,[z1,z2,z145,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1464]),(0,[z1,z2,z3,z4,z149,z11]),(0,[z1,z2,z3,z4,z5,z1465])],[(0,[z1,z2,z20,z4,z5,z166]),(0,[z1,z2,z221,z4,z5,z28]),(0,[z1,z2,z4,z5,z376,z465]),(0,[z1,z604,z2,z3,z115,z5])],[(0,[z169,z270,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1466,z5]),(0,[z235,z1,z359,z51,z5,z8]),(0,[z1,z2,z3,z4,z261,z39])],[(0,[z119,z214,z3,z4,z30,z5]),(0,[z1,z2,z3,z4,z5,z1467]),(0,[z1,z2,z1468,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1469]),(0,[z1,z2,z70,z4,z5,z1470]),(0,[z1,z2,z3,z4,z1471,z8]),(0,[z1,z1472,z3,z4,z5,z8]),(0,[z1,z2,z1473,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1474]),(0,[z1,z2,z4,z414,z8,z28]),(0,[z99,z2,z3,z4,z5,z331])]],
   [[(0,[z560,z2,z54,z4,z5,z8]),(0,[z169,z2,z3,z32,z5,z28]),(0,[z47,z152,z3,z4,z73,z8]),(0,[z1,z2,z146,z4,z5,z11])],[(0,[z1,z58,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z21]),(0,[z1,z2,z1475,z3,z4,z5]),(0,[z1,z1476,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1477]),(0,[z1,z2,z3,z1478,z5,z8]),(0,[z1,z2,z81,z50,z5,z8]),(0,[z1,z2,z184,z4,z5,z236])],[(0,[z1,z2,z269,z4,z5,z130]),(0,[z1,z2,z3,z4,z5,z1479]),(0,[z1,z585,z43,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1480]),(0,[z1,z2,z3,z4,z5,z1005]),(0,[z1,z2,z3,z4,z459,z258])],[(0,[z1,z2,z132,z4,z5,z256]),(0,[z1,z2,z3,z196,z5,z401]),(0,[z1,z58,z70,z4,z5,z8]),(0,[z1,z2,z3,z4,z1481,z5]),(0,[z1,z2,z3,z4,z5,z1482]),(0,[z1,z1483,z3,z4,z5,z8])],[(0,[z1,z200,z3,z4,z72,z8]),(0,[z1,z2,z3,z4,z377,z89]),(0,[z1,z2,z3,z4,z1484,z5]),(0,[z1,z2,z3,z4,z1485,z8])],[(0,[z1,z2,z3,z4,z73,z130]),(0,[z1,z2,z3,z4,z5,z1486]),(0,[z1,z103,z3,z4,z72,z193]),(0,[z1,z555,z3,z4,z5,z13]),(0,[z235,z1,z2,z51,z30,z5]),(0,[z1,z2,z4,z5,z1226,z8])],[(0,[z1,z2,z53,z4,z5,z728]),(0,[z1,z2,z262,z4,z5,z8]),(0,[z248,z2,z54,z4,z5,z8]),(0,[z1,z2,z3,z4,z149,z96])],[(0,[z1,z2,z3,z4,z5,z1487]),(0,[z1,z2,z3,z4,z5,z1488]),(0,[z1,z1489,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1490]),(0,[z1,z760,z3,z4,z30,z5])],[(0,[z1,z2,z53,z501,z5,z8]),(0,[z1,z2,z324,z4,z5,z28]),(0,[z1,z2,z3,z4,z1491,z5])],[(0,[z1,z2,z3,z247,z5,z6]),(0,[z1,z359,z3,z4,z5,z8]),(0,[z1,z2,z145,z325,z4,z5]),(0,[z1,z1492,z3,z4,z5,z8])],[(0,[z1,z2,z3,z196,z5,z6]),(0,[z1,z452,z3,z215,z5,z8]),(0,[z76,z2,z242,z4,z5,z224]),(0,[z1,z2,z3,z4,z5,z1493]),(0,[z1,z2,z43,z4,z5,z177]),(0,[z1,z2,z163,z4,z414,z8])],[(0,[z0,z1,z2,z4,z5,z236]),(0,[z1,z2,z3,z1494,z5,z8])],[(0,[z1,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z501,z5,z65]),(0,[z1,z2,z3,z4,z293,z6]),(0,[z2,z3,z970,z4,z5,z8]),(0,[z1,z152,z269,z4,z5,z8]),(0,[z2,z3,z215,z5,z73,z8]),(0,[z1,z2,z3,z4,z5,z1495]),(0,[z1496,z2,z3,z4,z5,z8]),(0,[z1,z2,z350,z4,z5,z170]),(0,[z1,z2,z81,z4,z414,z8]),(0,[z1,z432,z3,z4,z5,z12]),(0,[z1,z2,z4,z5,z236,z465])],[(0,[z119,z214,z53,z4,z5,z8]),(0,[z1,z2,z3,z4,z1497,z5]),(0,[z113,z2,z20,z4,z5,z6]),(0,[z563,z1,z2,z3,z8,z164]),(0,[z1,z2,z4,z5,z190,z28]),(0,[z1,z783,z3,z4,z30,z5])],[(0,[z1,z2,z3,z4,z5,z1498]),(0,[z63,z2,z3,z4,z5,z6]),(0,[z1,z2,z1356,z4,z5,z8])],[(0,[z230,z2,z3,z4,z5,z8]),(0,[z1,z2,z4,z5,z6,z782]),(0,[z1,z2,z3,z4,z1412,z6]),(0,[z29,z185,z2,z3,z8,z164])]],
   [[(0,[z1,z2,z3,z4,z5,z1499]),(0,[z1,z2,z611,z50,z5,z8]),(0,[z1,z154,z43,z4,z5,z89]),(0,[z1500,z2,z3,z4,z5,z8]),(0,[z1,z2,z105,z4,z467,z8]),(0,[z99,z2,z558,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1273])],[(0,[z1,z2,z3,z4,z5,z1501]),(0,[z1,z2,z3,z4,z5,z1502]),(0,[z1,z104,z4,z16,z5,z8]),(0,[z1,z2,z3,z51,z5,z177]),(0,[z1,z2,z146,z4,z5,z236])],[(0,[z1,z2,z831,z4,z5,z8]),(0,[z1,z452,z3,z4,z30,z5]),(0,[z1,z2,z1503,z4,z5,z8]),(0,[z1,z52,z2,z4,z5,z236])],[(0,[z1,z2,z3,z4,z1504,z8]),(0,[z1,z139,z2,z4,z5,z236]),(0,[z1,z2,z81,z50,z5,z28]),(0,[z1,z2,z558,z4,z5,z249])],[(0,[z1,z2,z3,z4,z497,z12]),(0,[z1,z1505,z3,z4,z5,z8]),(0,[z1,z154,z43,z4,z5,z12]),(0,[z1,z2,z350,z4,z5,z12]),(0,[z1,z2,z3,z4,z5,z1506])],[(0,[z1,z2,z3,z4,z210,z6]),(0,[z1,z403,z3,z4,z5,z12]),(0,[z29,z1,z78,z3,z8,z164])],[(0,[z1,z1507,z3,z4,z5,z8]),(0,[z1,z283,z54,z4,z5,z8]),(0,[z1,z2,z350,z4,z23,z8]),(0,[z1508,z2,z3,z4,z5,z8]),(0,[z1,z2,z1509,z4,z5,z8])],[(0,[z508,z2,z3,z4,z59,z8]),(0,[z1510,z2,z3,z4,z5,z8]),(0,[z1511,z2,z3,z4,z5,z8])],[(0,[z1,z2,z132,z4,z5,z1017]),(0,[z1,z378,z2,z4,z5,z28]),(0,[z1,z2,z262,z4,z5,z28]),(0,[z76,z403,z3,z4,z5,z224]),(0,[z1,z2,z375,z4,z5,z12]),(0,[z1,z1512,z3,z4,z5,z8]),(0,[z1,z432,z3,z4,z25,z8])],[(0,[z1,z2,z3,z501,z5,z12]),(0,[z1,z2,z3,z4,z5,z1513]),(0,[z1,z2,z269,z4,z73,z8]),(0,[z1,z2,z3,z4,z5,z1514]),(0,[z1,z2,z98,z4,z5,z28]),(0,[z1,z2,z163,z4,z5,z11])],[(0,[z1,z2,z3,z1515,z5,z8]),(0,[z1,z2,z1516,z4,z5,z8]),(0,[z1,z103,z104,z4,z72,z8]),(0,[z1,z2,z3,z4,z414,z12]),(0,[z1,z656,z2,z3,z30,z5])],[(0,[z113,z1,z2,z4,z5,z236]),(0,[z1,z2,z105,z4,z584,z8]),(0,[z1,z2,z324,z4,z5,z1517])],[(0,[z1,z2,z3,z4,z1518,z8]),(0,[z1,z2,z3,z4,z1519,z5]),(0,[z47,z2,z3,z48,z73,z8]),(0,[z1,z403,z3,z4,z117,z8]),(0,[z1,z2,z3,z4,z1520,z8]),(0,[z1,z2,z3,z4,z5,z1521]),(0,[z1522,z2,z3,z4,z5,z8]),(0,[z1,z359,z4,z51,z5,z8]),(0,[z235,z1,z2,z4,z5,z465]),(0,[z1,z2,z4,z239,z5,z236]),(0,[z1,z46,z2,z4,z5,z236])],[(0,[z1,z2,z221,z4,z5,z6]),(0,[z1,z1523,z3,z4,z5,z8]),(0,[z1,z2,z3,z93,z5,z12]),(0,[z1,z2,z900,z4,z5,z12]),(0,[z1,z2,z4,z30,z5,z973]),(0,[z1,z2,z1524,z4,z5,z8])],[(0,[z1,z154,z43,z4,z5,z128]),(0,[z1,z2,z327,z4,z5,z28])],[(0,[z1,z2,z3,z4,z1525,z8]),(0,[z1,z154,z2,z4,z377,z8]),(0,[z1,z2,z3,z4,z5,z1517]),(0,[z1,z628,z3,z4,z72,z8]),(0,[z1,z2,z282,z4,z71,z8])]],
   [[(0,[z1,z135,z3,z4,z5,z12]),(0,[z169,z2,z3,z32,z5,z6]),(0,[z1,z2,z503,z3,z4,z548])],[(0,[z1,z2,z1526,z4,z5,z8]),(0,[z55,z2,z3,z4,z5,z14]),(0,[z1,z139,z2,z3,z562,z5]),(0,[z230,z2,z3,z4,z5,z28]),(0,[z24,z1,z3,z4,z197,z12]),(0,[z1,z2,z4,z596,z5,z236])],[(0,[z1,z2,z3,z4,z5,z1527]),(0,[z1,z288,z2,z4,z5,z28]),(0,[z29,z1,z2,z3,z8,z164])],[(0,[z1,z2,z3,z1528,z5,z8]),(0,[z1,z2,z3,z4,z5,z1529]),(0,[z477,z2,z3,z4,z5,z361]),(0,[z1,z2,z3,z4,z5,z1530])],[(0,[z1,z642,z15,z4,z5,z8]),(0,[z235,z1,z2,z51,z5,z12]),(0,[z1,z2,z4,z5,z955,z28])],[(0,[z1,z2,z3,z4,z5,z401]),(0,[z1,z1531,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1532]),(0,[z55,z1,z2,z368,z4,z5]),(0,[z1,z2,z3,z4,z1394,z28]),(0,[z99,z2,z3,z4,z30,z5])],[(0,[z134,z2,z54,z4,z159,z8]),(0,[z1,z139,z364,z3,z4,z5])],[(0,[z1,z1533,z2,z3,z4,z5]),(0,[z1,z154,z43,z4,z147,z8]),(0,[z1,z2,z4,z5,z140,z162]),(0,[z1,z525,z3,z4,z5,z12]),(0,[z1534,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z251,z497,z8]),(0,[z1,z2,z269,z48,z5,z8]),(0,[z243,z2,z3,z33,z5,z8]),(1,[z1,z3,z4,z742,z8]),(0,[z1,z2,z324,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1535]),(0,[z1,z2,z4,z5,z1536,z236])],[],[(0,[z1,z1537,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z23,z384]),(0,[z235,z1,z2,z51,z115,z5]),(0,[z1,z2,z3,z4,z5,z1538]),(0,[z1,z2,z163,z4,z5,z236])],[(0,[z1,z2,z1539,z4,z5,z8]),(0,[z1,z2,z111,z3,z665,z4]),(0,[z1,z2,z4,z51,z377,z8])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1540])],[(0,[z169,z2,z3,z292,z5,z8]),(0,[z169,z2,z3,z32,z439,z5]),(0,[z1,z787,z3,z4,z5,z12])],[(0,[z1,z2,z252,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z1541]),(0,[z1,z1542,z3,z4,z5,z8]),(0,[z1,z366,z3,z562,z5,z8]),(0,[z1,z2,z3,z4,z42,z12]),(0,[z63,z359,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1520,z28])],[(0,[z1,z2,z1543,z4,z5,z8]),(0,[z1,z2,z349,z4,z5,z28]),(0,[z134,z178,z54,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1544]),(0,[z24,z1,z3,z4,z314,z8])]],
   [[(0,[z2,z3,z67,z5,z210,z8]),(0,[z1,z2,z3,z4,z1545,z8]),(0,[z1,z2,z3,z4,z1546,z8]),(0,[z1,z2,z3,z4,z5,z1547]),(0,[z1,z1548,z3,z4,z5,z8]),(0,[z1,z432,z3,z4,z30,z5])],[(0,[z705,z1,z3,z4,z197,z8]),(0,[z1,z2,z3,z4,z5,z1549]),(0,[z1,z2,z3,z4,z5,z1550]),(0,[z1,z2,z3,z4,z1551,z5]),(0,[z1,z2,z184,z4,z30,z71]),(0,[z1,z2,z3,z471,z5,z12])],[(0,[z1,z2,z105,z4,z5,z955])],[(0,[z1,z2,z54,z4,z5,z465]),(0,[z1,z58,z3,z4,z5,z6]),(0,[z1,z2,z70,z4,z5,z1550]),(0,[z1,z2,z1552,z4,z5,z8]),(0,[z1,z2,z3,z4,z1553,z5]),(0,[z1,z2,z259,z4,z5,z28]),(0,[z1,z2,z81,z50,z5,z6]),(0,[z1,z2,z873,z4,z30,z5])],[(0,[z1,z2,z3,z4,z5,z1554]),(0,[z1,z2,z3,z4,z5,z858]),(0,[z24,z1,z3,z4,z610,z8]),(0,[z1,z2,z4,z115,z5,z236]),(0,[z1,z2,z3,z4,z5,z1555])],[(0,[z1,z58,z221,z4,z5,z8]),(0,[z2,z3,z67,z5,z550,z12]),(0,[z1,z2,z3,z4,z5,z1556]),(0,[z1,z2,z3,z290,z5,z12]),(0,[z1,z2,z3,z4,z1557,z8])],[(0,[z235,z63,z2,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z1558]),(0,[z1,z2,z4,z834,z5,z8]),(0,[z1,z2,z3,z204,z5,z429])],[(0,[z1,z727,z3,z4,z5,z8]),(0,[z76,z1,z2,z368,z4,z5]),(0,[z1,z2,z4,z86,z5,z236])],[(0,[z1,z2,z262,z4,z5,z6]),(0,[z1,z154,z43,z4,z30,z5]),(0,[z1,z2,z3,z4,z1559,z5]),(0,[z1,z2,z105,z4,z30,z25]),(0,[z1,z2,z268,z4,z5,z28])],[(0,[z214,z3,z4,z247,z5,z8]),(0,[z1,z2,z1560,z4,z5,z8]),(0,[z1,z2,z3,z325,z4,z5]),(0,[z1,z139,z3,z4,z5,z507]),(0,[z1,z2,z3,z4,z459,z39]),(0,[z1,z2,z512,z4,z5,z331])],[(0,[z1,z2,z3,z1561,z5,z8]),(0,[z1,z2,z1562,z4,z5,z8])],[(0,[z1,z359,z3,z4,z5,z6]),(0,[z1,z2,z732,z4,z30,z5])],[(0,[z1,z2,z375,z4,z30,z5]),(0,[z1,z2,z3,z4,z5,z1346])],[(0,[z1,z1563,z2,z3,z4,z5]),(0,[z1,z1564,z3,z4,z5,z8]),(0,[z638,z1,z2,z3,z8,z164]),(0,[z1,z525,z3,z4,z149,z8]),(0,[z1,z1565,z3,z4,z5,z8]),(0,[z1,z2,z4,z51,z414,z8])],[(0,[z1,z2,z3,z4,z1566,z8]),(0,[z1567,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1568]),(0,[z1,z283,z4,z25,z5,z8]),(0,[z1,z2,z3,z4,z5,z782]),(0,[z1,z78,z3,z4,z5,z249]),(0,[z1,z2,z1569,z4,z5,z8])],[(0,[z1,z2,z3,z515,z5,z12])]],
   [[(0,[z1,z2,z81,z182,z5,z8]),(0,[z1,z2,z20,z4,z5,z263]),(0,[z1,z2,z3,z4,z5,z1470]),(0,[z1,z1570,z2,z3,z4,z5]),(0,[z1,z2,z278,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z1571]),(0,[z1,z2,z3,z4,z5,z1572])],[(0,[z1,z2,z3,z4,z5,z1573]),(0,[z1,z452,z3,z4,z5,z8]),(0,[z1,z2,z3,z1574,z4,z5]),(0,[z1,z2,z3,z4,z5,z1266]),(0,[z1,z2,z3,z4,z5,z1575]),(0,[z230,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z1576,z8])],[(0,[z1,z273,z558,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z341]),(0,[z1,z2,z3,z4,z420,z190]),(0,[z1,z2,z4,z5,z236,z12])],[(0,[z1,z2,z3,z4,z5,z904]),(0,[z1,z135,z3,z4,z30,z5]),(0,[z238,z2,z3,z67,z5,z8]),(0,[z1,z2,z4,z5,z8,z1577]),(0,[z1,z2,z3,z4,z343,z5]),(0,[z1578,z2,z3,z4,z5,z8]),(0,[z1,z2,z145,z4,z5,z754]),(0,[z1,z1579,z3,z4,z5,z8]),(0,[z99,z2,z3,z4,z5,z12])],[(0,[z1,z2,z3,z196,z497,z8]),(0,[z220,z2,z3,z67,z5,z8]),(0,[z1,z2,z687,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z100]),(0,[z1,z154,z283,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1580]),(0,[z1,z2,z841,z4,z5,z12])],[(0,[z1,z631,z15,z4,z5,z8]),(0,[z1,z2,z4,z5,z286,z28]),(0,[z1,z2,z3,z4,z5,z1581])],[(1,[z2,z970,z4,z5,z8]),(0,[z1,z2,z3,z439,z5,z12]),(0,[z1,z1582,z2,z3,z4,z5]),(0,[z1,z2,z379,z4,z264,z8]),(0,[z1,z2,z4,z71,z164,z28])],[(0,[z1,z2,z1583,z4,z5,z8]),(0,[z1,z2,z4,z5,z236,z14]),(0,[z1,z2,z1584,z4,z5,z8]),(0,[z1,z2,z3,z527,z5,z12])],[(0,[z1,z2,z3,z251,z5,z100]),(0,[z653,z2,z20,z4,z5,z8])],[(0,[z1,z395,z3,z4,z5,z162]),(0,[z185,z2,z3,z4,z5,z8]),(0,[z1,z525,z3,z4,z30,z5]),(0,[z1,z2,z3,z4,z1585,z5]),(0,[z1,z2,z231,z4,z5,z28])],[(0,[z1,z2,z3,z1586,z5,z8]),(0,[z1,z2,z1587,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1588]),(0,[z1,z2,z4,z5,z309,z8]),(0,[z1589,z2,z3,z4,z5,z8]),(0,[z1,z1590,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z1591,z8]),(0,[z1,z2,z3,z4,z5,z928]),(0,[z1,z2,z4,z5,z21,z28]),(0,[z1,z452,z262,z4,z5,z8]),(0,[z47,z2,z269,z4,z73,z8]),(0,[z1,z2,z1592,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1593]),(0,[z1594,z2,z3,z4,z5,z8]),(0,[z1,z2,z4,z72,z5,z236]),(0,[z1,z155,z2,z4,z5,z28]),(1,[z1,z2,z4,z5,z857])],[(0,[z119,z214,z3,z247,z5,z8]),(0,[z1,z2,z3,z562,z596,z5])],[(0,[z1,z2,z3,z4,z1595,z5]),(0,[z1,z2,z3,z215,z5,z797]),(0,[z1,z2,z3,z4,z1596,z8]),(0,[z63,z2,z3,z4,z414,z8])]],
   [[(0,[z119,z121,z214,z3,z4,z5]),(0,[z1,z2,z781,z4,z30,z5])],[(0,[z119,z214,z3,z4,z293,z8]),(0,[z169,z2,z3,z32,z5,z381]),(0,[z1,z2,z3,z4,z5,z709]),(0,[z1,z125,z3,z127,z5,z8]),(0,[z1,z154,z2,z4,z5,z236])],[(0,[z1,z2,z3,z251,z5,z823]),(0,[z24,z1,z15,z4,z25,z8]),(0,[z243,z2,z379,z4,z5,z8]),(0,[z1,z2,z379,z4,z5,z988])],[(0,[z1018,z214,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1597]),(0,[z1,z452,z3,z4,z5,z28]),(0,[z243,z2,z3,z4,z5,z12]),(0,[z1,z1598,z3,z4,z5,z8]),(0,[z1,z2,z87,z4,z5,z236])],[(0,[z1,z2,z3,z4,z5,z1447]),(0,[z1,z2,z3,z4,z5,z1599])],[(0,[z1,z2,z20,z196,z5,z8]),(0,[z1,z2,z77,z562,z5,z8]),(0,[z1,z3,z4,z742,z197,z8]),(0,[z1,z2,z324,z4,z71,z8]),(0,[z1,z2,z3,z4,z1600,z5])],[(0,[z1,z2,z3,z4,z5,z1601]),(0,[z1,z58,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z1602]),(0,[z1,z2,z1603,z4,z5,z8])],[(0,[z1,z125,z3,z696,z5,z8]),(0,[z1,z2,z324,z4,z377,z8]),(0,[z1,z2,z375,z4,z5,z89]),(0,[z614,z1,z3,z4,z197,z8]),(0,[z538,z1,z2,z4,z5,z28]),(0,[z1,z273,z3,z4,z30,z5])],[(0,[z1,z2,z3,z4,z5,z1604]),(0,[z1,z103,z3,z4,z72,z12]),(0,[z1,z2,z3,z664,z5,z12]),(0,[z299,z1,z2,z4,z5,z236])],[(0,[z599,z1,z2,z51,z5,z8]),(0,[z1,z66,z2,z3,z439,z5]),(0,[z1,z2,z4,z5,z305,z28])],[(0,[z1,z2,z242,z4,z5,z8])],[(0,[z1,z2,z3,z4,z377,z8]),(0,[z1,z103,z3,z4,z30,z72])],[(0,[z1,z2,z3,z1605,z5,z8]),(0,[z1,z2,z3,z1606,z4,z5]),(0,[z1,z114,z368,z4,z5,z162])],[(0,[z1,z2,z3,z4,z5,z381]),(0,[z1,z145,z283,z4,z5,z8]),(0,[z1,z2,z4,z51,z5,z236]),(0,[z1,z1607,z3,z4,z5,z8]),(0,[z185,z2,z3,z4,z5,z28]),(0,[z1,z2,z4,z5,z1405,z8])],[(0,[z1,z2,z3,z501,z1444,z5]),(0,[z1,z2,z3,z4,z5,z1608]),(0,[z1,z2,z4,z5,z309,z28]),(0,[z226,z2,z3,z4,z149,z8]),(0,[z63,z2,z3,z4,z5,z11]),(0,[z1,z359,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z1609,z8])],[(0,[z1,z2,z3,z4,z1610,z5]),(0,[z1,z2,z817,z4,z30,z5])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 16 512 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 472) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 472).take 475) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 947).take 471) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1418).take 127) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1545)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [472, 475, 471, 127] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 67).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 67).take 74).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 141).take 74).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 215).take 69).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 284).take 71).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 355).take 71).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc6 : chunkOK 5 ((bkB.flatten.drop 426).take 86).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [67, 74, 74, 69, 71, 71, 86] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_cons pc6 (windowsF_nil pcend)))))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 16) (nb1 := 512) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_38041

theorem PEqualNP.Outside.L_meta_38041 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277071592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277071592) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38041.solve