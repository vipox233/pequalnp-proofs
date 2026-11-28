import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40347

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
  Nat.testBit (4276809440 * 2 ^ 32 + 4209565920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0001661c4162e316#64 ++ 0x40001661c4162e31#64 ++ 0xb027ee3cc3e7e73f#64 ++ 0xab027ee3cc3e7e73#64 : BitVec 256),
   (0x00cb06c523096944#64 ++ 0x800cb06c52309694#64 ++ 0xd1db17c72319f9cf#64 ++ 0x7d1db17c72319f9c#64 : BitVec 256),
   (0x161418028c1414a9#64 ++ 0x0161418028c1414a#64 ++ 0x7e1c1807fc1e3ffe#64 ++ 0xf7e1c1807fc1e3ff#64 : BitVec 256),
   (0x2b601b6837a03e0e#64 ++ 0x02b601b6837a03e0#64 ++ 0xefe01ff83fe03e0d#64 ++ 0xfefe01ff83fe03e0#64 : BitVec 256),
   (0x4dfea0003adf8000#64 ++ 0x04dfea0003adf800#64 ++ 0x7fffe0003fffc00b#64 ++ 0xe7fffe0003fffc00#64 : BitVec 256),
   (0x8fbfddb7c0000000#64 ++ 0x08fbfddb7c000000#64 ++ 0x8fffffffc0000007#64 ++ 0xf8fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [7, 4]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [9, 8]⟩, ⟨.and, [10, 5]⟩, ⟨.or, [2, 12]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [14, 11]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0xb027ee3cc3e7e73f 0xab027ee3cc3e7e73

def z1 : W := mkw 0x00ca00c122090840 0x800ca00c12209084 0x41d811c3201818c0 0x541d811c3201818c

def z2 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xd1db17c72319f9cf 0x7d1db17c72319f9c

def z3 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x7e1c1807fc1e3ffe 0xf7e1c1807fc1e3ff

def z4 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe01ff83fe03e0d 0xfefe01ff83fe03e0

def z5 : W := mkw 0x4dfea0c13adf8840 0x84dfea0c13adf884 0x7ffff1c33fffd8cb 0xf7ffff1c33fffd8c

def z6 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x8fffffffc0000007 0xf8fffffffc000000

def z7 : W := mkw 0x008b048500094140 0x8008b04850009414 0x101b00070019c1c2 0x0101b00070019c1c

def z8 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fffe0003fffc00b 0xe7fffe0003fffc00

def z9 : W := mkw 0x8fbfddb7c0094140 0x88fbfddb7c009414 0x9fffffffc019c1c7 0xf9fffffffc019c1c

def z10 : W := mkw 0x0b601b6023002804 0x00b601b602300280 0xcfe01ff82300380d 0xfcfe01ff82300380

def z11 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0x81e01ff803e03e05 0x181e01ff803e03e0

def z12 : W := mkw 0x0b20192004001408 0x00b2019200400140 0xefe01ff83c003e0d 0xfefe01ff83c003e0

def z13 : W := mkw 0x82015db7c0000000 0x082015db7c000000 0x80001fffc0000004 0x180001fffc000000

def z14 : W := mkw 0x89abc5b540000000 0x089abc5b54000000 0x81e3e7f800000001 0x081e3e7f80000000

def z15 : W := mkw 0x0b20192000000000 0x00b2019200000000 0x8fe01ff800000005 0xf8fe01ff80000000

def z16 : W := mkw 0x2040024837a03e0e 0x02040024837a03e0 0x600000003fe03e08 0x0600000003fe03e0

def z17 : W := mkw 0xcffffdb7fadf8000 0x0cffffdb7fadf800 0xffffffffffffc00f 0xfffffffffffffc00

def z18 : W := mkw 0x0040024023096944 0x8004002402309694 0x500000002319f9c8 0x0500000002319f9c

def z19 : W := mkw 0x00cb66dd636beb56 0xc00cb66dd636beb5 0xf1ffffffe3ffffff 0xff1ffffffe3fffff

def z20 : W := mkw 0x00cb060423096104 0x000cb06042309610 0xd1db06042319e10f 0x6d1db06042319e10

def z21 : W := mkw 0x008b048500000000 0x0008b04850000000 0x81db17c700000007 0x781db17c70000000

def z22 : W := mkw 0x8fffdff7e3096944 0x88fffdff7e309694 0xdfffffffe319f9cf 0xfdfffffffe319f9c

def z23 : W := mkw 0x14140002881400a1 0x014140002881400a 0x101c0007c01e01f2 0x0101c0007c01e01f

def z24 : W := mkw 0x2960036833a02a06 0x02960036833a02a0 0x81e007f803e00001 0x081e007f803e0000

def z25 : W := mkw 0x0001441440000000 0x0000144144000000 0x8023e63800000001 0x08023e6380000000

def z26 : W := mkw 0xcdffe5b57adf8000 0x0cdffe5b57adf800 0xffffe7f83fffc00b 0xeffffe7f83fffc00

def z27 : W := mkw 0x36541a4abfb43eaf 0x036541a4abfb43ea 0x7e1c1807fffe3ffe 0xf7e1c1807fffe3ff

def z28 : W := mkw 0x120018028c1414a9 0x0120018028c1414a 0x70001807fc1e3ffc 0x170001807fc1e3ff

def z29 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0x91c307c40301e10f 0x291c307c40301e10

def z30 : W := mkw 0x0000200000428000 0x0000020000042800 0x3027e00003e7c00b 0xa3027e00003e7c00

def z31 : W := mkw 0x4dffe61c7bffe316 0x44dffe61c7bffe31 0xffffee3cffffe73f 0xeffffee3cffffe73

def z32 : W := mkw 0x5ffe9802be9d14a9 0x05ffe9802be9d14a 0x7fdc1807fc1e3ffe 0xf7fdc1807fc1e3ff

def z33 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x2fe7e0001fe7c001 0x82fe7e0001fe7c00

def z34 : W := mkw 0x069f1c8780000000 0x0069f1c878000000 0x8fdf1fc7c0000007 0xf8fdf1fc7c000000

def z35 : W := mkw 0x2960036833a02a06 0x02960036833a02a0 0xefe007f83fe00009 0xeefe007f83fe0000

def z36 : W := mkw 0xaf34d93ad4a0160a 0x0af34d93ad4a0160 0x2e24e838dce00600 0x82e24e838dce0060

def z37 : W := mkw 0x0614180280000000 0x0061418028000000 0x0e040800c0000000 0x80e040800c000000

def z38 : W := mkw 0x49ebe61c73ebe316 0x449ebe61c73ebe31 0xb1e7ee3cc3e7e73f 0xab1e7ee3cc3e7e73

def z39 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0x8023e63803e1c001 0x08023e63803e1c00

def z40 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0xb027e63803e7c00b 0xab027e63803e7c00

def z41 : W := mkw 0x22001b6805203e0e 0x022001b6805203e0 0x80001ff800003e04 0x180001ff800003e0

def z42 : W := mkw 0x49eaa00032cb8000 0x049eaa00032cb800 0x01e3e00003e1c001 0x001e3e00003e1c00

def z43 : W := mkw 0x449ea000085f8000 0x0449ea000085f800 0x101fe000001fc002 0x0101fe000001fc00

def z44 : W := mkw 0x16141a0a8d3436af 0x016141a0a8d3436a 0xfe3c1e3ffffe3fff 0xffe3c1e3ffffe3ff

def z45 : W := mkw 0x8920c13040000000 0x08920c1304000000 0x0020e03800000000 0x00020e0380000000

def z46 : W := mkw 0x9fbfddb7cc1414a9 0x09fbfddb7cc1414a 0xfffffffffc1e3fff 0xffffffffffc1e3ff

def z47 : W := mkw 0xbfffdfffffb43eaf 0x0bfffdfffffb43ea 0xfffffffffffe3fff 0xffffffffffffe3ff

def z48 : W := mkw 0x00402248236beb56 0xc00402248236beb5 0x7000000023fffff8 0x07000000023fffff

def z49 : W := mkw 0x4d34a00018d68000 0x04d34a00018d6800 0x3e27e0001fe7c00b 0xa3e27e0001fe7c00

def z50 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x8ffbf7fb00000001 0x58ffbf7fb0000000

def z51 : W := mkw 0x0040024023002804 0x0004002402300280 0xc1c017c02300380d 0x7c1c017c02300380

def z52 : W := mkw 0x0b215d3440000000 0x00b215d344000000 0x8fe7fffcc0000007 0xf8fe7fffcc000000

def z53 : W := mkw 0x2b617f7c77e2ff1e 0x42b617f7c77e2ff1 0xffe7fffcffe7ff3f 0xfffe7fffcffe7ff3

def z54 : W := mkw 0x820019a380000000 0x0820019a38000000 0x000011c300000000 0x1000011c30000000

def z55 : W := mkw 0x4dffe4147adf8000 0x04dffe4147adf800 0xffffee3cffffc00f 0xeffffee3cffffc00

def z56 : W := mkw 0x5ffeb802bedf94a9 0x05ffeb802bedf94a 0x7ffff807ffffffff 0xf7ffff807fffffff

def z57 : W := mkw 0x549ea002885f80a1 0x0549ea002885f80a 0x101fe007c01fc1f2 0x0101fe007c01fc1f

def z58 : W := mkw 0x0000000000000000 0x0000000000000000 0x30040804c006273e 0xa30040804c006273

def z59 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xf1df1fc7e31fffff 0xff1df1fc7e31ffff

def z60 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xcfe017f83fe01801 0x5cfe017f83fe0180

def z61 : W := mkw 0x00cb04c522094940 0x800cb04c52209494 0x51db11c72019d9c2 0x551db11c72019d9c

def z62 : W := mkw 0x00ca02c123092844 0x800ca02c12309284 0xc1d817c3231838cd 0x7c1d817c3231838c

def z63 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0x9027e63cc3e7c133 0x09027e63cc3e7c13

def z64 : W := mkw 0x8babddb7c0000000 0x08babddb7c000000 0x81e3ffffc0000005 0x181e3ffffc000000

def z65 : W := mkw 0x0001441440000000 0x0000144144000000 0x8027ee3cc0000007 0xa8027ee3cc000000

def z66 : W := mkw 0x8fffdff7e3002804 0x08fffdff7e300280 0xcfffffffe300380f 0xfcfffffffe300380

def z67 : W := mkw 0x3f741b6abfb43eaf 0x03f741b6abfb43ea 0xfffc1ffffffe3fff 0xffffc1ffffffe3ff

def z68 : W := mkw 0x49eaa00032cb8000 0x049eaa00032cb800 0x6fe3e0003fe1c009 0xe6fe3e0003fe1c00

def z69 : W := mkw 0x0920012000000000 0x0092001200000000 0x81e007f800000001 0x081e007f80000000

def z70 : W := mkw 0x100000000c1414a9 0x0100000000c1414a 0x700000003c1e3ff8 0x0700000003c1e3ff

def z71 : W := mkw 0x0000601840628212 0x4000060184062821 0x3027e838c3e7c63b 0xa3027e838c3e7c63

def z72 : W := mkw 0x56543802bedf94a9 0x056543802bedf94a 0x7e1c1807fffffffe 0xf7e1c1807fffffff

def z73 : W := mkw 0x0001060401006104 0x0000106040100610 0x8000060400002104 0x0800006040000210

def z74 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xc1db17c32319d8c1 0x5c1db17c32319d8c

def z75 : W := mkw 0x4dbea00018df8000 0x04dbea00018df800 0x3e3fe0001cffc002 0x83e3fe0001cffc00

def z76 : W := mkw 0x4dfea2403bdfa804 0x04dfea2403bdfa80 0xfffff7c03ffff80f 0xffffff7c03ffff80

def z77 : W := mkw 0x12001802840014a9 0x012001802840014a 0x50181807e0183ffe 0x750181807e0183ff

def z78 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x4e1810033c1818c0 0x54e1810033c1818c

def z79 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xcfc01ff83c003e04 0x5cfc01ff83c003e0

def z80 : W := mkw 0x9fbfddb7cc1414a9 0x09fbfddb7cc1414a 0xafffffffdc060637 0xfafffffffdc06063

def z81 : W := mkw 0x44dea0002a5f8000 0x044dea0002a5f800 0x51dfe000231fc00b 0x651dfe000231fc00

def z82 : W := mkw 0x008b048500000000 0x0008b04850000000 0xd1db17c7201839cf 0x7d1db17c7201839c

def z83 : W := mkw 0x00ca000022090000 0x000ca00002209000 0x51db00002319c00b 0x651db00002319c00

def z84 : W := mkw 0x0960024033802804 0x0096002403380280 0xefe017c03fe0380d 0xfefe017c03fe0380

def z85 : W := mkw 0x0001060401006104 0x0000106040100610 0x900306040301e10f 0x2900306040301e10

def z86 : W := mkw 0x2b201b2815a0360e 0x02b201b2815a0360 0xae200e381fe0260d 0xaae200e381fe0260

def z87 : W := mkw 0x89abc5b540000000 0x089abc5b54000000 0x81e7effcc0000007 0xa81e7effcc000000

def z88 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x0fdff1c7c0000002 0x50fdff1c7c000000

def z89 : W := mkw 0x0dbea00000428000 0x00dbea0000042800 0x3fffe00003e7c00b 0xe3fffe00003e7c00

def z90 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0xdfffffffe01839cf 0xfdfffffffe01839c

def z91 : W := mkw 0x000106c501006944 0x8000106c50100694 0x800017c7000039c4 0x1800017c7000039c

def z92 : W := mkw 0x86155db7c0000000 0x086155db7c000000 0x8e1c1fffc0000006 0xf8e1c1fffc000000

def z93 : W := mkw 0x49eaa0003adf8000 0x049eaa0003adf800 0x71e3e0003fffc009 0x071e3e0003fffc00

def z94 : W := mkw 0x00ca024023096944 0x800ca02402309694 0x51db00002319f9cb 0x651db00002319f9c

def z95 : W := mkw 0x22001b6805203e0e 0x022001b6805203e0 0xa0201ff803e03e0d 0xba0201ff803e03e0

def z96 : W := mkw 0x0000000000000000 0x0000000000000000 0x50181007201839ce 0x750181007201839c

def z97 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0x81c307c00301c001 0x081c307c00301c00

def z98 : W := mkw 0x3b601b6ab7a03eaf 0x03b601b6ab7a03ea 0xefe01fffffe03ffd 0xfefe01fffffe03ff

def z99 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000804c0002734 0x000000804c000273

def z100 : W := mkw 0x8fbfffbfc162e316 0x48fbfffbfc162e31 0x8fffffffc3e1c007 0xf8fffffffc3e1c00

def z101 : W := mkw 0x2b60196036801c08 0x02b60196036801c0 0x4fc011c03c001800 0x54fc011c03c00180

def z102 : W := mkw 0x16df1ec7af1d7ded 0x816df1ec7af1d7de 0xffdf1fc7ff1fffff 0xfffdf1fc7ff1ffff

def z103 : W := mkw 0x2920012810a00202 0x02920012810a0020 0x0020003800e00000 0x00020003800e0000

def z104 : W := mkw 0x2960036833a02a06 0x02960036833a02a0 0xc1e017f823e0380d 0x7c1e017f823e0380

def z105 : W := mkw 0x0000601840628212 0x4000060184062821 0x2024e838c0e60630 0x82024e838c0e6063

def z106 : W := mkw 0x0000000000000000 0x0000000000000000 0x80200e3800000005 0xa80200e380000000

def z107 : W := mkw 0x0960000032800000 0x0096000003280000 0x6fe000003fe00009 0xe6fe000003fe0000

def z108 : W := mkw 0x445420003adf8000 0x0445420003adf800 0x7e1c00003fffc00a 0xe7e1c00003fffc00

def z109 : W := mkw 0x049e800000000000 0x0049e80000000000 0x001fe00000000002 0x0001fe0000000000

def z110 : W := mkw 0x40cb26c53bdfe944 0x840cb26c53bdfe94 0xf1db17c73ffff9cf 0x7f1db17c73ffff9c

def z111 : W := mkw 0x2bea19e136891c48 0x82bea19e136891c4 0x4fd811c33c1818c0 0x54fd811c33c1818c

def z112 : W := mkw 0x4d35e61c59f6e316 0x44d35e61c59f6e31 0xbe27ee3cdfe7e73f 0xabe27ee3cdfe7e73

def z113 : W := mkw 0xafffdffff7a03e0e 0x0afffdffff7a03e0 0xefffffffffe03e0f 0xfefffffffffe03e0

def z114 : W := mkw 0x00cb66dd636beb56 0xc00cb66dd636beb5 0x81e3e7f803e1c001 0x081e3e7f803e1c00

def z115 : W := mkw 0x06155c16c0000000 0x006155c16c000000 0x8e3ffe3fc0000007 0xf8e3ffe3fc000000

def z116 : W := mkw 0x4dfe80003a9d0000 0x04dfe80003a9d000 0x4fd800003c180000 0x44fd800003c18000

def z117 : W := mkw 0x2beb1fed37a97f4e 0x82beb1fed37a97f4 0xfffb1fff3ff9ffcf 0xffffb1fff3ff9ffc

def z118 : W := mkw 0x29eb07ed33a96b46 0x829eb07ed33a96b4 0x81e307f803e1c001 0x081e307f803e1c00

def z119 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z120 : W := mkw 0x2b615f7c77a07f1e 0x42b615f7c77a07f1 0xefe01ffcffe03f3d 0xfefe01ffcffe03f3

def z121 : W := mkw 0x00ca02c123096944 0x800ca02c12309694 0x51d811c32319f9c8 0x551d811c32319f9c

def z122 : W := mkw 0x0001048500000000 0x0000104850000000 0x800017c700000004 0x1800017c70000000

def z123 : W := mkw 0x2040024833a02a06 0x02040024833a02a0 0x0000000003e00000 0x00000000003e0000

def z124 : W := mkw 0x969fdc97cc1414a9 0x0969fdc97cc1414a 0x7e1ff807fc1e3ffe 0xf7e1ff807fc1e3ff

def z125 : W := mkw 0x849fc497c0000000 0x0849fc497c000000 0x803fee3fc0000007 0xa803fee3fc000000

def z126 : W := mkw 0x02cb1ec527097d4c 0x802cb1ec527097d4 0xffdb1fc73f19ffcf 0xfffdb1fc73f19ffc

def z127 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0x9007ee3cc007e736 0x09007ee3cc007e73

def z128 : W := mkw 0x000022080162e316 0x4000022080162e31 0x0000000003e1c000 0x00000000003e1c00

def z129 : W := mkw 0x0000020801202206 0x0000002080120220 0xa0200e3803e0260d 0xaa0200e3803e0260

def z130 : W := mkw 0x8fbe99a380000000 0x08fbe99a38000000 0x0fd811c300000000 0x50fd811c30000000

def z131 : W := mkw 0x849fe497c042c110 0x4849fe497c042c11 0x101fe007c007c132 0x0101fe007c007c13

def z132 : W := mkw 0x12001802840014a9 0x012001802840014a 0x00001807c0003ff4 0x100001807c0003ff

def z133 : W := mkw 0x000164144042c110 0x4000164144042c11 0x1007e004c007c132 0x01007e004c007c13

def z134 : W := mkw 0x0000200000428000 0x0000020000042800 0x3000000003e7c008 0x03000000003e7c00

def z135 : W := mkw 0x4dfe80003a9d0000 0x04dfe80003a9d000 0x4fffe0003c180003 0xe4fffe0003c18000

def z136 : W := mkw 0x0000000000000000 0x0000000000000000 0x00001007000039c4 0x100001007000039c

def z137 : W := mkw 0x49eba6c533cbe944 0x849eba6c533cbe94 0x81e3e7c003e1c001 0x081e3e7c003e1c00

def z138 : W := mkw 0x4d34a00018d68000 0x04d34a00018d6800 0x2e24e0001ce60000 0x82e24e0001ce6000

def z139 : W := mkw 0x008b06c501096944 0x8008b06c50109694 0x901b17c70019f9c6 0x1901b17c70019f9c

def z140 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x6ffce0003cfe0000 0xc6ffce0003cfe000

def z141 : W := mkw 0x00cb06cd23296b46 0x800cb06cd23296b4 0xf1fb1fff23f9ffcf 0xff1fb1fff23f9ffc

def z142 : W := mkw 0x16143a0a8d76f7bf 0x416143a0a8d76f7b 0x7e1c1807fffffffe 0xf7e1c1807fffffff

def z143 : W := mkw 0x9fbe99a38c1414a9 0x09fbe99a38c1414a 0x4fd811c33c1818c0 0x54fd811c33c1818c

def z144 : W := mkw 0x0fbe992000000000 0x00fbe99200000000 0x8ffffff800000007 0xf8ffffff80000000

def z145 : W := mkw 0x141400000c1414a9 0x0141400000c1414a 0x7e1c00003c1e3ffa 0xe7e1c00003c1e3ff

def z146 : W := mkw 0x16155c16cc1414a9 0x016155c16cc1414a 0xfe3ffe3ffc1e3fff 0xffe3ffe3ffc1e3ff

def z147 : W := mkw 0x304002483fb43eaf 0x0304002483fb43ea 0x700000003ffe3ff8 0x0700000003ffe3ff

def z148 : W := mkw 0x5f34b8029cd694a9 0x05f34b8029cd694a 0x2e24e800dce60630 0x82e24e800dce6063

def z149 : W := mkw 0x2000024805203e0e 0x02000024805203e0 0x0000000000003e00 0x00000000000003e0

def z150 : W := mkw 0x0040004022000800 0x0004000402200080 0x41c011c020001800 0x541c011c02000180

def z151 : W := mkw 0x8f34d932c0000000 0x08f34d932c000000 0x0e24e838c0000000 0x80e24e838c000000

def z152 : W := mkw 0x0000020001006104 0x0000002000100610 0x100000000301e108 0x0100000000301e10

def z153 : W := mkw 0x008a008100000000 0x0008a00810000000 0x01d811c300000000 0x501d811c30000000

def z154 : W := mkw 0x12015e1ec52077bf 0x412015e1ec52077b 0x80001e3fc0003ff4 0x180001e3fc0003ff

def z155 : W := mkw 0x16151ec78d147ded 0x816151ec78d147de 0xfe1c1fc7fc1e3ffe 0xffe1c1fc7fc1e3ff

def z156 : W := mkw 0x0414000008140000 0x0041400000814000 0x7e1c00003c1e000a 0xe7e1c00003c1e000

def z157 : W := mkw 0x000022080162e316 0x4000022080162e31 0x3000000003e7e738 0x03000000003e7e73

def z158 : W := mkw 0x02017e1c4562f71e 0x402017e1c4562f71 0xfe27fe3cffe7ff3f 0xffe27fe3cffe7ff3

def z159 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0xa023ee3803e1e60d 0xaa023ee3803e1e60

def z160 : W := mkw 0x22001b6805203e0e 0x022001b6805203e0 0xee001ff83c003e0c 0xfee001ff83c003e0

def z161 : W := mkw 0x0000000000000000 0x0000000000000000 0x501800002018000a 0x6501800002018000

def z162 : W := mkw 0x00cb048522094140 0x800cb04852209414 0x51db00072319c1cb 0x651db00072319c1c

def z163 : W := mkw 0x0000020801202206 0x0000002080120220 0x8020063803e00001 0x08020063803e0000

def z164 : W := mkw 0x2961677c73e2eb16 0x42961677c73e2eb1 0x81e3e7f803e1c001 0x081e3e7f803e1c00

def z165 : W := mkw 0x2040224837e2ff1e 0x42040224837e2ff1 0x700000003fe7ff38 0x0700000003fe7ff3

def z166 : W := mkw 0x4dffa6c53bdfe944 0x84dffa6c53bdfe94 0xfffff7c73ffff9cf 0xffffff7c73ffff9c

def z167 : W := mkw 0x008b449540000000 0x0008b44954000000 0x81ffffffc0000007 0xf81ffffffc000000

def z168 : W := mkw 0x0960000032800000 0x0096000003280000 0x4fc000003c000000 0x44fc000003c00000

def z169 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fffe804ffffe73f 0xe7fffe804ffffe73

def z170 : W := mkw 0x8fbffdb7c042c110 0x48fbffdb7c042c11 0x9fffffffc007c137 0xf9fffffffc007c13

def z171 : W := mkw 0x49ebe61c73ebe316 0x449ebe61c73ebe31 0x81e3e63803e1c001 0x081e3e63803e1c00

def z172 : W := mkw 0x8fbfdff7c1006944 0x88fbfdff7c100694 0x8fffffffc00039c7 0xf8fffffffc00039c

def z173 : W := mkw 0x0dbfe61c4162e316 0x40dbfe61c4162e31 0xbfffee3cc3e7e73f 0xebfffee3cc3e7e73

def z174 : W := mkw 0x0960020833a02206 0x00960020833a0220 0xefe00e383fe0260d 0xeefe00e383fe0260

def z175 : W := mkw 0x5ffe9802be9d14a9 0x05ffe9802be9d14a 0x4fd810033c1818c0 0x54fd810033c1818c

def z176 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xd1c307c02319f9c9 0x0d1c307c02319f9c

def z177 : W := mkw 0x92015db7c40014a9 0x092015db7c40014a 0x80001fffc0003ff4 0x180001fffc0003ff

def z178 : W := mkw 0x0b217f3c4162e316 0x40b217f3c4162e31 0xbfe7fffcc3e7e73f 0xfbfe7fffcc3e7e73

def z179 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x6e1818033c183ecc 0xf6e1818033c183ec

def z180 : W := mkw 0x7ffebb6abfffbeaf 0x07ffebb6abfffbea 0xffffffffffffffff 0xffffffffffffffff

def z181 : W := mkw 0xafffddf7f6801c08 0x0afffddf7f6801c0 0xcffffffffc001807 0xfcffffffffc00180

def z182 : W := mkw 0x8dbfc5b7c0000000 0x08dbfc5b7c000000 0x81ffe7ffc0000003 0x081ffe7ffc000000

def z183 : W := mkw 0x22015f7c45207f1e 0x422015f7c45207f1 0x80001ffcc0003f34 0x180001ffcc0003f3

def z184 : W := mkw 0x849fc497c0000000 0x0849fc497c000000 0x81dff7c7c0000007 0x781dff7c7c000000

def z185 : W := mkw 0xcffffff7fbdfe944 0x8cffffff7fbdfe94 0xfffffffffffff9cf 0xffffffffffffff9c

def z186 : W := mkw 0x82015ff7c1006944 0x882015ff7c100694 0x80001fffc00039c4 0x180001fffc00039c

def z187 : W := mkw 0x49ea800032890000 0x049ea80003289000 0x01c0000000000000 0x001c000000000000

def z188 : W := mkw 0x8fbfffbfc162e316 0x48fbfffbfc162e31 0xbfffffffc3e7e73f 0xfbfffffffc3e7e73

def z189 : W := mkw 0x5ffffe1efffff7bf 0x45ffffe1efffff7b 0xfffffe3fffffffff 0xffffffe3ffffffff

def z190 : W := mkw 0x00cb26cd236beb56 0xc00cb26cd236beb5 0xf1db17c723ffffff 0x7f1db17c723fffff

def z191 : W := mkw 0x2b217f3c55e2f71e 0x42b217f3c55e2f71 0xbe27ee3cdfe7e73f 0xabe27ee3cdfe7e73

def z192 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x6e1c1803fc1e1ef0 0xd6e1c1803fc1e1ef

def z193 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0xbfffffffc006273f 0xfbfffffffc006273

def z194 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x2e040800dc060630 0x82e040800dc06063

def z195 : W := mkw 0x89abc5b540000000 0x089abc5b54000000 0x81fbf7ff00000007 0x781fbf7ff0000000

def z196 : W := mkw 0x2b20192814a0160a 0x02b20192814a0160 0x2e2008381ce00600 0x82e2008381ce0060

def z197 : W := mkw 0x22017f7c4562ff1e 0x422017f7c4562ff1 0xb027fffcc3e7ff3f 0xbb027fffcc3e7ff3

def z198 : W := mkw 0x14140002881400a1 0x014140002881400a 0x00180003001800c0 0x000180003001800c

def z199 : W := mkw 0x0000020801202206 0x0000002080120220 0x80000e3800002604 0x080000e380000260

def z200 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0x81db17c70301c007 0x781db17c70301c00

def z201 : W := mkw 0x0beb1fe523096944 0x80beb1fe52309694 0xdffb1fff2319f9cf 0xfdffb1fff2319f9c

def z202 : W := mkw 0x0dbe800000000000 0x00dbe80000000000 0x0fffe00000000003 0xe0fffe0000000000

def z203 : W := mkw 0x00ca2000224b8000 0x000ca2000224b800 0x71ffe00023ffc00b 0xe71ffe00023ffc00

def z204 : W := mkw 0x008b068501096144 0x8008b06850109614 0x901b06070319e1cf 0x2901b06070319e1c

def z205 : W := mkw 0x4dbea000085f8000 0x04dbea000085f800 0x1fffe000001fc003 0xe1fffe000001fc00

def z206 : W := mkw 0x9fbfddb7cc1414a9 0x09fbfddb7cc1414a 0xcffffffffc1818c7 0xfcffffffffc1818c

def z207 : W := mkw 0x2b201b6815a03e0e 0x02b201b6815a03e0 0xae201ff81ce03e04 0x9ae201ff81ce03e0

def z208 : W := mkw 0x0200180000000000 0x0020018000000000 0x0e00180000000004 0xf0e0018000000000

def z209 : W := mkw 0x4dfe80003a9d0000 0x04dfe80003a9d000 0x5fdb00003f19c00b 0x65fdb00003f19c00

def z210 : W := mkw 0x0414000008140000 0x0041400000814000 0x7e1c0804fc1e273e 0xe7e1c0804fc1e273

def z211 : W := mkw 0x100000000c1414a9 0x0100000000c1414a 0x200000001c060630 0x0200000001c06063

def z212 : W := mkw 0x0040000022000000 0x0004000002200000 0x41c0000023000009 0x641c000002300000

def z213 : W := mkw 0x849fc497c0000000 0x0849fc497c000000 0x001fe007c0000002 0x0001fe007c000000

def z214 : W := mkw 0x82015fbfc1206316 0x482015fbfc120631 0x80001fffc0002734 0x180001fffc000273

def z215 : W := mkw 0x0001441440000000 0x0000144144000000 0x80000e3cc0000004 0x080000e3cc000000

def z216 : W := mkw 0x000022080162e316 0x4000022080162e31 0x30040804c3e7e73e 0xa30040804c3e7e73

def z217 : W := mkw 0x2b611f6c37a07f0e 0x02b611f6c37a07f0 0xffe31ffc3fe1ff0f 0xfffe31ffc3fe1ff0

def z218 : W := mkw 0x0200180004001408 0x0020018000400140 0x6e0018003c003e0c 0xf6e0018003c003e0

def z219 : W := mkw 0x100022080d76f7bf 0x4100022080d76f7b 0x700000003ffffff8 0x0700000003ffffff

def z220 : W := mkw 0x2000000814a0160a 0x02000000814a0160 0x200000001ce00600 0x0200000001ce0060

def z221 : W := mkw 0x849fc497c0094140 0x8849fc497c009414 0x101fe007c019c1c2 0x0101fe007c019c1c

def z222 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x2e1c1807dc060636 0xf2e1c1807dc06063

def z223 : W := mkw 0x2040024837a03e0e 0x02040024837a03e0 0xe1c017c03fe03e0d 0x7e1c017c03fe03e0

def z224 : W := mkw 0x141400028c1414a9 0x0141400028c1414a 0x701c0007fc1e3ffa 0x0701c0007fc1e3ff

def z225 : W := mkw 0x0000000000000000 0x0000000000000000 0x300400000006000a 0xa300400000006000

def z226 : W := mkw 0x4dff86c53b9d6944 0x84dff86c53b9d694 0xdfdb17c73f19f9cf 0x7dfdb17c73f19f9c

def z227 : W := mkw 0x4920a00010c28000 0x04920a00010c2800 0x0020e00000e00000 0x00020e00000e0000

def z228 : W := mkw 0x00cb661c636be316 0x400cb661c636be31 0xf1ffee3ce3ffe73f 0xef1ffee3ce3ffe73

def z229 : W := mkw 0x4ffeb802badf8000 0x04ffeb802badf800 0x7ffff807ffffc00f 0xf7ffff807ffffc00

def z230 : W := mkw 0x0200180004001408 0x0020018000400140 0x7e041804fc063f3e 0xf7e041804fc063f3

def z231 : W := mkw 0x6ffe9b683fbd3e0e 0x06ffe9b683fbd3e0 0xeff81ff83ff83e0d 0xfeff81ff83ff83e0

def z232 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x8fe7eff8c0000001 0x88fe7eff8c000000

def z233 : W := mkw 0x000164144042c110 0x4000164144042c11 0x3007e804c007e73e 0xa3007e804c007e73

def z234 : W := mkw 0x869fddb7c0000000 0x0869fddb7c000000 0x801fffffc0000006 0x1801fffffc000000

def z235 : W := mkw 0x22cb1fed27297f4e 0x822cb1fed27297f4 0xd1db1fff2319ffcf 0x7d1db1fff2319ffc

def z236 : W := mkw 0x0614180280000000 0x0061418028000000 0x0e1c1807c0000006 0xf0e1c1807c000000

def z237 : W := mkw 0x0000000000000000 0x0000000000000000 0x10040004c0060132 0x010040004c006013

def z238 : W := mkw 0x09eb06c533896944 0x809eb06c53389694 0xfffb17c73ff9f9cf 0xffffb17c73ff9f9c

def z239 : W := mkw 0xcfffddb7fa9d0000 0x0cfffddb7fa9d000 0xcffffffffc180007 0xfcffffffffc18000

def z240 : W := mkw 0x0000020801202206 0x0000002080120220 0xb0240e3cc3e6273f 0xab0240e3cc3e6273

def z241 : W := mkw 0x604022483fffbe0e 0x0604022483fffbe0 0x700000003ffffe08 0x0700000003ffffe0

def z242 : W := mkw 0x16df1ec7af1d7ded 0x816df1ec7af1d7de 0xdfdb17c73f19f9cf 0x7dfdb17c73f19f9c

def z243 : W := mkw 0xaffffffff7e2ff1e 0x4affffffff7e2ff1 0xffffffffffe7ff3f 0xfffffffffffe7ff3

def z244 : W := mkw 0x8f34d932c0000000 0x08f34d932c000000 0x0e3cf83fc0000006 0xf0e3cf83fc000000

def z245 : W := mkw 0x89ebc7f563096944 0x889ebc7f56309694 0xd1fbf7ff2319f9cf 0x7d1fbf7ff2319f9c

def z246 : W := mkw 0x000146dd41206b56 0xc000146dd41206b5 0x80001fffc0003ff4 0x180001fffc0003ff

def z247 : W := mkw 0x8fbffdbfc0628212 0x48fbffdbfc062821 0xafffffffc0e60637 0xfafffffffc0e6063

def z248 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xafe00ff81fe00601 0x8afe00ff81fe0060

def z249 : W := mkw 0xefffffffffffbe0e 0x0efffffffffffbe0 0xfffffffffffffe0f 0xffffffffffffffe0

def z250 : W := mkw 0x16157e1ecd76f7bf 0x416157e1ecd76f7b 0xbe27ee3cdfe7e73f 0xabe27ee3cdfe7e73

def z251 : W := mkw 0x2f741b683fb43e0e 0x02f741b683fb43e0 0xfffc1ff83ffe3e0f 0xffffc1ff83ffe3e0

def z252 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xffe41ffcffe63f3f 0xfffe41ffcffe63f3

def z253 : W := mkw 0x0fbe980280000000 0x00fbe98028000000 0x0ffff807c0000007 0xf0ffff807c000000

def z254 : W := mkw 0xc49fe497c85f8000 0x0c49fe497c85f800 0x101fe007c01fc002 0x0101fe007c01fc00

def z255 : W := mkw 0x0001441440000000 0x0000144144000000 0xb027ee3cc006273f 0xab027ee3cc006273

def z256 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x5e1c1007fc1e19f2 0x55e1c1007fc1e19f

def z257 : W := mkw 0x5ffeb802bedf94a9 0x05ffeb802bedf94a 0x7fffe800ffffc63b 0xe7fffe800ffffc63

def z258 : W := mkw 0x8fbfddb7c8140000 0x08fbfddb7c814000 0xfffffffffc1e000f 0xffffffffffc1e000

def z259 : W := mkw 0x1614781acc7696bb 0x41614781acc7696b 0x7e3cf83ffcfe3ffe 0xf7e3cf83ffcfe3ff

def z260 : W := mkw 0x0000200000428000 0x0000020000042800 0x0023e00003e1c001 0x00023e00003e1c00

def z261 : W := mkw 0x0001461c41206316 0x40001461c4120631 0x80000e3cc0002734 0x080000e3cc000273

def z262 : W := mkw 0x2b615f7c77a03e0e 0x02b615f7c77a03e0 0xefe7fffcffe03e0f 0xfefe7fffcffe03e0

def z263 : W := mkw 0x9fbfddb7c40014a9 0x09fbfddb7c40014a 0x8fffffffc0003ff7 0xf8fffffffc0003ff

def z264 : W := mkw 0x06df1ec7a3096944 0x806df1ec7a309694 0xdfdf1fc7e319f9cf 0xfdfdf1fc7e319f9c

def z265 : W := mkw 0x4dffe6dd7bffeb56 0xc4dffe6dd7bffeb5 0xffffffffffffffff 0xffffffffffffffff

def z266 : W := mkw 0x16157e1ecd76f7bf 0x416157e1ecd76f7b 0xfe3ffe3fffffffff 0xffe3ffe3ffffffff

def z267 : W := mkw 0x0040000022090000 0x0004000002209000 0x500000002319c008 0x0500000002319c00

def z268 : W := mkw 0x828b5db7c0000000 0x0828b5db7c000000 0x81db1fffc0000007 0x781db1fffc000000

def z269 : W := mkw 0x0040024023096944 0x8004002402309694 0xd1c017c02319f9cd 0x7d1c017c02319f9c

def z270 : W := mkw 0x16df7edfef7fffff 0xc16df7edfef7ffff 0xffffffffffffffff 0xffffffffffffffff

def z271 : W := mkw 0x0414200008568000 0x0041420000856800 0x7e3fe0003fffc00b 0xe7e3fe0003fffc00

def z272 : W := mkw 0x00cb66dd636beb56 0xc00cb66dd636beb5 0xd1fbf7ff23f9f9cf 0x7d1fbf7ff23f9f9c

def z273 : W := mkw 0x0001260c0162e316 0x40001260c0162e31 0xb003060403e7e73f 0x2b003060403e7e73

def z274 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0x3007e004c3e7e73a 0x03007e004c3e7e73

def z275 : W := mkw 0x008b048500000000 0x0008b04850000000 0x001b000700000002 0x0001b00070000000

def z276 : W := mkw 0x4dbea00018d68000 0x04dbea00018d6800 0x2fffe0001ce60003 0xe2fffe0001ce6000

def z277 : W := mkw 0x008b06c501006944 0x8008b06c50100694 0x81db17c7000039c7 0x781db17c7000039c

def z278 : W := mkw 0x89abe7bd4162e316 0x489abe7bd4162e31 0xb1e7effcc3e7e73f 0xab1e7effcc3e7e73

def z279 : W := mkw 0x0414000008140000 0x0041400000814000 0x7e1c10073c1e39ce 0xf7e1c10073c1e39c

def z280 : W := mkw 0x449e8000081d0000 0x0449e8000081d000 0x0018000000180000 0x0001800000018000

def z281 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xc1d817c7201839c4 0x5c1d817c7201839c

def z282 : W := mkw 0x2b60196036801c08 0x02b60196036801c0 0x6fe011c03fe01809 0xf6fe011c03fe0180

def z283 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x0e0000001c000000 0x00e0000001c00000

def z284 : W := mkw 0x0000200800628212 0x4000020080062821 0x2000000000e60630 0x02000000000e6063

def z285 : W := mkw 0x3f757f7efff6ffbf 0x43f757f7efff6ffb 0xffffffffffffffff 0xffffffffffffffff

def z286 : W := mkw 0x008b048500094140 0x8008b04850009414 0x000300000001c000 0x0000300000001c00

def z287 : W := mkw 0x9fbfffbfcd76f7bf 0x49fbfffbfcd76f7b 0xffffffffffffffff 0xffffffffffffffff

def z288 : W := mkw 0x8fbfdfbfc1206316 0x48fbfdfbfc120631 0x8fffffffc0002737 0xf8fffffffc000273

def z289 : W := mkw 0x000020000042c110 0x4000020000042c11 0x100000000007c130 0x0100000000007c13

def z290 : W := mkw 0x8fffdff7e3096944 0x88fffdff7e309694 0x8fffffffc301c007 0xf8fffffffc301c00

def z291 : W := mkw 0x8fbed932c0000000 0x08fbed932c000000 0x0fffe838c0000003 0xe0fffe838c000000

def z292 : W := mkw 0x0200180280000000 0x0020018028000000 0x00001807c0000004 0x100001807c000000

def z293 : W := mkw 0xaffe99e3b6801c08 0x0affe99e3b6801c0 0x4fd811c33c001800 0x54fd811c33c00180

def z294 : W := mkw 0x0dfe800022090000 0x00dfe80002209000 0x5fffe0002319c00b 0xe5fffe0002319c00

def z295 : W := mkw 0x6beabb6837ebbe0e 0x06beabb6837ebbe0 0xefe3fff83fe1fe0d 0xfefe3fff83fe1fe0

def z296 : W := mkw 0x2b60196036801c08 0x02b60196036801c0 0x6fc019c03c003e0c 0xf6fc019c03c003e0

def z297 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x7e1c0800fc1e063a 0xe7e1c0800fc1e063

def z298 : W := mkw 0x2960036837a03e0e 0x02960036837a03e0 0xe1e007f83fe03e09 0x0e1e007f83fe03e0

def z299 : W := mkw 0x6ffebb683fffbe0e 0x06ffebb683fffbe0 0xfffffff83ffffe0f 0xffffffff83ffffe0

def z300 : W := mkw 0x0000000000000000 0x0000000000000000 0x200008000000260c 0xa200008000000260

def z301 : W := mkw 0x8fbfddb7c4001408 0x08fbfddb7c400140 0xeffffffffc003e0f 0xfeffffffffc003e0

def z302 : W := mkw 0x0dfe800032800000 0x00dfe80003280000 0x6fffe0003fe0000b 0xe6fffe0003fe0000

def z303 : W := mkw 0x82cb5ff7e3096944 0x882cb5ff7e309694 0xd1db1fffe319f9cf 0x7d1db1fffe319f9c

def z304 : W := mkw 0x5fffbec7bfdffded 0x85fffbec7bfdffde 0xffffffc7ffffffff 0xfffffffc7fffffff

def z305 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0x81c317c70301f9c5 0x181c317c70301f9c

def z306 : W := mkw 0x3f741b6abfb43eaf 0x03f741b6abfb43ea 0xefe41ff8ffe63e3d 0xfefe41ff8ffe63e3

def z307 : W := mkw 0x3f34192a9cb416ab 0x03f34192a9cb416a 0x2e240838dce60630 0x82e240838dce6063

def z308 : W := mkw 0x82017fbfc162e316 0x482017fbfc162e31 0xb027ffffc3e7e73f 0xbb027ffffc3e7e73

def z309 : W := mkw 0x169f1c878c1414a9 0x0169f1c878c1414a 0xffdf1fc7fc1e3fff 0xfffdf1fc7fc1e3ff

def z310 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x3e1c0807dc1e07f2 0x83e1c0807dc1e07f

def z311 : W := mkw 0x06157e1ec162e316 0x406157e1ec162e31 0xbe3ffe3fc3e7e73f 0xfbe3ffe3fc3e7e73

def z312 : W := mkw 0x4ffeb9203adf8000 0x04ffeb9203adf800 0xfffffff83fffc00f 0xffffffff83fffc00

def z313 : W := mkw 0x8f34d932c0000000 0x08f34d932c000000 0x8fe4fff8c0000005 0xf8fe4fff8c000000

def z314 : W := mkw 0x1fbe98028c1414a9 0x01fbe98028c1414a 0x7ffff807fc1e3fff 0xf7ffff807fc1e3ff

def z315 : W := mkw 0x2040004036801c08 0x02040004036801c0 0x400000003c001800 0x0400000003c00180

def z316 : W := mkw 0x0000000000000000 0x0000000000000000 0x400010002000380c 0x7400010002000380

def z317 : W := mkw 0x8babddb540000000 0x08babddb54000000 0x8fe3fff800000005 0xf8fe3fff80000000

def z318 : W := mkw 0x0415661c4976e316 0x40415661c4976e31 0xfe3fee3cffffe73f 0xefe3fee3cffffe73

def z319 : W := mkw 0x4040200032cb8000 0x04040200032cb800 0x0000000003e1c000 0x00000000003e1c00

def z320 : W := mkw 0x8fbed9b3c0000000 0x08fbed9b3c000000 0x0ffcf9fbc0000000 0xd0ffcf9fbc000000

def z321 : W := mkw 0x3fff1fefbfbd7fef 0x83fff1fefbfbd7fe 0xffff1fffffffffff 0xfffff1ffffffffff

def z322 : W := mkw 0x2b60192836a0160a 0x02b60192836a0160 0x6fe008383fe00609 0xe6fe008383fe0060

def z323 : W := mkw 0x2bea1be937a93e4e 0x82bea1be937a93e4 0xeff81ffb3ff83ecd 0xfeff81ffb3ff83ec

def z324 : W := mkw 0x0414000008140000 0x0041400000814000 0x2e0400001c060000 0x82e0400001c06000

def z325 : W := mkw 0x09aa800000000000 0x009aa80000000000 0x01e3e00000000001 0x001e3e0000000000

def z326 : W := mkw 0xcdffe497fadf8000 0x0cdffe497fadf800 0x7fffe007ffffc00b 0xe7fffe007ffffc00

def z327 : W := mkw 0x849e808380000000 0x0849e80838000000 0x0018000300000000 0x0001800030000000

def z328 : W := mkw 0x82005932c0000000 0x082005932c000000 0x00000838c0000000 0x000000838c000000

def z329 : W := mkw 0x0000020801202206 0x0000002080120220 0x2000000003e02608 0x02000000003e0260

def z330 : W := mkw 0x0041665c636beb56 0xc0041665c636beb5 0xf027ee3ce3ffffff 0xaf027ee3ce3fffff

def z331 : W := mkw 0x29eb07ed33a96b46 0x829eb07ed33a96b4 0xd1fb17ff23f9f9cf 0x7d1fb17ff23f9f9c

def z332 : W := mkw 0x12cb1ec7a7097ded 0x812cb1ec7a7097de 0xd1db1fc7e319ffff 0x7d1db1fc7e319fff

def z333 : W := mkw 0x2ffe9b6837a03e0e 0x02ffe9b6837a03e0 0xeffffff83fe03e0f 0xfeffffff83fe03e0

def z334 : W := mkw 0x0b60192032800000 0x00b6019203280000 0xefe01ff83fe0000d 0xfefe01ff83fe0000

def z335 : W := mkw 0x0960200032c28000 0x00960200032c2800 0x7fe7e0003fe7c00b 0xe7fe7e0003fe7c00

def z336 : W := mkw 0x008b669d416be356 0xc008b669d416be35 0xb03fee3fc3ffe7ff 0xab03fee3fc3ffe7f

def z337 : W := mkw 0x8f35dd36c0000000 0x08f35dd36c000000 0x8e27ee3cc0000007 0xa8e27ee3cc000000

def z338 : W := mkw 0x0000000000000000 0x0000000000000000 0x0027e00000000003 0xa0027e0000000000

def z339 : W := mkw 0x404020003adf8000 0x0404020003adf800 0x700000003fffc008 0x0700000003fffc00

def z340 : W := mkw 0x100000000c1414a9 0x0100000000c1414a 0x701810073c1e3ffe 0x7701810073c1e3ff

def z341 : W := mkw 0x00ca00c122090840 0x800ca00c12209084 0x51db11c32319d8cb 0x751db11c32319d8c

def z342 : W := mkw 0x000166144142e114 0x4000166144142e11 0x9007e604c307e13f 0x29007e604c307e13

def z343 : W := mkw 0xcffe99a3ba9d0000 0x0cffe99a3ba9d000 0x4fd811c33c180000 0x54fd811c33c18000

def z344 : W := mkw 0x0414000000000000 0x0041400000000000 0x0e1c000000000002 0xe0e1c00000000000

def z345 : W := mkw 0x849fe69fc162e316 0x4849fe69fc162e31 0xb03fee3fc3e7e73f 0xab03fee3fc3e7e73

def z346 : W := mkw 0x169f1c878c1d55e9 0x8169f1c878c1d55e 0x7e1f1807fc1ffffe 0xf7e1f1807fc1ffff

def z347 : W := mkw 0x9f34d932cc1414a9 0x09f34d932cc1414a 0x7e3cf83ffc1e3ffe 0xf7e3cf83ffc1e3ff

def z348 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x7e1c10033c1e18ca 0xf7e1c10033c1e18c

def z349 : W := mkw 0xcffef932fadf8000 0x0cffef932fadf800 0x7fffe838ffffc00b 0xe7fffe838ffffc00

def z350 : W := mkw 0x0001060401006104 0x0000106040100610 0x800306000301c001 0x0800306000301c00

def z351 : W := mkw 0x12001802840014a9 0x012001802840014a 0x30041807c0063ffe 0xb30041807c0063ff

def z352 : W := mkw 0x9fbe99a38c1414a9 0x09fbe99a38c1414a 0x7fdc19c7fc1e3ffe 0xf7fdc19c7fc1e3ff

def z353 : W := mkw 0x404022403bdfe944 0x8404022403bdfe94 0x700000003ffff9c8 0x0700000003ffff9c

def z354 : W := mkw 0xcffffdb7f2cb8000 0x0cffffdb7f2cb800 0x8fffffffc3e1c007 0xf8fffffffc3e1c00

def z355 : W := mkw 0x0200192000000000 0x0020019200000000 0x80001ff800000004 0x180001ff80000000

def z356 : W := mkw 0x0000601040428010 0x4000060104042801 0x0004e000c0060030 0x00004e000c006003

def z357 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0x6fc011c03fe03e08 0x56fc011c03fe03e0

def z358 : W := mkw 0x4d34e01858f68212 0x44d34e01858f6821 0x2e24e838dce60630 0x82e24e838dce6063

def z359 : W := mkw 0x100000000c1414a9 0x0100000000c1414a 0x70040804fc1e3ffe 0xa70040804fc1e3ff

def z360 : W := mkw 0x5f34b8029cd694a9 0x05f34b8029cd694a 0x7e3cf807fcfe3ffe 0xf7e3cf807fcfe3ff

def z361 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x7e1810033c1e3ff8 0x57e1810033c1e3ff

def z362 : W := mkw 0x8f35ddb7c0000000 0x08f35ddb7c000000 0x8e24ffffc0000004 0x98e24ffffc000000

def z363 : W := mkw 0x008b048500094140 0x8008b04850009414 0x501b10072019f9ce 0x7501b10072019f9c

def z364 : W := mkw 0x0b60180036801408 0x00b6018003680140 0x6fe018003fe03e0d 0xf6fe018003fe03e0

def z365 : W := mkw 0x22401b6837a03e0e 0x022401b6837a03e0 0xe0001ff83fe03e0c 0x1e0001ff83fe03e0

def z366 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x4ffbe0003ff9c001 0x44ffbe0003ff9c00

def z367 : W := mkw 0xafffdffff3a02a06 0x0afffdffff3a02a0 0x8fffffffc3e00007 0xf8fffffffc3e0000

def z368 : W := mkw 0xaffe9bebb7a03e0e 0x0affe9bebb7a03e0 0xeff81ffb3fe03e0d 0xfeff81ffb3fe03e0

def z369 : W := mkw 0x008a000000090000 0x0008a00000009000 0x101b00000019c002 0x0101b00000019c00

def z370 : W := mkw 0xcfbffdb7d8d68000 0x0cfbffdb7d8d6800 0xafffffffdce60007 0xfafffffffdce6000

def z371 : W := mkw 0x0041064423096944 0x8004106442309694 0xd00306042319f9cf 0x2d00306042319f9c

def z372 : W := mkw 0x0200180004001408 0x0020018000400140 0x0000180000003e04 0x10000180000003e0

def z373 : W := mkw 0x9fbfddb7c81400a1 0x09fbfddb7c81400a 0x9fffffffc01e01f7 0xf9fffffffc01e01f

def z374 : W := mkw 0x2b601b6833a02a06 0x02b601b6833a02a0 0x8fe01ff803e00005 0xf8fe01ff803e0000

def z375 : W := mkw 0x6dfea2483fffbe0e 0x06dfea2483fffbe0 0x7fffe0003ffffe0b 0xe7fffe0003ffffe0

def z376 : W := mkw 0x16157c16cc56d5b9 0x416157c16cc56d5b 0x7e1ff807fc1ffffe 0xf7e1ff807fc1ffff

def z377 : W := mkw 0x00cb46d563096944 0x800cb46d56309694 0xd1ffffffe319f9cf 0xfd1ffffffe319f9c

def z378 : W := mkw 0x0614180280000000 0x0061418028000000 0x3e1c1807c006273e 0xf3e1c1807c006273

def z379 : W := mkw 0x2bea1b6837a93e0e 0x02bea1b6837a93e0 0xfffb1ff83ff9fe0f 0xffffb1ff83ff9fe0

def z380 : W := mkw 0x000166dd4162eb56 0xc000166dd4162eb5 0xb027ffffc3e7ffff 0xbb027ffffc3e7fff

def z381 : W := mkw 0x0001060401006104 0x0000106040100610 0xd01b16072319f9cf 0x7d01b16072319f9c

def z382 : W := mkw 0x0001461c41206316 0x40001461c4120631 0x90030e3cc301e73f 0x290030e3cc301e73

def z383 : W := mkw 0x4041661c7bffe316 0x44041661c7bffe31 0xf027ee3cffffe73f 0xaf027ee3cffffe73

def z384 : W := mkw 0x2f741b6ab7a03e0e 0x02f741b6ab7a03e0 0xeffc1fffffe03e0f 0xfeffc1fffffe03e0

def z385 : W := mkw 0x0960000032800000 0x0096000003280000 0x01e0000003e00001 0x001e0000003e0000

def z386 : W := mkw 0x0001048500004140 0x8000104850000414 0x00000007000001c0 0x000000007000001c

def z387 : W := mkw 0x0040024023096944 0x8004002402309694 0x000000000301c000 0x0000000000301c00

def z388 : W := mkw 0x4dfee0187aff8212 0x44dfee0187aff821 0x7fffe838ffffc63b 0xe7fffe838ffffc63

def z389 : W := mkw 0x0000401840200212 0x4000040184020021 0x00000838c0000630 0x000000838c000063

def z390 : W := mkw 0x8b215db7c0000000 0x08b215db7c000000 0x8fe01fffc0000005 0xf8fe01fffc000000

def z391 : W := mkw 0x16541a42af143cad 0x016541a42af143ca 0xffdc1fc7ff1e3fff 0xfffdc1fc7ff1e3ff

def z392 : W := mkw 0x0614180284001408 0x0061418028400140 0x6e1c1807fc003e0e 0xf6e1c1807fc003e0

def z393 : W := mkw 0x2b60196836a01e0a 0x02b60196836a01e0 0x6fe019f83ce01e00 0xd6fe019f83ce01e0

def z394 : W := mkw 0x0000020001002004 0x0000002000100200 0x800006000300200d 0x2800006000300200

def z395 : W := mkw 0x0000200000428000 0x0000020000042800 0x1007e0000007c002 0x01007e0000007c00

def z396 : W := mkw 0x0000024001002804 0x0000002400100280 0x800017c000003804 0x1800017c00000380

def z397 : W := mkw 0x008b068501006104 0x0008b06850100610 0x91db17c70301e10f 0x791db17c70301e10

def z398 : W := mkw 0x4d34800018940000 0x04d3480001894000 0x0e0000001c000000 0x00e0000001c00000

def z399 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x5e1810073c1839ce 0x75e1810073c1839c

def z400 : W := mkw 0x40ca20003adf8000 0x040ca20003adf800 0x71db00003fffc00b 0x671db00003fffc00

def z401 : W := mkw 0x8fffddb7e2090000 0x08fffddb7e209000 0xdfffffffe319c00f 0xfdfffffffe319c00

def z402 : W := mkw 0x2b20192814a0160a 0x02b20192814a0160 0xafe01ff81ce00605 0xfafe01ff81ce0060

def z403 : W := mkw 0x36141b6a8d343eaf 0x036141b6a8d343ea 0xfe1c1ffffc1e3ffe 0xffe1c1ffffc1e3ff

def z404 : W := mkw 0x008b048500094140 0x8008b04850009414 0x91db17c70019c1c7 0x791db17c70019c1c

def z405 : W := mkw 0x49eaa00032cb8000 0x049eaa00032cb800 0x31e7e00003e7c00b 0xa31e7e00003e7c00

def z406 : W := mkw 0x0000000000000000 0x0000000000000000 0x6e0000003c000008 0xe6e0000003c00000

def z407 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0xa024ee3cc0e62734 0x8a024ee3cc0e6273

def z408 : W := mkw 0x449ea000085f8000 0x0449ea000085f800 0x7e1fe0003c1fc00a 0xe7e1fe0003c1fc00

def z409 : W := mkw 0x49eba6c533cbe944 0x849eba6c533cbe94 0xd1fbf7c723f9f9cf 0x7d1fbf7c723f9f9c

def z410 : W := mkw 0x10000002800000a1 0x010000002800000a 0x00000007c00001f0 0x000000007c00001f

def z411 : W := mkw 0x22401a4837a03e0e 0x022401a4837a03e0 0x6e0018003fe03e0c 0xf6e0018003fe03e0

def z412 : W := mkw 0x00cb06c523002804 0x000cb06c52300280 0xc1db17c72300380f 0x7c1db17c72300380

def z413 : W := mkw 0x0414000280000000 0x0041400028000000 0x001c0007c0000002 0x0001c0007c000000

def z414 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0x8027ee3cc3e1c007 0xa8027ee3cc3e1c00

def z415 : W := mkw 0x20cb06cd37a97f4e 0x820cb06cd37a97f4 0xf1db17c73ff9ffcf 0x7f1db17c73ff9ffc

def z416 : W := mkw 0x00cb04c522090840 0x800cb04c52209084 0xc1db17c7201818c7 0x7c1db17c7201818c

def z417 : W := mkw 0x5dfea002badf80a1 0x05dfea002badf80a 0x7fffe007ffffc1fb 0xe7fffe007ffffc1f

def z418 : W := mkw 0x9f34d932cc1414a9 0x09f34d932cc1414a 0x2e24e838dc060630 0x82e24e838dc06063

def z419 : W := mkw 0x14156416c856c1b1 0x414156416c856c1b 0x101fe007c01fc1f2 0x0101fe007c01fc1f

def z420 : W := mkw 0x2960016032800800 0x0296001603280080 0x01c001c000000000 0x001c001c00000000

def z421 : W := mkw 0x2b617f7c77e2ff1e 0x42b617f7c77e2ff1 0xefe3fff83fe1fe0d 0xfefe3fff83fe1fe0

def z422 : W := mkw 0x0001060401006104 0x0000106040100610 0xb0070e04c307e73f 0xab0070e04c307e73

def z423 : W := mkw 0x12011ec785007ded 0x812011ec785007de 0x80001fc7c0003ff4 0x180001fc7c0003ff

def z424 : W := mkw 0x22011fed05207f4e 0x822011fed05207f4 0x80001fff00003fc4 0x180001fff00003fc

def z425 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xc1c317c02301f80d 0x7c1c317c02301f80

def z426 : W := mkw 0x6dfea3683bffaa06 0x06dfea3683bffaa0 0xffffe7f83fffc00b 0xeffffe7f83fffc00

def z427 : W := mkw 0x2960024837a03e0e 0x02960024837a03e0 0x6fe000003fe03e09 0xe6fe000003fe03e0

def z428 : W := mkw 0x1415661ec976e3b7 0x41415661ec976e3b 0xb03fee3fc3ffe7ff 0xab03fee3fc3ffe7f

def z429 : W := mkw 0x9fffdff7ef1d7ded 0x89fffdff7ef1d7de 0xffffffffff1fffff 0xfffffffffff1ffff

def z430 : W := mkw 0xc9ebe5b572cb8000 0x0c9ebe5b572cb800 0x81e3e7f803e1c001 0x081e3e7f803e1c00

def z431 : W := mkw 0x2040024837a03e0e 0x02040024837a03e0 0xe0200e383fe03e0d 0xae0200e383fe03e0

def z432 : W := mkw 0x00cb66dd636beb56 0xc00cb66dd636beb5 0xb1e7effcc3e7e73f 0xab1e7effcc3e7e73

def z433 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0x9023e63c03e1e10f 0x29023e63c03e1e10

def z434 : W := mkw 0x16541a42af1d7ded 0x816541a42af1d7de 0x7e1c1807ff1ffffe 0xf7e1c1807ff1ffff

def z435 : W := mkw 0x4dfe80003a9d0000 0x04dfe80003a9d000 0x6ff800003ff80009 0xe6ff800003ff8000

def z436 : W := mkw 0x16155e1ecd3477bf 0x416155e1ecd3477b 0xfe1c1e3ffc1e3ffe 0xffe1c1e3ffc1e3ff

def z437 : W := mkw 0x0920000000000000 0x0092000000000000 0x0fe0000000000001 0xe0fe000000000000

def z438 : W := mkw 0xa9ebc7fd73a02a06 0x0a9ebc7fd73a02a0 0x81e3e7f803e00001 0x081e3e7f803e0000

def z439 : W := mkw 0x8fbf9da780000000 0x08fbf9da78000000 0x8fdb17c700000007 0x78fdb17c70000000

def z440 : W := mkw 0x12017e1ec562f7bf 0x412017e1ec562f7b 0xb027fe3fc3e7ffff 0xbb027fe3fc3e7fff

def z441 : W := mkw 0x0000601840628212 0x4000060184062821 0x0020e03800e00000 0x00020e03800e0000

def z442 : W := mkw 0x09ea000032890000 0x009ea00003289000 0x7ffb00003ff9c00b 0xe7ffb00003ff9c00

def z443 : W := mkw 0x14140002881400a1 0x014140002881400a 0x501c1007e01e39fe 0x7501c1007e01e39f

def z444 : W := mkw 0x69eaa36833ebaa06 0x069eaa36833ebaa0 0x81e3e7f803e1c001 0x081e3e7f803e1c00

def z445 : W := mkw 0x6f74bb683ff6be0e 0x06f74bb683ff6be0 0xefe4fff83fe63e0d 0xfefe4fff83fe63e0

def z446 : W := mkw 0x000062184162e316 0x4000062184162e31 0x3024e838c3e7e738 0x83024e838c3e7e73

def z447 : W := mkw 0x000022080162e316 0x4000022080162e31 0xb0200e3803e7e73d 0xab0200e3803e7e73

def z448 : W := mkw 0x0000020801206316 0x4000002080120631 0x0000000000002730 0x0000000000000273

def z449 : W := mkw 0x1001661c4d76f7bf 0x41001661c4d76f7b 0xf027ee3cffffffff 0xaf027ee3cfffffff

def z450 : W := mkw 0x6f34b9281cf6960a 0x06f34b9281cf6960 0x2e24e8381ce60600 0x82e24e8381ce6060

def z451 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000000000062738 0x0300000000006273

def z452 : W := mkw 0x2beb1fed37a97f4e 0x82beb1fed37a97f4 0xefe31ff83fe1fe0d 0xfefe31ff83fe1fe0

def z453 : W := mkw 0x0200180004001408 0x0020018000400140 0x2e0008001c000600 0x82e0008001c00060

def z454 : W := mkw 0x2beb1fed37a03e0e 0x02beb1fed37a03e0 0xeffb1fff3fe03e0f 0xfeffb1fff3fe03e0

def z455 : W := mkw 0x4dffa6043bdfe104 0x04dffa6043bdfe10 0xffffe6043fffe10f 0xeffffe6043fffe10

def z456 : W := mkw 0x2000036801202a06 0x02000036801202a0 0x800007f800000000 0x0800007f80000000

def z457 : W := mkw 0x3f741962be941ca9 0x03f741962be941ca 0x7fdc19c7fc1e3ffe 0xf7fdc19c7fc1e3ff

def z458 : W := mkw 0xcfffffbffbffe316 0x4cfffffbffbffe31 0xffffffffffffe73f 0xfffffffffffffe73

def z459 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x6e041800fc063e3c 0xf6e041800fc063e3

def z460 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x11ffe00003ffc003 0x011ffe00003ffc00

def z461 : W := mkw 0x808bc49540000000 0x0808bc4954000000 0x0003e00000000000 0x00003e0000000000

def z462 : W := mkw 0x0040024023096944 0x8004002402309694 0x501810072319f9ce 0x7501810072319f9c

def z463 : W := mkw 0x0001441440004110 0x4000144144000411 0x00000004c0000130 0x000000004c000013

def z464 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0xa027ee38c3e7c631 0x8a027ee38c3e7c63

def z465 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7ffff0073ffff9cf 0xf7ffff0073ffff9c

def z466 : W := mkw 0x04df06c52b1d6944 0x804df06c52b1d694 0xffdf17c73f1ff9cf 0xfffdf17c73f1ff9c

def z467 : W := mkw 0x0001461c41206316 0x40001461c4120631 0xa0200e3cc3e0273d 0xaa0200e3cc3e0273

def z468 : W := mkw 0x4dfea00032cb8000 0x04dfea00032cb800 0x0fffe00003e1c003 0xe0fffe00003e1c00

def z469 : W := mkw 0x96155db7cc1414a9 0x096155db7cc1414a 0xfe1c1ffffc1e3ffe 0xffe1c1ffffc1e3ff

def z470 : W := mkw 0x0040024823202a06 0x00040024823202a0 0xe1e01ff823e03e0d 0xfe1e01ff823e03e0

def z471 : W := mkw 0x4414a00008568000 0x04414a0000856800 0x0004e00000060000 0x00004e0000006000

def z472 : W := mkw 0x8fffddf7e2090840 0x88fffddf7e209084 0xcfffffffe01818c7 0xfcfffffffe01818c

def z473 : W := mkw 0x000126040142e104 0x0000126040142e10 0xb027e60403e7e10f 0xab027e60403e7e10

def z474 : W := mkw 0x000106c501006944 0x8000106c50100694 0x900317c70301f9cf 0x3900317c70301f9c

def z475 : W := mkw 0x0000000000000000 0x0000000000000000 0x81c017c000000005 0x781c017c00000000

def z476 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x2e041807dc063ff4 0x92e041807dc063ff

def z477 : W := mkw 0x008a000000000000 0x0008a00000000000 0x01db000000000003 0x601db00000000000

def z478 : W := mkw 0x449ea000085f8000 0x0449ea000085f800 0x303fe00003ffc00b 0xa303fe00003ffc00

def z479 : W := mkw 0x00cb46dd63296b56 0xc00cb46dd63296b5 0xd1db1fffe319ffff 0x7d1db1fffe319fff

def z480 : W := mkw 0x00ca000022090000 0x000ca00002209000 0x41d8000020180000 0x441d800002018000

def z481 : W := mkw 0x14140002881400a1 0x014140002881400a 0x00040000c0060030 0x000040000c006003

def z482 : W := mkw 0x8dbfc5b540000000 0x08dbfc5b54000000 0x8fffe7f800000003 0xe8fffe7f80000000

def z483 : W := mkw 0x00ca00c122090840 0x800ca00c12209084 0x01c001c000000000 0x001c001c00000000

def z484 : W := mkw 0x449fa485085fc140 0x8449fa485085fc14 0x101fe007001fc1c2 0x0101fe007001fc1c

def z485 : W := mkw 0x44dfa6c52b5fe944 0x844dfa6c52b5fe94 0xd1dff7c7231ff9cf 0x7d1dff7c7231ff9c

def z486 : W := mkw 0x2b607b7877e2be1e 0x42b607b7877e2be1 0xefe4fff8ffe63e3d 0xfefe4fff8ffe63e3

def z487 : W := mkw 0x000000c100000840 0x8000000c10000084 0x000011c3000018c0 0x1000011c3000018c

def z488 : W := mkw 0x14140002881400a1 0x014140002881400a 0x301c0807c01e27fe 0xa301c0807c01e27f

def z489 : W := mkw 0x4dffa4853adfc140 0x84dffa4853adfc14 0x7fffe0073fffc1cb 0xe7fffe0073fffc1c

def z490 : W := mkw 0x0000200000428000 0x0000020000042800 0x3027e804c3e7e73f 0xa3027e804c3e7e73

def z491 : W := mkw 0xdffffdb7fedf94a9 0x0dffffdb7fedf94a 0xffffffffffffffff 0xffffffffffffffff

def z492 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0xb023e63803e7e739 0x0b023e63803e7e73

def z493 : W := mkw 0x4d74a0003adf8000 0x04d74a0003adf800 0x7e24e0003fffc008 0x87e24e0003fffc00

def z494 : W := mkw 0x10000000040014a9 0x010000000040014a 0x0000000000003ff0 0x00000000000003ff

def z495 : W := mkw 0x8f34992280000000 0x08f3499228000000 0x0e00000000000000 0x00e0000000000000

def z496 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xfff81fff3ff83fcf 0xffff81fff3ff83fc

def z497 : W := mkw 0x2041665c77e2ff1e 0x42041665c77e2ff1 0xf027ee3cffe7ff3f 0xaf027ee3cffe7ff3

def z498 : W := mkw 0x6ffe99603e9d1c08 0x06ffe99603e9d1c0 0x4fd811c03c181800 0x54fd811c03c18180

def z499 : W := mkw 0x2beb7ffd77ebff5e 0xc2beb7ffd77ebff5 0xffffffffffffffff 0xffffffffffffffff

def z500 : W := mkw 0x00ca000022090000 0x000ca00002209000 0x01c300000301c001 0x001c300000301c00

def z501 : W := mkw 0x0bab1da500000000 0x00bab1da50000000 0x8ffb1fff00000007 0xf8ffb1fff0000000

def z502 : W := mkw 0x949fc497c81400a1 0x0949fc497c81400a 0x101fe007c01e01f2 0x0101fe007c01e01f

def z503 : W := mkw 0x00ca024023092804 0x000ca02402309280 0xd1db17c02319f80f 0x7d1db17c02319f80

def z504 : W := mkw 0x8dbfc497c0000000 0x08dbfc497c000000 0x0fffe007c0000003 0xe0fffe007c000000

def z505 : W := mkw 0x16141802840014a9 0x016141802840014a 0x0e1c1807c0003ff6 0xf0e1c1807c0003ff

def z506 : W := mkw 0x89aa81a100000000 0x089aa81a10000000 0x01c001c000000000 0x001c001c00000000

def z507 : W := mkw 0x404022083bffe316 0x4404022083bffe31 0x700000003fffe738 0x0700000003fffe73

def z508 : W := mkw 0x0b20192000000000 0x00b2019200000000 0x0e20083800000000 0x80e2008380000000

def z509 : W := mkw 0x10000000081400a1 0x010000000081400a 0x10000000001e01f0 0x010000000001e01f

def z510 : W := mkw 0x0001040400004100 0x0000104040000410 0x100300040001c102 0x0100300040001c10

def z511 : W := mkw 0x0041665c6362eb16 0x40041665c6362eb1 0xf1e7fffce3e7ff3f 0xff1e7fffce3e7ff3

def z512 : W := mkw 0x0414000008140000 0x0041400000814000 0x101c0000001e0002 0x0101c0000001e000

def z513 : W := mkw 0x0001060c01206306 0x00001060c0120630 0xb0230e3c03e1e70f 0xab0230e3c03e1e70

def z514 : W := mkw 0x008b669d4162e316 0x4008b669d4162e31 0xb1ffffffc3e7e73f 0xfb1ffffffc3e7e73

def z515 : W := mkw 0x000062184162a216 0x4000062184162a21 0xa024ee38c3e6263d 0xaa024ee38c3e6263

def z516 : W := mkw 0x8f35ff3ec162e316 0x48f35ff3ec162e31 0xbe27ee3cc3e7e73f 0xabe27ee3cc3e7e73

def z517 : W := mkw 0x16141802881400a1 0x016141802881400a 0x1e1c1807c01e01f6 0xf1e1c1807c01e01f

def z518 : W := mkw 0x0dbe800008140000 0x00dbe80000814000 0x7fffe0003c1e000b 0xe7fffe0003c1e000

def z519 : W := mkw 0x40002000085f8000 0x040002000085f800 0x10000000001fc000 0x010000000001fc00

def z520 : W := mkw 0x1f3419228c1414a9 0x01f3419228c1414a 0xfffc1ffffc1e3fff 0xffffc1ffffc1e3ff

def z521 : W := mkw 0x2b201b6805203e0e 0x02b201b6805203e0 0x8fe01ff800003e05 0xf8fe01ff800003e0

def z522 : W := mkw 0x0000000800200202 0x0000000080020020 0x2020083800e00600 0x82020083800e0060

def z523 : W := mkw 0x8fbffdb7c0428000 0x08fbffdb7c042800 0xbfffffffc3e7c00f 0xfbfffffffc3e7c00

def z524 : W := mkw 0x008b048500000000 0x0008b04850000000 0x81c307c000000001 0x081c307c00000000

def z525 : W := mkw 0xafffdffff7a97f4e 0x8afffdffff7a97f4 0xfffffffffff9ffcf 0xffffffffffff9ffc

def z526 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0xb0000e3cc3e7e73c 0x0b0000e3cc3e7e73

def z527 : W := mkw 0x8f34f93ac0628212 0x48f34f93ac062821 0x2e24e838c0e60630 0x82e24e838c0e6063

def z528 : W := mkw 0x4dffa6c53bdfe944 0x84dffa6c53bdfe94 0xffffe7c03fffc00b 0xeffffe7c03fffc00

def z529 : W := mkw 0x0000000008140000 0x0000000000814000 0x700000003c1e0008 0x0700000003c1e000

def z530 : W := mkw 0x10cb06c52f1d7ded 0x810cb06c52f1d7de 0xf1db17c73f1fffff 0x7f1db17c73f1ffff

def z531 : W := mkw 0x0000000000000000 0x0000000000000000 0x00040804c0000006 0xa00040804c000000

def z532 : W := mkw 0x0001461c41206316 0x40001461c4120631 0x8000063800000000 0x0800006380000000

def z533 : W := mkw 0x104002402f1d7ded 0x8104002402f1d7de 0x700000003f1ffff8 0x0700000003f1ffff

def z534 : W := mkw 0x3f741962be941ca9 0x03f741962be941ca 0x4fd811c33c1818c0 0x54fd811c33c1818c

def z535 : W := mkw 0x0000000000000000 0x0000000000000000 0x50000000201839c8 0x050000000201839c

def z536 : W := mkw 0x2960036833a02a06 0x02960036833a02a0 0xa1e00ff803e0260d 0xaa1e00ff803e0260

def z537 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x7e040800fc1e3ff8 0x87e040800fc1e3ff

def z538 : W := mkw 0x0920000010800000 0x0092000001080000 0x2e2000001ce00000 0x82e2000001ce0000

def z539 : W := mkw 0x0dbf848500000000 0x00dbf84850000000 0x8ffff7c700000007 0xf8ffff7c70000000

def z540 : W := mkw 0x80014497c0000000 0x080014497c000000 0x00000007c0000000 0x000000007c000000

def z541 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0x501b00072319f9ca 0x0501b00072319f9c

def z542 : W := mkw 0x00cb048522090000 0x000cb04852209000 0xd1db17c72319c00f 0x7d1db17c72319c00

def z543 : W := mkw 0x0d34800000000000 0x00d3480000000000 0x0e24e00000000000 0x80e24e0000000000

def z544 : W := mkw 0x6ffeb9283eff960a 0x06ffeb9283eff960 0x7fffe8383fffc60b 0xe7fffe8383fffc60

def z545 : W := mkw 0x4dfea2403bdfe944 0x84dfea2403bdfe94 0x7fffe0003ffff9cb 0xe7fffe0003ffff9c

def z546 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xd1db07c02319c00b 0x6d1db07c02319c00

def z547 : W := mkw 0x0000000000000000 0x0000000000000000 0x40181003201818c0 0x540181003201818c

def z548 : W := mkw 0x0414000008140000 0x0041400000814000 0x4e1800003c180000 0x44e1800003c18000

def z549 : W := mkw 0x3f34192a9cb416ab 0x03f34192a9cb416a 0x7e3c183ffcfe3ffe 0xf7e3c183ffcfe3ff

def z550 : W := mkw 0x12001802840014a9 0x012001802840014a 0x6e001807fc003ffc 0xf6e001807fc003ff

def z551 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x5fdfe0003c1fc002 0x45fdfe0003c1fc00

def z552 : W := mkw 0xcf34f932d8d68000 0x0cf34f932d8d6800 0x2e24e838dce60000 0x82e24e838dce6000

def z553 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0x6e2008383fe03e08 0x86e2008383fe03e0

def z554 : W := mkw 0x0961661c73e2e316 0x40961661c73e2e31 0xffe7ee3cffe7e73f 0xeffe7ee3cffe7e73

def z555 : W := mkw 0xa2015fffc5203e0e 0x0a2015fffc5203e0 0x80001fffc0003e04 0x180001fffc0003e0

def z556 : W := mkw 0x0000000000000000 0x0000000000000000 0x100000040000210e 0x2100000040000210

def z557 : W := mkw 0x0041064423006904 0x0004106442300690 0xd1c317c42301f90f 0x7d1c317c42301f90

def z558 : W := mkw 0x8fbfdfb7c1006104 0x08fbfdfb7c100610 0x9fffffffc301e10f 0xf9fffffffc301e10

def z559 : W := mkw 0x000022080162a206 0x0000022080162a20 0xb027ee3803e7e60f 0xab027ee3803e7e60

def z560 : W := mkw 0xabebdffd77a03e0e 0x0abebdffd77a03e0 0xefe3fff83fe03e0d 0xfefe3fff83fe03e0

def z561 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x3e040804dc06273e 0xa3e040804dc06273

def z562 : W := mkw 0x82015db7c0000000 0x082015db7c000000 0x8027ffffc0000007 0xb8027ffffc000000

def z563 : W := mkw 0x0000000000094140 0x8000000000009414 0x100000000019c1c0 0x0100000000019c1c

def z564 : W := mkw 0x0614180288140000 0x0061418028814000 0x7e1c1807fc1e000e 0xf7e1c1807fc1e000

def z565 : W := mkw 0x00ca00c122090840 0x800ca00c12209084 0x51d811c7201839ce 0x751d811c7201839c

def z566 : W := mkw 0x0200180004001408 0x0020018000400140 0x4e0010003c001800 0x54e0010003c00180

def z567 : W := mkw 0x2b603b6837e2be0e 0x02b603b6837e2be0 0xffe7fff83fe7fe0f 0xfffe7fff83fe7fe0

def z568 : W := mkw 0x0000000000000000 0x0000000000000000 0x0018100700000006 0x7001810070000000

def z569 : W := mkw 0x16de1802ae1d14a9 0x016de1802ae1d14a 0x7fdf1807ff1fffff 0xf7fdf1807ff1ffff

def z570 : W := mkw 0x5dfea0003edf94a9 0x05dfea0003edf94a 0x7fffe0003ffffffb 0xe7fffe0003ffffff

def z571 : W := mkw 0x4dfea2083bffe316 0x44dfea2083bffe31 0x7fffe0003fffe73b 0xe7fffe0003fffe73

def z572 : W := mkw 0x02001a080520360e 0x002001a080520360 0xee201e383fe03e0d 0xfee201e383fe03e0

def z573 : W := mkw 0x0200180004001408 0x0020018000400140 0x7e1818073c183fce 0xf7e1818073c183fc

def z574 : W := mkw 0x8ffe99e3a2090840 0x88ffe99e3a209084 0x4fd811c3201818c0 0x54fd811c3201818c

def z575 : W := mkw 0x569eb8028c5f94a9 0x0569eb8028c5f94a 0x7e1ff807fc1ffffe 0xf7e1ff807fc1ffff

def z576 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0xf03ffe3fe3ffffff 0xff03ffe3fe3fffff

def z577 : W := mkw 0xaf74db7af7a03e0e 0x0af74db7af7a03e0 0xefe4fff8ffe03e0d 0xfefe4fff8ffe03e0

def z578 : W := mkw 0x0001641440428000 0x0000164144042800 0xb027ee3cc3e7c00f 0xab027ee3cc3e7c00

def z579 : W := mkw 0x0001040400000000 0x0000104040000000 0x8003060400000007 0x2800306040000000

def z580 : W := mkw 0x0001441440000000 0x0000144144000000 0x0007e004c0000002 0x00007e004c000000

def z581 : W := mkw 0x0dbe800000000000 0x00dbe80000000000 0x0fd8000000000000 0x40fd800000000000

def z582 : W := mkw 0x6ffeb9603edf9c08 0x06ffeb9603edf9c0 0x7ffff1c03fffd80b 0xf7ffff1c03fffd80

def z583 : W := mkw 0x0b20192000000000 0x00b2019200000000 0x0fc011c000000000 0x50fc011c00000000

def z584 : W := mkw 0x0001461c41202206 0x00001461c4120220 0xa027ee3cc3e0260f 0xaa027ee3cc3e0260

def z585 : W := mkw 0x4000200018d68000 0x04000200018d6800 0x200000001ce60000 0x0200000001ce6000

def z586 : W := mkw 0x0b201b2801202206 0x00b201b280120220 0xafe01ff803e0260d 0xfafe01ff803e0260

def z587 : W := mkw 0x6fffbfed3fffff4e 0x86fffbfed3fffff4 0xffffffff3fffffcf 0xfffffffff3fffffc

def z588 : W := mkw 0x0001461441006104 0x0000146144100610 0x9027ee3cc301e10f 0xa9027ee3cc301e10

def z589 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0x91db07c70319c1c3 0x091db07c70319c1c

def z590 : W := mkw 0x00ca000022090000 0x000ca00002209000 0x51db10072319f9cf 0x751db10072319f9c

def z591 : W := mkw 0x0040024023002804 0x0004002402300280 0x4000000023003808 0x0400000002300380

def z592 : W := mkw 0x0f34192280000000 0x00f3419228000000 0x8ffc1fffc0000007 0xf8ffc1fffc000000

def z593 : W := mkw 0x8fffddb7f2800000 0x08fffddb7f280000 0xefffffffffe0000f 0xfefffffffffe0000

def z594 : W := mkw 0x32001b6a85203eaf 0x032001b6a85203ea 0x80001fffc0003ff4 0x180001fffc0003ff

def z595 : W := mkw 0x0000000000000000 0x0000000000000000 0x20040800c0060630 0x820040800c006063

def z596 : W := mkw 0x0040004022090840 0x8004000402209084 0x40000000201818c0 0x040000000201818c

def z597 : W := mkw 0x4dffe4147adfc110 0x44dffe4147adfc11 0x7fffe004ffffc13b 0xe7fffe004ffffc13

def z598 : W := mkw 0x0040000032800000 0x0004000003280000 0x600000003fe00008 0x0600000003fe0000

def z599 : W := mkw 0x008a008100090040 0x8008a00810009004 0x00180003001800c0 0x000180003001800c

def z600 : W := mkw 0x149f0487881d41e1 0x8149f0487881d41e 0x101f0007c01fc1f2 0x0101f0007c01fc1f

def z601 : W := mkw 0x408aa000004b8000 0x0408aa000004b800 0x0003e0000001c000 0x00003e0000001c00

def z602 : W := mkw 0x0000401040000000 0x0000040104000000 0x0024e838c0000000 0x80024e838c000000

def z603 : W := mkw 0xcffeb9a3badf8000 0x0cffeb9a3badf800 0x7ffff1c33fffc00b 0xf7ffff1c33fffc00

def z604 : W := mkw 0x4dffe61c7bffe316 0x44dffe61c7bffe31 0xffffe6383fffc00b 0xeffffe6383fffc00

def z605 : W := mkw 0x00cb26c5234be944 0x800cb26c5234be94 0xf1fff7c723fff9cf 0xff1fff7c723fff9c

def z606 : W := mkw 0x869fdc97c0000000 0x0869fdc97c000000 0x0e1ff807c0000006 0xf0e1ff807c000000

def z607 : W := mkw 0x504020003edf94a9 0x0504020003edf94a 0x700000003ffffff8 0x0700000003ffffff

def z608 : W := mkw 0x0001461c41206316 0x40001461c4120631 0xb0040e3cc006273e 0xab0040e3cc006273

def z609 : W := mkw 0x89abe7bd4162e316 0x489abe7bd4162e31 0x81e3e7f803e1c001 0x081e3e7f803e1c00

def z610 : W := mkw 0x2961677c73e2eb16 0x42961677c73e2eb1 0xb1e7effcc3e7e73f 0xab1e7effcc3e7e73

def z611 : W := mkw 0x00cb66d5634be954 0xc00cb66d5634be95 0xd1dff7c7e31ff9ff 0x7d1dff7c7e31ff9f

def z612 : W := mkw 0x800145b540000000 0x0800145b54000000 0x800007f800000000 0x0800007f80000000

def z613 : W := mkw 0x0000000000000000 0x0000000000000000 0x100300000301c00b 0x2100300000301c00

def z614 : W := mkw 0x0000000000000000 0x0000000000000000 0x701c1807e01e3ffe 0xf701c1807e01e3ff

def z615 : W := mkw 0x2b603b6837e2ff1e 0x42b603b6837e2ff1 0xffe01ff83fe7ff3d 0xfffe01ff83fe7ff3

def z616 : W := mkw 0xab615ffff7a03e0e 0x0ab615ffff7a03e0 0xefe01fffffe03e0d 0xfefe01fffffe03e0

def z617 : W := mkw 0x000164144042c110 0x4000164144042c11 0x0003e0000001c000 0x00003e0000001c00

def z618 : W := mkw 0x8fbe99a380000000 0x08fbe99a38000000 0x8ff81ffb00000005 0xf8ff81ffb0000000

def z619 : W := mkw 0x000106c501006944 0x8000106c50100694 0x800007c000000000 0x0800007c00000000

def z620 : W := mkw 0x12001802840014a9 0x012001802840014a 0x00000800c0000630 0x000000800c000063

def z621 : W := mkw 0x2b601b6837a97f4e 0x82b601b6837a97f4 0xffe01ff83ff9ffcd 0xfffe01ff83ff9ffc

def z622 : W := mkw 0x004106c523006944 0x8004106c52300694 0xc1c017c7230039cd 0x7c1c017c7230039c

def z623 : W := mkw 0x2b20192814a0160a 0x02b20192814a0160 0x6e2018383ce03e0c 0xf6e2018383ce03e0

def z624 : W := mkw 0x4dfe80c13a9d0840 0x84dfe80c13a9d084 0x4fd811c33c1818c0 0x54fd811c33c1818c

def z625 : W := mkw 0x2b611fed37a07f4e 0x82b611fed37a07f4 0xefe01fff3fe03fcd 0xfefe01fff3fe03fc

def z626 : W := mkw 0x3b601b683fb43eaf 0x03b601b683fb43ea 0xffe01ff83ffe3ffd 0xfffe01ff83ffe3ff

def z627 : W := mkw 0x4dfe80003a9d0000 0x04dfe80003a9d000 0x7fdc00003c1e000a 0xe7fdc00003c1e000

def z628 : W := mkw 0x8fbfdfbfc1202206 0x08fbfdfbfc120220 0xafffffffc3e0260f 0xfafffffffc3e0260

def z629 : W := mkw 0x449fe414485fc110 0x4449fe414485fc11 0x101fe004c01fc132 0x0101fe004c01fc13

def z630 : W := mkw 0x0000024001006944 0x8000002400100694 0x00000000000039c0 0x000000000000039c

def z631 : W := mkw 0x008b6495404bc150 0xc008b6495404bc15 0x101fe007c01fc1f2 0x0101fe007c01fc1f

def z632 : W := mkw 0x2b20192014801408 0x02b2019201480140 0x0e0000001c000000 0x00e0000001c00000

def z633 : W := mkw 0x2b601b6037803c0c 0x02b601b6037803c0 0xcfc017c03f00380d 0x7cfc017c03f00380

def z634 : W := mkw 0x404000003a9d0000 0x0404000003a9d000 0x400000003c180000 0x0400000003c18000

def z635 : W := mkw 0x8fff9fe7a3096944 0x88fff9fe7a309694 0xdfdb17c72319f9cf 0x7dfdb17c72319f9c

def z636 : W := mkw 0x0040024023002804 0x0004002402300280 0x81c007c003000001 0x081c007c00300000

def z637 : W := mkw 0x0001641c4062c312 0x40001641c4062c31 0x3027e83cc0e7c732 0x83027e83cc0e7c73

def z638 : W := mkw 0x2200196004001c08 0x02200196004001c0 0x000011c000001800 0x1000011c00000180

def z639 : W := mkw 0x0000000000000000 0x0000000000000000 0x10180007001801c2 0x010180007001801c

def z640 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0x8023ee3cc3e1e735 0x08023ee3cc3e1e73

def z641 : W := mkw 0xcfbffdb7c85f8000 0x0cfbffdb7c85f800 0x9fffffffc01fc007 0xf9fffffffc01fc00

def z642 : W := mkw 0x0dbfc41440000000 0x00dbfc4144000000 0x8fffee3cc0000007 0xe8fffee3cc000000

def z643 : W := mkw 0x4d74a0003ad68000 0x04d74a0003ad6800 0x6fe4e0003fe60009 0xe6fe4e0003fe6000

def z644 : W := mkw 0x449fe61c497fe316 0x4449fe61c497fe31 0xb03fee3cc3ffe73f 0xab03fee3cc3ffe73

def z645 : W := mkw 0x14df06c7ab1d69e5 0x814df06c7ab1d69e 0xd1df17c7e31ff9ff 0x7d1df17c7e31ff9f

def z646 : W := mkw 0x000022080162e316 0x4000022080162e31 0x3027e00003e7e73b 0xa3027e00003e7e73

def z647 : W := mkw 0x8fbe99a380000000 0x08fbe99a38000000 0x0fdc19c7c0000006 0xf0fdc19c7c000000

def z648 : W := mkw 0x000106c501006944 0x8000106c50100694 0xd01817c7201839ce 0x7d01817c7201839c

def z649 : W := mkw 0x120018000c1414a9 0x0120018000c1414a 0x7e0018003c1e3ffc 0xf7e0018003c1e3ff

def z650 : W := mkw 0x0000200000428000 0x0000020000042800 0x2024e00000e60000 0x82024e00000e6000

def z651 : W := mkw 0x061418000c141408 0x0061418000c14140 0x7e1c18003c1e3e0e 0xf7e1c18003c1e3e0

def z652 : W := mkw 0x2b20793854e2961a 0x42b20793854e2961 0x2e24e838dce60630 0x82e24e838dce6063

def z653 : W := mkw 0x161438028c5694a9 0x0161438028c5694a 0x7e3ff807ffffffff 0xf7e3ff807fffffff

def z654 : W := mkw 0x000164144042c110 0x4000164144042c11 0x3027e004c3e7c13b 0xa3027e004c3e7c13

def z655 : W := mkw 0x02401a4027003c0c 0x002401a4027003c0 0xefc01fc03f003e0d 0xfefc01fc03f003e0

def z656 : W := mkw 0x4d34a00018d68000 0x04d34a00018d6800 0x7e3ce0003cfe000a 0xe7e3ce0003cfe000

def z657 : W := mkw 0x0d7400003a940000 0x00d7400003a94000 0x7ffc00003ffe000b 0xe7ffc00003ffe000

def z658 : W := mkw 0x44dea0003adf8000 0x044dea0003adf800 0x701fe0003fffc00a 0x0701fe0003fffc00

def z659 : W := mkw 0x49eaa00032cb8000 0x049eaa00032cb800 0x51fbe00023f9c00b 0x651fbe00023f9c00

def z660 : W := mkw 0x2040024837a97f4e 0x82040024837a97f4 0x700000003ff9ffc8 0x0700000003ff9ffc

def z661 : W := mkw 0x89ebc7f563096944 0x889ebc7f56309694 0x81e3e7f80301c001 0x081e3e7f80301c00

def z662 : W := mkw 0x220019280420160a 0x0220019280420160 0x0000083800000600 0x0000008380000060

def z663 : W := mkw 0x22401b6827203e0e 0x022401b6827203e0 0xc1c01ff823003e0d 0x7c1c01ff823003e0

def z664 : W := mkw 0x2b60196036801c08 0x02b60196036801c0 0xcfe01ff83c001805 0xfcfe01ff83c00180

def z665 : W := mkw 0x004106c523096944 0x8004106c52309694 0xd00017c72319f9cc 0x1d00017c72319f9c

def z666 : W := mkw 0x16de18c3ae1d1ce9 0x816de18c3ae1d1ce 0x7fdc19c7fc1e3ffe 0xf7fdc19c7fc1e3ff

def z667 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fd800003fffc008 0x47fd800003fffc00

def z668 : W := mkw 0x404020003adf8000 0x0404020003adf800 0x7027e0003fffc00b 0xa7027e0003fffc00

def z669 : W := mkw 0x04de00002a1d0000 0x004de00002a1d000 0x7fdf00003f1fc00b 0xe7fdf00003f1fc00

def z670 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x101c1807c01e3ff6 0x1101c1807c01e3ff

def z671 : W := mkw 0x16151e068d1475ad 0x016151e068d1475a 0xfe1f1e07ff1fffff 0xffe1f1e07ff1ffff

def z672 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x8fd81fffc0000004 0x58fd81fffc000000

def z673 : W := mkw 0x0000601840628212 0x4000060184062821 0x3024e83cc0e6273e 0xa3024e83cc0e6273

def z674 : W := mkw 0x12001802840014a9 0x012001802840014a 0x00001003000018c0 0x100001003000018c

def z675 : W := mkw 0x0614180280000000 0x0061418028000000 0x5e1c1807e01839ce 0xf5e1c1807e01839c

def z676 : W := mkw 0x84dfc6d7e3096944 0x884dfc6d7e309694 0xd1dff7c7e319f9cf 0x7d1dff7c7e319f9c

def z677 : W := mkw 0xafbfdfffc5203e0e 0x0afbfdfffc5203e0 0x8fffffffc0003e07 0xf8fffffffc0003e0

def z678 : W := mkw 0x6fffff7c7fffff1e 0x46fffff7c7fffff1 0xfffffffcffffff3f 0xffffffffcffffff3

def z679 : W := mkw 0x1f741802be9414a9 0x01f741802be9414a 0x7ffc1807fffe3fff 0xf7ffc1807fffe3ff

def z680 : W := mkw 0x496020003adf8000 0x0496020003adf800 0x7fe000003fffc009 0xe7fe000003fffc00

def z681 : W := mkw 0x100000000c1414a9 0x0100000000c1414a 0x400000003c1818c0 0x0400000003c1818c

def z682 : W := mkw 0x4dffa4853adf8000 0x04dffa4853adf800 0xfffff7c73fffc00f 0xffffff7c73fffc00

def z683 : W := mkw 0x0000000004001408 0x0000000000400140 0x600000003c003e08 0x0600000003c003e0

def z684 : W := mkw 0x14140002881400a1 0x014140002881400a 0x7e1c0007fc1e01fa 0xe7e1c0007fc1e01f

def z685 : W := mkw 0x8fffffffe36beb56 0xc8fffffffe36beb5 0xffffffffe3ffffff 0xfffffffffe3fffff

def z686 : W := mkw 0x8fbe99a380000000 0x08fbe99a38000000 0x0ffff1c300000003 0xf0ffff1c30000000

def z687 : W := mkw 0x16de18c3ae1d1ce9 0x816de18c3ae1d1ce 0x4fd811c33c1818c0 0x54fd811c33c1818c

def z688 : W := mkw 0xafbfddbfd4a0160a 0x0afbfddbfd4a0160 0xafffffffdce00607 0xfafffffffdce0060

def z689 : W := mkw 0x0001641c40628212 0x40001641c4062821 0xa027ee3cc0e60637 0xaa027ee3cc0e6063

def z690 : W := mkw 0x0dff86c523096944 0x80dff86c52309694 0xdffff7c72319f9cf 0xfdffff7c72319f9c

def z691 : W := mkw 0x1614781acc7696bb 0x41614781acc7696b 0x2e24e838dce60630 0x82e24e838dce6063

def z692 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x4e1c1807fc1818c6 0xf4e1c1807fc1818c

def z693 : W := mkw 0x0614180280000000 0x0061418028000000 0x0e18100300000000 0x50e1810030000000

def z694 : W := mkw 0x000164144042c110 0x4000164144042c11 0x9027ee3cc007c137 0xa9027ee3cc007c13

def z695 : W := mkw 0x3f741b6abfb43eaf 0x03f741b6abfb43ea 0xeff81ffb3ff83ecd 0xfeff81ffb3ff83ec

def z696 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x0e3fe83fc0000002 0x80e3fe83fc000000

def z697 : W := mkw 0x6b603b683fffbe0e 0x06b603b683fffbe0 0xffe01ff83ffffe0d 0xfffe01ff83ffffe0

def z698 : W := mkw 0x8414c012c0000000 0x08414c012c000000 0x0004e000c0000000 0x00004e000c000000

def z699 : W := mkw 0x4ffeb8003edf9408 0x04ffeb8003edf940 0x7ffff8003ffffe0f 0xf7ffff8003ffffe0

def z700 : W := mkw 0x0001461c41206316 0x40001461c4120631 0x8027ee3cc0002737 0xa8027ee3cc000273

def z701 : W := mkw 0x4dfea2083bffa206 0x04dfea2083bffa20 0xffffee383fffe60f 0xeffffee383fffe60

def z702 : W := mkw 0x2beb1fe537897d4c 0x82beb1fe537897d4 0xdfdb17c73f19f9cf 0x7dfdb17c73f19f9c

def z703 : W := mkw 0x0040024023002804 0x0004002402300280 0xd1d817c7231839cf 0x7d1d817c7231839c

def z704 : W := mkw 0x5ffeb802bedf94a9 0x05ffeb802bedf94a 0x7ffff0033fffd8cb 0xf7ffff0033fffd8c

def z705 : W := mkw 0x0000000000000000 0x0000000000000000 0x2020000003e00009 0xa2020000003e0000

def z706 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x4e181807fc183ff4 0x54e181807fc183ff

def z707 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x5e1c1807fc1e3ff6 0x55e1c1807fc1e3ff

def z708 : W := mkw 0x0bab5db540000000 0x00bab5db54000000 0x8fffffffc0000007 0xf8fffffffc000000

def z709 : W := mkw 0x2b617d7476c2dd18 0x42b617d7476c2dd1 0x5fc7f1c4fc07d932 0x55fc7f1c4fc07d93

def z710 : W := mkw 0x2040224833e2eb16 0x42040224833e2eb1 0x3000000003e7e738 0x03000000003e7e73

def z711 : W := mkw 0xdf34f932dcd694a9 0x0df34f932dcd694a 0x2e24e838dce60630 0x82e24e838dce6063

def z712 : W := mkw 0x04de20002a5f8000 0x004de20002a5f800 0x7fffe0003fffc00b 0xe7fffe0003fffc00

def z713 : W := mkw 0x008b06c501096944 0x8008b06c50109694 0x91db17c70019f9c7 0x791db17c70019f9c

def z714 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fffe0003fffe73b 0xe7fffe0003fffe73

def z715 : W := mkw 0x89abc5b540000000 0x089abc5b54000000 0x81e3effcc0000005 0x081e3effcc000000

def z716 : W := mkw 0x2960036833a02a06 0x02960036833a02a0 0xcfe007f83fe00001 0x4cfe007f83fe0000

def z717 : W := mkw 0x8fbfddb7c0094140 0x88fbfddb7c009414 0x8fffffffc001c007 0xf8fffffffc001c00

def z718 : W := mkw 0x8dbfc5b540000000 0x08dbfc5b54000000 0x8ffff7ff00000007 0xf8ffff7ff0000000

def z719 : W := mkw 0x12015edfc5207fff 0xc12015edfc5207ff 0x80001fffc0003ff4 0x180001fffc0003ff

def z720 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x3fe7e0001fe7c00b 0xa3fe7e0001fe7c00

def z721 : W := mkw 0x0b601b6033802804 0x00b601b603380280 0xefe01ff83fe0380d 0xfefe01ff83fe0380

def z722 : W := mkw 0x3d74036abbb42aa7 0x03d74036abbb42aa 0x91fc07ffc3fe01f3 0x091fc07ffc3fe01f

def z723 : W := mkw 0x008b068501006104 0x0008b06850100610 0xd1db17c72319f9cf 0x7d1db17c72319f9c

def z724 : W := mkw 0x2b601b6837a97f4e 0x82b601b6837a97f4 0xefe01ff83fe1fe0d 0xfefe01ff83fe1fe0

def z725 : W := mkw 0xc2417db7fadf8000 0x0c2417db7fadf800 0xf0001fffffffc00c 0x1f0001fffffffc00

def z726 : W := mkw 0x0960024833a02a06 0x00960024833a02a0 0xefe01ff83fe03e0d 0xfefe01ff83fe03e0

def z727 : W := mkw 0x9fbfddb7cc1414a9 0x09fbfddb7cc1414a 0xdffffffffc1e19f7 0xfdffffffffc1e19f

def z728 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xeff81fff3fe03e0f 0xfeff81fff3fe03e0

def z729 : W := mkw 0x4d34a00018d68000 0x04d34a00018d6800 0x2e27e0001fe7c001 0x82e27e0001fe7c00

def z730 : W := mkw 0x604022483ff6be0e 0x0604022483ff6be0 0x600000003fe63e08 0x0600000003fe63e0

def z731 : W := mkw 0xc49fe497c8568000 0x0c49fe497c856800 0x001fe007c0060002 0x0001fe007c006000

def z732 : W := mkw 0x8fbfddb7c8140000 0x08fbfddb7c814000 0x9fffffffc01e0007 0xf9fffffffc01e000

def z733 : W := mkw 0x2b20192814a0160a 0x02b20192814a0160 0xefe01ff83ce03e0d 0xfefe01ff83ce03e0

def z734 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xcfe017f83fe0380d 0x7cfe017f83fe0380

def z735 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x7e3ff807fc1e3fff 0xf7e3ff807fc1e3ff

def z736 : W := mkw 0x9fbfddb7cc1414a9 0x09fbfddb7cc1414a 0xafffffffdc063ff7 0xfafffffffdc063ff

def z737 : W := mkw 0x44dea0003adf8000 0x044dea0003adf800 0x7e1fe0003fffc00a 0xe7e1fe0003fffc00

def z738 : W := mkw 0x849fc497c0000000 0x0849fc497c000000 0x81ffffffc0000007 0xf81ffffffc000000

def z739 : W := mkw 0x36543a4abff6ffbf 0x436543a4abff6ffb 0x7e1c1807fffffffe 0xf7e1c1807fffffff

def z740 : W := mkw 0x8f35ddb7c0000000 0x08f35ddb7c000000 0x8fe4ffffc0000005 0xf8fe4ffffc000000

def z741 : W := mkw 0x5beab802b6cb94a9 0x05beab802b6cb94a 0x01e3f807c3e1fff5 0x101e3f807c3e1fff

def z742 : W := mkw 0x4dfea1203adf8000 0x04dfea1203adf800 0xffffe7f83fffc00b 0xeffffe7f83fffc00

def z743 : W := mkw 0x02015e1c4520771e 0x402015e1c4520771 0x80001e3cc0003f34 0x180001e3cc0003f3

def z744 : W := mkw 0x4dbea00018df8000 0x04dbea00018df800 0x3e3fe0001fffc00b 0xa3e3fe0001fffc00

def z745 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x8fffffffc00039c7 0xf8fffffffc00039c

def z746 : W := mkw 0x8babddb540000000 0x08babddb54000000 0x8ffbffff00000007 0xf8ffbffff0000000

def z747 : W := mkw 0x2bab1dad14a9574a 0x82bab1dad14a9574 0x3e3b083f1cf9c7c2 0x83e3b083f1cf9c7c

def z748 : W := mkw 0x00cb04c522094940 0x800cb04c52209494 0x51db11c72319d9cb 0x751db11c72319d9c

def z749 : W := mkw 0x00cb46d563096944 0x800cb46d56309694 0xd1dff7c7e319f9cf 0x7d1dff7c7e319f9c

def z750 : W := mkw 0x000062184162a216 0x4000062184162a21 0xb027ee38c3e7e63f 0xab027ee38c3e7e63

def z751 : W := mkw 0xd49fe497c85f80a1 0x0d49fe497c85f80a 0x101fe007c01fc1f2 0x0101fe007c01fc1f

def z752 : W := mkw 0x3b601b6ab7a03eaf 0x03b601b6ab7a03ea 0xffe41fffffe63fff 0xfffe41fffffe63ff

def z753 : W := mkw 0x2040224837ebff5e 0xc2040224837ebff5 0x700000003ffffff8 0x0700000003ffffff

def z754 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0xa027ee38c3e7e63d 0xaa027ee38c3e7e63

def z755 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x8fe7effcc0000007 0xa8fe7effcc000000

def z756 : W := mkw 0x8fbfddb7c8140000 0x08fbfddb7c814000 0xcffffffffc180007 0xfcffffffffc18000

def z757 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x7e3c1807fffe3fff 0xf7e3c1807fffe3ff

def z758 : W := mkw 0x49eaa00032cb8000 0x049eaa00032cb800 0x4fe3e0003fe1c001 0x44fe3e0003fe1c00

def z759 : W := mkw 0x0fbf9da500000000 0x00fbf9da50000000 0x8fffffff00000007 0xf8fffffff0000000

def z760 : W := mkw 0x00ca60d9626b8a52 0xc00ca60d9626b8a5 0x61fcf9fbe0fe1ef0 0xd61fcf9fbe0fe1ef

def z761 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0xafffffffc000260f 0xfafffffffc000260

def z762 : W := mkw 0x9f34d932cc1414a9 0x09f34d932cc1414a 0xfffcfffffc1e3fff 0xffffcfffffc1e3ff

def z763 : W := mkw 0x00ca02c123096944 0x800ca02c12309694 0x51d811c72319f9ce 0x751d811c72319f9c

def z764 : W := mkw 0x89abc5b540000000 0x089abc5b54000000 0x81e7eff8c0000001 0x881e7eff8c000000

def z765 : W := mkw 0x16157e1ecd76f7bf 0x416157e1ecd76f7b 0xce3bf63b3ff9d8c1 0x5ce3bf63b3ff9d8c

def z766 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0xfe3c1e3ffc1e3fff 0xffe3c1e3ffc1e3ff

def z767 : W := mkw 0x8fbfddb7c4001408 0x08fbfddb7c400140 0x8fffffffc0003e07 0xf8fffffffc0003e0

def z768 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xd1df17c7e31ff9ff 0x7d1df17c7e31ff9f

def z769 : W := mkw 0x22015f3c4520771e 0x422015f3c4520771 0x80000e3cc0002734 0x080000e3cc000273

def z770 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x5fffe0003fffc003 0x45fffe0003fffc00

def z771 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x7e1c1007fc1e3ffa 0x57e1c1007fc1e3ff

def z772 : W := mkw 0x0b20192000000000 0x00b2019200000000 0x8fe7fff800000007 0xf8fe7fff80000000

def z773 : W := mkw 0x89abc5b540000000 0x089abc5b54000000 0x81e3eff800000005 0xa81e3eff80000000

def z774 : W := mkw 0x00cb46d563096944 0x800cb46d56309694 0xd1db1fffe319f9cf 0x7d1db1fffe319f9c

def z775 : W := mkw 0x004022482362eb16 0x4004022482362eb1 0x7000000023e7ff38 0x07000000023e7ff3

def z776 : W := mkw 0x0b60192036801408 0x00b6019203680140 0xefe01ff83fe03e0d 0xfefe01ff83fe03e0

def z777 : W := mkw 0x2b20192814a0160a 0x02b20192814a0160 0xafe00ff81ce00601 0x8afe00ff81ce0060

def z778 : W := mkw 0xa4dfc6dff7a03e0e 0x0a4dfc6dff7a03e0 0x601fe007ffe03e0a 0x0601fe007ffe03e0

def z779 : W := mkw 0x008b449540000000 0x0008b44954000000 0x81e3e7f800000001 0x081e3e7f80000000

def z780 : W := mkw 0x0001669d4162e356 0xc0001669d4162e35 0xb027ee3fc3e7e7ff 0xab027ee3fc3e7e7f

def z781 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xcfe01ff83fe03e05 0x5cfe01ff83fe03e0

def z782 : W := mkw 0x00cb048522090000 0x000cb04852209000 0xd1db17c72319f9cf 0x7d1db17c72319f9c

def z783 : W := mkw 0x445420003adf8000 0x0445420003adf800 0x7e3fe0003fffc00b 0xe7e3fe0003fffc00

def z784 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xffe41ff83fe63e0f 0xfffe41ff83fe63e0

def z785 : W := mkw 0x89abc5b540000000 0x089abc5b54000000 0x81fbe7ff00000003 0x081fbe7ff0000000

def z786 : W := mkw 0x669ebb680d7fbe0e 0x0669ebb680d7fbe0 0x901ffff8001ffe06 0x1901ffff8001ffe0

def z787 : W := mkw 0x6dfea1603adf8800 0x06dfea1603adf880 0x7fffe1c03fffc00b 0xe7fffe1c03fffc00

def z788 : W := mkw 0x141400028c1414a9 0x0141400028c1414a 0x7e1c0007fc1e3ffa 0xe7e1c0007fc1e3ff

def z789 : W := mkw 0x16543a4aaf7fffff 0xc16543a4aaf7ffff 0x7e1c1807fffffffe 0xf7e1c1807fffffff

def z790 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7ffbe0003fffc009 0x47ffbe0003fffc00

def z791 : W := mkw 0x8babddb540000000 0x08babddb54000000 0x8fe7fffcc0000007 0xf8fe7fffcc000000

def z792 : W := mkw 0x1f355d36cc1414a9 0x01f355d36cc1414a 0xfffffffffc1e3fff 0xffffffffffc1e3ff

def z793 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fffe0003ffff9cb 0xe7fffe0003ffff9c

def z794 : W := mkw 0x0001641c4062c312 0x40001641c4062c31 0x3027e83cc3e7c73b 0xa3027e83cc3e7c73

def z795 : W := mkw 0x0001641440428000 0x0000164144042800 0xb027ee3cc3e7e73f 0xab027ee3cc3e7e73

def z796 : W := mkw 0x000166dd4162eb56 0xc000166dd4162eb5 0xf03fffffe3ffffff 0xff03fffffe3fffff

def z797 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x8ffcffffc0000004 0xd8ffcffffc000000

def z798 : W := mkw 0x5dfea002badf80a1 0x05dfea002badf80a 0x7fffe807ffffe7ff 0xe7fffe807ffffe7f

def z799 : W := mkw 0x8fbebbab8162e316 0x48fbebbab8162e31 0x3fd811c303e7e738 0x53fd811c303e7e73

def z800 : W := mkw 0xcdfea083badf8000 0x0cdfea083badf800 0x7fffe0033fffc00b 0xe7fffe0033fffc00

def z801 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0xb027fe3fc3e7ffff 0xbb027fe3fc3e7fff

def z802 : W := mkw 0x8fbfddb7c4001408 0x08fbfddb7c400140 0xafffffffdc000607 0xfafffffffdc00060

def z803 : W := mkw 0x869fddb7c0000000 0x0869fddb7c000000 0x81dfffffc0000007 0x781dfffffc000000

def z804 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0x9027ee3cc3e7e737 0x09027ee3cc3e7e73

def z805 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xafe00ff81fe0260d 0xaafe00ff81fe0260

def z806 : W := mkw 0x8f74db72e3096944 0x88f74db72e309694 0x5e24e838e319f9c8 0x85e24e838e319f9c

def z807 : W := mkw 0x00cb04c522094940 0x800cb04c52209494 0x41db11c32019d8c0 0x541db11c32019d8c

def z808 : W := mkw 0x20cb06cd33a96b46 0x820cb06cd33a96b4 0xd1db17c723f9f9cf 0x7d1db17c723f9f9c

def z809 : W := mkw 0x8fbfddb7c8140000 0x08fbfddb7c814000 0xfffffffffc1e273f 0xffffffffffc1e273

def z810 : W := mkw 0x2b601b6833a02a06 0x02b601b6833a02a0 0xefe01ff83fe0000d 0xfefe01ff83fe0000

def z811 : W := mkw 0x99abc5b54c1414a9 0x099abc5b54c1414a 0xf1e3e7f83c1e3ff9 0x0f1e3e7f83c1e3ff

def z812 : W := mkw 0xcdfea1a13adf8000 0x0cdfea1a13adf800 0x7fffe1c03fffc00b 0xe7fffe1c03fffc00

def z813 : W := mkw 0x0040024023096944 0x8004002402309694 0xd1d817c72319f9cf 0x7d1d817c72319f9c

def z814 : W := mkw 0x00cb46dd63296b56 0xc00cb46dd63296b5 0xf1fb1fffe3f9ffff 0xff1fb1fffe3f9fff

def z815 : W := mkw 0x00cb04c522094940 0x800cb04c52209494 0x51db11c72019f9ce 0x751db11c72019f9c

def z816 : W := mkw 0x9fbfddb7c40014a9 0x09fbfddb7c40014a 0x8fffffffc00018c7 0xf8fffffffc00018c

def z817 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x8fdfffffc0000006 0x58fdfffffc000000

def z818 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe01ffcffe03f3d 0xfefe01ffcffe03f3

def z819 : W := mkw 0x00ca02c123096944 0x800ca02c12309694 0x41d811c32319d8c0 0x541d811c32319d8c

def z820 : W := mkw 0x9f34f93acc7696bb 0x49f34f93acc7696b 0x2e24e838dce60630 0x82e24e838dce6063

def z821 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fe7e0003fffc009 0x87fe7e0003fffc00

def z822 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fffe0043fffe10f 0xe7fffe0043fffe10

def z823 : W := mkw 0x2b601b6837a93e4e 0x82b601b6837a93e4 0xefe01ff83ff83ecd 0xfefe01ff83ff83ec

def z824 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefc01ff83fe03e0c 0x5efc01ff83fe03e0

def z825 : W := mkw 0x9fbfddb7c81400a1 0x09fbfddb7c81400a 0xdfffffffe01e39ff 0xfdfffffffe01e39f

def z826 : W := mkw 0x8dbfc5b7c0000000 0x08dbfc5b7c000000 0x81e7e7f8c0000001 0x081e7e7f8c000000

def z827 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xffdb17c73f19f9cf 0xfffdb17c73f19f9c

def z828 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0x91db17c70319f9c7 0x191db17c70319f9c

def z829 : W := mkw 0x8babddb7c0000000 0x08babddb7c000000 0x81e3f7fb00000001 0x181e3f7fb0000000

def z830 : W := mkw 0x4dffc61c7bbd6316 0x44dffc61c7bbd631 0xcfd80e3cfc182734 0x4cfd80e3cfc18273

def z831 : W := mkw 0x00cb46dd63296b56 0xc00cb46dd63296b5 0xd1db17ff2319f9cf 0x7d1db17ff2319f9c

def z832 : W := mkw 0x604022483fffff1e 0x4604022483fffff1 0x700000003fffff38 0x0700000003fffff3

def z833 : W := mkw 0x16df1ec7af1d7ded 0x816df1ec7af1d7de 0xafc70fc0df07c631 0x8afc70fc0df07c63

def z834 : W := mkw 0x9fbfddb7cc1d55e9 0x89fbfddb7cc1d55e 0xfffffffffc1fffff 0xffffffffffc1ffff

def z835 : W := mkw 0x8fbfddb7c0004100 0x08fbfddb7c000410 0x9fffffffc001c107 0xf9fffffffc001c10

def z836 : W := mkw 0x32015f7ec5207fbf 0x432015f7ec5207fb 0x80001fffc0003ff4 0x180001fffc0003ff

def z837 : W := mkw 0xc49fe497c85fc110 0x4c49fe497c85fc11 0x101fe007c01fc132 0x0101fe007c01fc13

def z838 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x6e1c1807fc1e3ff4 0xd6e1c1807fc1e3ff

def z839 : W := mkw 0x8fbfddb7c8140000 0x08fbfddb7c814000 0xafffffffdc060007 0xfafffffffdc06000

def z840 : W := mkw 0xa2015fffc5207f4e 0x8a2015fffc5207f4 0x80001fffc0003fc4 0x180001fffc0003fc

def z841 : W := mkw 0x8fbfddb7c0094140 0x88fbfddb7c009414 0xdfffffffe019f9cf 0xfdfffffffe019f9c

def z842 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x8ffff7fb00000003 0xf8ffff7fb0000000

def z843 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0xb03fee3fc3ffe7ff 0xab03fee3fc3ffe7f

def z844 : W := mkw 0x8babddb7c0000000 0x08babddb7c000000 0x81e3eff8c0000001 0x081e3eff8c000000

def z845 : W := mkw 0x00cb06cd23296b46 0x800cb06cd23296b4 0xd1fb17ff23f9f9cf 0x7d1fb17ff23f9f9c

def z846 : W := mkw 0x8dbfc5b7c0000000 0x08dbfc5b7c000000 0x81fff7ffc0000007 0x781fff7ffc000000

def z847 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7ffff807ffffffff 0xf7ffff807fffffff

def z848 : W := mkw 0x3b601b6ab7a03eaf 0x03b601b6ab7a03ea 0xfff81ffffff83fff 0xffff81ffffff83ff

def z849 : W := mkw 0x169f5c97cc1414a9 0x0169f5c97cc1414a 0xfffffffffc1e3fff 0xffffffffffc1e3ff

def z850 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xd1db17c32319d8cb 0x7d1db17c32319d8c

def z851 : W := mkw 0x4d35a6c519d6e944 0x84d35a6c519d6e94 0xae24f7c71ce639c4 0x9ae24f7c71ce639c

def z852 : W := mkw 0x0b215d3440000000 0x00b215d344000000 0x8fe3fff800000005 0xf8fe3fff80000000

def z853 : W := mkw 0x9fbfddb7c81400a1 0x09fbfddb7c81400a 0xfffffffffc1e01ff 0xffffffffffc1e01f

def z854 : W := mkw 0x4dfea0403adf8800 0x04dfea0403adf880 0x7ffff1c03fffd80b 0xf7ffff1c03fffd80

def z855 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xf1fb17c723f9f9cf 0xff1fb17c723f9f9c

def z856 : W := mkw 0x0dfe800032890000 0x00dfe80003289000 0x7fffe0003ff9c00b 0xe7fffe0003ff9c00

def z857 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x8fffeff8c0000003 0xe8fffeff8c000000

def z858 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0xa027ee3cc3e7e735 0x8a027ee3cc3e7e73

def z859 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0xa027ee3cc3e7c637 0xaa027ee3cc3e7c63

def z860 : W := mkw 0x9fbfddb7c40014a9 0x09fbfddb7c40014a 0xbfffffffc0063fff 0xfbfffffffc0063ff

def z861 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xc1db17c32319f8cd 0x7c1db17c32319f8c

def z862 : W := mkw 0xcfbfddb7d8940000 0x0cfbfddb7d894000 0x8fffffffdc000007 0xf8fffffffdc00000

def z863 : W := mkw 0x00cb46d563096954 0xc00cb46d56309695 0xd1db17c7e319f9ff 0x7d1db17c7e319f9f

def z864 : W := mkw 0x8babddb7c0000000 0x08babddb7c000000 0x81fbffffc0000007 0x781fbffffc000000

def z865 : W := mkw 0x89abc5b540000000 0x089abc5b54000000 0x81e3f7f800000005 0x781e3f7f80000000

def z866 : W := mkw 0x0001669d4162e316 0x40001669d4162e31 0xb027ffffc3e7e73f 0xbb027ffffc3e7e73

def z867 : W := mkw 0x00402248236beb56 0xc00402248236beb5 0x701c1807e3fffffe 0xf701c1807e3fffff

def z868 : W := mkw 0x9f34d932cc1414a9 0x09f34d932cc1414a 0xefe4fff8fc063e3d 0xfefe4fff8fc063e3

def z869 : W := mkw 0x00cb04c522090840 0x800cb04c52209084 0xd1db17c72319d8cf 0x7d1db17c72319d8c

def z870 : W := mkw 0x9fbfddb7cc1414a9 0x09fbfddb7cc1414a 0xfffffffffc1e063f 0xffffffffffc1e063

def z871 : W := mkw 0x49eaa0003adf8000 0x049eaa0003adf800 0x7fe3e0003fffc009 0xe7fe3e0003fffc00

def z872 : W := mkw 0x4dfea0c13adf8840 0x84dfea0c13adf884 0x7fffe1c03fffc00b 0xe7fffe1c03fffc00

def z873 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe017f83fe01809 0xfefe017f83fe0180

def z874 : W := mkw 0x008b449540000000 0x0008b44954000000 0x81fbf7ff00000007 0x781fbf7ff0000000

def z875 : W := mkw 0x8dbfc5b7c0000000 0x08dbfc5b7c000000 0x81ffefffc0000007 0xa81ffefffc000000

def z876 : W := mkw 0x069f5c97c0000000 0x0069f5c97c000000 0x8fffffffc0000007 0xf8fffffffc000000

def z877 : W := mkw 0x0dbea00008568000 0x00dbea0000856800 0x7fffe0003fffc00b 0xe7fffe0003fffc00

def z878 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0xf027fe3ce3e7ff3f 0xff027fe3ce3e7ff3

def z879 : W := mkw 0x2b601b6837a07f4e 0x82b601b6837a07f4 0xefe01ff83fe03fcd 0xfefe01ff83fe03fc

def z880 : W := mkw 0x29eb67fd73ebeb56 0xc29eb67fd73ebeb5 0x81e3e7f803e1c001 0x081e3e7f803e1c00

def z881 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0xdfffffffe018000f 0xfdfffffffe018000

def z882 : W := mkw 0xc49fe495485f8000 0x0c49fe495485f800 0x101fe000001fc002 0x0101fe000001fc00

def z883 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fffe004ffffc13b 0xe7fffe004ffffc13

def z884 : W := mkw 0x9fbfddb7c40014a9 0x09fbfddb7c40014a 0xeffffffffc003fff 0xfeffffffffc003ff

def z885 : W := mkw 0x0fbe992280000000 0x00fbe99228000000 0x8fffffffc0000007 0xf8fffffffc000000

def z886 : W := mkw 0x0dbfc49540000000 0x00dbfc4954000000 0x8fffffffc0000007 0xf8fffffffc000000

def z887 : W := mkw 0x12003802844294a9 0x012003802844294a 0x3027f807c3e7ffff 0xb3027f807c3e7fff

def z888 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xfff81ff83ff83e0f 0xffff81ff83ff83e0

def z889 : W := mkw 0x1fbe99228c1414a9 0x01fbe99228c1414a 0xfffffffffc1e3fff 0xffffffffffc1e3ff

def z890 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x6fffe0003fffc001 0xc6fffe0003fffc00

def z891 : W := mkw 0x5dfea002badf80a1 0x05dfea002badf80a 0x7fffe0033fffc0cb 0xe7fffe0033fffc0c

def z892 : W := mkw 0x00cb04c522094940 0x800cb04c52209494 0xd1db17c72019d9c7 0x7d1db17c72019d9c

def z893 : W := mkw 0x0000601840628212 0x4000060184062821 0x2027e838c3e7c631 0x82027e838c3e7c63

def z894 : W := mkw 0x2960036833a02a06 0x02960036833a02a0 0xefe017f83fe0380d 0xfefe017f83fe0380

def z895 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fdfe0003fffc00a 0x47fdfe0003fffc00

def z896 : W := mkw 0x0415461c49346316 0x40415461c4934631 0xfe1c0e3cfc1e273e 0xefe1c0e3cfc1e273

def z897 : W := mkw 0x4dbea00018d68000 0x04dbea00018d6800 0x3fffe0001fe7c00b 0xe3fffe0001fe7c00

def z898 : W := mkw 0x008b048500094140 0x8008b04850009414 0xd1db17c72019f9cf 0x7d1db17c72019f9c

def z899 : W := mkw 0x2b601b6ab7a03e0e 0x02b601b6ab7a03e0 0xefe01fffffe03e0d 0xfefe01fffffe03e0

def z900 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xd1db17c32319f9c9 0x5d1db17c32319f9c

def z901 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0xfffff7c03fffc00f 0xffffff7c03fffc00

def z902 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe41ff8ffe63e3d 0xfefe41ff8ffe63e3

def z903 : W := mkw 0x89abc5b540000000 0x089abc5b54000000 0xb1e7effcc006273f 0xab1e7effcc006273

def z904 : W := mkw 0x89abc5b540000000 0x089abc5b54000000 0x8fe3e7f800000001 0xe8fe3e7f80000000

def z905 : W := mkw 0x0200180004001408 0x0020018000400140 0x7e1c1807fc1e3ffe 0xf7e1c1807fc1e3ff

def z906 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe01fff3fe03fcd 0xfefe01fff3fe03fc

def z907 : W := mkw 0x00cb06cd23296b46 0x800cb06cd23296b4 0xf1db17c723f9ffcf 0x7f1db17c723f9ffc

def z908 : W := mkw 0x8fbfddb7c0004110 0x48fbfddb7c000411 0x8fffffffc0000137 0xf8fffffffc000013

def z909 : W := mkw 0x00ca02c123096944 0x800ca02c12309694 0x51db11c32319f9cb 0x751db11c32319f9c

def z910 : W := mkw 0x000062184162e316 0x4000062184162e31 0x3027e838c3e7e73b 0xa3027e838c3e7e73

def z911 : W := mkw 0xcfbfddb7c81d0000 0x0cfbfddb7c81d000 0x8fffffffc0180007 0xf8fffffffc018000

def z912 : W := mkw 0x8b215db7c0000000 0x08b215db7c000000 0x8fe7ffffc0000007 0xf8fe7ffffc000000

def z913 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xffe01ff83fe63f3d 0xfffe01ff83fe63f3

def z914 : W := mkw 0x00402248236beb56 0xc00402248236beb5 0x5000000023f9f9c8 0x05000000023f9f9c

def z915 : W := mkw 0x8fbfddb7c4001408 0x08fbfddb7c400140 0xfffffffffc063f3f 0xffffffffffc063f3

def z916 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x7e1c0807fc1e3ffa 0x87e1c0807fc1e3ff

def z917 : W := mkw 0x89abc5b540000000 0x089abc5b54000000 0x81ffffffc0000007 0xf81ffffffc000000

def z918 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0xb027ee3cc3e7c733 0x8b027ee3cc3e7c73

def z919 : W := mkw 0x8fbfddb7c4001408 0x08fbfddb7c400140 0xfffffffffc183fcf 0xffffffffffc183fc

def z920 : W := mkw 0x5dfea002badf80a1 0x05dfea002badf80a 0x7ffff007fffff9ff 0xf7ffff007fffff9f

def z921 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe01ff83fe01e01 0xdefe01ff83fe01e0

def z922 : W := mkw 0x8fbfddb7c0090040 0x88fbfddb7c009004 0x8fffffffc01800c7 0xf8fffffffc01800c

def z923 : W := mkw 0x49eaa00032cb8000 0x049eaa00032cb800 0x7fe7e0003fe7c00b 0xe7fe7e0003fe7c00

def z924 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe00ff83fe00609 0xeefe00ff83fe0060

def z925 : W := mkw 0x8babddb540000000 0x08babddb54000000 0x81e3fff800000005 0x181e3fff80000000

def z926 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x8ffbffffc0000005 0x58ffbffffc000000

def z927 : W := mkw 0x0dfea00032c28000 0x00dfea00032c2800 0x7fffe0003fe7c00b 0xe7fffe0003fe7c00

def z928 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0x3027e83cc3e7e73a 0x83027e83cc3e7e73

def z929 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x2fffe0001fe7c003 0xe2fffe0001fe7c00

def z930 : W := mkw 0x66543a483fffbe0e 0x066543a483fffbe0 0x7e1c18003ffffe0e 0xf7e1c18003ffffe0

def z931 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0xb027ee38c3e7c63b 0xab027ee38c3e7c63

def z932 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0xb027ee38c3e7e739 0x8b027ee38c3e7e73

def z933 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0xf03fee3ce3ffe73f 0xef03fee3ce3ffe73

def z934 : W := mkw 0x0dbe812000000000 0x00dbe81200000000 0x8fffe7f800000003 0xe8fffe7f80000000

def z935 : W := mkw 0x000166dd4162eb56 0xc000166dd4162eb5 0xb027effcc3e7e73f 0xab027effcc3e7e73

def z936 : W := mkw 0x2960036833a02a06 0x02960036833a02a0 0xefe00ff83fe0260d 0xeefe00ff83fe0260

def z937 : W := mkw 0x8fbfddb540000000 0x08fbfddb54000000 0x8ffffff800000007 0xf8ffffff80000000

def z938 : W := mkw 0x2040224837e2be0e 0x02040224837e2be0 0x700000003fe7fe08 0x0700000003fe7fe0

def z939 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x5ffbe0003ff9c00b 0x65ffbe0003ff9c00

def z940 : W := mkw 0x4d74a0003adf8000 0x04d74a0003adf800 0x7e27e0003fffc00b 0xa7e27e0003fffc00

def z941 : W := mkw 0x0921453440000000 0x0092145344000000 0x81e3e7f800000001 0x081e3e7f80000000

def z942 : W := mkw 0xdffe99a3be9d14a9 0x0dffe99a3be9d14a 0x4fd811c33c1818c0 0x54fd811c33c1818c

def z943 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe01ff83ce03e04 0xdefe01ff83ce03e0

def z944 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe7fff83fe03e0f 0xfefe7fff83fe03e0

def z945 : W := mkw 0x6040224833ebaa06 0x06040224833ebaa0 0x0000000003e1c000 0x00000000003e1c00

def z946 : W := mkw 0x9fbfddb7cc1414a9 0x09fbfddb7cc1414a 0xeffffffffc063e3f 0xfeffffffffc063e3

def z947 : W := mkw 0x89abc5b540000000 0x089abc5b54000000 0x81fbe7f800000003 0x681fbe7f80000000

def z948 : W := mkw 0x404022483bffeb56 0xc404022483bffeb5 0x700000003ffffff8 0x0700000003ffffff

def z949 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7ffff0033fffd8cb 0xf7ffff0033fffd8c

def z950 : W := mkw 0x9fbfddb7cc1414a9 0x09fbfddb7cc1414a 0xeffffffffc183ecf 0xfeffffffffc183ec

def z951 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x8fffffffc0002737 0xf8fffffffc000273

def z952 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0x8fe007f81fe00001 0x08fe007f81fe0000

def z953 : W := mkw 0x2040224837e2be1e 0x42040224837e2be1 0x600000003fe63e38 0x0600000003fe63e3

def z954 : W := mkw 0x2040224833e2eb16 0x42040224833e2eb1 0x0000000003e1c000 0x00000000003e1c00

def z955 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0xcfffffffe000380f 0xfcfffffffe000380

def z956 : W := mkw 0x9fbfddb7c81d41e1 0x89fbfddb7c81d41e 0x9fffffffc01fc1f7 0xf9fffffffc01fc1f

def z957 : W := mkw 0x8babddb544001408 0x08babddb54400140 0xefe3fff83c003e0d 0xfefe3fff83c003e0

def z958 : W := mkw 0x0b201b280520360e 0x00b201b280520360 0xefe01ff83fe03e0d 0xfefe01ff83fe03e0

def z959 : W := mkw 0x8babddb7c0000000 0x08babddb7c000000 0x8fe3ffffc0000005 0xf8fe3ffffc000000

def z960 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0xafffffffc0060637 0xfafffffffc006063

def z961 : W := mkw 0x89abc5b540000000 0x089abc5b54000000 0x81e7e7fcc0000003 0x081e7e7fcc000000

def z962 : W := mkw 0x0960012032800000 0x0096001203280000 0xefe007f83fe00009 0xeefe007f83fe0000

def z963 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xf1db1fc72319ffcf 0xff1db1fc72319ffc

def z964 : W := mkw 0x0960200032c28000 0x00960200032c2800 0x6fe3e0003fe1c009 0xe6fe3e0003fe1c00

def z965 : W := mkw 0x2b201b6815a03e0e 0x02b201b6815a03e0 0xafe01ff81ce03e05 0xfafe01ff81ce03e0

def z966 : W := mkw 0x8fbfddb7c8140000 0x08fbfddb7c814000 0xfffffffffc1e39cf 0xffffffffffc1e39c

def z967 : W := mkw 0x49eaa00032cb8000 0x049eaa00032cb800 0x7ffbe0003ff9c00b 0xe7ffbe0003ff9c00

def z968 : W := mkw 0x89abc5b540000000 0x089abc5b54000000 0x81e3e7fc00000007 0x281e3e7fc0000000

def z969 : W := mkw 0x2b601b6837a07f0e 0x02b601b6837a07f0 0xffe01ff83fe1ff0d 0xfffe01ff83fe1ff0

def z970 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0xbfffffffc006000f 0xfbfffffffc006000

def z971 : W := mkw 0x00cb46d563096944 0x800cb46d56309694 0xf1ffffffe31fffff 0xff1ffffffe31ffff

def z972 : W := mkw 0x8fbfddb7d0800000 0x08fbfddb7d080000 0xafffffffdce00007 0xfafffffffdce0000

def z973 : W := mkw 0x104022482f7fffff 0xc104022482f7ffff 0x700000003ffffff8 0x0700000003ffffff

def z974 : W := mkw 0x8fbfddb7cc141408 0x08fbfddb7cc14140 0xfffffffffc1e3e0f 0xffffffffffc1e3e0

def z975 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x8fe7ffffc0000005 0x98fe7ffffc000000

def z976 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7ffff0073fffc00f 0xf7ffff0073fffc00

def z977 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7e3fe0003fffc00a 0x87e3fe0003fffc00

def z978 : W := mkw 0x604022483fffff4e 0x8604022483fffff4 0x700000003fffffc8 0x0700000003fffffc

def z979 : W := mkw 0x8dbfc5b548140000 0x08dbfc5b54814000 0xffffe7f83c1e000b 0xeffffe7f83c1e000

def z980 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xffe31ff83fe1fe0f 0xfffe31ff83fe1fe0

def z981 : W := mkw 0x2b601b6837a07f1e 0x42b601b6837a07f1 0xefe01ff83fe03f3d 0xfefe01ff83fe03f3

def z982 : W := mkw 0xc49fe497c85fc140 0x8c49fe497c85fc14 0x101fe007c01fc1c2 0x0101fe007c01fc1c

def z983 : W := mkw 0x0001665c4162eb56 0xc0001665c4162eb5 0xb027ee3cc3e7ffff 0xab027ee3cc3e7fff

def z984 : W := mkw 0x0001641c40628212 0x40001641c4062821 0xb027ee3cc3e7c63f 0xab027ee3cc3e7c63

def z985 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0xeffffffffc00000f 0xfeffffffffc00000

def z986 : W := mkw 0x8fbfddb7c4001408 0x08fbfddb7c400140 0xcffffffffc001807 0xfcffffffffc00180

def z987 : W := mkw 0x000022080162a206 0x0000022080162a20 0xb027ee3cc3e7e73f 0xab027ee3cc3e7e73

def z988 : W := mkw 0x0fbfdd3440000000 0x00fbfdd344000000 0x8ffffffcc0000007 0xf8ffffffcc000000

def z989 : W := mkw 0x0001441440000000 0x0000144144000000 0x81e7fffcc0000007 0xf81e7fffcc000000

def z990 : W := mkw 0x9fbfddb7cc1414a9 0x09fbfddb7cc1414a 0x9fffffffc01e3ff7 0xf9fffffffc01e3ff

def z991 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x9fffffffc301c00f 0xf9fffffffc301c00

def z992 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe017f83fe03e09 0x5efe017f83fe03e0

def z993 : W := mkw 0x2b60196036801c08 0x02b60196036801c0 0xefe01ff83fe0180d 0xfefe01ff83fe0180

def z994 : W := mkw 0x89abc5b7c0000000 0x089abc5b7c000000 0x81e3e7ffc0000001 0x081e3e7ffc000000

def z995 : W := mkw 0x76543a4abfffbeaf 0x076543a4abfffbea 0x7e1c1807fffffffe 0xf7e1c1807fffffff

def z996 : W := mkw 0x8dbfc5b540000000 0x08dbfc5b54000000 0x8ffbe7f800000001 0x48ffbe7f80000000

def z997 : W := mkw 0x949fe497c856c1b1 0x4949fe497c856c1b 0x101fe007c01fc1f2 0x0101fe007c01fc1f

def z998 : W := mkw 0x0fbe99200c141408 0x00fbe99200c14140 0xfffffff83c1e3e0f 0xffffffff83c1e3e0

def z999 : W := mkw 0x0b215d3444001408 0x00b215d344400140 0xffe7fffcfc063f3f 0xfffe7fffcfc063f3

def z1000 : W := mkw 0x80cbc6d563096944 0x880cbc6d56309694 0xd1dbf7c72319f9cf 0x7d1dbf7c72319f9c

def z1001 : W := mkw 0x2960036837a03e0e 0x02960036837a03e0 0xefe007f83fe03e09 0xeefe007f83fe03e0

def z1002 : W := mkw 0x89abc5b540000000 0x089abc5b54000000 0x81e7e7f800000003 0xa81e7e7f80000000

def z1003 : W := mkw 0x22015f7c45207f1e 0x422015f7c45207f1 0x80001ff800003e04 0x180001ff800003e0

def z1004 : W := mkw 0x2040224837e2ff1e 0x42040224837e2ff1 0x600000003fe1fe08 0x0600000003fe1fe0

def z1005 : W := mkw 0x8dbfc5b7c0000000 0x08dbfc5b7c000000 0x8fffe7ffc0000003 0xe8fffe7ffc000000

def z1006 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x8fe3e7f800000001 0x08fe3e7f80000000

def z1007 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fffe8003fffe60f 0xe7fffe8003fffe60

def z1008 : W := mkw 0x2b601b6837a97f4e 0x82b601b6837a97f4 0xfff81fff3ff9ffcf 0xffff81fff3ff9ffc

def z1009 : W := mkw 0x9fbfddb7cc1414a9 0x09fbfddb7cc1414a 0xeffffffffc1e1ef7 0xfeffffffffc1e1ef

def z1010 : W := mkw 0x00ca024023092804 0x000ca02402309280 0xd1db17c72319f9cf 0x7d1db17c72319f9c

def z1011 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x6fe7e0003fe7c009 0xe6fe7e0003fe7c00

def z1012 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0xfe27ee3cffe7e73f 0xefe27ee3cffe7e73

def z1013 : W := mkw 0x89abc5b540000000 0x089abc5b54000000 0xd1fbf7ff201839cf 0x7d1fbf7ff201839c

def z1014 : W := mkw 0x008b449540000000 0x0008b44954000000 0x81e7effcc0000007 0xa81e7effcc000000

def z1015 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0xcfffffffe01818c7 0xfcfffffffe01818c

def z1016 : W := mkw 0x22403a4837e2ff1e 0x422403a4837e2ff1 0x7e041804ffe7ff3e 0xf7e041804ffe7ff3

def z1017 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x81ffffffc0000007 0x181ffffffc000000

def z1018 : W := mkw 0x496020003adf8000 0x0496020003adf800 0x7fe7e0003fffc00b 0xe7fe7e0003fffc00

def z1019 : W := mkw 0x00402248236beb56 0xc00402248236beb5 0x3000000003e7e738 0x03000000003e7e73

def z1020 : W := mkw 0x9fbfddb7cc1414a9 0x09fbfddb7cc1414a 0xbfffffffdc1e07f7 0xfbfffffffdc1e07f

def z1021 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xd1fb1fff2319f9cf 0xfd1fb1fff2319f9c

def z1022 : W := mkw 0x9fbfddb7cc1414a9 0x09fbfddb7cc1414a 0xfffffffffc1e18cf 0xffffffffffc1e18c

def z1023 : W := mkw 0x8b20d93040000000 0x08b20d9304000000 0x8fe0fff800000005 0xf8fe0fff80000000

def z1024 : W := mkw 0x9fbfddb7cc1414a9 0x09fbfddb7cc1414a 0x8fffffffdc000007 0xf8fffffffdc00000

def z1025 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x9fffffffc01801c7 0xf9fffffffc01801c

def z1026 : W := mkw 0x2b601b6837a93e0e 0x02b601b6837a93e0 0xffe01ff83ff9fe0d 0xfffe01ff83ff9fe0

def z1027 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x4fffe0003ff9c003 0xe4fffe0003ff9c00

def z1028 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0x51db11c72319f9ca 0x551db11c72319f9c

def z1029 : W := mkw 0x2b201b2815a0360e 0x02b201b2815a0360 0xafe01ff81fe0260d 0xfafe01ff81fe0260

def z1030 : W := mkw 0x02401a4827203e0e 0x002401a4827203e0 0xefe01ff83fe03e0d 0xfefe01ff83fe03e0

def z1031 : W := mkw 0x0b20192010800000 0x00b2019201080000 0xafe01ff81ce00005 0xfafe01ff81ce0000

def z1032 : W := mkw 0x00ca00c122090840 0x800ca00c12209084 0x41db11c32319d8c1 0x541db11c32319d8c

def z1033 : W := mkw 0x00402248236beb56 0xc00402248236beb5 0x0000000003e1c000 0x00000000003e1c00

def z1034 : W := mkw 0xafbfddb7d4801408 0x0afbfddb7d480140 0x8fffffffdc000007 0xf8fffffffdc00000

def z1035 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0xb1e7fffcc3e7e73f 0xfb1e7fffcc3e7e73

def z1036 : W := mkw 0x00cb46dd63296b56 0xc00cb46dd63296b5 0xf1df1fffe31fffff 0xff1df1fffe31ffff

def z1037 : W := mkw 0xa2015fffc5207f1e 0x4a2015fffc5207f1 0x80001fffc0003f34 0x180001fffc0003f3

def z1038 : W := mkw 0x3b601b6ab7a03eaf 0x03b601b6ab7a03ea 0xefe01ff8ffe03e3d 0xfefe01ff8ffe03e3

def z1039 : W := mkw 0x8fbed932c0000000 0x08fbed932c000000 0x8ffffff8c0000007 0xf8ffffff8c000000

def z1040 : W := mkw 0x8fbfddb7c0004140 0x88fbfddb7c000414 0x8fffffffc00001c7 0xf8fffffffc00001c

def z1041 : W := mkw 0x704022483fffbeaf 0x0704022483fffbea 0x700000003ffffff8 0x0700000003ffffff

def z1042 : W := mkw 0x00ca00c122090840 0x800ca00c12209084 0x51db11c72319f9cf 0x751db11c72319f9c

def z1043 : W := mkw 0x8babddb7c0000000 0x08babddb7c000000 0x81e7ffffc0000007 0xb81e7ffffc000000

def z1044 : W := mkw 0x8dbfc5b540000000 0x08dbfc5b54000000 0x8fe7e7f800000001 0x88fe7e7f80000000

def z1045 : W := mkw 0x0921453440000000 0x0092145344000000 0x81e7effcc0000007 0xa81e7effcc000000

def z1046 : W := mkw 0x9babddb7c40014a9 0x09babddb7c40014a 0x81e3ffffc0003ff5 0x181e3ffffc0003ff

def z1047 : W := mkw 0x3b601b6837a03eaf 0x03b601b6837a03ea 0xefe01ff83fe03ffd 0xfefe01ff83fe03ff

def z1048 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x6ffbe0003ff9c009 0xe6ffbe0003ff9c00

def z1049 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xf1db17c7231fffff 0x7f1db17c7231ffff

def z1050 : W := mkw 0x0920200010c28000 0x00920200010c2800 0x3e27e0001fe7c00b 0xa3e27e0001fe7c00

def z1051 : W := mkw 0x9fbfddb7c81400a1 0x09fbfddb7c81400a 0x8fffffffc01800c7 0xf8fffffffc01800c

def z1052 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x7e181807fc1e3ffc 0x57e181807fc1e3ff

def z1053 : W := mkw 0x49eaa00032cb8000 0x049eaa00032cb800 0x2fe3e0001fe1c001 0x82fe3e0001fe1c00

def z1054 : W := mkw 0x0baa992000000000 0x00baa99200000000 0x8fe3fff800000005 0xf8fe3fff80000000

def z1055 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0xffffffffe01e3fff 0xfffffffffe01e3ff

def z1056 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fffe800ffffc63b 0xe7fffe800ffffc63

def z1057 : W := mkw 0x00cb06cd23296b46 0x800cb06cd23296b4 0xd1db1fff2319ffcf 0x7d1db1fff2319ffc

def z1058 : W := mkw 0x828b5db7c0000000 0x0828b5db7c000000 0x81ffffffc0000007 0xf81ffffffc000000

def z1059 : W := mkw 0x8babddb540000000 0x08babddb54000000 0x8fe3eff800000001 0x88fe3eff80000000

def z1060 : W := mkw 0x0001665c4162eb16 0x40001665c4162eb1 0xb027fffcc3e7ff3f 0xbb027fffcc3e7ff3

def z1061 : W := mkw 0x00cb46dd63296b56 0xc00cb46dd63296b5 0xd1ffffffe319ffff 0xfd1ffffffe319fff

def z1062 : W := mkw 0x008b449540000000 0x0008b44954000000 0xf1ffffffe01e3fff 0xff1ffffffe01e3ff

def z1063 : W := mkw 0x9fbfddb7cc1414a9 0x09fbfddb7cc1414a 0xbfffffffdc06273f 0xfbfffffffdc06273

def z1064 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x3fffe0001fffc003 0x83fffe0001fffc00

def z1065 : W := mkw 0x161419228c1414a9 0x0161419228c1414a 0xfe1c1ffffc1e3ffe 0xffe1c1ffffc1e3ff

def z1066 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xc1db17c72319d8c7 0x7c1db17c72319d8c

def z1067 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0xb03ffe3fc3e7e73f 0xfb03ffe3fc3e7e73

def z1068 : W := mkw 0x9dbfc5b7c81400a1 0x09dbfc5b7c81400a 0x91ffe7ffc01e01f3 0x091ffe7ffc01e01f

def z1069 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x9fffffffc000210f 0xf9fffffffc000210

def z1070 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x8ffffffbc0000001 0xd8ffffffbc000000

def z1071 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe00ff83fe03e09 0x8efe00ff83fe03e0

def z1072 : W := mkw 0x0000601840628212 0x4000060184062821 0x3027e83cc3e7e73f 0xa3027e83cc3e7e73

def z1073 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xeff81ffb3ff83ecd 0xfeff81ffb3ff83ec

def z1074 : W := mkw 0x4dfea0813adf8040 0x84dfea0813adf804 0x7fffe0033fffc0cb 0xe7fffe0033fffc0c

def z1075 : W := mkw 0x4d74a0003ad68000 0x04d74a0003ad6800 0x7fe7e0003fe7c00b 0xe7fe7e0003fe7c00

def z1076 : W := mkw 0x00ca00c122090840 0x800ca00c12209084 0x51d811c32319d8c8 0x551d811c32319d8c

def z1077 : W := mkw 0x8f35dd36c0000000 0x08f35dd36c000000 0x8fe7fffcc0000007 0xf8fe7fffcc000000

def z1078 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xf1df17c7231ff9cf 0xff1df17c7231ff9c

def z1079 : W := mkw 0x8dbfc5b540000000 0x08dbfc5b54000000 0x8fffeffcc0000007 0xe8fffeffcc000000

def z1080 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x8ffbfffb00000005 0xf8ffbfffb0000000

def z1081 : W := mkw 0x8dbfc5b540000000 0x08dbfc5b54000000 0x81ffe7f800000003 0x081ffe7f80000000

def z1082 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0x7e1f1807ff1fffff 0xf7e1f1807ff1ffff

def z1083 : W := mkw 0x4dfea00032cb8000 0x04dfea00032cb800 0x6fffe0003fe1c00b 0xe6fffe0003fe1c00

def z1084 : W := mkw 0x00ca00c122090840 0x800ca00c12209084 0x51db11c32019d8c2 0x551db11c32019d8c

def z1085 : W := mkw 0x161418028c1414a9 0x0161418028c1414a 0xffdc1fc7fc1e3fff 0xfffdc1fc7fc1e3ff

def z1086 : W := mkw 0x4dfea002badf8000 0x04dfea002badf800 0x7fffe007ffffc00b 0xe7fffe007ffffc00

def z1087 : W := mkw 0x2960036833a02a06 0x02960036833a02a0 0xafe007f81fe00001 0x8afe007f81fe0000

def z1088 : W := mkw 0x00ca00c122094940 0x800ca00c12209494 0x51d811c32019d9c0 0x551d811c32019d9c

def z1089 : W := mkw 0x0b20593040000000 0x00b2059304000000 0x8fe4fff8c0000005 0xf8fe4fff8c000000

def z1090 : W := mkw 0x8f34d932c0000000 0x08f34d932c000000 0x8fe4eff8c0000001 0x88fe4eff8c000000

def z1091 : W := mkw 0x4d34a00018d68000 0x04d34a00018d6800 0x7e3fe0003fffc00b 0xe7e3fe0003fffc00

def z1092 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xd1db1fc7e319ffff 0x7d1db1fc7e319fff

def z1093 : W := mkw 0x00cb46d563096944 0x800cb46d56309694 0xd1fbf7ff2319f9cf 0x7d1fbf7ff2319f9c

def z1094 : W := mkw 0x0000200000428000 0x0000020000042800 0x7e27e0003fe7c00b 0xe7e27e0003fe7c00

def z1095 : W := mkw 0x49ebe6dd73ebeb56 0xc49ebe6dd73ebeb5 0x81e3e7f803e1c001 0x081e3e7f803e1c00

def z1096 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xd1db17c72319d9c3 0x5d1db17c72319d9c

def z1097 : W := mkw 0x9fbfddb7c81400a1 0x09fbfddb7c81400a 0xbfffffffc01e27ff 0xfbfffffffc01e27f

def z1098 : W := mkw 0x304022483ff6ffbf 0x4304022483ff6ffb 0x700000003ffffff8 0x0700000003ffffff

def z1099 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xafe01ff81fe00605 0xfafe01ff81fe0060

def z1100 : W := mkw 0x449ea000085f8000 0x0449ea000085f800 0x7e3fe0003fffc00b 0xe7e3fe0003fffc00

def z1101 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fffe0073fffc1cb 0xe7fffe0073fffc1c

def z1102 : W := mkw 0x22015ffd45207f5e 0xc22015ffd45207f5 0x80001fffc0003ff4 0x180001fffc0003ff

def z1103 : W := mkw 0x92015fbfc52077bf 0x492015fbfc52077b 0x80001fffc0003ff4 0x180001fffc0003ff

def z1104 : W := mkw 0x0001661c4162e316 0x40001661c4162e31 0xf027ee3ce3ffffff 0xaf027ee3ce3fffff

def z1105 : W := mkw 0x0414200008568000 0x0041420000856800 0x3e27e0001fe7c00b 0xa3e27e0001fe7c00

def z1106 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xc1db17c72319f9c5 0x5c1db17c72319f9c

def z1107 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xd1fff7c72319f9cf 0xfd1fff7c72319f9c

def z1108 : W := mkw 0x9fbfddb7c00000a1 0x09fbfddb7c00000a 0x8fffffffc00001f7 0xf8fffffffc00001f

def z1109 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7ffff0003ffff80f 0xf7ffff0003ffff80

def z1110 : W := mkw 0x8f34d932c0000000 0x08f34d932c000000 0x8ffcffffc0000007 0xf8ffcffffc000000

def z1111 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0xffffee383fffc00f 0xeffffee383fffc00

def z1112 : W := mkw 0x9fbfddb7cc1414a9 0x09fbfddb7cc1414a 0xcffbf7fb3c1818c1 0x5cffbf7fb3c1818c

def z1113 : W := mkw 0x8dbfc5b7c0000000 0x08dbfc5b7c000000 0x81fbe7fb00000001 0x081fbe7fb0000000

def z1114 : W := mkw 0x9fbfddb7cc1414a9 0x09fbfddb7cc1414a 0xcffffffffc183ff7 0xfcffffffffc183ff

def z1115 : W := mkw 0x5dfea002badf80a1 0x05dfea002badf80a 0x7fffe000ffffc03b 0xe7fffe000ffffc03

def z1116 : W := mkw 0x9fbfddb7c40014a9 0x09fbfddb7c40014a 0xdfffffffe0183fff 0xfdfffffffe0183ff

def z1117 : W := mkw 0x09ea200032cb8000 0x009ea200032cb800 0x7fffe0003fffc00b 0xe7fffe0003fffc00

def z1118 : W := mkw 0x0414000008140000 0x0041400000814000 0x7e1c1807fc1e3ffe 0xf7e1c1807fc1e3ff

def z1119 : W := mkw 0x4dfea0c13adf8840 0x84dfea0c13adf884 0x7ffff1c73ffff9cf 0xf7ffff1c73ffff9c

def z1120 : W := mkw 0x3b601b6ab7a03eaf 0x03b601b6ab7a03ea 0xefe01ffb3fe03ecd 0xfefe01ffb3fe03ec

def z1121 : W := mkw 0x89abc5b540094140 0x889abc5b54009414 0x81e3e7f80001c001 0x081e3e7f80001c00

def z1122 : W := mkw 0x149f6497c85fc1f1 0xc149f6497c85fc1f 0x101fe007c01fc1f2 0x0101fe007c01fc1f

def z1123 : W := mkw 0x3f34793adcf696bb 0x43f34793adcf696b 0x2e24e838dce60630 0x82e24e838dce6063

def z1124 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x8fe7fff8c0000005 0xf8fe7fff8c000000

def z1125 : W := mkw 0x2b60192836a0160a 0x02b60192836a0160 0xefe01ff83fe0060d 0xfefe01ff83fe0060

def z1126 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xd1df1fc7e319f9cf 0xfd1df1fc7e319f9c

def z1127 : W := mkw 0x9fbfddb7cc1414a9 0x09fbfddb7cc1414a 0xafe7eff8dc060631 0x8afe7eff8dc06063

def z1128 : W := mkw 0x7ffe9962be9d1ca9 0x07ffe9962be9d1ca 0x4fd811c33c1818c0 0x54fd811c33c1818c

def z1129 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xcfe01ff83fe01805 0xfcfe01ff83fe0180

def z1130 : W := mkw 0x12015e1ec52077bf 0x412015e1ec52077b 0x80000e3cc0002734 0x080000e3cc000273

def z1131 : W := mkw 0x9fbfddb7c40014a9 0x09fbfddb7c40014a 0x8fffffffc0000637 0xf8fffffffc000063

def z1132 : W := mkw 0x9fbfddb7cc1414a9 0x09fbfddb7cc1414a 0xdffffffffc1839cf 0xfdffffffffc1839c

def z1133 : W := mkw 0x0f34992000000000 0x00f3499200000000 0x8fe4fff800000005 0xf8fe4fff80000000

def z1134 : W := mkw 0x0b601b2833a02206 0x00b601b2833a0220 0xefe01ff83fe0260d 0xfefe01ff83fe0260

def z1135 : W := mkw 0x5dfea0003adf80a1 0x05dfea0003adf80a 0x7fffe0003fffc1fb 0xe7fffe0003fffc1f

def z1136 : W := mkw 0x09aa812000000000 0x009aa81200000000 0x81e3e7f800000001 0x081e3e7f80000000

def z1137 : W := mkw 0x4dfea0813adf8000 0x04dfea0813adf800 0x7ffff1c33fffc00b 0xf7ffff1c33fffc00

def z1138 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x8ffff7ffc0000003 0x58ffff7ffc000000

def z1139 : W := mkw 0x4dfea0403adf8840 0x84dfea0403adf884 0x7fffe0003fffd8cb 0xe7fffe0003fffd8c

def z1140 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x9fffffffc0060137 0xf9fffffffc006013

def z1141 : W := mkw 0x89abc5b540094140 0x889abc5b54009414 0x91fbe7ff0019c1c3 0x091fbe7ff0019c1c

def z1142 : W := mkw 0x604022483bffaa06 0x0604022483bffaa0 0x700000003fffc008 0x0700000003fffc00

def z1143 : W := mkw 0x00cb06c533896944 0x800cb06c53389694 0xf1db17c73ff9f9cf 0x7f1db17c73ff9f9c

def z1144 : W := mkw 0x0f355d36c0000000 0x00f355d36c000000 0x8fffffffc0000007 0xf8fffffffc000000

def z1145 : W := mkw 0x0d7420003ad68000 0x00d7420003ad6800 0x7fffe0003fffc00b 0xe7fffe0003fffc00

def z1146 : W := mkw 0x449fe495485fc150 0xc449fe495485fc15 0x101fe007c01fc1f2 0x0101fe007c01fc1f

def z1147 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xafe01ff81fe03e05 0x9afe01ff81fe03e0

def z1148 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x8ffbf7ff00000007 0x78ffbf7ff0000000

def z1149 : W := mkw 0x00ca02c123092844 0x800ca02c12309284 0xd1db17c32319f8cf 0x7d1db17c32319f8c

def z1150 : W := mkw 0x00ca02c123096944 0x800ca02c12309694 0xd1d817c32319f9cd 0x7d1d817c32319f9c

def z1151 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xefe41ffcffe03e0f 0xfefe41ffcffe03e0

def z1152 : W := mkw 0x00cb46dd63296b46 0x800cb46dd63296b4 0xf1ffffffe3f9ffcf 0xff1ffffffe3f9ffc

def z1153 : W := mkw 0x89abc5b540000000 0x089abc5b54000000 0x81fbf7fb00000001 0x581fbf7fb0000000

def z1154 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x7fffe804ffffc00f 0xe7fffe804ffffc00

def z1155 : W := mkw 0x00cb06cd23296b56 0xc00cb06cd23296b5 0xd1db17c72319ffff 0x7d1db17c72319fff

def z1156 : W := mkw 0x4dfea0003adf8000 0x04dfea0003adf800 0x0fe3e0001fe1c001 0x00fe3e0001fe1c00

def z1157 : W := mkw 0x8babddb540000000 0x08babddb54000000 0x8fe3f7f800000001 0x58fe3f7f80000000

def z1158 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xd1d817c72319f9cc 0x5d1d817c72319f9c

def z1159 : W := mkw 0x8fbed9b3c0000000 0x08fbed9b3c000000 0x8ffcfffbc0000005 0xf8ffcfffbc000000

def z1160 : W := mkw 0x0041064423006904 0x0004106442300690 0xd1db17c72319f9cf 0x7d1db17c72319f9c

def z1161 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0xafffffffc3e0000f 0xfafffffffc3e0000

def z1162 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xffe01ffc3fe03f0f 0xfffe01ffc3fe03f0

def z1163 : W := mkw 0x2b60196836a01e0a 0x02b60196836a01e0 0xefe01ff83ce01e05 0xfefe01ff83ce01e0

def z1164 : W := mkw 0x8fbfddb7c0000000 0x08fbfddb7c000000 0x8fffefffc0000003 0x88fffefffc000000

def z1165 : W := mkw 0x6040224837ebbe0e 0x06040224837ebbe0 0x600000003fe1fe08 0x0600000003fe1fe0

def z1166 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xfffc1ffffffe3fff 0xffffc1ffffffe3ff

def z1167 : W := mkw 0x00cb06c523096944 0x800cb06c52309694 0xd1db17c72019f9c6 0x5d1db17c72019f9c

def z1168 : W := mkw 0x8fbfddb7c0090000 0x08fbfddb7c009000 0x9fffffffc019c007 0xf9fffffffc019c00

def z1169 : W := mkw 0x2b601b6837a03e0e 0x02b601b6837a03e0 0xffe01ff83ff83fcd 0xfffe01ff83ff83fc

def z1170 : W := mkw 0x9fbfddb7c81400a1 0x09fbfddb7c81400a 0x8fffffffc0060037 0xf8fffffffc006003

def z1171 : W := mkw 0x00cb06cd23296b46 0x800cb06cd23296b4 0xf1ff1fffe3ffffff 0xff1ff1fffe3fffff

def z1172 : W := mkw 0x89abc5b540000000 0x089abc5b54000000 0x81e3f7ff00000005 0x181e3f7ff0000000

def z1173 : W := mkw 0x7f34b92a9cf696ab 0x07f34b92a9cf696a 0x2e24e838dce60630 0x82e24e838dce6063

def z1174 : W := mkw 0x8920c13040000000 0x08920c1304000000 0x81e0e7f800000001 0x081e0e7f80000000

def z1175 : W := mkw 0x8fbe99a380000000 0x08fbe99a38000000 0x8ffffffb00000007 0xf8ffffffb0000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z7,z2,z3,z4,z8,z9]),(0,[z0,z2,z10,z3,z4,z8,z6]),(0,[z0,z2,z3,z11,z4,z8,z6]),(0,[z0,z2,z12,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z13,z14]),(0,[z0,z2,z15,z3,z16,z8,z6]),(0,[z0,z2,z3,z4,z13,z6,z17])],[(0,[z0,z18,z19,z3,z4,z8,z6]),(0,[z0,z20,z2,z3,z4,z8,z6]),(0,[z0,z21,z2,z3,z4,z8,z22]),(0,[z0,z2,z23,z3,z24,z8,z6]),(0,[z25,z0,z2,z3,z4,z8,z14]),(0,[z0,z2,z3,z4,z8,z6,z26]),(0,[z0,z2,z3,z4,z27,z8,z6]),(0,[z0,z2,z28,z3,z4,z8,z6])],[(0,[z0,z29,z2,z3,z4,z8,z6]),(0,[z30,z2,z3,z4,z8,z31,z6]),(0,[z0,z2,z3,z4,z8,z32,z6]),(0,[z0,z2,z3,z4,z33,z8,z6]),(0,[z0,z2,z34,z3,z4,z8,z6]),(0,[z0,z18,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z35,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z36])],[(0,[z0,z2,z37,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z38,z8,z6])],[(0,[z39,z0,z2,z3,z4,z8,z6]),(0,[z40,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z41,z4,z42,z6]),(0,[z0,z2,z3,z41,z4,z43,z6])],[(0,[z0,z2,z3,z44,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z45,z6]),(0,[z0,z2,z3,z4,z8,z46,z47])],[(1,[z0,z48,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z49,z6]),(0,[z0,z2,z3,z4,z8,z50,z6]),(0,[z0,z51,z2,z3,z4,z8,z46])],[(0,[z0,z2,z52,z3,z4,z53,z8]),(0,[z0,z2,z3,z4,z8,z54,z6]),(0,[z0,z2,z3,z4,z8,z55,z6]),(0,[z0,z2,z3,z4,z8,z56,z46]),(0,[z0,z2,z3,z4,z8,z57,z6])]],
   [[(0,[z58,z0,z59,z3,z4,z8,z6]),(0,[z0,z2,z3,z60,z4,z8,z6]),(0,[z0,z61,z2,z3,z4,z8,z6]),(0,[z0,z62,z2,z3,z4,z8,z6]),(0,[z63,z0,z2,z3,z4,z8,z6]),(1,[z0,z2,z3,z4,z8,z64])],[(0,[z65,z0,z2,z3,z16,z4,z8]),(0,[z0,z2,z3,z4,z8,z6,z66]),(0,[z0,z2,z3,z4,z67,z8,z14]),(1,[z0,z2,z3,z4,z68,z6]),(0,[z0,z2,z69,z3,z4,z8,z6]),(0,[z0,z2,z70,z3,z4,z8,z14])],[(0,[z71,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z43,z8,z14]),(0,[z0,z2,z3,z4,z8,z72,z6])],[(0,[z73,z0,z2,z3,z4,z8,z6]),(1,[z0,z74,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z75,z8,z6])],[(0,[z0,z2,z3,z4,z8,z76,z6]),(0,[z0,z2,z77,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z46]),(0,[z0,z2,z3,z4,z8,z14,z26])],[(0,[z39,z0,z2,z78,z4,z8,z6]),(0,[z0,z2,z3,z79,z4,z8,z6]),(1,[z0,z2,z3,z4,z8,z80]),(0,[z0,z2,z3,z4,z81,z8,z6]),(0,[z0,z82,z2,z3,z4,z8,z46])],[(0,[z0,z83,z19,z3,z4,z8,z6]),(0,[z0,z2,z84,z3,z4,z8,z6]),(0,[z0,z2,z3,z3,z4,z8,z14])],[(0,[z85,z0,z2,z3,z4,z8,z14]),(0,[z0,z2,z3,z86,z4,z8,z6]),(0,[z0,z2,z78,z3,z4,z8,z87]),(0,[z0,z2,z3,z4,z8,z88,z6]),(0,[z0,z2,z89,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z90]),(0,[z0,z83,z2,z3,z4,z8,z6]),(0,[z91,z0,z83,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z92,z6]),(0,[z0,z2,z3,z4,z93,z8,z6]),(0,[z0,z94,z2,z3,z4,z8,z6])]],
   [[(1,[z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z95,z4,z8,z6]),(0,[z96,z0,z97,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z98,z8,z6])],[(0,[z99,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z100]),(0,[z0,z2,z3,z101,z4,z8,z14]),(0,[z0,z2,z3,z102,z4,z8,z14]),(0,[z0,z2,z3,z103,z4,z8,z6]),(0,[z0,z2,z3,z104,z4,z8,z6])],[(1,[z105,z1,z3,z4,z8,z6]),(0,[z106,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z107,z3,z4,z56,z6]),(0,[z0,z2,z3,z4,z108,z8,z6]),(0,[z0,z2,z109,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z110,z8,z6])],[(0,[z0,z2,z3,z4,z111,z8,z6]),(0,[z0,z2,z3,z4,z112,z8,z6]),(1,[z0,z2,z15,z3,z8,z113])],[(0,[z0,z2,z114,z3,z4,z8,z6]),(0,[z0,z2,z115,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z116,z8,z46]),(0,[z0,z51,z2,z3,z117,z8,z6]),(0,[z0,z2,z3,z118,z4,z8,z6]),(0,[z119,z0,z2,z3,z4,z8,z14])],[(0,[z0,z2,z3,z4,z120,z8,z6]),(0,[z65,z0,z121,z3,z4,z8,z6]),(0,[z122,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z123,z4,z8,z46]),(0,[z0,z2,z3,z4,z8,z6,z124])],[(0,[z0,z2,z3,z4,z8,z125,z6]),(0,[z0,z2,z126,z3,z4,z8,z6]),(0,[z127,z0,z2,z3,z4,z8,z6])],[(0,[z128,z0,z2,z3,z4,z8,z6]),(0,[z129,z0,z61,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z130,z6]),(0,[z0,z2,z3,z4,z8,z131,z6]),(0,[z0,z2,z23,z3,z4,z8,z14]),(0,[z0,z2,z132,z3,z4,z56,z6])]],
   [[(0,[z39,z2,z78,z3,z4,z8,z6]),(0,[z133,z0,z2,z3,z4,z8,z46]),(0,[z134,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z135,z8,z6]),(0,[z136,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z137,z8,z6]),(0,[z0,z2,z3,z4,z138,z56,z6]),(0,[z0,z2,z3,z4,z8,z22,z46]),(0,[z0,z139,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z140,z8,z6]),(0,[z0,z2,z3,z4,z8,z5,z6]),(0,[z129,z0,z141,z3,z4,z8,z6]),(0,[z0,z2,z3,z142,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z143]),(1,[z0,z2,z144,z3,z4,z8]),(0,[z0,z2,z145,z3,z4,z8,z6])],[(0,[z0,z1,z3,z4,z138,z8,z6]),(0,[z0,z2,z3,z146,z4,z8,z6]),(0,[z0,z21,z3,z4,z8,z6,z22]),(0,[z0,z2,z3,z4,z147,z8,z6]),(0,[z0,z2,z3,z4,z8,z148,z6]),(0,[z0,z2,z3,z149,z4,z8,z6])],[(0,[z0,z150,z2,z3,z4,z8,z6]),(1,[z91,z0,z3,z4,z138,z6]),(1,[z0,z18,z3,z4,z8,z151]),(0,[z0,z2,z3,z4,z8,z13,z46])],[(0,[z152,z0,z2,z3,z4,z8,z6]),(0,[z30,z2,z19,z3,z4,z8,z6]),(0,[z0,z153,z2,z3,z4,z8,z6]),(1,[z0,z2,z154,z3,z4,z6]),(0,[z0,z2,z3,z4,z116,z8,z6]),(0,[z0,z2,z3,z155,z4,z8,z6]),(0,[z0,z2,z156,z132,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z17])],[(0,[z157,z0,z2,z3,z16,z4,z8]),(0,[z0,z2,z158,z3,z4,z8,z6]),(0,[z159,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z160,z4,z8,z6])],[(0,[z161,z0,z2,z3,z4,z8,z6]),(1,[z71,z2,z3,z4,z8,z6]),(0,[z0,z162,z2,z3,z4,z8,z6])],[(0,[z163,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z164,z4,z8,z6]),(0,[z0,z2,z3,z165,z4,z53,z8]),(0,[z0,z83,z2,z3,z4,z166,z6])]],
   [[(1,[z0,z167,z2,z3,z4,z8]),(0,[z133,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z168,z3,z4,z8,z6]),(0,[z0,z2,z15,z3,z4,z8,z113])],[(0,[z0,z0,z2,z3,z4,z8,z6]),(0,[z0,z19,z3,z102,z4,z8,z6]),(0,[z105,z2,z3,z4,z116,z8,z6]),(0,[z58,z0,z2,z3,z4,z169,z6]),(0,[z0,z2,z3,z4,z8,z6,z170]),(0,[z0,z2,z3,z4,z171,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z172]),(0,[z0,z2,z173,z3,z4,z8,z6])],[(0,[z0,z2,z174,z3,z4,z8,z6]),(0,[z0,z18,z2,z3,z4,z8,z14]),(0,[z0,z2,z3,z4,z8,z175,z6]),(0,[z0,z176,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z177]),(0,[z0,z2,z178,z3,z4,z8,z6])],[(0,[z0,z7,z1,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z4,z8,z6]),(0,[z71,z91,z2,z3,z4,z8,z6])],[(0,[z0,z2,z52,z3,z4,z8,z6]),(0,[z0,z2,z179,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z180,z6]),(0,[z0,z2,z70,z3,z4,z8,z46])],[(0,[z0,z2,z3,z4,z8,z6,z181]),(1,[z0,z2,z3,z4,z8,z182]),(0,[z0,z2,z3,z4,z43,z8,z46]),(0,[z0,z2,z3,z4,z8,z45,z14])],[(0,[z105,z0,z2,z3,z4,z8,z6]),(0,[z30,z105,z2,z3,z4,z8,z6]),(0,[z0,z1,z97,z3,z4,z8,z6]),(0,[z0,z2,z3,z183,z4,z53,z6]),(0,[z65,z0,z21,z2,z3,z4,z8])],[]],
   [[],[(0,[z0,z2,z3,z4,z117,z8,z6]),(0,[z0,z2,z3,z4,z8,z184,z6]),(0,[z0,z2,z3,z4,z8,z6,z185]),(0,[z0,z2,z3,z4,z8,z186,z6]),(0,[z0,z2,z3,z3,z4,z8,z46]),(0,[z0,z2,z69,z3,z4,z8,z14])],[(0,[z85,z0,z2,z3,z4,z8,z46]),(0,[z0,z2,z3,z4,z187,z8,z6]),(1,[z65,z2,z3,z4,z8,z188])],[(0,[z0,z1,z3,z4,z8,z6,z22]),(0,[z0,z2,z3,z4,z8,z189,z6]),(0,[z0,z2,z190,z3,z4,z8,z6]),(0,[z0,z2,z3,z191,z4,z8,z6])],[(0,[z0,z2,z192,z3,z4,z8,z6]),(0,[z58,z0,z2,z3,z4,z8,z193]),(0,[z0,z2,z3,z101,z4,z8,z46]),(0,[z0,z2,z3,z4,z8,z6,z188]),(0,[z0,z2,z3,z102,z4,z8,z46]),(0,[z0,z2,z194,z3,z4,z8,z195]),(0,[z0,z7,z3,z196,z4,z8,z6]),(0,[z0,z2,z3,z196,z67,z8,z6]),(0,[z0,z2,z3,z4,z67,z8,z6]),(0,[z0,z2,z70,z3,z4,z8,z6]),(0,[z0,z2,z3,z197,z4,z8,z6])],[(0,[z0,z2,z198,z3,z4,z8,z6]),(0,[z199,z0,z2,z3,z4,z8,z6]),(0,[z0,z200,z2,z3,z4,z8,z6]),(0,[z0,z2,z201,z3,z4,z8,z6]),(0,[z0,z2,z15,z202,z3,z4,z8])],[(0,[z0,z203,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z24,z53,z8,z6]),(0,[z0,z204,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z8,z6]),(0,[z0,z2,z3,z4,z205,z8,z6])],[(0,[z0,z83,z2,z3,z4,z8,z14]),(0,[z119,z0,z2,z3,z4,z8,z46])]],
   [[(0,[z1,z2,z19,z3,z4,z8,z6]),(1,[z0,z2,z3,z4,z8,z206]),(0,[z0,z2,z3,z183,z4,z8,z6]),(0,[z0,z2,z3,z207,z4,z8,z6]),(0,[z0,z2,z208,z3,z4,z8,z6]),(1,[z0,z2,z3,z4,z8,z14]),(0,[z0,z2,z107,z3,z41,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z113])],[(0,[z0,z2,z3,z4,z209,z8,z6]),(0,[z0,z2,z210,z3,z4,z8,z6]),(0,[z0,z2,z211,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z195,z6]),(0,[z0,z212,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z213,z14])],[(0,[z0,z18,z3,z4,z8,z151,z6]),(0,[z0,z2,z23,z3,z4,z8,z46]),(0,[z0,z2,z3,z8,z213,z6,z113])],[(0,[z0,z2,z3,z4,z8,z214,z6])],[(0,[z215,z0,z2,z3,z4,z8,z6]),(0,[z216,z0,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z217,z8,z6]),(0,[z0,z1,z2,z3,z4,z8,z14]),(0,[z0,z2,z218,z3,z67,z8,z6]),(0,[z0,z2,z202,z3,z4,z8,z13])],[(0,[z0,z2,z219,z3,z4,z8,z6]),(0,[z0,z2,z3,z220,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z221,z6]),(0,[z0,z2,z222,z3,z4,z8,z6]),(0,[z0,z2,z3,z223,z4,z8,z6]),(0,[z0,z2,z224,z3,z4,z8,z6])],[(0,[z225,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z226,z6]),(0,[z0,z2,z3,z4,z227,z8,z6]),(0,[z0,z2,z228,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z229,z6])]],
   [[(0,[z129,z0,z2,z3,z4,z8,z6])],[(0,[z105,z85,z2,z3,z4,z8,z6]),(0,[z0,z2,z230,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z231,z6]),(0,[z157,z0,z18,z2,z3,z4,z8]),(0,[z0,z2,z3,z4,z8,z232,z6]),(0,[z233,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z234,z6]),(0,[z0,z2,z3,z235,z4,z8,z6])],[(0,[z2,z19,z3,z4,z116,z8,z6]),(0,[z30,z0,z2,z3,z41,z4,z6]),(0,[z0,z2,z194,z3,z4,z8,z46]),(0,[z0,z2,z236,z3,z4,z8,z6])],[(0,[z237,z0,z2,z3,z4,z8,z6]),(0,[z30,z0,z2,z107,z3,z4,z6]),(0,[z0,z2,z12,z3,z4,z8,z46]),(0,[z0,z2,z238,z3,z4,z8,z6])],[(0,[z0,z2,z3,z165,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z239]),(0,[z240,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z241,z6])],[(0,[z0,z2,z3,z242,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z243]),(0,[z0,z2,z3,z4,z8,z244,z6]),(1,[z0,z2,z3,z4,z8,z195]),(0,[z0,z18,z2,z3,z4,z8,z46]),(0,[z0,z2,z3,z4,z8,z245,z6])],[(0,[z246,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z247]),(1,[z0,z2,z3,z248,z8,z6]),(0,[z0,z2,z3,z4,z8,z166,z6]),(0,[z0,z2,z3,z4,z8,z6,z249])],[(0,[z39,z0,z2,z3,z4,z8,z46]),(0,[z0,z2,z3,z250,z4,z8,z6]),(0,[z0,z2,z3,z4,z251,z8,z6])]],
   [[(1,[z0,z2,z3,z252,z8,z6]),(0,[z2,z3,z4,z116,z8,z31,z6]),(0,[z0,z2,z253,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z254])],[(0,[z58,z39,z2,z3,z4,z8,z6]),(0,[z255,z0,z2,z3,z4,z8,z6])],[(0,[z0,z2,z256,z3,z4,z8,z6]),(0,[z96,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z257,z6]),(0,[z0,z2,z3,z4,z8,z6,z258])],[(0,[z0,z2,z3,z259,z4,z8,z6]),(0,[z260,z0,z2,z3,z4,z8,z6]),(0,[z261,z0,z2,z3,z41,z4,z6]),(0,[z0,z2,z3,z4,z262,z8,z6]),(0,[z0,z2,z3,z196,z4,z8,z14]),(0,[z0,z2,z132,z3,z4,z8,z263]),(0,[z0,z2,z264,z3,z4,z8,z6])],[],[(0,[z0,z2,z3,z4,z8,z265,z6]),(0,[z0,z2,z3,z266,z4,z8,z6]),(0,[z96,z0,z2,z102,z4,z8,z6]),(0,[z0,z267,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z268,z6]),(0,[z0,z269,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z270,z4,z8,z6]),(0,[z105,z0,z2,z3,z4,z8,z14]),(0,[z0,z2,z271,z3,z4,z8,z6]),(0,[z0,z2,z272,z3,z4,z8,z6]),(0,[z273,z0,z2,z3,z4,z8,z6]),(0,[z274,z0,z2,z3,z4,z8,z6])],[(0,[z0,z2,z154,z3,z4,z8,z6]),(0,[z0,z275,z2,z3,z4,z8,z6]),(0,[z0,z21,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z276,z8,z6]),(0,[z0,z277,z2,z3,z4,z8,z6])]],
   [[(0,[z0,z2,z3,z53,z67,z8,z6]),(0,[z0,z2,z156,z3,z4,z56,z6]),(0,[z0,z2,z3,z4,z8,z14,z278])],[(1,[z39,z2,z78,z4,z8,z6]),(1,[z0,z2,z3,z4,z33,z6]),(0,[z0,z2,z3,z4,z117,z8,z14]),(0,[z0,z2,z279,z3,z4,z8,z6]),(0,[z0,z2,z3,z43,z8,z213,z6])],[(0,[z0,z2,z3,z4,z280,z8,z6]),(0,[z0,z281,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z282,z4,z8,z6]),(0,[z0,z83,z2,z3,z4,z8,z46]),(0,[z0,z2,z132,z4,z42,z8,z6])],[(0,[z0,z2,z283,z3,z4,z8,z6]),(0,[z284,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z285,z8,z6]),(0,[z0,z286,z2,z3,z4,z8,z6]),(1,[z0,z2,z3,z4,z8,z46])],[(0,[z0,z2,z3,z4,z8,z6,z287]),(0,[z0,z2,z3,z4,z8,z6,z288])],[(0,[z0,z74,z2,z3,z4,z8,z6]),(0,[z289,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z290]),(0,[z0,z2,z3,z4,z8,z291,z6]),(0,[z0,z2,z292,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z293])],[(1,[z0,z2,z3,z4,z8,z90]),(0,[z0,z97,z2,z194,z4,z8,z6]),(0,[z0,z2,z294,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z295,z6])],[(0,[z58,z0,z74,z3,z4,z8,z6]),(0,[z0,z2,z3,z296,z4,z8,z6]),(0,[z0,z2,z297,z3,z4,z8,z6]),(0,[z0,z18,z2,z3,z4,z8,z151]),(0,[z0,z2,z3,z298,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z241,z299])]],
   [[(0,[z300,z0,z2,z3,z4,z8,z6]),(1,[z129,z2,z3,z53,z8,z6]),(0,[z0,z2,z3,z4,z31,z56,z6]),(0,[z0,z2,z3,z4,z8,z6,z301]),(1,[z0,z2,z236,z4,z8,z46])],[(0,[z0,z21,z2,z3,z4,z8,z151]),(0,[z0,z2,z302,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z303,z6])],[(0,[z0,z2,z3,z4,z8,z130,z46]),(0,[z0,z2,z3,z4,z8,z304,z6]),(0,[z0,z305,z2,z3,z4,z8,z6]),(0,[z128,z0,z2,z3,z4,z8,z46])],[(0,[z0,z2,z3,z4,z252,z8,z6]),(0,[z0,z2,z3,z4,z306,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z9]),(0,[z0,z2,z3,z4,z8,z14,z22]),(0,[z0,z2,z3,z4,z307,z8,z6]),(0,[z0,z2,z3,z4,z8,z308,z6])],[(0,[z58,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z196,z8,z213,z6]),(0,[z0,z2,z3,z309,z4,z8,z6]),(0,[z216,z0,z2,z3,z4,z8,z14]),(0,[z0,z2,z3,z4,z8,z213,z6])],[(0,[z0,z2,z3,z24,z101,z8,z6]),(0,[z0,z2,z310,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z182,z6]),(0,[z0,z2,z3,z4,z68,z8,z6]),(0,[z0,z2,z3,z41,z4,z56,z6]),(0,[z0,z2,z311,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z299,z6])],[(0,[z105,z39,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z143,z46]),(0,[z0,z2,z3,z4,z8,z312,z6])],[(0,[z0,z7,z2,z3,z4,z8,z313]),(0,[z0,z2,z3,z314,z4,z8,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z8,z6]),(0,[z129,z0,z2,z3,z4,z8,z14]),(0,[z0,z2,z3,z315,z4,z8,z6]),(0,[z316,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z317,z6]),(0,[z0,z2,z318,z3,z4,z8,z6]),(0,[z0,z2,z236,z4,z8,z6,z46]),(0,[z0,z2,z3,z4,z319,z8,z46])],[(0,[z0,z2,z3,z4,z8,z320,z6]),(0,[z0,z19,z3,z4,z117,z8,z6]),(0,[z0,z2,z3,z4,z321,z8,z6]),(0,[z0,z2,z3,z322,z4,z8,z6]),(0,[z0,z2,z202,z3,z4,z6,z17])],[(0,[z0,z2,z3,z4,z323,z8,z6]),(0,[z0,z2,z324,z3,z4,z8,z6]),(0,[z0,z2,z236,z3,z4,z8,z14])],[(0,[z39,z0,z2,z266,z4,z8,z6]),(0,[z0,z2,z325,z3,z4,z8,z14]),(0,[z0,z2,z107,z15,z3,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z326])],[(0,[z0,z2,z3,z4,z8,z327,z6]),(0,[z0,z2,z3,z4,z8,z328,z6]),(0,[z0,z2,z132,z3,z35,z8,z6])],[(0,[z105,z1,z2,z3,z4,z8,z6]),(0,[z329,z0,z2,z3,z4,z8,z6]),(0,[z0,z330,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z331,z4,z8,z6]),(0,[z0,z2,z332,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z333,z8,z6]),(0,[z0,z2,z334,z3,z8,z6,z17])],[(1,[z0,z2,z3,z60,z8,z6]),(0,[z0,z2,z335,z3,z4,z53,z6]),(0,[z0,z336,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z166,z14]),(0,[z0,z2,z156,z3,z4,z8,z258])],[]],
   [[(0,[z0,z2,z3,z4,z8,z337,z6]),(0,[z0,z2,z3,z4,z319,z8,z6])],[(0,[z105,z0,z2,z3,z4,z8,z46]),(0,[z0,z2,z3,z4,z166,z56,z6])],[(0,[z338,z0,z2,z3,z4,z8,z6]),(0,[z96,z0,z2,z3,z4,z8,z14]),(0,[z0,z2,z3,z4,z339,z13,z6])],[(1,[z261,z2,z3,z4,z116,z6]),(0,[z0,z2,z340,z3,z4,z8,z6]),(0,[z0,z2,z3,z24,z43,z8,z6])],[(1,[z0,z2,z3,z4,z8,z87]),(0,[z261,z0,z341,z3,z4,z8,z6]),(0,[z2,z3,z4,z8,z130,z6,z188]),(0,[z0,z2,z3,z4,z117,z8,z46]),(0,[z342,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z343])],[(0,[z0,z2,z3,z266,z4,z8,z14]),(0,[z0,z2,z344,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z345,z6])],[(0,[z0,z2,z3,z196,z4,z8,z6]),(0,[z0,z2,z3,z346,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z347]),(0,[z0,z2,z132,z3,z98,z8,z6])],[(0,[z0,z2,z348,z3,z4,z8,z6]),(0,[z0,z21,z2,z3,z4,z8,z14]),(0,[z0,z2,z3,z4,z8,z6,z349]),(0,[z0,z2,z3,z4,z67,z8,z46])]],
   [[(0,[z350,z0,z2,z3,z4,z8,z6]),(0,[z105,z0,z19,z3,z4,z8,z6]),(1,[z0,z2,z335,z3,z4,z6]),(0,[z0,z2,z335,z3,z4,z8,z6]),(0,[z0,z2,z351,z3,z4,z8,z6]),(0,[z65,z0,z18,z2,z3,z4,z8]),(0,[z0,z2,z3,z4,z8,z6,z352]),(0,[z0,z2,z3,z4,z353,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z354]),(0,[z0,z2,z3,z4,z8,z46,z46]),(0,[z0,z2,z355,z3,z4,z8,z6])],[(0,[z356,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z357,z4,z8,z6]),(0,[z157,z2,z3,z4,z8,z130,z6])],[(0,[z65,z2,z3,z4,z8,z6,z188]),(0,[z0,z2,z218,z4,z67,z8,z6]),(1,[z0,z2,z334,z3,z8,z6])],[(0,[z0,z2,z3,z4,z358,z8,z6]),(0,[z0,z2,z359,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z360,z6]),(0,[z0,z2,z202,z3,z4,z8,z6])],[(0,[z0,z2,z59,z3,z4,z8,z6]),(0,[z0,z2,z361,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z362,z6]),(0,[z0,z363,z2,z3,z4,z8,z6]),(0,[z0,z2,z364,z3,z4,z8,z6])],[(1,[z0,z2,z3,z16,z8,z213]),(0,[z0,z2,z3,z365,z4,z8,z6])],[(0,[z0,z2,z3,z4,z366,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z367])],[(0,[z133,z0,z2,z3,z53,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z368]),(0,[z0,z369,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z370]),(0,[z0,z2,z218,z3,z4,z8,z6])]],
   [[(0,[z0,z371,z2,z3,z4,z8,z6]),(0,[z0,z2,z372,z3,z4,z8,z6]),(0,[z0,z2,z23,z3,z4,z8,z373]),(0,[z0,z2,z3,z374,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z375,z6])],[(0,[z0,z2,z3,z376,z4,z8,z6]),(0,[z65,z0,z377,z3,z4,z8,z6]),(0,[z0,z2,z378,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z379,z8,z6]),(0,[z91,z380,z2,z3,z4,z8,z6])],[],[(0,[z381,z0,z2,z3,z4,z8,z6]),(0,[z129,z0,z2,z3,z4,z8,z46]),(0,[z382,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z383,z8,z6])],[(0,[z58,z0,z2,z3,z4,z8,z14]),(0,[z0,z2,z3,z4,z384,z8,z6]),(0,[z0,z2,z107,z3,z4,z8,z6])],[(1,[z0,z83,z3,z4,z166,z6]),(0,[z0,z2,z385,z3,z4,z8,z6]),(0,[z0,z2,z236,z3,z4,z8,z46]),(0,[z0,z2,z3,z4,z8,z299,z14])],[(0,[z386,z0,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z116,z56,z6]),(0,[z0,z387,z2,z3,z4,z8,z6])]],
   [[(0,[z0,z2,z3,z4,z8,z388,z6]),(0,[z389,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z78,z3,z4,z8,z6]),(0,[z58,z2,z3,z266,z4,z8,z6]),(0,[z0,z2,z3,z117,z67,z8,z6]),(0,[z0,z2,z3,z4,z8,z46,z17]),(0,[z0,z2,z3,z4,z8,z390,z6])],[(0,[z0,z2,z3,z391,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z166,z46]),(0,[z0,z2,z218,z3,z24,z8,z6]),(0,[z0,z2,z132,z3,z4,z8,z6]),(0,[z0,z2,z392,z3,z4,z8,z6])],[(0,[z0,z2,z3,z393,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z313,z6]),(0,[z0,z2,z202,z3,z4,z339,z6]),(0,[z0,z2,z3,z4,z339,z8,z13])],[(0,[z394,z0,z2,z3,z4,z8,z6]),(0,[z395,z0,z2,z3,z4,z8,z6]),(0,[z96,z0,z2,z3,z4,z33,z6]),(0,[z96,z0,z3,z102,z4,z8,z6]),(0,[z396,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z15,z3,z4,z8,z22])],[(0,[z0,z167,z2,z19,z3,z4,z8]),(1,[z30,z2,z3,z4,z31,z6]),(0,[z0,z397,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z42,z8,z6]),(0,[z255,z0,z2,z3,z4,z8,z46])],[(0,[z0,z7,z19,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z398,z8,z6]),(0,[z0,z2,z399,z3,z4,z8,z6]),(0,[z96,z0,z2,z3,z4,z8,z46]),(0,[z0,z2,z3,z4,z400,z8,z6]),(0,[z0,z2,z107,z3,z67,z8,z6])],[(0,[z0,z7,z2,z3,z4,z8,z6]),(0,[z0,z7,z2,z3,z196,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z401]),(0,[z0,z18,z2,z3,z402,z8,z6]),(0,[z0,z2,z107,z3,z24,z8,z6]),(0,[z0,z2,z107,z3,z4,z42,z6]),(0,[z0,z2,z325,z3,z4,z8,z6]),(0,[z0,z2,z107,z3,z4,z43,z6]),(0,[z0,z2,z3,z4,z403,z8,z6]),(0,[z0,z2,z3,z41,z43,z8,z6]),(0,[z0,z404,z2,z3,z4,z8,z6])],[(0,[z2,z78,z3,z266,z4,z8,z6]),(0,[z0,z2,z3,z4,z405,z8,z6]),(0,[z0,z51,z3,z4,z117,z8,z6]),(0,[z406,z0,z2,z3,z4,z8,z6])]],
   [[(0,[z0,z2,z3,z266,z4,z8,z46]),(0,[z96,z0,z2,z3,z4,z8,z90]),(0,[z407,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z408,z8,z6]),(0,[z0,z2,z3,z4,z409,z8,z6])],[(1,[z0,z59,z3,z4,z8,z6]),(0,[z0,z2,z410,z3,z4,z8,z6]),(1,[z0,z2,z3,z4,z8,z258]),(0,[z0,z2,z3,z411,z4,z8,z14]),(0,[z0,z412,z2,z3,z4,z8,z6])],[(0,[z157,z0,z2,z15,z3,z4,z8]),(0,[z0,z21,z2,z3,z4,z8,z46]),(0,[z0,z2,z413,z3,z4,z8,z6]),(0,[z414,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z415,z4,z8,z6])],[(1,[z0,z121,z3,z4,z8,z6]),(0,[z0,z416,z2,z3,z4,z8,z6]),(0,[z0,z2,z23,z3,z4,z417,z6]),(0,[z0,z2,z3,z4,z8,z418,z46])],[(0,[z58,z0,z2,z3,z252,z8,z6]),(0,[z0,z7,z2,z3,z117,z8,z6])],[(0,[z85,z2,z19,z3,z4,z8,z6]),(0,[z0,z2,z419,z3,z4,z8,z6]),(0,[z0,z2,z3,z420,z4,z8,z6]),(0,[z0,z2,z3,z4,z421,z8,z6]),(0,[z422,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z423,z3,z4,z8,z6]),(0,[z0,z2,z3,z424,z4,z8,z6]),(0,[z0,z425,z2,z3,z4,z8,z6])],[(0,[z30,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z426,z6]),(0,[z0,z2,z3,z427,z4,z8,z6])],[(0,[z261,z0,z2,z107,z3,z4,z6]),(0,[z0,z2,z377,z3,z4,z8,z6]),(0,[z0,z2,z428,z3,z4,z8,z6])]],
   [[(0,[z0,z2,z3,z4,z8,z6,z429]),(0,[z0,z2,z156,z4,z8,z56,z6]),(0,[z0,z2,z15,z3,z43,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z430])],[(1,[z0,z21,z3,z4,z8,z22]),(1,[z0,z2,z3,z4,z8,z373])],[(0,[z261,z2,z3,z4,z116,z8,z6]),(0,[z0,z2,z3,z431,z4,z8,z6]),(0,[z0,z2,z432,z3,z4,z8,z6]),(0,[z0,z2,z3,z16,z4,z8,z22])],[(1,[z133,z2,z3,z101,z8,z6]),(0,[z433,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z22]),(0,[z0,z2,z3,z434,z4,z8,z6]),(1,[z0,z2,z156,z4,z56,z6]),(0,[z0,z2,z202,z3,z4,z8,z14])],[(1,[z0,z2,z52,z3,z4,z8]),(0,[z0,z2,z3,z4,z42,z166,z6]),(1,[z0,z2,z3,z402,z8,z6]),(1,[z0,z2,z132,z4,z42,z6]),(0,[z0,z2,z3,z4,z8,z46,z113])],[(0,[z105,z2,z3,z266,z4,z8,z6]),(0,[z0,z121,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z373]),(0,[z0,z2,z3,z43,z8,z299,z6])],[(0,[z0,z2,z3,z4,z435,z8,z6]),(0,[z0,z2,z3,z436,z4,z8,z6]),(0,[z0,z2,z437,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z438])],[(0,[z0,z2,z3,z4,z8,z439,z6]),(0,[z58,z0,z2,z3,z4,z8,z46]),(0,[z261,z0,z2,z3,z4,z8,z6]),(1,[z0,z2,z3,z4,z8,z301]),(0,[z0,z2,z218,z3,z4,z8,z14]),(0,[z0,z2,z440,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z213,z46])]],
   [[(0,[z441,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z442,z3,z4,z8,z6]),(0,[z0,z2,z443,z3,z4,z8,z6]),(0,[z0,z2,z4,z42,z8,z56,z6]),(0,[z0,z2,z3,z4,z8,z299,z46]),(0,[z0,z2,z3,z4,z8,z444,z6])],[(0,[z0,z1,z3,z102,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z445,z6]),(0,[z446,z0,z2,z3,z4,z8,z6]),(0,[z447,z0,z2,z3,z4,z8,z6])],[(0,[z448,z0,z2,z3,z4,z8,z6]),(1,[z0,z2,z3,z4,z8,z9]),(0,[z0,z2,z449,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z450,z6])],[(0,[z0,z1,z2,z3,z4,z8,z46]),(0,[z451,z0,z2,z3,z4,z8,z6]),(0,[z157,z0,z2,z3,z4,z8,z14]),(0,[z0,z2,z3,z4,z452,z8,z6]),(0,[z0,z2,z453,z3,z4,z8,z6]),(1,[z0,z2,z23,z24,z8,z6]),(1,[z0,z2,z3,z41,z43,z6])],[(0,[z85,z0,z1,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z454,z8,z6]),(0,[z0,z2,z107,z3,z4,z8,z14])],[(1,[z0,z97,z194,z4,z8,z6]),(0,[z0,z83,z3,z4,z8,z166,z6])],[(0,[z0,z2,z3,z4,z8,z455,z6]),(0,[z0,z97,z19,z3,z4,z8,z6]),(0,[z30,z0,z2,z3,z4,z166,z6]),(0,[z0,z2,z3,z456,z4,z8,z6])],[(0,[z0,z2,z3,z4,z457,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z458]),(0,[z0,z97,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z42,z138,z6]),(1,[z0,z2,z3,z4,z8,z263]),(1,[z0,z2,z202,z3,z4,z17])]],
   [[(0,[z0,z2,z78,z3,z4,z8,z206]),(0,[z0,z2,z78,z3,z4,z8,z14]),(0,[z0,z2,z459,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z460,z8,z6]),(0,[z0,z2,z3,z4,z8,z461,z6]),(0,[z0,z462,z2,z3,z4,z8,z6])],[(0,[z0,z48,z2,z19,z3,z4,z8]),(1,[z0,z2,z3,z4,z8,z50]),(0,[z0,z2,z141,z3,z4,z8,z6]),(0,[z463,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z132,z3,z4,z8,z14]),(0,[z0,z2,z3,z4,z8,z14,z6])],[(0,[z39,z2,z19,z3,z4,z8,z6]),(0,[z464,z0,z2,z3,z4,z8,z6]),(1,[z0,z2,z3,z4,z465,z6]),(0,[z0,z97,z2,z102,z4,z8,z6]),(0,[z0,z2,z3,z4,z138,z8,z14]),(0,[z0,z2,z466,z3,z4,z8,z6]),(0,[z467,z0,z2,z3,z4,z8,z6])],[(0,[z157,z0,z2,z3,z4,z8,z130]),(0,[z0,z97,z194,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z263]),(0,[z0,z2,z3,z4,z468,z8,z6]),(0,[z0,z2,z107,z3,z4,z299,z6]),(0,[z0,z2,z3,z4,z8,z6,z469])],[(0,[z0,z470,z2,z3,z4,z8,z6]),(1,[z0,z377,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z471,z8,z6]),(0,[z0,z2,z3,z24,z196,z8,z6]),(0,[z0,z2,z3,z24,z4,z8,z6]),(1,[z0,z2,z3,z4,z417,z6]),(0,[z0,z2,z3,z4,z42,z8,z14])],[(0,[z0,z2,z3,z4,z8,z6,z472]),(0,[z0,z2,z3,z4,z8,z31,z6]),(0,[z473,z0,z2,z3,z4,z8,z6])],[(0,[z474,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z188,z46]),(0,[z475,z0,z2,z3,z4,z8,z6]),(0,[z0,z7,z2,z3,z4,z8,z14]),(0,[z0,z2,z476,z3,z4,z8,z6]),(0,[z0,z477,z2,z3,z4,z8,z6]),(0,[z0,z2,z144,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z478,z8,z6]),(0,[z0,z2,z479,z3,z4,z8,z6]),(0,[z261,z0,z2,z3,z4,z166,z6]),(0,[z0,z2,z3,z4,z42,z116,z6])]],
   [[(0,[z58,z0,z2,z78,z4,z8,z6]),(0,[z30,z0,z2,z156,z3,z4,z6]),(0,[z0,z2,z3,z117,z8,z213,z6])],[(0,[z0,z480,z2,z3,z4,z8,z6]),(0,[z30,z0,z2,z3,z4,z138,z6]),(0,[z0,z2,z481,z3,z4,z8,z6]),(0,[z0,z2,z3,z196,z4,z8,z46]),(0,[z0,z2,z132,z3,z4,z8,z482])],[(0,[z0,z483,z2,z3,z4,z8,z6]),(0,[z65,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z24,z117,z8,z6]),(0,[z0,z2,z3,z4,z484,z8,z6]),(0,[z0,z2,z156,z3,z4,z8,z64]),(0,[z0,z2,z3,z4,z8,z64,z6]),(0,[z0,z2,z3,z4,z485,z8,z6])],[(0,[z0,z2,z3,z4,z486,z8,z6]),(0,[z487,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z488,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z489,z6]),(0,[z490,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z491]),(0,[z492,z0,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z493,z8,z6]),(0,[z0,z2,z494,z3,z4,z8,z6]),(0,[z0,z2,z3,z411,z4,z8,z6])],[(1,[z464,z2,z3,z4,z8,z6]),(0,[z0,z2,z23,z24,z4,z8,z6]),(0,[z0,z2,z107,z3,z8,z213,z6])],[(0,[z2,z19,z3,z266,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z495,z6]),(0,[z30,z0,z2,z3,z4,z8,z14]),(1,[z157,z2,z3,z4,z8,z130]),(1,[z0,z2,z3,z496,z8,z6]),(0,[z0,z2,z202,z3,z4,z8,z46]),(0,[z0,z2,z107,z3,z8,z299,z6]),(0,[z0,z2,z3,z497,z4,z8,z6]),(1,[z0,z2,z3,z4,z339,z13])],[(0,[z0,z18,z1,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z87,z6]),(0,[z0,z2,z334,z3,z4,z8,z6])]],
   [[(0,[z0,z2,z3,z4,z8,z46,z287]),(0,[z0,z2,z3,z4,z8,z498,z6])],[(0,[z0,z2,z3,z4,z499,z8,z6]),(0,[z30,z0,z2,z3,z4,z116,z6]),(0,[z261,z0,z2,z156,z3,z4,z6]),(0,[z0,z194,z3,z102,z4,z8,z6]),(0,[z0,z500,z2,z3,z4,z8,z6]),(0,[z0,z2,z501,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z47]),(0,[z0,z2,z3,z4,z8,z502,z46]),(0,[z0,z503,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z504,z6]),(0,[z0,z2,z505,z3,z4,z8,z6])],[(0,[z0,z19,z3,z4,z138,z8,z6]),(0,[z0,z2,z3,z4,z8,z506,z6]),(0,[z0,z2,z3,z4,z507,z8,z6]),(0,[z261,z0,z2,z3,z4,z138,z6]),(0,[z0,z2,z508,z3,z4,z8,z6]),(0,[z0,z2,z218,z3,z4,z8,z46]),(0,[z0,z2,z509,z3,z4,z8,z6]),(0,[z0,z2,z156,z3,z4,z8,z6])],[(0,[z510,z0,z2,z3,z4,z8,z6]),(0,[z58,z0,z2,z266,z4,z8,z6]),(0,[z0,z511,z2,z3,z4,z8,z6]),(0,[z0,z2,z512,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z502])],[(0,[z513,z0,z2,z3,z4,z8,z6]),(0,[z0,z514,z2,z3,z4,z8,z6])],[(0,[z515,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z16,z4,z8,z14])],[(0,[z0,z167,z2,z3,z4,z8,z6]),(0,[z2,z3,z101,z4,z53,z8,z6]),(0,[z157,z0,z2,z3,z4,z8,z46]),(0,[z0,z2,z3,z248,z4,z8,z6])],[(0,[z261,z0,z2,z3,z4,z8,z14]),(0,[z0,z2,z3,z4,z8,z516,z6]),(0,[z0,z2,z107,z3,z4,z8,z46]),(0,[z0,z2,z517,z3,z4,z8,z6])]],
   [[(1,[z0,z2,z3,z35,z8,z6]),(0,[z0,z2,z3,z4,z8,z177,z46]),(0,[z0,z2,z518,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z519,z8,z6]),(0,[z0,z2,z3,z520,z4,z8,z6]),(0,[z0,z2,z3,z521,z4,z8,z6])],[(0,[z522,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z523]),(0,[z65,z0,z2,z15,z3,z4,z8]),(0,[z0,z524,z2,z3,z4,z8,z6]),(0,[z0,z3,z4,z8,z151,z6,z22]),(0,[z0,z2,z144,z3,z4,z8,z299])],[(0,[z261,z0,z2,z3,z4,z116,z6]),(0,[z0,z2,z3,z4,z8,z6,z525]),(0,[z0,z387,z2,z3,z4,z8,z46]),(0,[z0,z2,z3,z8,z6,z254,z17])],[(0,[z0,z2,z78,z3,z4,z8,z46]),(0,[z96,z0,z2,z3,z248,z8,z6]),(0,[z526,z0,z2,z3,z4,z8,z6])],[(0,[z0,z83,z1,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z527,z6]),(0,[z0,z2,z3,z4,z8,z528,z6]),(0,[z529,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z132,z3,z4,z8,z46]),(0,[z0,z2,z530,z3,z4,z8,z6])],[(0,[z531,z0,z2,z3,z4,z8,z6]),(0,[z532,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z53,z8,z6]),(0,[z0,z2,z533,z3,z4,z8,z6]),(0,[z0,z3,z4,z138,z8,z166,z6]),(0,[z0,z2,z3,z4,z534,z8,z6])],[(1,[z0,z2,z3,z183,z4,z6]),(0,[z30,z261,z2,z3,z4,z8,z6]),(0,[z157,z0,z2,z3,z4,z8,z6]),(0,[z535,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z202,z3,z4,z8,z17])],[(0,[z0,z2,z19,z3,z4,z8,z6]),(0,[z0,z2,z3,z536,z4,z8,z6]),(0,[z129,z133,z2,z3,z4,z8,z6]),(0,[z0,z97,z2,z3,z4,z8,z14]),(0,[z0,z2,z537,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z42,z8,z46]),(0,[z0,z2,z3,z41,z4,z8,z6])]],
   [[(0,[z0,z2,z2,z3,z4,z8,z6]),(1,[z0,z2,z3,z4,z5,z6]),(0,[z157,z65,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z465,z6]),(0,[z0,z51,z7,z3,z4,z8,z6]),(0,[z0,z2,z538,z3,z4,z8,z6]),(0,[z0,z2,z539,z3,z4,z8,z6]),(0,[z0,z462,z2,z3,z4,z8,z14]),(0,[z0,z2,z3,z4,z8,z461,z14]),(0,[z0,z2,z3,z4,z8,z540,z6]),(0,[z0,z541,z2,z3,z4,z8,z6]),(0,[z0,z542,z2,z3,z4,z8,z6])],[(0,[z261,z0,z479,z3,z4,z8,z6]),(0,[z0,z7,z2,z3,z4,z8,z46]),(0,[z0,z2,z543,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z14,z14])],[(1,[z0,z2,z3,z4,z366,z6]),(0,[z65,z0,z2,z3,z4,z8,z188]),(1,[z0,z7,z3,z196,z8,z6]),(0,[z0,z2,z3,z4,z8,z544,z6]),(0,[z91,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z545,z6]),(0,[z0,z546,z2,z3,z4,z8,z6])],[(0,[z0,z19,z3,z4,z8,z6,z22]),(0,[z547,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z548,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z549,z8,z6]),(0,[z0,z2,z550,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z551,z8,z6]),(0,[z0,z18,z2,z3,z4,z8,z22]),(0,[z0,z2,z3,z24,z4,z8,z14]),(0,[z0,z2,z3,z4,z8,z6,z552])],[(0,[z0,z2,z3,z4,z8,z31,z14]),(0,[z0,z2,z3,z4,z138,z8,z6]),(0,[z0,z2,z3,z553,z4,z8,z6]),(0,[z0,z2,z23,z3,z67,z8,z6]),(0,[z0,z2,z554,z3,z4,z8,z6]),(0,[z0,z2,z15,z3,z4,z339,z8]),(0,[z0,z2,z3,z4,z8,z6,z555])],[(0,[z556,z0,z2,z3,z4,z8,z6]),(1,[z0,z2,z3,z4,z49,z6]),(0,[z0,z557,z2,z3,z4,z8,z6]),(1,[z96,z0,z102,z4,z8,z6]),(0,[z0,z2,z3,z16,z8,z213,z6])],[(0,[z0,z2,z3,z4,z8,z6,z558]),(0,[z91,z0,z3,z4,z138,z8,z6]),(0,[z0,z2,z23,z3,z4,z8,z317]),(0,[z559,z0,z2,z3,z4,z8,z6])]],
   [[(1,[z0,z2,z3,z4,z8,z232]),(0,[z0,z2,z3,z4,z8,z14,z560])],[(0,[z0,z2,z561,z3,z4,z8,z6]),(0,[z30,z0,z2,z3,z4,z8,z46]),(0,[z0,z2,z3,z4,z8,z562,z6]),(0,[z0,z2,z3,z4,z8,z14,z130]),(0,[z563,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z15,z3,z196,z8,z6]),(0,[z0,z18,z21,z3,z4,z8,z6]),(0,[z0,z2,z15,z3,z4,z8,z6])],[(0,[z65,z0,z2,z3,z4,z8,z14]),(0,[z0,z2,z564,z3,z4,z8,z6])],[(0,[z0,z565,z2,z3,z4,z8,z6]),(0,[z0,z2,z566,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z567,z8,z6]),(0,[z568,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z569,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z570,z6]),(0,[z0,z2,z3,z4,z8,z14,z245])],[(0,[z0,z2,z3,z4,z8,z571,z6])],[(0,[z0,z2,z572,z3,z4,z8,z6]),(0,[z0,z2,z573,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z574]),(0,[z0,z2,z3,z4,z8,z575,z6])],[(0,[z0,z341,z2,z3,z4,z8,z6]),(1,[z576,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z577]),(0,[z0,z2,z132,z3,z4,z42,z6]),(0,[z578,z0,z2,z3,z4,z8,z6])],[(0,[z579,z0,z2,z3,z4,z8,z6]),(0,[z580,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z581,z3,z4,z8,z6]),(0,[z0,z2,z15,z3,z117,z8,z6]),(1,[z380,z2,z3,z4,z8,z6]),(0,[z0,z2,z218,z3,z4,z8,z182]),(0,[z0,z2,z236,z70,z4,z8,z6])]],
   [[(0,[z0,z2,z3,z4,z8,z582,z6]),(0,[z0,z2,z583,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z482,z6]),(0,[z0,z2,z3,z16,z4,z8,z46]),(0,[z584,z0,z2,z3,z4,z8,z6])],[(0,[z0,z1,z3,z4,z117,z8,z6]),(0,[z0,z2,z3,z4,z585,z8,z6])],[(0,[z129,z0,z2,z3,z53,z8,z6]),(0,[z261,z0,z2,z3,z4,z8,z46]),(0,[z65,z0,z2,z3,z4,z8,z130]),(0,[z0,z2,z586,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z587,z6]),(0,[z91,z0,z2,z3,z4,z166,z6]),(0,[z588,z0,z2,z3,z4,z8,z6]),(0,[z0,z589,z2,z3,z4,z8,z6]),(0,[z0,z2,z156,z3,z4,z8,z14]),(0,[z0,z590,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z506,z14])],[(0,[z0,z48,z2,z3,z4,z8,z6]),(0,[z105,z0,z1,z3,z4,z8,z6]),(0,[z0,z51,z2,z3,z4,z8,z6]),(0,[z0,z51,z2,z3,z196,z8,z6]),(0,[z0,z591,z2,z3,z4,z8,z6]),(0,[z0,z2,z15,z3,z4,z8,z151]),(0,[z0,z2,z592,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z593])],[(0,[z129,z2,z3,z4,z53,z8,z6]),(0,[z96,z0,z2,z3,z4,z465,z6]),(0,[z0,z2,z3,z402,z4,z8,z6]),(0,[z0,z2,z3,z4,z594,z8,z6]),(0,[z0,z2,z3,z4,z8,z56,z6]),(0,[z0,z2,z3,z16,z4,z339,z8])],[(0,[z595,z0,z2,z3,z4,z8,z6]),(0,[z0,z596,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z597,z6]),(0,[z0,z598,z2,z3,z4,z8,z6])],[(0,[z0,z599,z2,z3,z4,z8,z6]),(0,[z157,z0,z2,z3,z4,z8,z188]),(0,[z0,z2,z600,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z80]),(0,[z0,z2,z3,z4,z601,z8,z6]),(0,[z0,z2,z15,z3,z8,z6,z113])],[(0,[z602,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z603])]],
   [[(0,[z0,z2,z3,z4,z8,z604,z6]),(0,[z0,z2,z605,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z606,z6]),(0,[z0,z2,z3,z4,z339,z8,z14]),(0,[z0,z2,z3,z16,z4,z8,z6])],[(0,[z0,z2,z3,z4,z8,z6,z6]),(0,[z0,z2,z3,z67,z43,z8,z6]),(0,[z0,z524,z2,z3,z4,z8,z14])],[(0,[z0,z2,z3,z4,z49,z8,z6]),(0,[z0,z97,z2,z3,z4,z8,z46]),(0,[z0,z2,z3,z4,z8,z607,z6]),(0,[z608,z0,z2,z3,z4,z8,z6]),(0,[z0,z82,z2,z3,z4,z8,z6]),(0,[z0,z2,z202,z3,z16,z4,z8])],[(0,[z0,z2,z3,z4,z8,z609,z6]),(0,[z0,z2,z3,z610,z4,z8,z6])],[(0,[z0,z2,z3,z4,z8,z14,z46])],[(0,[z0,z2,z3,z4,z53,z8,z14]),(0,[z91,z0,z2,z3,z4,z138,z6])],[(0,[z0,z2,z611,z3,z4,z8,z6])],[(0,[z0,z2,z19,z3,z4,z8,z14]),(0,[z0,z576,z2,z3,z4,z8,z6]),(0,[z96,z464,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z24,z4,z8,z46]),(0,[z0,z2,z3,z4,z8,z612,z6]),(0,[z0,z2,z70,z4,z8,z14,z6]),(0,[z0,z2,z3,z41,z4,z8,z14])]],
   [[(0,[z613,z0,z2,z3,z4,z8,z6]),(0,[z614,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z31,z46]),(0,[z0,z2,z3,z4,z615,z8,z6]),(0,[z96,z0,z2,z3,z496,z8,z6]),(0,[z0,z380,z2,z3,z4,z8,z6]),(1,[z0,z2,z3,z4,z8,z317]),(0,[z0,z2,z3,z4,z8,z6,z418]),(0,[z0,z2,z3,z4,z8,z6,z616])],[(0,[z617,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z618,z6]),(0,[z133,z0,z2,z3,z101,z8,z6]),(0,[z619,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z4,z8,z14,z6,z46])],[(0,[z0,z2,z620,z3,z4,z8,z6]),(0,[z91,z0,z2,z3,z4,z8,z14]),(0,[z0,z18,z2,z3,z621,z8,z6]),(0,[z0,z2,z3,z16,z4,z8,z151]),(0,[z0,z2,z3,z123,z4,z8,z6]),(0,[z0,z622,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z623,z4,z8,z6]),(0,[z0,z2,z3,z4,z624,z8,z6]),(0,[z0,z2,z3,z4,z625,z8,z6]),(0,[z0,z2,z3,z4,z626,z8,z6])],[(0,[z0,z2,z3,z4,z627,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z628]),(0,[z0,z2,z3,z4,z629,z8,z6]),(0,[z0,z2,z194,z3,z4,z8,z14]),(0,[z630,z0,z2,z3,z4,z8,z6])],[(0,[z0,z631,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z632,z4,z8,z6]),(0,[z0,z2,z3,z633,z4,z8,z6]),(1,[z0,z2,z3,z4,z169,z6]),(0,[z58,z0,z2,z3,z4,z8,z50]),(0,[z0,z2,z3,z4,z634,z8,z6]),(0,[z65,z0,z2,z3,z4,z8,z46]),(0,[z0,z2,z3,z4,z8,z6,z635]),(0,[z0,z636,z2,z3,z4,z8,z6]),(0,[z637,z0,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z638,z4,z8,z6]),(0,[z639,z0,z2,z3,z4,z8,z6]),(0,[z640,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z41,z4,z299,z6])],[(1,[z85,z19,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z641]),(0,[z0,z2,z15,z3,z4,z8,z213])]],
   [[(0,[z0,z2,z642,z3,z4,z8,z6]),(0,[z0,z3,z196,z4,z117,z8,z6]),(0,[z0,z2,z3,z4,z643,z8,z6]),(0,[z0,z2,z3,z4,z8,z151,z46]),(0,[z0,z2,z3,z4,z644,z8,z6]),(0,[z0,z2,z3,z4,z8,z13,z6])],[(1,[z0,z2,z271,z3,z4,z6]),(0,[z25,z0,z2,z3,z4,z8,z6]),(0,[z39,z0,z2,z3,z4,z8,z14]),(0,[z0,z2,z645,z3,z4,z8,z6]),(0,[z0,z2,z15,z3,z4,z8,z14]),(0,[z646,z0,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z8,z647,z6])],[(0,[z0,z2,z24,z4,z67,z8,z6])],[(0,[z648,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z46,z429]),(0,[z0,z2,z3,z4,z8,z14,z17]),(0,[z0,z2,z649,z3,z4,z8,z6])],[(0,[z650,z0,z2,z3,z4,z8,z6]),(0,[z58,z0,z2,z3,z60,z8,z6]),(1,[z0,z341,z3,z4,z8,z6]),(0,[z0,z2,z156,z3,z4,z8,z46]),(0,[z0,z2,z651,z3,z4,z8,z6])],[(0,[z0,z2,z3,z652,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z14,z151])],[(0,[z0,z83,z2,z3,z4,z138,z6])]],
   [[(1,[z0,z2,z3,z4,z8,z193]),(0,[z0,z2,z3,z653,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z151,z6]),(1,[z0,z2,z3,z621,z8,z6]),(0,[z0,z2,z218,z23,z4,z8,z6]),(0,[z654,z0,z2,z3,z4,z8,z6])],[(1,[z0,z2,z3,z165,z4,z8]),(0,[z0,z2,z655,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z656,z8,z6]),(1,[z0,z51,z3,z117,z8,z6]),(1,[z0,z2,z3,z4,z8,z313]),(1,[z0,z2,z3,z4,z8,z241])],[(1,[z58,z2,z266,z4,z8,z6]),(0,[z0,z2,z657,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z43,z8,z6]),(0,[z0,z2,z3,z4,z658,z8,z6]),(1,[z0,z2,z3,z8,z6,z254])],[(0,[z0,z2,z3,z4,z42,z31,z6]),(0,[z0,z2,z3,z4,z659,z8,z6]),(0,[z0,z51,z2,z3,z4,z8,z14]),(0,[z0,z2,z518,z3,z4,z8,z46]),(0,[z0,z2,z3,z4,z339,z8,z46])],[(0,[z0,z2,z3,z4,z8,z6,z193]),(0,[z0,z2,z3,z660,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z661,z6]),(0,[z0,z2,z3,z4,z8,z56,z14]),(0,[z0,z2,z3,z16,z4,z8,z113])],[(0,[z0,z2,z3,z662,z4,z8,z6]),(0,[z0,z2,z3,z663,z4,z8,z6])],[(0,[z85,z0,z19,z3,z4,z8,z6]),(0,[z0,z2,z3,z3,z4,z8,z6]),(0,[z0,z2,z3,z664,z4,z8,z6]),(0,[z0,z2,z218,z3,z4,z8,z301]),(0,[z0,z2,z3,z16,z4,z8,z213]),(0,[z0,z665,z2,z3,z4,z8,z6])],[(0,[z85,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z666,z4,z8,z6]),(1,[z0,z61,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z667,z8,z6]),(0,[z0,z2,z3,z4,z668,z8,z6]),(0,[z0,z2,z669,z3,z4,z8,z6]),(1,[z0,z2,z218,z67,z8,z6]),(0,[z0,z2,z3,z4,z108,z8,z14]),(0,[z0,z2,z670,z3,z4,z8,z6])]],
   [[(0,[z0,z2,z3,z671,z4,z8,z6]),(0,[z0,z2,z3,z4,z53,z8,z46]),(0,[z133,z2,z3,z101,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z672,z6]),(0,[z673,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z23,z3,z4,z68,z6])],[(0,[z0,z2,z3,z4,z8,z6,z206]),(1,[z0,z141,z3,z4,z8,z6]),(0,[z129,z0,z2,z3,z101,z8,z6]),(0,[z0,z2,z3,z101,z4,z8,z6]),(0,[z0,z2,z3,z102,z4,z8,z6])],[(0,[z0,z2,z19,z3,z4,z8,z46]),(0,[z0,z2,z674,z3,z4,z8,z6]),(0,[z30,z0,z2,z132,z3,z4,z6]),(0,[z96,z0,z2,z3,z4,z8,z232]),(0,[z0,z2,z675,z3,z4,z8,z6]),(0,[z0,z2,z3,z41,z4,z8,z46]),(0,[z0,z2,z3,z4,z8,z676,z6])],[(0,[z0,z2,z3,z4,z8,z6,z677]),(0,[z0,z2,z3,z4,z339,z8,z6])],[(0,[z119,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z271,z3,z266,z4,z6]),(0,[z0,z2,z3,z4,z8,z678,z6]),(0,[z0,z2,z3,z4,z8,z14,z188]),(0,[z0,z2,z3,z679,z4,z8,z6]),(1,[z0,z2,z107,z3,z299,z6]),(0,[z0,z2,z3,z4,z680,z8,z6])],[(0,[z0,z2,z154,z3,z266,z4,z6]),(0,[z0,z2,z681,z3,z4,z8,z6]),(0,[z30,z0,z2,z3,z4,z31,z6]),(0,[z91,z0,z2,z3,z4,z8,z46]),(0,[z0,z2,z3,z4,z8,z682,z6]),(0,[z683,z0,z2,z3,z4,z8,z6]),(1,[z0,z2,z3,z4,z8,z482])],[(1,[z0,z2,z4,z8,z14,z46]),(0,[z0,z2,z3,z4,z8,z278,z6]),(0,[z0,z2,z684,z3,z4,z8,z6])],[(1,[z0,z479,z3,z4,z8,z6]),(0,[z157,z0,z21,z2,z3,z4,z8]),(0,[z0,z2,z23,z3,z4,z8,z6]),(0,[z0,z2,z156,z3,z4,z42,z6]),(0,[z0,z2,z3,z4,z8,z612,z14])]],
   [[(0,[z0,z2,z3,z4,z8,z6,z685]),(0,[z0,z2,z3,z4,z8,z686,z6]),(0,[z96,z576,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z687,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z688]),(0,[z0,z2,z3,z4,z138,z8,z46]),(0,[z0,z2,z3,z4,z8,z6,z560]),(0,[z0,z2,z3,z4,z8,z14,z113])],[(0,[z0,z2,z3,z4,z116,z8,z14]),(0,[z96,z0,z2,z194,z4,z8,z6]),(0,[z689,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z690,z3,z4,z8,z6])],[(0,[z0,z2,z3,z691,z4,z8,z6]),(0,[z0,z2,z3,z101,z67,z8,z6]),(0,[z0,z2,z692,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z8,z169,z6]),(0,[z0,z2,z693,z3,z4,z8,z6]),(0,[z261,z0,z2,z132,z3,z4,z6]),(0,[z0,z2,z3,z4,z621,z8,z6]),(0,[z694,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z339,z8,z17])],[(0,[z0,z2,z3,z4,z695,z8,z6]),(0,[z0,z2,z3,z4,z496,z8,z6]),(0,[z0,z2,z194,z3,z4,z8,z80]),(0,[z0,z2,z3,z4,z8,z696,z6]),(0,[z0,z2,z15,z3,z4,z8,z46]),(0,[z0,z2,z3,z4,z8,z697,z6])],[(0,[z133,z0,z2,z3,z4,z8,z14]),(0,[z0,z2,z3,z4,z8,z698,z6]),(0,[z0,z2,z3,z4,z8,z699,z6]),(0,[z0,z2,z3,z4,z8,z417,z6]),(1,[z0,z2,z3,z98,z8,z6]),(0,[z700,z0,z2,z3,z4,z8,z6])],[(0,[z58,z0,z2,z3,z4,z366,z6]),(0,[z0,z2,z3,z4,z8,z701,z6]),(0,[z0,z2,z3,z4,z702,z8,z6]),(0,[z261,z0,z2,z3,z4,z31,z6]),(0,[z0,z703,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z8,z704,z6]),(0,[z705,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z706,z3,z4,z8,z6]),(0,[z0,z2,z194,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z46,z491])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z2,z154,z3,z4,z6]),(0,[z0,z2,z271,z3,z4,z46]),(0,[z0,z2,z707,z4,z8,z6])],[(0,[z0,z2,z708,z3,z4,z8]),(0,[z0,z2,z3,z4,z366,z14]),(0,[z133,z2,z3,z709,z8,z6]),(0,[z608,z2,z3,z4,z116,z6]),(0,[z255,z2,z3,z4,z8,z188]),(0,[z0,z7,z3,z196,z8,z14]),(0,[z0,z2,z3,z98,z8,z14])],[(0,[z71,z2,z3,z4,z8,z6]),(0,[z0,z2,z15,z3,z8,z688]),(0,[z0,z2,z3,z710,z4,z8]),(0,[z0,z3,z4,z8,z46,z711]),(0,[z0,z2,z15,z3,z8,z560])],[(0,[z0,z2,z712,z3,z4,z6])],[(0,[z0,z341,z3,z4,z8,z46]),(0,[z157,z2,z3,z497,z4,z8]),(0,[z0,z713,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z714,z6]),(0,[z0,z2,z132,z436,z4,z6]),(0,[z0,z2,z3,z4,z8,z715]),(0,[z0,z2,z3,z716,z8,z6]),(0,[z464,z2,z3,z4,z33,z6]),(0,[z0,z2,z3,z4,z8,z717]),(0,[z0,z2,z3,z4,z8,z718])],[(0,[z85,z19,z3,z4,z8,z6]),(0,[z85,z48,z19,z3,z4,z8]),(0,[z0,z2,z719,z3,z4,z6]),(0,[z0,z2,z3,z496,z33,z6])],[(0,[z0,z2,z3,z4,z720,z6]),(0,[z0,z2,z721,z3,z8,z6]),(0,[z0,z2,z3,z621,z8,z46]),(0,[z0,z2,z3,z722,z8,z6])]],
   [[(0,[z0,z2,z107,z3,z567,z6]),(0,[z0,z2,z3,z496,z8,z46])],[(0,[z58,z2,z266,z4,z8,z46]),(0,[z0,z723,z3,z4,z8,z6]),(0,[z0,z2,z3,z724,z8,z6]),(0,[z0,z2,z107,z3,z426,z6]),(0,[z0,z2,z3,z98,z8,z482]),(0,[z0,z2,z3,z4,z8,z725])],[(0,[z0,z2,z726,z3,z8,z6]),(0,[z0,z74,z3,z4,z8,z193]),(0,[z0,z2,z3,z4,z8,z727]),(0,[z0,z18,z377,z3,z4,z8]),(0,[z0,z2,z3,z728,z8,z6])],[(0,[z0,z2,z3,z4,z729,z6]),(0,[z0,z2,z3,z496,z8,z90]),(0,[z0,z2,z3,z4,z8,z730])],[(0,[z58,z74,z266,z4,z8,z6]),(0,[z0,z2,z3,z8,z6,z731]),(0,[z0,z2,z3,z4,z8,z732]),(0,[z0,z2,z3,z733,z8,z46]),(0,[z0,z2,z15,z3,z8,z36])],[(0,[z0,z2,z3,z734,z8,z6]),(0,[z0,z2,z735,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z736]),(0,[z0,z2,z3,z4,z68,z14]),(0,[z0,z2,z3,z16,z8,z502]),(0,[z0,z2,z3,z4,z737,z14])],[(0,[z0,z2,z3,z4,z8,z738]),(0,[z0,z2,z3,z60,z8,z50]),(0,[z0,z61,z3,z4,z8,z46]),(0,[z0,z2,z3,z4,z739,z8]),(0,[z0,z2,z3,z4,z8,z740]),(0,[z0,z2,z132,z4,z741,z6]),(0,[z0,z2,z684,z4,z8,z46]),(0,[z0,z2,z3,z4,z742,z14])],[(0,[z0,z2,z3,z4,z8,z193]),(0,[z0,z2,z743,z3,z4,z6]),(0,[z0,z2,z144,z3,z43,z8])]],
   [[(0,[z246,z0,z3,z4,z138,z6]),(0,[z0,z2,z3,z4,z744,z6]),(0,[z0,z141,z3,z4,z8,z46]),(0,[z0,z2,z3,z165,z4,z8]),(0,[z0,z2,z3,z4,z8,z745]),(0,[z0,z2,z3,z4,z8,z746]),(0,[z0,z51,z3,z117,z8,z6]),(0,[z0,z51,z3,z747,z8,z6]),(0,[z0,z2,z3,z4,z8,z241])],[(0,[z0,z2,z3,z252,z366,z6]),(0,[z0,z748,z3,z4,z8,z6]),(0,[z0,z749,z3,z4,z8,z6]),(0,[z750,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z8,z46,z751]),(0,[z0,z2,z3,z8,z6,z254])],[(0,[z0,z2,z3,z752,z8,z6]),(0,[z0,z269,z3,z117,z8,z6]),(0,[z71,z2,z3,z4,z166,z6]),(0,[z0,z2,z3,z35,z8,z46])],[(0,[z0,z2,z3,z753,z4,z8]),(0,[z464,z2,z3,z4,z465,z6]),(0,[z754,z2,z3,z4,z8,z6]),(0,[z96,z0,z102,z248,z8,z6]),(0,[z0,z2,z107,z3,z299,z46]),(0,[z0,z2,z107,z3,z444,z6])],[(0,[z0,z2,z3,z4,z8,z14]),(0,[z613,z19,z3,z4,z8,z6]),(0,[z0,z2,z256,z4,z8,z46])],[(0,[z0,z2,z3,z4,z8,z755]),(0,[z0,z2,z3,z248,z8,z232])],[(0,[z0,z61,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z756]),(0,[z0,z2,z757,z4,z8,z6]),(0,[z0,z2,z3,z4,z758,z6]),(0,[z0,z479,z3,z4,z8,z46]),(0,[z0,z2,z759,z3,z4,z8]),(0,[z0,z2,z3,z16,z8,z221]),(0,[z0,z2,z222,z4,z8,z46]),(0,[z0,z2,z218,z67,z8,z6])],[]],
   [[(0,[z760,z2,z3,z4,z8,z6]),(0,[z0,z141,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z8,z761]),(0,[z0,z2,z3,z4,z8,z762]),(0,[z0,z763,z3,z4,z8,z14]),(0,[z0,z2,z325,z3,z4,z26])],[(0,[z0,z2,z3,z4,z8,z764]),(0,[z0,z2,z3,z4,z5,z46]),(0,[z58,z2,z765,z4,z8,z6]),(0,[z0,z2,z766,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z767])],[(0,[z0,z1,z3,z4,z8,z9]),(0,[z0,z768,z3,z4,z8,z6]),(0,[z30,z479,z3,z4,z8,z6]),(0,[z576,z2,z3,z248,z8,z6]),(0,[z0,z2,z3,z769,z4,z6])],[(0,[z19,z3,z4,z140,z8,z6]),(0,[z0,z2,z3,z4,z366,z46]),(0,[z0,z7,z3,z196,z8,z46]),(0,[z0,z2,z279,z4,z56,z6]),(0,[z0,z2,z3,z4,z8,z482]),(0,[z0,z2,z3,z98,z8,z46])],[(0,[z0,z2,z3,z4,z770,z6]),(0,[z0,z2,z771,z4,z8,z6]),(0,[z71,z2,z3,z4,z138,z6])],[(0,[z0,z479,z3,z4,z8,z6]),(0,[z0,z2,z772,z3,z4,z8]),(0,[z96,z0,z102,z4,z33,z6])],[(0,[z0,z2,z3,z4,z8,z773]),(0,[z0,z774,z3,z4,z8,z6]),(0,[z261,z2,z3,z197,z4,z6]),(0,[z0,z775,z2,z3,z4,z8]),(0,[z0,z2,z4,z8,z741,z6]),(0,[z0,z2,z776,z3,z8,z46]),(0,[z0,z2,z3,z777,z8,z14]),(0,[z0,z2,z3,z8,z6,z778])]],
   [[(0,[z85,z167,z19,z3,z4,z8]),(0,[z0,z779,z2,z3,z4,z8]),(0,[z0,z2,z154,z3,z4,z14]),(0,[z0,z2,z3,z4,z33,z232]),(0,[z780,z2,z3,z4,z8,z6]),(0,[z0,z2,z218,z722,z8,z6])],[(0,[z30,z2,z554,z3,z4,z6]),(0,[z255,z2,z3,z4,z8,z287]),(0,[z0,z2,z202,z3,z4,z312])],[(0,[z0,z2,z3,z781,z8,z6]),(0,[z0,z2,z335,z3,z67,z6]),(0,[z71,z2,z3,z4,z8,z14]),(0,[z0,z782,z3,z4,z8,z6]),(0,[z0,z82,z3,z4,z8,z429])],[(0,[z0,z2,z156,z4,z56,z258])],[(0,[z0,z2,z3,z252,z8,z6]),(0,[z0,z2,z3,z4,z783,z14])],[(0,[z0,z2,z3,z784,z8,z6]),(0,[z0,z2,z3,z4,z8,z785]),(0,[z0,z82,z3,z4,z8,z22]),(0,[z0,z2,z3,z4,z786,z6])],[(0,[z85,z19,z3,z4,z8,z14]),(0,[z0,z2,z3,z4,z787,z6]),(0,[z576,z2,z3,z4,z33,z6]),(0,[z0,z2,z788,z4,z8,z6])],[(0,[z0,z2,z3,z789,z4,z8])]],
   [[(0,[z0,z2,z3,z4,z790,z6]),(0,[z0,z2,z3,z4,z8,z791]),(0,[z0,z2,z3,z792,z4,z8]),(0,[z0,z2,z3,z4,z793,z6]),(0,[z794,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z68,z46]),(0,[z795,z2,z3,z4,z8,z6])],[(0,[z0,z18,z3,z4,z8,z337]),(0,[z0,z2,z653,z4,z8,z46]),(0,[z796,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z8,z797]),(0,[z588,z19,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z798,z6]),(0,[z0,z377,z3,z16,z4,z8]),(0,[z2,z3,z4,z8,z130,z799]),(0,[z0,z2,z3,z402,z8,z22]),(0,[z0,z541,z3,z4,z8,z151]),(0,[z0,z2,z3,z411,z8,z213])],[(0,[z407,z1,z3,z4,z8,z6]),(0,[z0,z2,z218,z67,z8,z182]),(0,[z0,z2,z505,z4,z8,z46])],[(0,[z0,z2,z3,z4,z6,z800]),(0,[z261,z2,z440,z3,z4,z6]),(0,[z96,z0,z102,z4,z465,z6]),(0,[z801,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z802])],[(0,[z0,z48,z2,z3,z4,z8]),(0,[z39,z2,z78,z4,z8,z6]),(0,[z0,z2,z706,z4,z8,z46]),(0,[z0,z2,z4,z8,z661,z46])],[(0,[z0,z2,z3,z4,z8,z803]),(0,[z804,z2,z3,z4,z8,z6]),(0,[z0,z2,z684,z4,z56,z6]),(0,[z0,z2,z69,z3,z8,z560])],[(0,[z0,z2,z3,z4,z8,z46]),(0,[z0,z2,z3,z60,z366,z6]),(0,[z0,z2,z107,z144,z3,z299])]],
   [[(0,[z0,z2,z3,z805,z8,z6]),(0,[z129,z2,z3,z709,z8,z6]),(0,[z0,z3,z4,z8,z806,z6]),(0,[z0,z807,z3,z4,z8,z6]),(0,[z0,z3,z808,z4,z8,z46]),(0,[z0,z2,z3,z8,z786,z6])],[(0,[z0,z59,z3,z4,z8,z50]),(0,[z0,z2,z3,z4,z8,z809]),(0,[z0,z2,z3,z16,z8,z697])],[(0,[z0,z74,z3,z4,z8,z6]),(0,[z261,z2,z3,z4,z624,z6]),(0,[z0,z2,z3,z4,z8,z90]),(0,[z0,z2,z3,z810,z8,z6]),(0,[z0,z2,z4,z8,z6,z811])],[(0,[z0,z2,z23,z24,z8,z373]),(0,[z0,z2,z3,z4,z14,z812]),(0,[z0,z813,z3,z4,z8,z14]),(0,[z0,z2,z3,z8,z213,z641])],[(0,[z0,z83,z3,z4,z5,z6]),(0,[z0,z2,z3,z252,z169,z6]),(0,[z576,z2,z3,z4,z465,z6]),(0,[z0,z2,z236,z4,z8,z46]),(0,[z0,z814,z3,z4,z8,z6])],[(0,[z0,z815,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z816]),(0,[z0,z2,z3,z4,z8,z817])],[(0,[z0,z2,z3,z818,z8,z6]),(0,[z0,z2,z3,z165,z183,z4]),(0,[z0,z2,z218,z67,z8,z14]),(0,[z0,z2,z4,z8,z811,z46])],[(0,[z58,z2,z154,z266,z4,z6]),(0,[z0,z3,z747,z117,z8,z6]),(0,[z0,z819,z3,z4,z8,z6])]],
   [[(0,[z2,z19,z3,z4,z49,z6]),(0,[z105,z760,z3,z4,z8,z6]),(0,[z0,z3,z4,z8,z6,z820]),(0,[z0,z2,z3,z4,z821,z6]),(0,[z0,z2,z564,z4,z8,z46])],[(0,[z105,z1,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z822,z6]),(0,[z464,z2,z3,z4,z8,z232])],[(0,[z0,z2,z3,z823,z8,z6]),(0,[z0,z2,z3,z824,z8,z6]),(0,[z0,z2,z3,z4,z8,z825]),(0,[z0,z2,z132,z4,z42,z263]),(0,[z0,z2,z15,z3,z8,z113])],[(0,[z30,z2,z3,z4,z388,z6]),(0,[z0,z2,z154,z3,z4,z46]),(0,[z129,z2,z335,z3,z53,z6]),(0,[z0,z2,z3,z4,z8,z826])],[(0,[z0,z167,z3,z4,z8,z22]),(0,[z0,z827,z3,z4,z8,z6]),(0,[z0,z2,z4,z722,z8,z6])],[(0,[z0,z2,z3,z747,z8,z6]),(0,[z71,z2,z3,z4,z8,z46]),(0,[z0,z828,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z8,z829]),(0,[z2,z3,z4,z116,z830,z6])],[(0,[z0,z2,z3,z252,z8,z193]),(0,[z58,z2,z271,z266,z4,z6]),(0,[z0,z2,z335,z3,z165,z4]),(0,[z0,z2,z23,z24,z8,z317])]],
   [[(0,[z0,z831,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z832]),(0,[z0,z2,z146,z4,z8,z14]),(1,[z0,z833,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z834]),(0,[z0,z2,z144,z3,z4,z8])],[(0,[z0,z2,z3,z4,z8,z835]),(0,[z85,z19,z3,z4,z8,z46]),(0,[z246,z2,z3,z4,z116,z6]),(0,[z0,z2,z3,z4,z836,z6]),(0,[z0,z2,z3,z8,z6,z837]),(0,[z216,z2,z3,z4,z8,z506])],[(0,[z105,z2,z3,z4,z49,z6]),(0,[z91,z0,z3,z4,z138,z6]),(0,[z0,z2,z4,z27,z8,z46])],[(0,[z0,z2,z838,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z839]),(0,[z0,z2,z3,z4,z6,z840]),(0,[z380,z83,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z841])],[(0,[z0,z2,z3,z252,z8,z14]),(0,[z0,z723,z3,z4,z8,z46]),(0,[z0,z2,z3,z724,z8,z46]),(0,[z0,z387,z3,z4,z8,z418])],[(0,[z71,z91,z3,z4,z138,z6]),(0,[z0,z2,z202,z3,z4,z725])],[(0,[z0,z2,z3,z4,z8,z842]),(0,[z0,z2,z44,z4,z8,z46]),(0,[z129,z2,z3,z183,z53,z6]),(0,[z843,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z844]),(0,[z0,z2,z23,z24,z417,z6]),(0,[z0,z2,z3,z41,z57,z6])],[(0,[z0,z167,z2,z3,z4,z8]),(0,[z0,z2,z3,z4,z783,z6]),(0,[z261,z2,z3,z4,z116,z6]),(0,[z0,z2,z3,z41,z120,z6]),(0,[z261,z0,z2,z3,z35,z6]),(0,[z65,z514,z2,z3,z4,z8])]],
   [[(0,[z0,z845,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z846])],[(0,[z0,z2,z3,z4,z847,z6]),(0,[z0,z2,z3,z848,z8,z6]),(0,[z0,z2,z518,z3,z4,z491])],[(0,[z614,z0,z102,z4,z8,z6])],[(0,[z30,z2,z3,z4,z265,z6]),(0,[z0,z2,z3,z849,z4,z8]),(0,[z0,z850,z3,z4,z8,z6]),(0,[z0,z51,z3,z117,z8,z46]),(0,[z0,z3,z4,z851,z8,z6]),(0,[z0,z2,z4,z8,z72,z46])],[(0,[z0,z2,z852,z3,z4,z8]),(0,[z0,z2,z3,z4,z8,z182]),(0,[z0,z2,z107,z144,z3,z8]),(0,[z0,z2,z3,z4,z8,z853])],[(0,[z0,z2,z3,z4,z854,z6]),(0,[z39,z2,z78,z4,z8,z14]),(0,[z0,z855,z3,z4,z8,z6]),(0,[z0,z2,z856,z3,z4,z6]),(0,[z0,z2,z675,z4,z8,z46])],[(0,[z30,z19,z3,z4,z138,z6]),(0,[z0,z2,z3,z4,z8,z857])],[(0,[z858,z2,z3,z4,z8,z6]),(0,[z859,z2,z3,z4,z8,z6]),(1,[z0,z2,z4,z741,z6]),(0,[z0,z2,z3,z4,z8,z811])]],
   [[(0,[z0,z2,z3,z4,z8,z860])],[(0,[z0,z861,z3,z4,z8,z6]),(0,[z30,z2,z3,z4,z112,z6]),(0,[z65,z2,z3,z4,z8,z188]),(0,[z0,z2,z218,z67,z8,z46])],[(0,[z0,z2,z3,z4,z8,z862]),(0,[z0,z59,z3,z4,z366,z6]),(0,[z0,z74,z3,z4,z8,z14]),(0,[z0,z2,z3,z60,z169,z6]),(1,[z2,z765,z4,z8,z6]),(0,[z0,z2,z335,z52,z3,z4]),(0,[z2,z3,z101,z709,z8,z6]),(0,[z91,z0,z3,z4,z851,z6])],[(1,[z760,z3,z4,z8,z6]),(0,[z0,z863,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z864]),(0,[z0,z2,z3,z4,z8,z865]),(0,[z866,z2,z3,z4,z8,z6]),(0,[z0,z2,z132,z35,z42,z6])],[(0,[z0,z18,z167,z3,z4,z8]),(0,[z0,z167,z377,z3,z4,z8]),(0,[z0,z867,z2,z3,z4,z8]),(0,[z0,z2,z3,z4,z8,z868]),(0,[z0,z2,z236,z4,z8,z811]),(0,[z0,z2,z3,z4,z339,z177])],[(0,[z0,z2,z3,z4,z339,z375])],[(0,[z129,z61,z3,z53,z8,z6]),(0,[z30,z2,z3,z4,z358,z6]),(0,[z0,z869,z3,z4,z8,z6]),(0,[z65,z2,z178,z3,z4,z8]),(0,[z0,z2,z3,z4,z8,z870]),(0,[z0,z813,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z871,z6])],[(0,[z0,z2,z3,z4,z872,z6]),(0,[z0,z2,z3,z4,z8,z206]),(0,[z0,z2,z3,z873,z8,z6]),(0,[z58,z2,z266,z4,z8,z50]),(0,[z0,z874,z2,z3,z4,z8]),(0,[z0,z2,z3,z4,z8,z875]),(0,[z30,z0,z2,z3,z35,z6]),(0,[z0,z2,z4,z8,z609,z46]),(0,[z0,z2,z3,z496,z465,z6])]],
   [[(0,[z0,z2,z876,z3,z4,z8]),(0,[z0,z2,z877,z3,z4,z6]),(0,[z129,z141,z3,z53,z8,z6]),(0,[z878,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z879,z8,z6]),(0,[z0,z2,z3,z786,z299,z6]),(0,[z0,z2,z15,z3,z8,z778])],[(0,[z0,z2,z880,z4,z8,z6]),(0,[z105,z1,z3,z4,z8,z14]),(0,[z0,z2,z3,z4,z8,z881]),(0,[z96,z0,z833,z4,z8,z6]),(0,[z0,z83,z3,z4,z166,z6]),(0,[z0,z3,z4,z8,z820,z46]),(0,[z0,z2,z3,z8,z14,z882])],[(0,[z760,z19,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z883,z6]),(0,[z0,z2,z142,z4,z8,z46]),(0,[z157,z0,z2,z3,z402,z8]),(0,[z0,z2,z3,z4,z8,z884])],[(0,[z2,z19,z271,z3,z4,z6]),(0,[z0,z3,z4,z851,z166,z6]),(0,[z0,z2,z885,z3,z4,z8])],[(0,[z0,z2,z886,z3,z4,z8]),(0,[z0,z2,z887,z3,z4,z6]),(0,[z0,z2,z3,z888,z8,z6]),(0,[z0,z2,z3,z889,z4,z8])],[(0,[z0,z2,z3,z4,z890,z6]),(0,[z0,z2,z3,z60,z8,z193]),(0,[z0,z2,z3,z4,z891,z6]),(0,[z0,z892,z3,z4,z8,z6]),(0,[z893,z2,z3,z4,z8,z6]),(0,[z0,z782,z3,z4,z8,z46])],[],[(0,[z0,z2,z3,z252,z8,z46]),(0,[z58,z2,z266,z60,z8,z6]),(0,[z129,z2,z52,z3,z53,z8]),(0,[z261,z341,z3,z4,z116,z6]),(0,[z0,z2,z3,z894,z8,z6])]],
   [[(0,[z0,z2,z3,z4,z895,z6]),(0,[z0,z2,z156,z653,z4,z6]),(0,[z0,z2,z896,z3,z4,z6])],[(0,[z0,z2,z3,z4,z897,z6]),(0,[z0,z2,z3,z16,z615,z8]),(0,[z0,z898,z3,z4,z8,z6]),(0,[z0,z2,z3,z899,z8,z6])],[(0,[z0,z74,z3,z252,z8,z6]),(0,[z0,z900,z3,z4,z8,z6]),(0,[z464,z2,z3,z496,z8,z6]),(0,[z0,z2,z3,z4,z901,z6]),(0,[z91,z0,z3,z4,z138,z14])],[(0,[z0,z2,z3,z902,z8,z6]),(0,[z0,z2,z3,z4,z8,z903]),(0,[z0,z7,z3,z196,z8,z9]),(0,[z795,z2,z3,z4,z8,z46]),(0,[z0,z524,z3,z4,z8,z245])],[(0,[z105,z281,z3,z4,z8,z6]),(0,[z689,z1,z3,z4,z8,z6]),(0,[z2,z3,z765,z4,z8,z6]),(0,[z0,z2,z210,z4,z56,z6]),(0,[z0,z2,z3,z4,z8,z195]),(0,[z0,z2,z3,z4,z8,z904])],[(0,[z0,z2,z905,z4,z8,z6]),(0,[z105,z2,z271,z3,z4,z6]),(0,[z0,z2,z3,z248,z8,z6]),(0,[z0,z2,z3,z906,z8,z6]),(0,[z648,z0,z3,z4,z138,z6])],[(0,[z0,z907,z3,z4,z8,z6]),(0,[z0,z703,z3,z117,z8,z6]),(0,[z0,z2,z12,z3,z8,z47])],[(0,[z0,z121,z3,z4,z8,z6]),(0,[z240,z2,z3,z53,z8,z6]),(0,[z0,z2,z3,z4,z8,z908]),(0,[z0,z909,z3,z4,z8,z6]),(0,[z261,z2,z3,z4,z116,z14]),(0,[z910,z2,z3,z4,z8,z6])]],
   [[(0,[z39,z2,z78,z4,z8,z46]),(0,[z0,z2,z3,z4,z8,z911]),(0,[z0,z2,z3,z4,z8,z912])],[(0,[z0,z2,z3,z913,z8,z6]),(0,[z0,z914,z2,z3,z4,z8]),(0,[z0,z2,z3,z4,z8,z915]),(0,[z0,z2,z916,z4,z8,z6]),(0,[z0,z2,z3,z4,z6,z725])],[(0,[z0,z2,z3,z4,z8,z917]),(0,[z0,z2,z3,z4,z366,z50]),(0,[z918,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z919]),(0,[z0,z2,z3,z4,z920,z6])],[(0,[z422,z19,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z6,z812])],[(0,[z0,z2,z3,z921,z8,z6]),(0,[z0,z2,z3,z4,z8,z922]),(0,[z0,z2,z3,z4,z923,z6]),(0,[z0,z2,z335,z3,z4,z14]),(0,[z0,z2,z3,z924,z8,z6]),(0,[z0,z2,z3,z660,z8,z213]),(0,[z0,z2,z3,z4,z8,z925])],[(0,[z0,z74,z3,z4,z8,z46]),(0,[z0,z21,z3,z4,z8,z22]),(0,[z0,z2,z4,z741,z56,z6]),(0,[z0,z2,z4,z42,z741,z6]),(0,[z0,z2,z3,z8,z46,z254])],[(0,[z0,z2,z3,z4,z8,z926]),(0,[z0,z2,z927,z3,z4,z6]),(0,[z928,z2,z3,z4,z8,z6]),(0,[z0,z2,z334,z3,z8,z14])],[(0,[z133,z2,z3,z101,z8,z6]),(0,[z0,z2,z3,z4,z929,z6])]],
   [[(0,[z39,z2,z399,z4,z8,z6]),(0,[z0,z2,z52,z3,z4,z8]),(0,[z0,z2,z3,z4,z33,z6]),(0,[z0,z2,z3,z402,z8,z6]),(0,[z0,z2,z23,z24,z68,z6]),(0,[z0,z2,z3,z4,z8,z930])],[(0,[z0,z1,z3,z621,z8,z6]),(0,[z261,z479,z3,z4,z116,z6]),(0,[z0,z2,z3,z4,z465,z232]),(0,[z931,z2,z3,z4,z8,z6]),(0,[z932,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z778])],[(0,[z2,z3,z709,z53,z8,z6]),(0,[z0,z2,z351,z4,z42,z6]),(0,[z933,z2,z3,z4,z8,z6]),(0,[z0,z2,z934,z3,z4,z8]),(0,[z0,z819,z3,z4,z8,z46])],[(0,[z0,z18,z190,z3,z4,z8]),(0,[z935,z2,z3,z4,z8,z6]),(1,[z0,z2,z3,z4,z725])],[(0,[z105,z1,z3,z4,z8,z46]),(0,[z0,z2,z3,z936,z8,z6]),(0,[z0,z83,z3,z4,z851,z6]),(0,[z0,z2,z3,z4,z8,z937])],[(0,[z0,z59,z3,z4,z169,z6]),(0,[z0,z2,z3,z35,z56,z6]),(0,[z0,z2,z649,z4,z8,z14])],[(0,[z0,z2,z3,z938,z4,z8])],[(0,[z129,z2,z3,z53,z8,z6]),(0,[z0,z2,z3,z4,z8,z799]),(0,[z0,z2,z4,z8,z14,z347]),(0,[z0,z2,z23,z24,z8,z6]),(1,[z0,z2,z722,z8,z6])]],
   [[(0,[z0,z2,z3,z4,z939,z6]),(0,[z0,z2,z3,z4,z940,z6]),(0,[z0,z2,z941,z3,z4,z8]),(0,[z2,z3,z4,z8,z6,z942]),(0,[z0,z2,z3,z4,z13,z725])],[(0,[z0,z2,z3,z943,z8,z6]),(0,[z0,z2,z3,z944,z8,z6]),(0,[z65,z2,z3,z4,z8,z799]),(0,[z0,z2,z4,z8,z14,z352]),(0,[z0,z83,z3,z4,z166,z14]),(0,[z0,z462,z3,z4,z8,z151]),(0,[z0,z2,z3,z4,z8,z945]),(0,[z0,z2,z15,z3,z519,z8])],[(0,[z0,z363,z3,z196,z8,z6]),(0,[z0,z2,z309,z4,z8,z14]),(0,[z0,z2,z3,z402,z8,z151])],[(0,[z96,z0,z102,z496,z8,z6]),(0,[z0,z2,z3,z4,z8,z946]),(0,[z0,z2,z3,z4,z8,z947]),(0,[z0,z18,z3,z402,z8,z151])],[(0,[z0,z2,z3,z4,z948,z8]),(0,[z0,z2,z3,z4,z949,z6]),(0,[z0,z2,z3,z4,z8,z950]),(0,[z2,z3,z4,z8,z799,z6]),(0,[z0,z97,z833,z4,z8,z6]),(0,[z0,z2,z517,z4,z8,z46])],[(0,[z0,z2,z3,z4,z8,z951]),(0,[z0,z2,z3,z496,z8,z232]),(0,[z91,z0,z3,z4,z138,z46]),(0,[z0,z2,z314,z4,z8,z14])],[(0,[z0,z2,z3,z952,z8,z6]),(0,[z0,z2,z3,z953,z4,z8]),(0,[z0,z2,z3,z954,z4,z8]),(0,[z0,z2,z3,z4,z465,z6]),(0,[z0,z2,z3,z4,z8,z955]),(0,[z0,z2,z3,z4,z8,z956]),(0,[z0,z2,z3,z4,z8,z957])],[(0,[z0,z2,z958,z3,z8,z6]),(0,[z0,z2,z3,z4,z8,z959]),(0,[z0,z2,z3,z4,z417,z373])]],
   [[(0,[z0,z2,z3,z4,z8,z960]),(0,[z0,z59,z3,z4,z8,z193]),(0,[z0,z74,z3,z60,z8,z6]),(0,[z0,z2,z3,z4,z8,z961]),(0,[z30,z2,z3,z4,z31,z14]),(0,[z0,z2,z23,z722,z8,z6]),(0,[z0,z2,z962,z3,z8,z6])],[(0,[z0,z963,z3,z4,z8,z6]),(0,[z0,z2,z964,z3,z4,z6]),(0,[z0,z2,z3,z965,z8,z6]),(0,[z0,z2,z3,z4,z8,z966])],[(0,[z58,z59,z266,z4,z8,z6]),(0,[z0,z2,z3,z709,z8,z6]),(0,[z261,z2,z3,z4,z116,z46])],[(0,[z30,z2,z3,z4,z830,z6]),(0,[z576,z2,z3,z496,z8,z6]),(0,[z0,z2,z3,z4,z967,z6])],[(0,[z614,z2,z266,z4,z8,z6]),(0,[z2,z3,z4,z709,z8,z6])],[(0,[z0,z2,z3,z4,z8,z968]),(0,[z0,z2,z3,z60,z8,z6]),(0,[z0,z2,z3,z248,z8,z14]),(0,[z25,z2,z3,z4,z8,z278])],[(0,[z0,z2,z3,z969,z8,z6]),(0,[z0,z2,z3,z4,z8,z970]),(0,[z0,z2,z3,z4,z830,z6])],[(0,[z0,z2,z335,z3,z4,z46]),(0,[z0,z121,z3,z4,z8,z14]),(0,[z0,z971,z3,z4,z8,z6])]],
   [[],[(0,[z464,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z972])],[(0,[z157,z2,z3,z4,z8,z130]),(0,[z0,z2,z28,z4,z8,z14])],[(0,[z0,z2,z973,z3,z4,z8]),(0,[z0,z2,z3,z4,z8,z87]),(0,[z0,z2,z3,z4,z417,z317]),(0,[z0,z2,z3,z4,z8,z974])],[],[(0,[z0,z2,z3,z4,z169,z50]),(0,[z0,z2,z3,z4,z8,z975]),(0,[z0,z2,z3,z4,z976,z6]),(0,[z0,z2,z3,z4,z977,z6]),(0,[z0,z2,z3,z4,z8,z978]),(1,[z0,z3,z4,z8,z806]),(0,[z0,z2,z3,z4,z8,z979]),(0,[z0,z2,z3,z4,z319,z177]),(0,[z0,z2,z334,z3,z339,z8])],[(0,[z0,z2,z3,z980,z8,z6]),(0,[z0,z2,z3,z981,z8,z6]),(0,[z0,z2,z3,z8,z6,z982])],[(0,[z0,z2,z335,z3,z4,z6]),(0,[z133,z2,z3,z101,z8,z14]),(0,[z0,z833,z102,z4,z8,z6]),(0,[z983,z2,z3,z4,z8,z6]),(0,[z984,z2,z3,z4,z8,z6]),(0,[z0,z2,z156,z4,z56,z14])]],
   [[(0,[z39,z2,z78,z4,z8,z206]),(0,[z0,z2,z3,z4,z33,z14]),(0,[z0,z2,z3,z402,z8,z14]),(0,[z0,z2,z3,z4,z8,z985]),(0,[z0,z2,z132,z4,z42,z14])],[(0,[z0,z2,z3,z4,z8,z986]),(0,[z987,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z8,z6,z882]),(0,[z0,z2,z334,z3,z8,z6])],[(0,[z0,z2,z988,z3,z4,z8]),(0,[z0,z2,z488,z24,z8,z6]),(0,[z233,z2,z3,z101,z8,z6]),(0,[z989,z0,z2,z3,z4,z8]),(0,[z0,z2,z77,z4,z42,z6]),(0,[z0,z2,z722,z67,z8,z6])],[(0,[z2,z3,z4,z8,z830,z6]),(0,[z0,z2,z877,z3,z4,z46]),(0,[z0,z2,z3,z4,z8,z990])],[(0,[z0,z2,z3,z4,z8,z991]),(0,[z0,z2,z3,z992,z8,z6]),(0,[z0,z2,z3,z993,z8,z6]),(0,[z2,z3,z4,z8,z799,z188]),(0,[z0,z83,z3,z4,z166,z46]),(0,[z0,z2,z3,z4,z8,z994]),(0,[z0,z2,z3,z4,z8,z995]),(0,[z0,z2,z3,z16,z8,z213])],[(0,[z39,z59,z3,z4,z8,z6]),(0,[z96,z0,z102,z4,z8,z232]),(0,[z0,z2,z218,z67,z8,z301])],[(0,[z0,z2,z3,z4,z8,z996])],[(0,[z0,z2,z765,z4,z8,z6]),(0,[z129,z2,z3,z53,z8,z14]),(0,[z0,z2,z23,z24,z8,z14]),(0,[z0,z2,z3,z8,z997,z46]),(0,[z0,z2,z998,z3,z4,z8]),(1,[z0,z2,z3,z786,z6])]],
   [[(0,[z0,z760,z3,z4,z8,z6]),(0,[z0,z2,z999,z3,z4,z8]),(0,[z0,z2,z132,z4,z42,z482])],[(0,[z0,z97,z194,z4,z8,z14]),(0,[z0,z3,z4,z8,z1000,z6]),(0,[z0,z2,z3,z1001,z8,z6])],[(0,[z0,z2,z3,z183,z4,z6]),(0,[z0,z2,z3,z4,z8,z1002]),(0,[z30,z2,z318,z3,z4,z6])],[(0,[z350,z19,z3,z4,z8,z6]),(0,[z58,z2,z266,z4,z169,z6]),(0,[z0,z2,z3,z1003,z4,z6]),(0,[z0,z2,z3,z1004,z4,z8]),(0,[z30,z2,z3,z4,z31,z46])],[(0,[z0,z281,z3,z4,z138,z6]),(0,[z0,z2,z3,z4,z8,z1005]),(0,[z0,z2,z3,z4,z741,z6]),(0,[z0,z898,z3,z4,z8,z46])],[(0,[z576,z2,z3,z4,z8,z232])],[(0,[z0,z2,z3,z4,z8,z1006]),(0,[z0,z2,z3,z4,z1007,z6]),(0,[z0,z2,z3,z248,z33,z6]),(0,[z0,z2,z3,z4,z465,z14])],[(0,[z2,z3,z4,z830,z31,z6]),(0,[z0,z2,z3,z1008,z8,z6]),(0,[z0,z2,z15,z3,z333,z8])]],
   [[(0,[z0,z2,z3,z4,z8,z1009]),(0,[z0,z2,z3,z248,z8,z46]),(0,[z0,z1010,z3,z4,z8,z6]),(0,[z0,z2,z132,z98,z42,z6]),(0,[z0,z2,z962,z3,z8,z14])],[(0,[z0,z3,z4,z138,z5,z6]),(0,[z0,z2,z3,z4,z1011,z6]),(0,[z1012,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z35,z8,z263])],[(0,[z0,z121,z3,z4,z8,z46]),(0,[z96,z0,z102,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z1013]),(0,[z0,z1014,z2,z3,z4,z8]),(0,[z0,z2,z3,z8,z213,z778])],[(0,[z0,z2,z3,z4,z8,z1015]),(0,[z30,z2,z3,z4,z31,z6]),(0,[z0,z2,z3,z248,z8,z90]),(0,[z0,z2,z202,z3,z4,z26])],[(0,[z673,z1,z3,z4,z8,z6]),(0,[z0,z2,z3,z1016,z4,z8]),(0,[z0,z2,z3,z4,z8,z1017])],[(0,[z0,z2,z3,z60,z8,z14]),(0,[z0,z2,z3,z4,z1018,z6]),(0,[z65,z2,z3,z4,z8,z278]),(0,[z0,z1019,z2,z3,z4,z8]),(0,[z0,z2,z3,z4,z8,z1020]),(0,[z0,z2,z3,z43,z6,z326])],[(0,[z0,z1021,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z1022]),(0,[z0,z2,z3,z4,z8,z1023]),(0,[z0,z3,z4,z8,z6,z711]),(0,[z0,z462,z3,z4,z8,z45])],[(0,[z0,z2,z107,z3,z180,z6]),(0,[z0,z2,z3,z594,z43,z6])]],
   [[(0,[z0,z59,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z1024]),(0,[z0,z2,z3,z4,z8,z1025]),(0,[z0,z3,z4,z747,z8,z6]),(0,[z0,z3,z196,z747,z8,z6]),(0,[z0,z2,z3,z4,z8,z258])],[(0,[z464,z2,z3,z4,z8,z14]),(0,[z0,z2,z3,z4,z68,z373])],[(0,[z576,z2,z3,z4,z8,z6]),(0,[z133,z2,z3,z101,z8,z46]),(0,[z0,z2,z156,z4,z56,z64])],[(0,[z85,z760,z3,z4,z8,z6]),(0,[z380,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z33,z46]),(0,[z0,z2,z3,z1026,z8,z6]),(0,[z0,z2,z3,z402,z8,z46]),(0,[z0,z2,z3,z98,z8,z263]),(0,[z0,z2,z132,z4,z42,z46])],[(0,[z0,z2,z4,z8,z14,z469])],[(0,[z0,z2,z3,z4,z1027,z6]),(0,[z0,z1028,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z33,z90]),(0,[z0,z2,z833,z4,z8,z6])],[(0,[z0,z2,z3,z1029,z8,z6]),(0,[z0,z2,z230,z67,z8,z6]),(0,[z0,z2,z334,z202,z3,z8])]],
   [[(0,[z0,z2,z1030,z3,z8,z6]),(0,[z380,z3,z4,z138,z8,z6]),(0,[z0,z2,z1031,z3,z8,z6]),(0,[z0,z2,z3,z4,z8,z373]),(0,[z0,z1032,z3,z4,z8,z6]),(0,[z0,z2,z3,z16,z8,z778])],[(0,[z0,z1033,z2,z3,z4,z8]),(0,[z0,z2,z3,z4,z8,z1034]),(0,[z1035,z2,z3,z4,z8,z6]),(1,[z0,z3,z4,z851,z6]),(0,[z0,z1036,z3,z4,z8,z6])],[(0,[z129,z2,z3,z53,z8,z46]),(0,[z0,z404,z3,z4,z8,z22]),(0,[z0,z2,z23,z24,z8,z46]),(0,[z0,z2,z156,z4,z56,z6])],[(0,[z0,z2,z3,z4,z6,z1037]),(0,[z0,z2,z3,z1038,z8,z6]),(0,[z0,z2,z3,z4,z8,z1039]),(0,[z0,z2,z132,z4,z42,z6])],[(0,[z0,z341,z3,z4,z5,z6]),(0,[z0,z97,z194,z4,z8,z46]),(0,[z0,z2,z3,z4,z8,z1040]),(0,[z0,z2,z3,z4,z8,z1041])],[(0,[z0,z1042,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z1043]),(0,[z0,z2,z3,z4,z8,z1044]),(0,[z0,z2,z3,z4,z68,z317]),(0,[z0,z2,z24,z722,z8,z6]),(0,[z0,z2,z3,z8,z6,z751])],[(0,[z261,z2,z3,z4,z830,z6]),(0,[z0,z2,z3,z4,z8,z301]),(0,[z0,z2,z1045,z3,z4,z8]),(0,[z0,z2,z3,z4,z8,z1046])],[(0,[z0,z2,z3,z1047,z8,z6])]],
   [[(0,[z0,z19,z3,z4,z8,z9]),(0,[z0,z2,z3,z4,z1048,z6]),(0,[z0,z1049,z3,z4,z8,z6]),(0,[z0,z2,z1050,z3,z4,z6])],[(0,[z0,z2,z3,z4,z366,z193]),(0,[z490,z2,z3,z4,z31,z6]),(0,[z0,z2,z692,z4,z8,z46]),(0,[z0,z2,z3,z4,z465,z46]),(0,[z0,z97,z194,z4,z8,z80]),(0,[z0,z2,z3,z4,z8,z9]),(0,[z0,z3,z4,z8,z1000,z14])],[(0,[z0,z7,z3,z86,z8,z6]),(0,[z0,z2,z3,z4,z8,z1051]),(0,[z0,z2,z3,z183,z4,z14]),(0,[z0,z2,z391,z4,z8,z46]),(0,[z0,z2,z310,z4,z8,z46]),(0,[z0,z7,z3,z196,z8,z313]),(0,[z0,z21,z3,z4,z8,z806]),(0,[z0,z2,z958,z3,z8,z46]),(0,[z0,z2,z3,z41,z43,z6])],[(0,[z0,z74,z3,z4,z8,z50]),(0,[z58,z2,z266,z4,z366,z6]),(0,[z0,z2,z1052,z4,z8,z6]),(0,[z576,z97,z3,z4,z8,z6])],[(0,[z381,z19,z3,z4,z8,z6]),(0,[z0,z97,z561,z4,z8,z6]),(0,[z129,z2,z3,z165,z53,z8]),(0,[z0,z97,z194,z4,z8,z6]),(0,[z0,z2,z3,z4,z465,z90]),(0,[z0,z2,z15,z3,z8,z525]),(0,[z0,z2,z3,z4,z1053,z6]),(0,[z0,z2,z3,z4,z8,z317]),(0,[z0,z2,z156,z4,z741,z6]),(0,[z0,z2,z1054,z3,z4,z8])],[(0,[z474,z19,z3,z4,z8,z6]),(0,[z479,z3,z4,z116,z8,z6])],[(0,[z0,z2,z3,z4,z8,z1055]),(0,[z0,z2,z3,z4,z8,z263]),(0,[z0,z2,z202,z3,z4,z17])],[(0,[z0,z2,z3,z4,z1056,z6]),(0,[z0,z1057,z3,z4,z8,z6]),(0,[z0,z2,z4,z403,z8,z46]),(0,[z0,z2,z3,z1008,z8,z14])]],
   [[(0,[z0,z2,z3,z4,z8,z1058]),(0,[z0,z2,z3,z4,z8,z50]),(0,[z59,z3,z266,z4,z8,z6]),(0,[z0,z2,z3,z60,z8,z46]),(0,[z0,z2,z3,z4,z8,z1059])],[(0,[z0,z2,z3,z4,z169,z6])],[(0,[z0,z2,z3,z4,z49,z14]),(0,[z96,z0,z102,z4,z8,z14]),(0,[z1060,z2,z3,z4,z8,z6]),(0,[z91,z380,z3,z4,z138,z6]),(0,[z0,z971,z3,z4,z8,z46]),(0,[z0,z2,z518,z3,z4,z17]),(0,[z0,z1061,z3,z4,z8,z6])],[(0,[z0,z377,z3,z4,z8,z6]),(0,[z0,z1062,z2,z3,z4,z8]),(0,[z0,z2,z3,z4,z8,z1063]),(0,[z0,z2,z3,z4,z1064,z6]),(0,[z0,z2,z3,z4,z417,z6]),(0,[z0,z2,z1065,z4,z8,z6])],[(0,[z0,z1066,z3,z4,z8,z6]),(0,[z39,z2,z78,z4,z8,z87]),(0,[z65,z121,z3,z4,z8,z188]),(0,[z464,z2,z3,z4,z8,z46]),(0,[z1067,z2,z3,z4,z8,z6])],[(0,[z0,z2,z271,z3,z4,z6]),(0,[z0,z2,z3,z4,z8,z1068])],[(0,[z0,z2,z3,z4,z8,z1069]),(0,[z0,z2,z3,z4,z8,z1070]),(0,[z0,z2,z3,z1071,z8,z6])],[(0,[z39,z2,z765,z4,z8,z6]),(0,[z464,z2,z3,z4,z8,z90])]],
   [[(0,[z0,z59,z3,z4,z8,z14]),(0,[z0,z21,z377,z3,z4,z8]),(0,[z1072,z2,z3,z4,z8,z6])],[(0,[z0,z341,z3,z4,z8,z6]),(0,[z0,z2,z3,z1073,z8,z6]),(0,[z0,z2,z3,z4,z1074,z6]),(0,[z0,z2,z3,z4,z1075,z6]),(0,[z2,z765,z266,z4,z8,z6]),(0,[z0,z1076,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z8,z1077]),(0,[z0,z1078,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z1079]),(0,[z576,z2,z3,z4,z8,z14]),(0,[z0,z2,z334,z202,z3,z17])],[(0,[z0,z19,z3,z621,z8,z6]),(0,[z0,z2,z3,z4,z8,z1080]),(0,[z380,z2,z3,z4,z8,z14])],[(0,[z0,z2,z3,z621,z8,z6]),(0,[z0,z2,z434,z4,z8,z46]),(0,[z0,z2,z334,z3,z8,z46]),(0,[z0,z2,z3,z4,z8,z1081])],[(0,[z0,z2,z3,z496,z8,z6]),(0,[z0,z2,z3,z4,z8,z313]),(0,[z0,z2,z3,z196,z8,z313]),(0,[z0,z2,z3,z4,z339,z13])],[(0,[z0,z2,z1082,z4,z8,z6]),(0,[z58,z2,z266,z4,z8,z6]),(0,[z0,z2,z3,z4,z1083,z6]),(0,[z0,z1084,z3,z4,z8,z6])],[(0,[z1,z760,z3,z4,z8,z6]),(0,[z96,z576,z102,z4,z8,z6]),(0,[z0,z2,z1085,z4,z8,z6]),(1,[z0,z3,z747,z8,z6]),(0,[z0,z2,z3,z4,z1086,z6])]],
   [[(0,[z0,z2,z3,z1087,z8,z6]),(0,[z0,z2,z15,z3,z8,z577]),(0,[z0,z1088,z3,z4,z8,z6])],[(0,[z0,z2,z1089,z3,z4,z8]),(0,[z0,z2,z335,z3,z24,z6]),(0,[z0,z2,z3,z733,z8,z6]),(0,[z0,z2,z340,z4,z8,z14]),(0,[z0,z2,z3,z4,z8,z1090]),(0,[z0,z2,z107,z3,z295,z6])],[(0,[z0,z2,z3,z4,z1091,z6]),(0,[z0,z1092,z3,z4,z8,z6]),(0,[z0,z377,z15,z3,z4,z8]),(0,[z0,z2,z107,z3,z241,z299])],[(0,[z0,z1093,z3,z4,z8,z6]),(0,[z0,z2,z3,z117,z8,z313]),(0,[z1094,z0,z2,z3,z4,z6])],[(0,[z382,z19,z3,z4,z8,z6]),(0,[z2,z3,z4,z8,z46,z942])],[(0,[z0,z2,z4,z1095,z8,z6]),(0,[z0,z1096,z3,z4,z8,z6]),(0,[z0,z2,z3,z183,z4,z46]),(0,[z0,z2,z3,z4,z8,z1097]),(0,[z0,z2,z550,z67,z8,z6]),(0,[z0,z2,z15,z3,z8,z593]),(0,[z0,z2,z3,z4,z339,z725])],[(0,[z0,z2,z3,z4,z1098,z8]),(0,[z0,z2,z3,z8,z6,z997]),(0,[z0,z2,z3,z1099,z8,z6]),(0,[z0,z2,z520,z4,z8,z14])],[(0,[z513,z19,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z1100,z6]),(0,[z0,z2,z3,z4,z1101,z6]),(0,[z0,z18,z3,z621,z8,z151]),(0,[z0,z2,z3,z35,z8,z6])]],
   [[(0,[z0,z59,z3,z252,z8,z6]),(0,[z0,z2,z107,z3,z299,z6])],[(0,[z0,z2,z52,z3,z183,z4]),(0,[z0,z341,z3,z4,z166,z6]),(0,[z0,z2,z3,z8,z14,z254]),(0,[z0,z2,z107,z3,z312,z6])],[(0,[z0,z2,z3,z1102,z4,z6]),(0,[z0,z2,z3,z4,z6,z1103]),(0,[z1104,z2,z3,z4,z8,z6]),(0,[z0,z2,z1105,z3,z4,z6]),(0,[z0,z2,z4,z8,z14,z46]),(0,[z0,z2,z3,z41,z43,z14])],[(0,[z0,z1106,z3,z4,z8,z6]),(0,[z0,z1107,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z1108]),(0,[z0,z2,z670,z24,z8,z6]),(0,[z0,z2,z670,z4,z42,z6])],[(0,[z0,z74,z3,z4,z366,z6]),(0,[z0,z2,z3,z4,z169,z193]),(0,[z0,z2,z3,z4,z851,z6])],[(0,[z0,z2,z3,z4,z49,z46]),(0,[z65,z377,z3,z4,z8,z188]),(0,[z96,z0,z102,z4,z8,z46]),(0,[z0,z541,z3,z196,z8,z6]),(0,[z0,z21,z3,z4,z8,z245])],[(0,[z0,z2,z3,z4,z1109,z6]),(0,[z0,z2,z3,z4,z8,z1110])],[(0,[z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1111,z6]),(0,[z0,z2,z359,z4,z8,z14])]],
   [[(0,[z0,z2,z3,z4,z8,z1112]),(0,[z0,z2,z3,z4,z8,z1113]),(0,[z0,z2,z3,z4,z8,z1114]),(0,[z96,z464,z102,z4,z8,z6]),(0,[z96,z0,z102,z4,z8,z90]),(0,[z0,z2,z3,z4,z1115,z6]),(0,[z0,z2,z3,z4,z8,z1116])],[(0,[z0,z2,z1117,z3,z4,z6]),(0,[z0,z2,z1118,z4,z8,z6]),(0,[z105,z1,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z366,z6]),(0,[z0,z2,z3,z4,z169,z14]),(0,[z0,z2,z3,z4,z1119,z6]),(0,[z0,z7,z3,z196,z8,z6]),(0,[z0,z3,z4,z138,z851,z6]),(0,[z0,z2,z3,z98,z8,z6]),(0,[z0,z2,z3,z35,z42,z6]),(0,[z0,z2,z3,z4,z108,z612]),(0,[z0,z2,z3,z41,z786,z6]),(0,[z0,z2,z3,z8,z778,z113])],[(0,[z0,z2,z3,z1120,z8,z6]),(0,[z0,z2,z3,z4,z8,z1121]),(0,[z0,z2,z107,z3,z786,z6]),(0,[z0,z2,z3,z4,z725,z17])],[(0,[z0,z2,z1122,z3,z8,z6]),(0,[z0,z59,z3,z4,z8,z46]),(0,[z0,z3,z4,z1123,z8,z6]),(0,[z0,z377,z3,z4,z8,z14]),(0,[z576,z3,z102,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z1124]),(0,[z0,z2,z3,z1125,z8,z6]),(0,[z0,z2,z3,z4,z417,z14]),(0,[z0,z2,z4,z8,z14,z124]),(1,[z0,z2,z3,z8,z778])],[(0,[z0,z1126,z3,z4,z8,z6]),(0,[z0,z341,z3,z4,z138,z6]),(0,[z0,z3,z833,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z1127]),(0,[z2,z3,z4,z8,z1128,z6]),(0,[z0,z2,z776,z3,z8,z6])],[(0,[z0,z2,z3,z4,z49,z6]),(0,[z0,z2,z3,z1129,z8,z6]),(0,[z0,z2,z271,z3,z4,z14]),(0,[z157,z2,z3,z4,z8,z799]),(0,[z576,z2,z3,z4,z8,z46]),(0,[z0,z2,z1130,z3,z4,z6]),(0,[z0,z2,z3,z4,z8,z1131])],[(0,[z0,z2,z3,z4,z8,z1132]),(0,[z380,z2,z3,z4,z8,z46]),(0,[z0,z2,z1133,z3,z4,z8])],[(0,[z105,z1,z3,z4,z49,z6]),(0,[z0,z2,z1134,z3,z8,z6]),(0,[z0,z2,z3,z4,z8,z232]),(0,[z0,z7,z3,z747,z8,z6]),(0,[z0,z2,z392,z4,z8,z46])]],
   [[(0,[z576,z2,z3,z4,z8,z90]),(0,[z0,z3,z4,z8,z151,z806]),(0,[z0,z2,z3,z4,z1135,z6]),(0,[z0,z2,z1136,z3,z4,z8])],[(0,[z0,z2,z3,z4,z1137,z6]),(0,[z515,z1,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z1138]),(0,[z58,z2,z266,z4,z8,z193]),(0,[z0,z341,z3,z4,z8,z14]),(0,[z0,z97,z194,z4,z8,z195])],[(0,[z0,z2,z3,z4,z1139,z6]),(0,[z0,z2,z3,z4,z8,z1140]),(0,[z0,z2,z573,z67,z8,z6]),(0,[z0,z2,z3,z4,z8,z1141]),(0,[z0,z3,z4,z8,z806,z22]),(0,[z0,z2,z3,z4,z8,z1142]),(0,[z0,z2,z4,z8,z46,z430]),(0,[z0,z1143,z3,z4,z8,z6])],[(0,[z0,z2,z1144,z3,z4,z8])],[(0,[z0,z2,z1145,z3,z4,z6]),(0,[z0,z2,z443,z24,z8,z6]),(0,[z0,z2,z3,z621,z8,z14]),(0,[z0,z2,z3,z4,z8,z64]),(0,[z0,z2,z3,z43,z786,z6])],[(0,[z0,z2,z3,z1146,z8,z6]),(0,[z0,z2,z378,z4,z8,z46]),(0,[z157,z2,z3,z4,z8,z143]),(0,[z216,z2,z3,z4,z8,z130]),(0,[z0,z2,z3,z496,z8,z14]),(0,[z0,z2,z3,z1147,z8,z6]),(0,[z0,z51,z3,z117,z8,z14]),(0,[z0,z2,z3,z4,z68,z6]),(0,[z0,z2,z3,z4,z737,z6]),(0,[z0,z2,z156,z4,z56,z46]),(0,[z0,z2,z12,z3,z8,z113])],[(0,[z0,z2,z3,z4,z8,z1148]),(0,[z58,z2,z266,z4,z8,z14]),(0,[z2,z78,z765,z4,z8,z6]),(0,[z65,z0,z2,z3,z402,z8]),(0,[z0,z2,z3,z4,z742,z6])],[(0,[z0,z1149,z3,z4,z8,z6]),(1,[z2,z3,z4,z8,z799]),(0,[z0,z2,z3,z248,z465,z6])]],
   [[(0,[z0,z2,z3,z252,z8,z50]),(0,[z0,z2,z4,z8,z46,z438]),(0,[z0,z2,z3,z123,z8,z502])],[(0,[z0,z470,z3,z117,z8,z6]),(0,[z0,z1150,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z80])],[(0,[z0,z2,z3,z1151,z8,z6]),(0,[z0,z2,z3,z411,z8,z461]),(0,[z0,z1152,z3,z4,z8,z6])],[(0,[z19,z3,z671,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z1153]),(0,[z0,z2,z3,z4,z1154,z6]),(0,[z0,z61,z3,z4,z8,z14]),(0,[z0,z1155,z3,z4,z8,z6]),(0,[z0,z1093,z3,z4,z8,z14])],[(0,[z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z1156,z6]),(0,[z0,z2,z3,z4,z8,z1157]),(0,[z0,z1158,z3,z4,z8,z6])],[(0,[z0,z141,z3,z4,z8,z14]),(0,[z0,z194,z833,z4,z8,z6]),(0,[z0,z3,z808,z4,z8,z6]),(0,[z0,z2,z3,z41,z43,z46])],[(0,[z0,z59,z3,z60,z8,z6]),(0,[z0,z2,z3,z67,z68,z6])],[(0,[z0,z2,z3,z4,z8,z1159]),(0,[z0,z1160,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z1161]),(0,[z157,z330,z2,z3,z4,z8]),(0,[z0,z2,z3,z24,z68,z6]),(0,[z0,z2,z3,z35,z8,z14])]],
   [[(0,[z0,z2,z3,z1162,z8,z6]),(0,[z0,z2,z3,z1163,z8,z6]),(0,[z0,z2,z3,z4,z8,z1164]),(0,[z0,z590,z3,z4,z166,z6]),(0,[z0,z2,z3,z4,z8,z1165]),(0,[z0,z2,z107,z3,z299,z14])],[(0,[z0,z2,z3,z1166,z8,z6]),(0,[z0,z763,z3,z4,z8,z6]),(0,[z0,z1167,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z1168]),(0,[z0,z2,z15,z302,z3,z8]),(0,[z0,z2,z202,z3,z254,z17])],[(1,[z2,z3,z709,z8,z6]),(0,[z464,z2,z3,z248,z8,z6]),(0,[z0,z2,z3,z1169,z8,z6]),(0,[z128,z2,z3,z4,z8,z143])],[(0,[z105,z565,z3,z4,z8,z6]),(0,[z0,z479,z3,z4,z8,z14]),(0,[z0,z2,z15,z3,z262,z8]),(0,[z0,z2,z3,z4,z8,z806]),(0,[z0,z2,z3,z4,z1103,z46])],[(0,[z0,z2,z3,z4,z169,z46]),(0,[z0,z2,z3,z4,z8,z1170]),(0,[z0,z18,z3,z4,z8,z806]),(0,[z0,z18,z3,z4,z8,z418]),(0,[z0,z1171,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z108,z13])],[(0,[z0,z2,z3,z4,z8,z1172]),(0,[z0,z3,z4,z8,z1173,z6])],[(0,[z58,z2,z266,z252,z8,z6]),(1,[z2,z3,z4,z830,z6]),(0,[z0,z377,z3,z4,z8,z46]),(0,[z0,z2,z3,z4,z8,z1174]),(0,[z0,z2,z3,z4,z417,z46])],[(0,[z0,z2,z3,z4,z5,z14]),(0,[z0,z74,z3,z4,z169,z6]),(0,[z0,z2,z3,z4,z8,z1175]),(0,[z0,z18,z3,z4,z8,z151]),(0,[z0,z2,z3,z35,z8,z482]),(0,[z0,z2,z3,z777,z8,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 537) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 537).take 532) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1069).take 142) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1211)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [537, 532, 142] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 126).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 126).take 128).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 254).take 2).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [126, 128, 2] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

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

end PEqualNP.Outside.L_meta_40347

theorem PEqualNP.Outside.L_meta_40347 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4209565920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4209565920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_40347.solve