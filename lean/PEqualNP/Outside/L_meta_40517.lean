import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40517

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
  Nat.testBit (4276809450 * 2 ^ 32 + 4243120288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00209082c602e150#64 ++ 0x400209082c602e15#64 ++ 0xe067b18fc607e3ff#64 ++ 0xae067b18fc607e3f#64 : BitVec 256),
   (0x108a163602d96cc4#64 ++ 0x8108a163602d96cc#64 ++ 0xb19a5e7607f9fccf#64 ++ 0x7b19a5e7607f9fcc#64 : BitVec 256),
   (0x06146058182c16a1#64 ++ 0x006146058182c16a#64 ++ 0xee1c6078783e3ffe#64 ++ 0xfee1c6078783e3ff#64 : BitVec 256),
   (0x4b607b806f403b06#64 ++ 0x04b607b806f403b0#64 ++ 0x5fe07f807fc03f0d#64 ++ 0xf5fe07f807fc03f0#64 : BitVec 256),
   (0x2dff800075b78008#64 ++ 0x02dff800075b7800#64 ++ 0x6fff80007fffc00b#64 ++ 0xf6fff80007fffc00#64 : BitVec 256),
   (0x8fdf6d6d00000000#64 ++ 0x08fdf6d6d0000000#64 ++ 0x9fffffff80000007#64 ++ 0xe9fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [6, 10]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [9, 4]⟩, ⟨.or, [11, 13]⟩, ⟨.and, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00209082c602e150 0x400209082c602e15 0xe067b18fc607e3ff 0xae067b18fc607e3f

def z1 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0xee1c6078783e3ffe 0xfee1c6078783e3ff

def z2 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xb19a5e7607f9fccf 0x7b19a5e7607f9fcc

def z3 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x6fff80007fffc00b 0xf6fff80007fffc00

def z4 : W := mkw 0x2fffe0587dbf96a9 0x02fffe0587dbf96a 0xefffe0787fffffff 0xfefffe0787ffffff

def z5 : W := mkw 0x4b60fb82ef42fb56 0x44b60fb82ef42fb5 0xffe7ff8fffc7ffff 0xfffe7ff8fffc7fff

def z6 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x9fffffff80000007 0xe9fffffff8000000

def z7 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x5fe07f807fc03f0d 0xf5fe07f807fc03f0

def z8 : W := mkw 0x82007def82006150 0x482007def8200615 0x90007fff800023f4 0x090007fff800023f

def z9 : W := mkw 0x00000010182c16a1 0x000000010182c16a 0x60000000783e3ff8 0x160000000783e3ff

def z10 : W := mkw 0x89cb0d2500000000 0x089cb0d250000000 0x11e39f8780000001 0x011e39f878000000

def z11 : W := mkw 0x9fdf7f7f02d96cc4 0x89fdf7f7f02d96cc 0xbf9a5e7607f9fccf 0x7bf9a5e7607f9fcc

def z12 : W := mkw 0x0414004810240021 0x0041400481024002 0x0004000800060030 0x0000400080006003

def z13 : W := mkw 0x29eb9082e793e158 0x429eb9082e793e15 0xe1e7b18fc7c7e3ff 0xae1e7b18fc7c7e3f

def z14 : W := mkw 0x52007fb60a487fc6 0x852007fb60a487fc 0x90007ff600003fc4 0x090007ff600003fc

def z15 : W := mkw 0x6fffe9807db7930a 0x06fffe9807db7930 0x6fffa1807fffc30b 0xf6fffa1807fffc30

def z16 : W := mkw 0x2d75800075b78008 0x02d75800075b7800 0x6e6580007fffc008 0x96e6580007fffc00

def z17 : W := mkw 0x008a162402402804 0x0008a16240240280 0x919a5e7607c03c0f 0x7919a5e7607c03c0

def z18 : W := mkw 0x10aa96b6c6dbedd4 0xc10aa96b6c6dbedd 0xf1ffffffc7ffffff 0xff1ffffffc7fffff

def z19 : W := mkw 0x169e767e1afd7ee5 0x8169e767e1afd7ee 0xff9e7e7e7fffffff 0xfff9e7e7e7ffffff

def z20 : W := mkw 0x4b407b002b403a06 0x04b407b002b403a0 0x1f805e003fc03c0d 0x71f805e003fc03c0

def z21 : W := mkw 0x108a16b682d96dd4 0xc108a16b682d96dd 0xb19a7fff87f9ffff 0x7b19a7fff87f9fff

def z22 : W := mkw 0x8f55694918241221 0x08f5569491824122 0x4e65a189f8060330 0x84e65a189f806033

def z23 : W := mkw 0x249f800010b78008 0x0249f800010b7800 0x201f8000003fc002 0x0201f8000003fc00

def z24 : W := mkw 0x42007b800a403b06 0x042007b800a403b0 0x10007f8000003f04 0x010007f8000003f0

def z25 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z26 : W := mkw 0x4b406b0029401a06 0x04b406b0029401a0 0x1f804e0039c01c00 0x51f804e0039c01c0

def z27 : W := mkw 0x0200600008001200 0x0020060000800120 0x4e00600078003f0c 0xf4e00600078003f0

def z28 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0x8e1c607838381c06 0xf8e1c607838381c0

def z29 : W := mkw 0x0020108046002100 0x0002010804600210 0xe0643188460623ff 0xae0643188460623f

def z30 : W := mkw 0x0dff9082c602e150 0x40dff9082c602e15 0xefffb18fc607e3ff 0xeefffb18fc607e3f

def z31 : W := mkw 0x0940000021000000 0x0094000002100000 0x0f80000039c00000 0x50f80000039c0000

def z32 : W := mkw 0xafffed6d75b78008 0x0afffed6d75b7800 0xffffffffffffc00f 0xfffffffffffffc00

def z33 : W := mkw 0x8f55694900000000 0x08f5569490000000 0x0e65a18980000000 0x80e65a1898000000

def z34 : W := mkw 0x2f75e0487d269229 0x02f75e0487d26922 0x4e65a00878060330 0x84e65a0087806033

def z35 : W := mkw 0x00209082c602e150 0x400209082c602e15 0x000000000601c000 0x0000000000601c00

def z36 : W := mkw 0x1000121202d96cc4 0x81000121202d96cc 0x2000000007f9fcc8 0x12000000007f9fcc

def z37 : W := mkw 0x2ddf000031b50008 0x02ddf000031b5000 0x0f98000039f80000 0x50f98000039f8000

def z38 : W := mkw 0x402012806f403b06 0x0402012806f403b0 0x406031807fc03f0d 0xb406031807fc03f0

def z39 : W := mkw 0x049e000010b50000 0x0049e000010b5000 0x6f9e00007fffc00b 0xf6f9e00007fffc00

def z40 : W := mkw 0x8fdf6d6d08001200 0x08fdf6d6d0800120 0xdffffffff8003f0f 0xfdffffffff8003f0

def z41 : W := mkw 0x06146058102c04a1 0x006146058102c04a 0xae1c6078003e00f6 0xeae1c6078003e00f

def z42 : W := mkw 0x1614767e1a6c7ee5 0x81614767e1a6c7ee 0xfe1c7e7e783e3ffe 0xffe1c7e7e783e3ff

def z43 : W := mkw 0x69eb9b8067d3a90e 0x069eb9b8067d3a90 0x11e39f8007c1c001 0x011e39f8007c1c00

def z44 : W := mkw 0x0020800044028000 0x0002080004402800 0x600000004607c008 0x0600000004607c00

def z45 : W := mkw 0x0000108282006150 0x4000010828200615 0x8000318f800023f4 0x08000318f800023f

def z46 : W := mkw 0x108a0436009944c0 0x8108a0436009944c 0xa01a00760039c0c2 0x0a01a00760039c0c

def z47 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0x31821e0607f9fcc9 0x131821e0607f9fcc

def z48 : W := mkw 0x0000120002402804 0x0000012000240280 0x11805e0007c03c0d 0x711805e0007c03c0

def z49 : W := mkw 0x00208082c402c150 0x400208082c402c15 0xe067a18fc007c3f2 0x8e067a18fc007c3f

def z50 : W := mkw 0x99cb1f2702d16844 0x899cb1f2702d1684 0x11e39f8787c1c001 0x011e39f8787c1c00

def z51 : W := mkw 0x8000046d00000000 0x08000046d0000000 0x8000007f80000000 0x08000007f8000000

def z52 : W := mkw 0x8fdf6d7d182c16a1 0x08fdf6d7d182c16a 0xfffffffff83e3fff 0xffffffffff83e3ff

def z53 : W := mkw 0x00209082c602e150 0x400209082c602e15 0x600000004607e3f8 0x0600000004607e3f

def z54 : W := mkw 0x8ffffdefc602e150 0x48ffffdefc602e15 0xffffffffc607e3ff 0xeffffffffc607e3f

def z55 : W := mkw 0x1000162602406844 0x8100016260240684 0x10001e0600000000 0x010001e060000000

def z56 : W := mkw 0x04140058102c04a1 0x004140058102c04a 0xa01c0078003e00f2 0x0a01c0078003e00f

def z57 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xb1ffffff87f9fccf 0xfb1ffffff87f9fcc

def z58 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0042008400623fe 0xae0042008400623f

def z59 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0x0e18407038381c00 0x50e18407038381c0

def z60 : W := mkw 0x2d75800075268008 0x02d7580007526800 0x4e65800078060000 0x84e6580007806000

def z61 : W := mkw 0x0000000000000000 0x0000000000000000 0x8067b18f80000007 0xa8067b18f8000000

def z62 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x6f9800007fffc008 0x56f9800007fffc00

def z63 : W := mkw 0x2020800065938008 0x0202080006593800 0x0000000007c1c000 0x00000000007c1c00

def z64 : W := mkw 0x0634f0cac602e150 0x40634f0cac602e15 0xee7ff1ffc607e3ff 0xeee7ff1ffc607e3f

def z65 : W := mkw 0x0b40690000000000 0x00b4069000000000 0x1fe07f8000000005 0xe1fe07f800000000

def z66 : W := mkw 0xcfff7fed6f403b06 0x0cfff7fed6f403b0 0xdfffffffffc03f0f 0xfdfffffffffc03f0

def z67 : W := mkw 0x0000100202006040 0x0000010020200604 0xa00210060601e0cf 0x2a00210060601e0c

def z68 : W := mkw 0x2dff9082f7b7e158 0x42dff9082f7b7e15 0xefffb18fffffe3ff 0xfefffb18fffffe3f

def z69 : W := mkw 0x4f747bd87f6c3fa7 0x04f747bd87f6c3fa 0xfffc7ff87ffe3fff 0xffffc7ff87ffe3ff

def z70 : W := mkw 0x0960120067402804 0x0096012006740280 0x5fe05e007fc03c0d 0xf5fe05e007fc03c0

def z71 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0x6e1c4070783e1c0a 0xf6e1c4070783e1c0

def z72 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0x6e184070783e3ff8 0x56e184070783e3ff

def z73 : W := mkw 0x4b60fb82ef42fb56 0x44b60fb82ef42fb5 0x7fe07f807fc7fffd 0xf7fe07f807fc7fff

def z74 : W := mkw 0x99cb1f3702d96cc4 0x899cb1f3702d96cc 0xb1fbdff787f9fccf 0x7b1fbdff787f9fcc

def z75 : W := mkw 0x02006058080816a1 0x002006058080816a 0x8000607800003ff4 0x08000607800003ff

def z76 : W := mkw 0x0614600018241200 0x0061460001824120 0x6e1c6000783e3f0e 0xf6e1c6000783e3f0

def z77 : W := mkw 0x86146d7d182c16a1 0x086146d7d182c16a 0xfe1c7ffff83e3ffe 0xffe1c7ffff83e3ff

def z78 : W := mkw 0x29cb000021910008 0x029cb00002191000 0x0180000001c00000 0x00180000001c0000

def z79 : W := mkw 0x008a042400000000 0x0008a04240000000 0x919a5e7600000007 0x6919a5e760000000

def z80 : W := mkw 0x92007f7f02486cc4 0x892007f7f02486cc 0x90007fff80003cc4 0x090007fff80003cc

def z81 : W := mkw 0x09609082e702e150 0x409609082e702e15 0xefe7b18fffc7e3ff 0xfefe7b18fffc7e3f

def z82 : W := mkw 0x0020800044028000 0x0002080004402800 0x606780004607c00b 0xa606780004607c00

def z83 : W := mkw 0x82006d7d080816a1 0x082006d7d080816a 0x90007fff80003ff4 0x090007fff80003ff

def z84 : W := mkw 0x0614604800000000 0x0061460480000000 0x8e7ff1ff80000007 0xe8e7ff1ff8000000

def z85 : W := mkw 0x00208080c4028110 0x400208080c402811 0x4065a189c0060330 0x84065a189c006033

def z86 : W := mkw 0x2dff8080f5b78118 0x42dff8080f5b7811 0x6fffa189ffffc33b 0xf6fffa189ffffc33

def z87 : W := mkw 0x5bea7fb66fd97fc6 0x85bea7fb66fd97fc 0xfffa7ff67ff9ffcf 0xffffa7ff67ff9ffc

def z88 : W := mkw 0x0000100202006040 0x0000010020200604 0xe006300e4607e3ff 0xae006300e4607e3f

def z89 : W := mkw 0x0960000065000000 0x0096000006500000 0x4fe000007fc00009 0xf4fe000007fc0000

def z90 : W := mkw 0x00209082c602e150 0x400209082c602e15 0x006391878601c001 0x0006391878601c00

def z91 : W := mkw 0x4b60fb82ef42fb56 0x44b60fb82ef42fb5 0x5fe3ff87ffc1ff0d 0xf5fe3ff87ffc1ff0

def z92 : W := mkw 0x0614604818241221 0x0061460481824122 0x4e04200878060330 0x84e0420087806033

def z93 : W := mkw 0x89cb0d2500000000 0x089cb0d250000000 0x91fbdff780000007 0x691fbdff78000000

def z94 : W := mkw 0xa9eb8d2565938008 0x0a9eb8d256593800 0x11e39f8787c1c001 0x011e39f8787c1c00

def z95 : W := mkw 0x1bca7f3602d96cc4 0x81bca7f3602d96cc 0xbffa7ff607f9fccf 0xfbffa7ff607f9fcc

def z96 : W := mkw 0x402012806f403b06 0x0402012806f403b0 0x400000007fc03f08 0x1400000007fc03f0

def z97 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x1f984e7000000000 0x41f984e700000000

def z98 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x5f804e007fc03f08 0x55f804e007fc03f0

def z99 : W := mkw 0x1000120202d16844 0x81000120202d1684 0x0000000007c1c000 0x00000000007c1c00

def z100 : W := mkw 0x0414000010240000 0x0041400001024000 0x6e1c0000783e000a 0xf6e1c0000783e000

def z101 : W := mkw 0x2020800075b78008 0x02020800075b7800 0x600000007fffc008 0x1600000007fffc00

def z102 : W := mkw 0x108a063400d90c84 0x8108a063400d90c8 0x11984e7001f81c00 0x511984e7001f81c0

def z103 : W := mkw 0x4b60e980ed029312 0x44b60e980ed02931 0x4e65a189f8060330 0x84e65a189f806033

def z104 : W := mkw 0x00209082c602e150 0x400209082c602e15 0x4067b18fc607c331 0x84067b18fc607c33

def z105 : W := mkw 0x80000d2500000000 0x080000d250000000 0x10001f8780000000 0x010001f878000000

def z106 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x0ffb80003ff9c001 0x50ffb80003ff9c00

def z107 : W := mkw 0x108a8436809bc4d0 0xc108a8436809bc4d 0xa01f807f803fc0f2 0x0a01f807f803fc0f

def z108 : W := mkw 0x008a000000910000 0x0008a00000091000 0x219a000007f9c00b 0x7219a000007f9c00

def z109 : W := mkw 0x849f046d00000000 0x0849f046d0000000 0x801f807f80000002 0x0801f807f8000000

def z110 : W := mkw 0x6fffeb007df79a0e 0x06fffeb007df79a0 0x7fffce007fffdc0b 0xf7fffce007fffdc0

def z111 : W := mkw 0x0000001000080480 0x0000000100008048 0x8000407000003cc4 0x08000407000003cc

def z112 : W := mkw 0x108a162602d16844 0x8108a162602d1684 0x11821e0607c1c001 0x011821e0607c1c00

def z113 : W := mkw 0x6f75fb807f66bb0e 0x06f75fb807f66bb0 0x5fe5ff807fc63f0d 0xf5fe5ff807fc63f0

def z114 : W := mkw 0x1000121202d96cc4 0x81000121202d96cc 0x31805e0007f9fccd 0x731805e0007f9fcc

def z115 : W := mkw 0x0634f0dade2ef7f1 0x40634f0dade2ef7f 0xee7ff1fffe3fffff 0xfee7ff1fffe3ffff

def z116 : W := mkw 0x0d74000075240000 0x00d7400007524000 0x6ffc00007ffe000b 0xf6ffc00007ffe000

def z117 : W := mkw 0x4b6069806d001302 0x04b6069806d00130 0x4e60218078000300 0x84e6021807800030

def z118 : W := mkw 0x0940090000000000 0x0094009000000000 0x11e01f8000000001 0x011e01f800000000

def z119 : W := mkw 0x0ddf000000910000 0x00ddf00000091000 0x2fff800007f9c00b 0xf2fff800007f9c00

def z120 : W := mkw 0xadff846d75b78008 0x0adff846d75b7800 0xefff807fffffc00b 0xfefff807fffffc00

def z121 : W := mkw 0x1000163602486cc4 0x81000163602486cc 0x90005e7600003cc4 0x090005e7600003cc

def z122 : W := mkw 0x2fffe04875b78008 0x02fffe04875b7800 0xefffe0787fffc00f 0xfefffe0787fffc00

def z123 : W := mkw 0x4f747bc86f403b06 0x04f747bc86f403b0 0xdffc7ff87fc03f0f 0xfdffc7ff87fc03f0

def z124 : W := mkw 0x002090024602e040 0x0002090024602e04 0xe06790064607e0cf 0xae06790064607e0c

def z125 : W := mkw 0x00209082c602e150 0x400209082c602e15 0x6065a189c607e3f8 0x86065a189c607e3f

def z126 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0xa01c6078003e3ff6 0x0a01c6078003e3ff

def z127 : W := mkw 0x496012806f403b06 0x0496012806f403b0 0x4fe000007fc03f09 0xf4fe000007fc03f0

def z128 : W := mkw 0xc2007fed0a403b06 0x0c2007fed0a403b0 0x90007fff80003f04 0x090007fff80003f0

def z129 : W := mkw 0x0000000000000000 0x0000000000000000 0x4004200840060330 0x8400420084006033

def z130 : W := mkw 0x2dff8002f5b7c058 0x42dff8002f5b7c05 0xefff800fffffc0fb 0xfefff800fffffc0f

def z131 : W := mkw 0x0000100202006040 0x0000010020200604 0xa067b18f8601e0cf 0xaa067b18f8601e0c

def z132 : W := mkw 0x0000001000080480 0x0000000100008048 0x2000000000383cc8 0x12000000000383cc

def z133 : W := mkw 0x249f805810bf84a9 0x0249f805810bf84a 0xa01f8078003fc0f2 0x0a01f8078003fc0f

def z134 : W := mkw 0x82006d6d00000000 0x082006d6d0000000 0x90007fff80000004 0x090007fff8000000

def z135 : W := mkw 0x0614604818241221 0x0061460481824122 0x6e1c2008783e033a 0xf6e1c2008783e033

def z136 : W := mkw 0xcfff6ded6d001302 0x0cfff6ded6d00130 0xdffffffff8000307 0xedffffffff800030

def z137 : W := mkw 0x100012121afd7ee5 0x8100012121afd7ee 0x600000007ffffff8 0x1600000007ffffff

def z138 : W := mkw 0x7fffffb67fffffce 0x87fffffb67fffffc 0xfffffff67fffffcf 0xffffffff67fffffc

def z139 : W := mkw 0x10aa16b646d96dc4 0x810aa16b646d96dc 0xf1fa7ff647f9ffcf 0xff1fa7ff647f9ffc

def z140 : W := mkw 0x6ffffb82fff7fb5e 0x46ffffb82fff7fb5 0xffffff8fffffffff 0xfffffff8ffffffff

def z141 : W := mkw 0x008a042400000000 0x0008a04240000000 0x11821e0600000001 0x011821e060000000

def z142 : W := mkw 0x8fdf6d7d182c16a1 0x08fdf6d7d182c16a 0x1f984e7038381c00 0x51f984e7038381c0

def z143 : W := mkw 0x0000000000000000 0x0000000000000000 0x8007800f80000002 0x08007800f8000000

def z144 : W := mkw 0x149e047e10bd44e1 0x8149e047e10bd44e 0xa01e007e003fc0f2 0x0a01e007e003fc0f

def z145 : W := mkw 0x2f75e0587d2e96a9 0x02f75e0587d2e96a 0xee7de078783e3ffe 0xfee7de078783e3ff

def z146 : W := mkw 0x82006d6d00000000 0x082006d6d0000000 0x9067ffff80000007 0xa9067ffff8000000

def z147 : W := mkw 0x108a163402d92c84 0x8108a163402d92c8 0x11985e7007f83c0d 0x711985e7007f83c0

def z148 : W := mkw 0x020072000a403a04 0x0020072000a403a0 0x5f807e007fc03f0d 0xf5f807e007fc03f0

def z149 : W := mkw 0xcfdf7fed0a403b06 0x0cfdf7fed0a403b0 0x9fffffff80003f07 0xe9fffffff80003f0

def z150 : W := mkw 0x42006b0008401a06 0x042006b0008401a0 0x10004e0000001c00 0x010004e0000001c0

def z151 : W := mkw 0xaffffdeff7b7e158 0x4affffdeff7b7e15 0xffffffffffffe3ff 0xfffffffffffffe3f

def z152 : W := mkw 0x00209082c602e150 0x400209082c602e15 0xc065b18fc00623f4 0x8c065b18fc00623f

def z153 : W := mkw 0x0020800044028000 0x0002080004402800 0x4065800040060000 0x8406580004006000

def z154 : W := mkw 0x108a1436029964c0 0x8108a1436029964c 0xa01a10760639e0cf 0x2a01a10760639e0c

def z155 : W := mkw 0x00000010080816a1 0x000000010080816a 0x0000000000003ff0 0x00000000000003ff

def z156 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xa01a007607f9fcca 0x1a01a007607f9fcc

def z157 : W := mkw 0x2ffff0daffbff7f9 0x42ffff0daffbff7f 0xeffff1ffffffffff 0xfeffff1fffffffff

def z158 : W := mkw 0x0000000000000000 0x0000000000000000 0x0065a18980000000 0x80065a1898000000

def z159 : W := mkw 0x2dff801075bf8488 0x02dff801075bf848 0xefffc0707ffffccf 0xfefffc0707ffffcc

def z160 : W := mkw 0x061472581a6c3ea5 0x0061472581a6c3ea 0xff9c7e787ffe3fff 0xfff9c7e787ffe3ff

def z161 : W := mkw 0x249f800010b78008 0x0249f800010b7800 0x219f800007ffc00b 0x7219f800007ffc00

def z162 : W := mkw 0x00000010182c16a1 0x000000010182c16a 0xe0184070783e3ffe 0x7e0184070783e3ff

def z163 : W := mkw 0x0614604818241221 0x0061460481824122 0xee042008780623fe 0xaee042008780623f

def z164 : W := mkw 0x2dff805875bf84a9 0x02dff805875bf84a 0xefff80787fffc0fb 0xfefff80787fffc0f

def z165 : W := mkw 0x2dff900277b7e048 0x02dff900277b7e04 0xefff90067fffe0cf 0xfefff90067fffe0c

def z166 : W := mkw 0x8fdf6d6d18241221 0x08fdf6d6d1824122 0xdffffffff8060337 0xedffffffff806033

def z167 : W := mkw 0x108a063400d90c84 0x8108a063400d90c8 0xb1984e7001f83cce 0x7b1984e7001f83cc

def z168 : W := mkw 0x0020800044028000 0x0002080004402800 0xe067a0084607e3ff 0xae067a0084607e3f

def z169 : W := mkw 0x108a162602d16844 0x8108a162602d1684 0x11825e0607c1fc0d 0x711825e0607c1fc0

def z170 : W := mkw 0x0f7460587d2c16a1 0x00f7460587d2c16a 0xeffc60787ffe3fff 0xfeffc60787ffe3ff

def z171 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0xee7ff1fff83e3fff 0xfee7ff1fff83e3ff

def z172 : W := mkw 0x6ffffb807ff7bb0e 0x06ffffb807ff7bb0 0x7fffff807fffff0f 0xf7fffff807fffff0

def z173 : W := mkw 0x00aa800044938000 0x000aa80004493800 0x61ff800047ffc00b 0xf61ff800047ffc00

def z174 : W := mkw 0x4b60fb80ef42bb16 0x44b60fb80ef42bb1 0x5fe5ff89ffc63f3d 0xf5fe5ff89ffc63f3

def z175 : W := mkw 0x4b607b82ef407b56 0x44b607b82ef407b5 0xdfe07f8fffc03ffd 0xfdfe07f8fffc03ff

def z176 : W := mkw 0x108a963682dbecd4 0xc108a963682dbecd 0xb19fde7f87fffcff 0x7b19fde7f87fffcf

def z177 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x1ffbdff780000001 0x41ffbdff78000000

def z178 : W := mkw 0x402012907f6c3fa7 0x0402012907f6c3fa 0x600000007ffe3ff8 0x1600000007ffe3ff

def z179 : W := mkw 0x2fdf605839bd16a9 0x02fdf605839bd16a 0xef9c607879fe3ffe 0xfef9c607879fe3ff

def z180 : W := mkw 0x00209282c642e954 0x400209282c642e95 0xf1e7ff8fc7c7ffff 0xff1e7ff8fc7c7fff

def z181 : W := mkw 0xcfdf6f6d29401a06 0x0cfdf6f6d29401a0 0x9fffffffb9c01c07 0xf9fffffffb9c01c0

def z182 : W := mkw 0x0fdf604800000000 0x00fdf60480000000 0x8fffe07800000007 0xe8fffe0780000000

def z183 : W := mkw 0x4b607bd86f483fa7 0x04b607bd86f483fa 0xdfe07ff87fc03ffd 0xfdfe07ff87fc03ff

def z184 : W := mkw 0x8fdf6d7d080816a1 0x08fdf6d7d080816a 0x9fffffff80003ff7 0xe9fffffff80003ff

def z185 : W := mkw 0x349f843610bfc4c8 0x8349f843610bfc4c 0xa01f8076003fc0c2 0x0a01f8076003fc0c

def z186 : W := mkw 0x3dff963677ffeccc 0x83dff963677ffecc 0xffffde767ffffccf 0xfffffde767ffffcc

def z187 : W := mkw 0x40209282ef42fb56 0x440209282ef42fb5 0xe067b18fffc7ffff 0xbe067b18fffc7fff

def z188 : W := mkw 0x3dff96b6f7ffeddc 0xc3dff96b6f7ffedd 0xffffffffffffffff 0xffffffffffffffff

def z189 : W := mkw 0xafdf6d6d31b50008 0x0afdf6d6d31b5000 0x9fffffffb9f80007 0xf9fffffffb9f8000

def z190 : W := mkw 0x849f046d00000000 0x0849f046d0000000 0x807fb1ff80000007 0xa807fb1ff8000000

def z191 : W := mkw 0xafffed6d75b78008 0x0afffed6d75b7800 0x7fffce707fffc00b 0xf7fffce707fffc00

def z192 : W := mkw 0x0200604800000000 0x0020060480000000 0x8000607800000004 0x0800060780000000

def z193 : W := mkw 0x2d758080f5268118 0x42d758080f526811 0x4e65a189f8060330 0x84e65a189f806033

def z194 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0x119a5e7607f9dc01 0x5119a5e7607f9dc0

def z195 : W := mkw 0x10209292c6dbedd4 0xc10209292c6dbedd 0x6000000047fffff8 0x16000000047fffff

def z196 : W := mkw 0x29eb800065938008 0x029eb80006593800 0x01e3800007c1c001 0x001e3800007c1c00

def z197 : W := mkw 0x208b800000938008 0x0208b80000093800 0x000380000001c000 0x0000380000001c00

def z198 : W := mkw 0x0020108246006140 0x0002010824600614 0xe06231864601e3cf 0xae06231864601e3c

def z199 : W := mkw 0x002090804602a100 0x0002090804602a10 0x6067b1804607e30f 0xa6067b1804607e30

def z200 : W := mkw 0x00201082c6006150 0x400201082c600615 0xc060318fc60023fd 0xac060318fc60023f

def z201 : W := mkw 0x0020000044000000 0x0002000004400000 0x4060000046000009 0xa406000004600000

def z202 : W := mkw 0x149e167e12fd6ce5 0x8149e167e12fd6ce 0xb19e5e7e07fffcff 0x7b19e5e7e07fffcf

def z203 : W := mkw 0x4b6069806d001302 0x04b6069806d00130 0x4fe021807fc00309 0xf4fe021807fc0030

def z204 : W := mkw 0x008a042400000000 0x0008a04240000000 0x11984e7000000000 0x411984e700000000

def z205 : W := mkw 0x008a120002d12804 0x0008a120002d1280 0x319a5e0007f9fc0f 0x7319a5e0007f9fc0

def z206 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0xae18407038383cce 0x7ae18407038383cc

def z207 : W := mkw 0x9fdf6d7f009944c0 0x89fdf6d7f009944c 0xbfffffff8039c0c7 0xebfffffff8039c0c

def z208 : W := mkw 0x3dff921277ffeccc 0x83dff921277ffecc 0x6fff80007ffffccb 0xf6fff80007ffffcc

def z209 : W := mkw 0x169e767e1afd7ee5 0x8169e767e1afd7ee 0xbf9a5e763ff9fccf 0x7bf9a5e763ff9fcc

def z210 : W := mkw 0x1200767e0a487ee5 0x81200767e0a487ee 0x90007e7e00003ff4 0x090007e7e00003ff

def z211 : W := mkw 0x8fdf6d6d10240000 0x08fdf6d6d1024000 0xfffffffff83e000f 0xffffffffff83e000

def z212 : W := mkw 0x0fdf6058182c16a1 0x00fdf6058182c16a 0xefffe078783e3fff 0xfefffe078783e3ff

def z213 : W := mkw 0x000080028002c050 0x4000080028002c05 0xa007800f8007c0f2 0x0a007800f8007c0f

def z214 : W := mkw 0x0200600008001200 0x0020060000800120 0x0e00400038001c00 0x50e00400038001c0

def z215 : W := mkw 0x0000121002482c84 0x00000121002482c8 0xb1985e7007f83ccf 0x7b1985e7007f83cc

def z216 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0xffe47f887fc63fff 0xfffe47f887fc63ff

def z217 : W := mkw 0x108a063600d94cc4 0x8108a063600d94cc 0xb19a4e7601f9dcc2 0x5b19a4e7601f9dcc

def z218 : W := mkw 0x5ffe7ffe7ffd7fe7 0x85ffe7ffe7ffd7fe 0xfffe7ffe7fffffff 0xffffe7ffe7ffffff

def z219 : W := mkw 0x0000108282006150 0x4000010828200615 0x8067b18f800023f7 0xa8067b18f800023f

def z220 : W := mkw 0x2ddf000031b50008 0x02ddf000031b5000 0x2f9a00003ff9c00b 0x72f9a00003ff9c00

def z221 : W := mkw 0x0000000000000000 0x0000000000000000 0x0067800000000003 0xa006780000000000

def z222 : W := mkw 0x0020108046002100 0x0002010804600210 0x4000000046002308 0x0400000004600230

def z223 : W := mkw 0x00000010182c16a1 0x000000010182c16a 0xe0042008783e3ffe 0xbe0042008783e3ff

def z224 : W := mkw 0x8f556d6d00000000 0x08f556d6d0000000 0x9e65ffff80000004 0x89e65ffff8000000

def z225 : W := mkw 0x00aa94a6c602e150 0x400aa94a6c602e15 0xf1ffffffc607e3ff 0xef1ffffffc607e3f

def z226 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0xefffa0087fffe3ff 0xfefffa0087fffe3f

def z227 : W := mkw 0x0020008044000100 0x0002000804400010 0x4060218040000300 0x8406021804000030

def z228 : W := mkw 0xa49f846d10b78008 0x0a49f846d10b7800 0xa01f807f803fc002 0x0a01f807f803fc00

def z229 : W := mkw 0x2960800075b78008 0x02960800075b7800 0x6fe000007fffc009 0xf6fe000007fffc00

def z230 : W := mkw 0x4b6069806d001302 0x04b6069806d00130 0x4e60618078003f0c 0xf4e60618078003f0

def z231 : W := mkw 0x0000000010240000 0x0000000001024000 0x60000000783e0008 0x160000000783e000

def z232 : W := mkw 0x0220f082ce02f350 0x40220f082ce02f35 0xee67f18ffe07ffff 0xfee67f18ffe07fff

def z233 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0xefffb18fffffc00f 0xfefffb18fffffc00

def z234 : W := mkw 0x8fdf6d7d00080480 0x08fdf6d7d0008048 0xbfffffff80383ccf 0xfbfffffff80383cc

def z235 : W := mkw 0x59ea1fa667d16946 0x859ea1fa667d1694 0x11e21f8607c1c001 0x011e21f8607c1c00

def z236 : W := mkw 0x0000000000000000 0x0000000000000000 0x8018407000000006 0x6801840700000000

def z237 : W := mkw 0x49601b8067402906 0x049601b806740290 0x11e01f8007c00001 0x011e01f8007c0000

def z238 : W := mkw 0x10000436000844c0 0x810000436000844c 0x80000076000000c0 0x080000076000000c

def z239 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0xdfe7ff8fffc03f0f 0xfdfe7ff8fffc03f0

def z240 : W := mkw 0x8f75e9c9c4028110 0x48f75e9c9c402811 0x4e65a189c0060330 0x84e65a189c006033

def z241 : W := mkw 0x0020108046002100 0x0002010804600210 0x406031804600230d 0xa406031804600230

def z242 : W := mkw 0x02006058182c16a1 0x002006058182c16a 0xe0006078783e3ffc 0x1e0006078783e3ff

def z243 : W := mkw 0x4b60fb806f42bb06 0x04b60fb806f42bb0 0x7fe7ff807fc7ff0f 0xf7fe7ff807fc7ff0

def z244 : W := mkw 0x0960108067002100 0x0096010806700210 0x4fe031807fc0230d 0xf4fe031807fc0230

def z245 : W := mkw 0x4bea7fa46f403b06 0x04bea7fa46f403b0 0xdffa7ff67fc03f0f 0xfdffa7ff67fc03f0

def z246 : W := mkw 0x0000000018241221 0x0000000001824122 0x4000000078060330 0x0400000007806033

def z247 : W := mkw 0x6ffffbd87fffbfaf 0x06ffffbd87fffbfa 0xfffffff87fffffff 0xffffffff87ffffff

def z248 : W := mkw 0x0000001000080480 0x0000000100008048 0xa018407000383cce 0x7a018407000383cc

def z249 : W := mkw 0x8bcb6d6d00000000 0x08bcb6d6d0000000 0x91e3ffff80000005 0x091e3ffff8000000

def z250 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0x4e18607078383f0c 0xf4e18607078383f0

def z251 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0x31984e7007f9fcc8 0x531984e7007f9fcc

def z252 : W := mkw 0x0000000000000000 0x0000000000000000 0x201800000038000a 0x7201800000038000

def z253 : W := mkw 0x29eb800065938008 0x029eb80006593800 0x4fe380007fc1c009 0xf4fe380007fc1c00

def z254 : W := mkw 0x0000000000000000 0x0000000000000000 0x4e00000078000008 0xf4e0000007800000

def z255 : W := mkw 0x9fdf7f7f02d96cc4 0x89fdf7f7f02d96cc 0xbfffffff87f9fccf 0xfbfffffff87f9fcc

def z256 : W := mkw 0x8fffed6d44028000 0x08fffed6d4402800 0xffffffffc607c00f 0xeffffffffc607c00

def z257 : W := mkw 0x063470d85e2c37a1 0x0063470d85e2c37a 0xee7c71f87e3e3fff 0xfee7c71f87e3e3ff

def z258 : W := mkw 0x6dff9b8077f7a90e 0x06dff9b8077f7a90 0x7fff9f807fffc00b 0xf7fff9f807fffc00

def z259 : W := mkw 0x5b607fb66f487fc6 0x85b607fb66f487fc 0xdfe07ff67fc03fcd 0xfdfe07ff67fc03fc

def z260 : W := mkw 0x04140058102c04a1 0x004140058102c04a 0xe01c2078403e23fe 0xae01c2078403e23f

def z261 : W := mkw 0x2d75800075268008 0x02d7580007526800 0x6e7d8000783e000a 0xf6e7d8000783e000

def z262 : W := mkw 0x4b60f982ef02f352 0x44b60f982ef02f35 0xee67b18ffe07e3ff 0xaee67b18ffe07e3f

def z263 : W := mkw 0x008a042400000000 0x0008a04240000000 0x91ffffff80000007 0xe91ffffff8000000

def z264 : W := mkw 0x008a042400000000 0x0008a04240000000 0x801a007600000002 0x0801a00760000000

def z265 : W := mkw 0x9fdf6f7d00d90c84 0x89fdf6f7d00d90c8 0x1f984e7001f81c00 0x51f984e7001f81c0

def z266 : W := mkw 0x49601b8067402906 0x049601b806740290 0x5fe01f807fc00009 0xf5fe01f807fc0000

def z267 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0x4e1c6078783e1f30 0xd4e1c6078783e1f3

def z268 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x4fe780007fc7c001 0x84fe780007fc7c00

def z269 : W := mkw 0x10aa96a6c6d3e954 0xc10aa96a6c6d3e95 0xf1e7bf8fc7c7e3ff 0xaf1e7bf8fc7c7e3f

def z270 : W := mkw 0x20209082f7b7e158 0x420209082f7b7e15 0x600000007fffe3f8 0x1600000007fffe3f

def z271 : W := mkw 0x8f55694900000000 0x08f5569490000000 0x8e7de1f980000006 0xe8e7de1f98000000

def z272 : W := mkw 0x4f747b807f643b06 0x04f747b807f643b0 0x7ffc7f807ffe3f0f 0xf7ffc7f807ffe3f0

def z273 : W := mkw 0x108a062400d10804 0x8108a062400d1080 0x11800e0001c00000 0x011800e0001c0000

def z274 : W := mkw 0xafffe94975b78008 0x0afffe94975b7800 0x6fffa189ffffc00b 0xf6fffa189ffffc00

def z275 : W := mkw 0x4fff7b806f403b06 0x04fff7b806f403b0 0x5fffff807fc03f0f 0xf5fffff807fc03f0

def z276 : W := mkw 0x4b407b802b403b06 0x04b407b802b403b0 0x1f807f8039c03f04 0x51f807f8039c03f0

def z277 : W := mkw 0x00209082c602e150 0x400209082c602e15 0x8067b18f8601c007 0xa8067b18f8601c00

def z278 : W := mkw 0x00208002c402c050 0x400208002c402c05 0xe067800fc607c0fb 0xae067800fc607c0f

def z279 : W := mkw 0x020070da8a0877f1 0x4020070da8a0877f 0x800071ff80003ff4 0x0800071ff80003ff

def z280 : W := mkw 0x04140010182c16a1 0x004140010182c16a 0x6e1c0000783e3ffa 0xf6e1c0000783e3ff

def z281 : W := mkw 0x49601b8067402906 0x049601b806740290 0x11e05f8007c03c0d 0x711e05f8007c03c0

def z282 : W := mkw 0x5bea7fa66fd17b46 0x85bea7fa66fd17b4 0x5fe27f867fc1ff0d 0xf5fe27f867fc1ff0

def z283 : W := mkw 0x00209092de2ef7f1 0x400209092de2ef7f 0xe067b18ffe3fffff 0xbe067b18ffe3ffff

def z284 : W := mkw 0x8fdf694900000000 0x08fdf69490000000 0x0fffa18980000003 0xe0fffa1898000000

def z285 : W := mkw 0x3dff843675bfc4c8 0x83dff843675bfc4c 0xefff80767fffc0cb 0xfefff80767fffc0c

def z286 : W := mkw 0x0020800044028000 0x0002080004402800 0xe067b18fc607c00f 0xae067b18fc607c00

def z287 : W := mkw 0x10aa963646dbecc4 0x810aa963646dbecc 0xf1ffde7647fffccf 0xff1ffde7647fffcc

def z288 : W := mkw 0x1000063400480c84 0x81000063400480c8 0x10004e7000001c00 0x010004e7000001c0

def z289 : W := mkw 0x4b6079806f003302 0x04b6079806f00330 0x4e6031807e00230d 0xa4e6031807e00230

def z290 : W := mkw 0x1000021000d90c84 0x81000021000d90c8 0x0000000001f81c00 0x10000000001f81c0

def z291 : W := mkw 0x29eb800065938008 0x029eb80006593800 0x21fb800007f9c00b 0x721fb800007f9c00

def z292 : W := mkw 0x108a162602d16844 0x8108a162602d1684 0x319a1e0607f9c00b 0x7319a1e0607f9c00

def z293 : W := mkw 0x202080107dbf96a9 0x0202080107dbf96a 0x600000007ffffff8 0x1600000007ffffff

def z294 : W := mkw 0x128a767e0ad97ee5 0x8128a767e0ad97ee 0xb19a7e7e07f9ffff 0x7b19a7e7e07f9fff

def z295 : W := mkw 0xadff8d2575b78008 0x0adff8d2575b7800 0x7fff9f87ffffc00b 0xf7fff9f87ffffc00

def z296 : W := mkw 0x0000000000000000 0x0000000000000000 0x8004200800000006 0xa800420080000000

def z297 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0xce04607878063ff4 0x8ce04607878063ff

def z298 : W := mkw 0x0960000065000000 0x0096000006500000 0x4e60000078000000 0x84e6000007800000

def z299 : W := mkw 0x0ddf000000000000 0x00ddf00000000000 0x0fff800000000003 0xe0fff80000000000

def z300 : W := mkw 0x4020128067402906 0x0402012806740290 0x0000000007c00000 0x00000000007c0000

def z301 : W := mkw 0x5b607b926fd97fc6 0x85b607b926fd97fc 0x7fe07f807ff9ffcd 0xf7fe07f807ff9ffc

def z302 : W := mkw 0x00209082c602e150 0x400209082c602e15 0xe007800fc607e3fa 0x0e007800fc607e3f

def z303 : W := mkw 0x8fdf7d6f02006040 0x08fdf7d6f0200604 0xbfffffff8601e0cf 0xebfffffff8601e0c

def z304 : W := mkw 0x02006058080816a1 0x002006058080816a 0xe004607840063ffe 0xae004607840063ff

def z305 : W := mkw 0x0614604800000000 0x0061460480000000 0x8e1c607800000006 0xe8e1c60780000000

def z306 : W := mkw 0x008a000000000000 0x0008a00000000000 0x019a000000000003 0x6019a00000000000

def z307 : W := mkw 0x42007b800a403b06 0x042007b800a403b0 0x11807f8007c03f0d 0x711807f8007c03f0

def z308 : W := mkw 0x0b407b0002402804 0x00b407b000240280 0x1fe07f8007c03c0d 0xf1fe07f8007c03c0

def z309 : W := mkw 0x108a0436009944c0 0x8108a0436009944c 0xb19a5e760039c0c7 0x6b19a5e760039c0c

def z310 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0xffffffffc00623ff 0xeffffffffc00623f

def z311 : W := mkw 0x9fdf7f7f02486cc4 0x89fdf7f7f02486cc 0x9fffffff80003cc7 0xe9fffffff80003cc

def z312 : W := mkw 0x8f55694900000000 0x08f5569490000000 0x1fe5ff8980000005 0xe1fe5ff898000000

def z313 : W := mkw 0x108a163602486cc4 0x8108a163602486cc 0x919a5e7600003cc7 0x6919a5e7600003cc

def z314 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x21ff800007ffc003 0x021ff800007ffc00

def z315 : W := mkw 0x49609b82e742e956 0x449609b82e742e95 0xf1e7bf8fc7c7e3ff 0xaf1e7bf8fc7c7e3f

def z316 : W := mkw 0x8220fdefc602e150 0x48220fdefc602e15 0xf067ffffc607e3ff 0xaf067ffffc607e3f

def z317 : W := mkw 0x5bca7f362bd97ec6 0x85bca7f362bd97ec 0xbf9a5e763ff9fccf 0x7bf9a5e763ff9fcc

def z318 : W := mkw 0x00209082c602e150 0x400209082c602e15 0x60679187c607c00b 0xa60679187c607c00

def z319 : W := mkw 0x42007b800a403b06 0x042007b800a403b0 0x5e007f8078003f0c 0xf5e007f8078003f0

def z320 : W := mkw 0x6b60fb807ff7bb0e 0x06b60fb807ff7bb0 0x7fe07f807fffff0d 0xf7fe07f807fffff0

def z321 : W := mkw 0x2ddf800010b78008 0x02ddf800010b7800 0x2fff8000003fc003 0xe2fff8000003fc00

def z322 : W := mkw 0x0614604818241221 0x0061460481824122 0x0e00000038000000 0x00e0000003800000

def z323 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x1ff87ff000000005 0xe1ff87ff00000000

def z324 : W := mkw 0xcfff7fed6f403b06 0x0cfff7fed6f403b0 0x5ff87ff07fc03f0d 0xf5ff87ff07fc03f0

def z325 : W := mkw 0x6bebfb806fd3bb0e 0x06bebfb806fd3bb0 0x5fe3ff807fc1ff0d 0xf5fe3ff807fc1ff0

def z326 : W := mkw 0x069e647c182c16a1 0x0069e647c182c16a 0xff9e7e7e783e3fff 0xfff9e7e7e783e3ff

def z327 : W := mkw 0x2ddf800031b78008 0x02ddf800031b7800 0x2f9f800039ffc002 0x52f9f800039ffc00

def z328 : W := mkw 0x8fdf6d7d102c04a1 0x08fdf6d7d102c04a 0xbfffffff803e00f7 0xebfffffff803e00f

def z329 : W := mkw 0x102096b6c64aedd4 0xc102096b6c64aedd 0xf067ffffc607ffff 0xaf067ffffc607fff

def z330 : W := mkw 0x0000000000000000 0x0000000000000000 0x11805e0000000005 0x611805e000000000

def z331 : W := mkw 0x10209292c6dbedd4 0xc10209292c6dbedd 0xe067b18fc7ffffff 0xbe067b18fc7fffff

def z332 : W := mkw 0x2dff908077b7a108 0x02dff908077b7a10 0x6fffb1807fffe30f 0xf6fffb1807fffe30

def z333 : W := mkw 0x0000108282006150 0x4000010828200615 0xe004318fc00623fe 0xae004318fc00623f

def z334 : W := mkw 0x0000000000000000 0x0000000000000000 0x600400004006000a 0xa600400004006000

def z335 : W := mkw 0xcfffffefef42fb56 0x4cfffffefef42fb5 0xffffffffffc7ffff 0xfffffffffffc7fff

def z336 : W := mkw 0x00209082c602e150 0x400209082c602e15 0x4063b187c601e30d 0xa4063b187c601e30

def z337 : W := mkw 0x4b607b907f6c3fa7 0x04b607b907f6c3fa 0x7fe07f807ffe3ffd 0xf7fe07f807ffe3ff

def z338 : W := mkw 0x4000020029401a06 0x04000020029401a0 0x0000000039c01c00 0x10000000039c01c0

def z339 : W := mkw 0x00209092c60ae5d0 0x400209092c60ae5d 0xe07ff1ffc63fffff 0xfe07ff1ffc63ffff

def z340 : W := mkw 0x9fdf6f7d00d90c84 0x89fdf6f7d00d90c8 0x9fffffff81f81c07 0xf9fffffff81f81c0

def z341 : W := mkw 0x0634f0dade2ef7f1 0x40634f0dade2ef7f 0xee1c60787e3ffffe 0xfee1c60787e3ffff

def z342 : W := mkw 0x3ddf063431fd0c8c 0x83ddf063431fd0c8 0x1f984e7039f81c00 0x51f984e7039f81c0

def z343 : W := mkw 0x8f75f9cbc602e150 0x48f75f9cbc602e15 0xee67b18fc607e3ff 0xaee67b18fc607e3f

def z344 : W := mkw 0x0ddf042400000000 0x00ddf04240000000 0x9fffde7600000007 0xe9fffde760000000

def z345 : W := mkw 0x09ea000065910000 0x009ea00006591000 0x6ffa00007ff9c00b 0xf6ffa00007ff9c00

def z346 : W := mkw 0x0940000000000000 0x0094000000000000 0x0fe0000000000001 0xe0fe000000000000

def z347 : W := mkw 0x42207b806f403b06 0x042207b806f403b0 0x50007f807fc03f0c 0x150007f807fc03f0

def z348 : W := mkw 0x0614705a1a2c76e1 0x00614705a1a2c76e 0xee1e707e7e3fffff 0xfee1e707e7e3ffff

def z349 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x1fffce7000000003 0xe1fffce700000000

def z350 : W := mkw 0x0000000000000000 0x0000000000000000 0x400020004000230c 0xa400020004000230

def z351 : W := mkw 0x10aa96b6c6dbedd4 0xc10aa96b6c6dbedd 0xb1fbdff787f9fccf 0x7b1fbdff787f9fcc

def z352 : W := mkw 0x4b607b826f407b46 0x04b607b826f407b4 0xffe27f867fc1ffcf 0xfffe27f867fc1ffc

def z353 : W := mkw 0x0614604800000000 0x0061460480000000 0x0e04200800000000 0x80e0420080000000

def z354 : W := mkw 0x00001012020864c0 0x000001012020864c 0xa01a50760639fccf 0x7a01a50760639fcc

def z355 : W := mkw 0x061470da9a2c77f1 0x4061470da9a2c77f 0xee1c71fff83e3ffe 0xfee1c71fff83e3ff

def z356 : W := mkw 0x3ffff67e7ffffeed 0x83ffff67e7ffffee 0xfffffe7e7fffffff 0xffffffe7e7ffffff

def z357 : W := mkw 0x108a0436009944c0 0x8108a0436009944c 0xa01a40760039fcce 0x7a01a40760039fcc

def z358 : W := mkw 0x00208080c4028110 0x400208080c402811 0x6067a189c607c33b 0xa6067a189c607c33

def z359 : W := mkw 0x8ffffdffde2ef7f1 0x48ffffdffde2ef7f 0xfffffffffe3fffff 0xffffffffffe3ffff

def z360 : W := mkw 0x04140058102c04a1 0x004140058102c04a 0xee1c0078783e00fa 0xfee1c0078783e00f

def z361 : W := mkw 0x0614604810240000 0x0061460481024000 0xee1c6078783e000e 0xfee1c6078783e000

def z362 : W := mkw 0xc9eb1fa567402906 0x0c9eb1fa56740290 0x11e39f8787c00001 0x011e39f8787c0000

def z363 : W := mkw 0x16bef6fedefffff5 0xc16bef6fedefffff 0xffffffffffffffff 0xffffffffffffffff

def z364 : W := mkw 0x0614604800000000 0x0061460480000000 0x0e18407000000000 0x40e1840700000000

def z365 : W := mkw 0x0414000010240000 0x0041400001024000 0xee1c2008783e23fe 0xfee1c2008783e23f

def z366 : W := mkw 0x0414004800000000 0x0041400480000000 0x801c007800000002 0x0801c00780000000

def z367 : W := mkw 0x0434800054268000 0x0043480005426800 0x6e7f80007e3fc00b 0xf6e7f80007e3fc00

def z368 : W := mkw 0x4b606b806d401b06 0x04b606b806d401b0 0x5fe06f8079c01f00 0xd5fe06f8079c01f0

def z369 : W := mkw 0x0614e05a982ed6f1 0x40614e05a982ed6f 0xee1fe07ff83ffffe 0xfee1fe07ff83ffff

def z370 : W := mkw 0x4b607b8067402906 0x04b607b806740290 0x1fe07f8007c00005 0xe1fe07f8007c0000

def z371 : W := mkw 0x8200694900000000 0x0820069490000000 0x0000218980000000 0x0000021898000000

def z372 : W := mkw 0xefffffed7ff7bb0e 0x0efffffed7ff7bb0 0xffffffffffffff0f 0xfffffffffffffff0

def z373 : W := mkw 0x1000163602d96cc4 0x81000163602d96cc 0xb0005e7607f9fccc 0x1b0005e7607f9fcc

def z374 : W := mkw 0x0b40690000000000 0x00b4069000000000 0x1f804e0000000000 0x41f804e000000000

def z375 : W := mkw 0x269fe05818bf96a9 0x0269fe05818bf96a 0xee1fe078783ffffe 0xfee1fe078783ffff

def z376 : W := mkw 0x1ddf163602d96cc4 0x81ddf163602d96cc 0xbfffde7607f9fccf 0xfbfffde7607f9fcc

def z377 : W := mkw 0x0000000000000000 0x0000000000000000 0x0063918780000001 0x0006391878000000

def z378 : W := mkw 0x0000000000000000 0x0000000000000000 0x0180000007c00009 0x70180000007c0000

def z379 : W := mkw 0x0000001000080480 0x0000000100008048 0x0018407000381c00 0x50018407000381c0

def z380 : W := mkw 0x169e647e18bd56e1 0x8169e647e18bd56e 0xee1e607e783ffffe 0xfee1e607e783ffff

def z381 : W := mkw 0x00208080c4028110 0x400208080c402811 0xc067b18fc0060337 0xac067b18fc006033

def z382 : W := mkw 0x5beaffb6efdbffd6 0xc5beaffb6efdbffd 0xffffffffffffffff 0xffffffffffffffff

def z383 : W := mkw 0x402000806d001302 0x0402000806d00130 0x4000000078000300 0x0400000007800030

def z384 : W := mkw 0x00209082c602e150 0x400209082c602e15 0x606780004607e3fb 0xa606780004607e3f

def z385 : W := mkw 0x4b406b0029401a06 0x04b406b0029401a0 0x5f806e0079c03f0c 0xf5f806e0079c03f0

def z386 : W := mkw 0x8ffffdefc602e150 0x48ffffdefc602e15 0x9fffffff8601c007 0xe9fffffff8601c00

def z387 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0x8e18607838383ff4 0x58e18607838383ff

def z388 : W := mkw 0x8fff7ded46002100 0x08fff7ded4600210 0xdfffffffc600230f 0xedfffffffc600230

def z389 : W := mkw 0x0f546958182c16a1 0x00f546958182c16a 0xfffc7ff8783e3fff 0xffffc7ff8783e3ff

def z390 : W := mkw 0x0000000008001200 0x0000000000800120 0x4000000078003f08 0x14000000078003f0

def z391 : W := mkw 0x00209080c602a110 0x400209080c602a11 0x4065b189c606233d 0xa4065b189c606233

def z392 : W := mkw 0x1614725a1afd7ee5 0x81614725a1afd7ee 0xee1c60787ffffffe 0xfee1c60787ffffff

def z393 : W := mkw 0x6dff92807ff7bb0e 0x06dff92807ff7bb0 0x6fff80007fffff0b 0xf6fff80007fffff0

def z394 : W := mkw 0x5bea7fb46fd93f86 0x85bea7fb46fd93f8 0x5ff87ff07ff83f0d 0xf5ff87ff07ff83f0

def z395 : W := mkw 0x4b606b006d401a06 0x04b606b006d401a0 0x5fe04e007fc01c09 0xf5fe04e007fc01c0

def z396 : W := mkw 0x00208080c4028110 0x400208080c402811 0xe065a189c00623fe 0xae065a189c00623f

def z397 : W := mkw 0x02006058080816a1 0x002006058080816a 0xa018607800383ffe 0x7a018607800383ff

def z398 : W := mkw 0x0634e0c8dc269331 0x40634e0c8dc26933 0x4e65a189f8060330 0x84e65a189f806033

def z399 : W := mkw 0x349f963612ffeccc 0x8349f963612ffecc 0xb19fde7607fffccf 0x7b19fde7607fffcc

def z400 : W := mkw 0x928a7f7f02d96cc4 0x8928a7f7f02d96cc 0xb19a7fff87f9fccf 0x7b19a7fff87f9fcc

def z401 : W := mkw 0x0000120202406844 0x0000012020240684 0xb1825e0607c1fccf 0x7b1825e0607c1fcc

def z402 : W := mkw 0x4b406b0029401a06 0x04b406b0029401a0 0x1fe07f8039c01c05 0xf1fe07f8039c01c0

def z403 : W := mkw 0x8fdf6d7d182c16a1 0x08fdf6d7d182c16a 0x9fffffffb8381c07 0xf9fffffffb8381c0

def z404 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0x6e042008783e3ff8 0x96e042008783e3ff

def z405 : W := mkw 0x949f047f009944c0 0x8949f047f009944c 0xa01f807f8039c0c2 0x0a01f807f8039c0c

def z406 : W := mkw 0x0b60f982c602e150 0x40b60f982c602e15 0xffe7ff8fc607e3ff 0xeffe7ff8fc607e3f

def z407 : W := mkw 0x0020108046002100 0x0002010804600210 0x0060118006000001 0x0006011800600000

def z408 : W := mkw 0x000080028002c050 0x4000080028002c05 0x200000000007c0f0 0x0200000000007c0f

def z409 : W := mkw 0x169e667c18fd1ea5 0x8169e667c18fd1ea 0x1f984e7039f81c00 0x51f984e7039f81c0

def z410 : W := mkw 0x008a001000990480 0x0008a00100099048 0xa19a407007f9fccf 0x7a19a407007f9fcc

def z411 : W := mkw 0x828a6d6d00000000 0x0828a6d6d0000000 0x919a7fff80000007 0x6919a7fff8000000

def z412 : W := mkw 0xcb607fed6f403b06 0x0cb607fed6f403b0 0xdfe07fffffc03f0d 0xfdfe07fffffc03f0

def z413 : W := mkw 0x9fdf7f6f02d16844 0x89fdf7f6f02d1684 0x9fffffff87c1c007 0xe9fffffff87c1c00

def z414 : W := mkw 0xafffed7d7dbf96a9 0x0afffed7d7dbf96a 0xffffffffffffffff 0xffffffffffffffff

def z415 : W := mkw 0x008a000000910000 0x0008a00000091000 0x201a00000039c002 0x0201a00000039c00

def z416 : W := mkw 0x2dff842475b78008 0x02dff842475b7800 0xffffde767fffc00f 0xfffffde767fffc00

def z417 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0xae1c4078383e1cf2 0x5ae1c4078383e1cf

def z418 : W := mkw 0x149e163612fd6cc4 0x8149e163612fd6cc 0xff9e5e767ffffccf 0xfff9e5e767ffffcc

def z419 : W := mkw 0x10000012009944c0 0x810000012009944c 0x200000000039c0c0 0x0200000000039c0c

def z420 : W := mkw 0x42007b828a407b56 0x442007b828a407b5 0x90007f8f80003ff4 0x090007f8f80003ff

def z421 : W := mkw 0x1000121202486cc4 0x81000121202486cc 0x0000000000003cc0 0x00000000000003cc

def z422 : W := mkw 0x04140058102c04a1 0x004140058102c04a 0x0018007000380000 0x0001800700038000

def z423 : W := mkw 0x100016b682486dd4 0xc100016b682486dd 0x90007fff80003ff4 0x090007fff80003ff

def z424 : W := mkw 0x0200601008081680 0x0020060100808168 0xee18607078383fce 0xfee18607078383fc

def z425 : W := mkw 0x82006d6d00000000 0x082006d6d0000000 0x10004e7000000000 0x010004e700000000

def z426 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x8e7fa1ff80000002 0x88e7fa1ff8000000

def z427 : W := mkw 0x8fff6d6d65000000 0x08fff6d6d6500000 0xdfffffffffc0000f 0xfdfffffffffc0000

def z428 : W := mkw 0x42207b804e403b06 0x042207b804e403b0 0x50607f8046003f0d 0xa50607f8046003f0

def z429 : W := mkw 0x8bcb6d2500000000 0x08bcb6d250000000 0x1fe3ff8780000005 0xe1fe3ff878000000

def z430 : W := mkw 0x0000020000400804 0x0000002000040080 0x11804e0001c01c00 0x511804e0001c01c0

def z431 : W := mkw 0x0ddf000000000000 0x00ddf00000000000 0x8fffb18f80000007 0xe8fffb18f8000000

def z432 : W := mkw 0x49609b82e742e956 0x449609b82e742e95 0x11e39f8787c1c001 0x011e39f8787c1c00

def z433 : W := mkw 0x00000058000804a1 0x000000058000804a 0x80000078000000f0 0x080000078000000f

def z434 : W := mkw 0x000080028002c050 0x4000080028002c05 0xe007a00fc007e3fe 0xae007a00fc007e3f

def z435 : W := mkw 0x2434800075b78008 0x02434800075b7800 0x6e1c00007fffc00a 0xf6e1c00007fffc00

def z436 : W := mkw 0x0614604818241221 0x0061460481824122 0x4e04600878063f3c 0xf4e04600878063f3

def z437 : W := mkw 0x0020108046002100 0x0002010804600210 0xc067b18fc600230f 0xac067b18fc600230

def z438 : W := mkw 0x108a043400990480 0x8108a04340099048 0x0018007000380000 0x0001800700038000

def z439 : W := mkw 0xafffed6d65938008 0x0afffed6d6593800 0x9fffffff87c1c007 0xe9fffffff87c1c00

def z440 : W := mkw 0x40209282ef42fb56 0x440209282ef42fb5 0x600000007fc7fff8 0x1600000007fc7fff

def z441 : W := mkw 0x89eb9da7c602e150 0x489eb9da7c602e15 0x11e39f878601c001 0x011e39f878601c00

def z442 : W := mkw 0x0000100202006040 0x0000010020200604 0x000210060601c001 0x0000210060601c00

def z443 : W := mkw 0x2ddf000031b50008 0x02ddf000031b5000 0x6f9c000079fe000a 0xf6f9c000079fe000

def z444 : W := mkw 0x2dff9082f7b7e158 0x42dff9082f7b7e15 0x6fff80007fffe3fb 0xf6fff80007fffe3f

def z445 : W := mkw 0x4f7469d87d2c17a3 0x04f7469d87d2c17a 0xee7c61f8783e3ffe 0xfee7c61f8783e3ff

def z446 : W := mkw 0x0000001000080480 0x0000000100008048 0xa0180070003800c2 0x0a0180070003800c

def z447 : W := mkw 0x4b6069806d001302 0x04b6069806d00130 0x5fe07f8078000305 0xe5fe07f807800030

def z448 : W := mkw 0x8f55694900000000 0x08f5569490000000 0x0e00000000000000 0x00e0000000000000

def z449 : W := mkw 0x8f55694900000000 0x08f5569490000000 0x8e67b18f80000007 0xa8e67b18f8000000

def z450 : W := mkw 0x008a142602006040 0x0008a14260200604 0xb19a5e760601e0cf 0x6b19a5e760601e0c

def z451 : W := mkw 0x2634e0587dbf96a9 0x02634e0587dbf96a 0xee1c60787ffffffe 0xfee1c60787ffffff

def z452 : W := mkw 0x06146058080816a1 0x006146058080816a 0x8e1c607800003ff6 0xe8e1c607800003ff

def z453 : W := mkw 0x4f74fbdaff6efff7 0x44f74fbdaff6efff 0xffffffffffffffff 0xffffffffffffffff

def z454 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000318f80000004 0x08000318f8000000

def z455 : W := mkw 0x4b607b906f483f86 0x04b607b906f483f8 0xfff87ff07ff83fcf 0xffff87ff07ff83fc

def z456 : W := mkw 0x0414000010240000 0x0041400001024000 0x201c0000003e0002 0x0201c0000003e000

def z457 : W := mkw 0x2fffe0007db79208 0x02fffe0007db7920 0x6fffe0007fffff0f 0xf6fffe0007fffff0

def z458 : W := mkw 0x8ddf0d6d00000000 0x08ddf0d6d0000000 0x91ff9fff80000003 0x091ff9fff8000000

def z459 : W := mkw 0x108a0436009944c0 0x8108a0436009944c 0xa19a007607f9c0cb 0x7a19a007607f9c0c

def z460 : W := mkw 0x2dff9082f7b7e158 0x42dff9082f7b7e15 0x6fff9187ffffc00b 0xf6fff9187ffffc00

def z461 : W := mkw 0x3dff863475ff8c8c 0x83dff863475ff8c8 0x7fffce707fffdc0b 0xf7fffce707fffdc0

def z462 : W := mkw 0x4f546b58396c1ea7 0x04f546b58396c1ea 0xff9c6e7879fe3ffe 0xfff9c6e7879fe3ff

def z463 : W := mkw 0x49400b0021400806 0x049400b002140080 0x11800e0001c00000 0x011800e0001c0000

def z464 : W := mkw 0x0000100202006040 0x0000010020200604 0x200000000601e0c8 0x0200000000601e0c

def z465 : W := mkw 0x2fffe0487db79229 0x02fffe0487db7922 0x6fffa0087fffc33b 0xf6fffa0087fffc33

def z466 : W := mkw 0x42007bd80a483fa7 0x042007bd80a483fa 0x90007ff800003ff4 0x090007ff800003ff

def z467 : W := mkw 0x4f747bd87f6c3fa7 0x04f747bd87f6c3fa 0x5ff87ff07ff83f0d 0xf5ff87ff07ff83f0

def z468 : W := mkw 0x10aa96b6c6dbedd4 0xc10aa96b6c6dbedd 0xf19a5e7647ffffff 0x7f19a5e7647fffff

def z469 : W := mkw 0x0634e0585c2e96a1 0x00634e0585c2e96a 0xee7fe0787e3fffff 0xfee7fe0787e3ffff

def z470 : W := mkw 0x00209082c602e150 0x400209082c602e15 0xe00420084607e3fe 0xae00420084607e3f

def z471 : W := mkw 0x2ddf000031b50008 0x02ddf000031b5000 0x0fff800039f80003 0xf0fff800039f8000

def z472 : W := mkw 0x108a042600914040 0x8108a04260091404 0x000200060001c000 0x0000200060001c00

def z473 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x4e6021807fc03f08 0x94e6021807fc03f0

def z474 : W := mkw 0x602092807ff7bb0e 0x0602092807ff7bb0 0x600000007fffff08 0x1600000007fffff0

def z475 : W := mkw 0x8b406d6d00000000 0x08b406d6d0000000 0x9fe07fff80000005 0xe9fe07fff8000000

def z476 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x9f9c6e7800000006 0xe9f9c6e780000000

def z477 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x1ffdeff980000000 0xc1ffdeff98000000

def z478 : W := mkw 0x0634e0d8dc2e97b1 0x40634e0d8dc2e97b 0xee7de1f9f83e3ffe 0xfee7de1f9f83e3ff

def z479 : W := mkw 0x2dff800075268008 0x02dff80007526800 0x4fff800078060003 0xe4fff80007806000

def z480 : W := mkw 0x0000100202006040 0x0000010020200604 0x80001006000020c4 0x080001006000020c

def z481 : W := mkw 0x4bea7b806fd13b06 0x04bea7b806fd13b0 0x7ffa7f807ff9ff0f 0xf7ffa7f807ff9ff0

def z482 : W := mkw 0x049f000000000000 0x0049f00000000000 0x001f800000000002 0x0001f80000000000

def z483 : W := mkw 0x169e667c18fd1ea5 0x8169e667c18fd1ea 0xff9c6e7879fe3ffe 0xfff9c6e7879fe3ff

def z484 : W := mkw 0x9fffffffc6dbedd4 0xc9fffffffc6dbedd 0xffffffffc7ffffff 0xfffffffffc7fffff

def z485 : W := mkw 0x069e646c00000000 0x0069e646c0000000 0x9f9e7e7e00000007 0xe9f9e7e7e0000000

def z486 : W := mkw 0x00209082c602e150 0x400209082c602e15 0xa067918f8607c0f3 0x0a067918f8607c0f

def z487 : W := mkw 0x2dff80107dbf96a9 0x02dff80107dbf96a 0x6fff80007ffffffb 0xf6fff80007ffffff

def z488 : W := mkw 0x04140058102c04a1 0x004140058102c04a 0xa01c4078003e3cfe 0x7a01c4078003e3cf

def z489 : W := mkw 0x46147bd81a6c3fa7 0x046147bd81a6c3fa 0xfe1c7ff8783e3ffe 0xffe1c7ff8783e3ff

def z490 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x9f9a5e7600000007 0x69f9a5e760000000

def z491 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x5fe03f807fc00301 0x85fe03f807fc0030

def z492 : W := mkw 0x2fdf605839bd16a9 0x02fdf605839bd16a 0x0f98407039f81c00 0x50f98407039f81c0

def z493 : W := mkw 0x5bca6f3429d91e86 0x85bca6f3429d91e8 0x1f984e7039f81c00 0x51f984e7039f81c0

def z494 : W := mkw 0x0000120002402804 0x0000012000240280 0x11801e0007c00001 0x011801e0007c0000

def z495 : W := mkw 0x0bca6d2400000000 0x00bca6d240000000 0x9ffa7ff600000007 0xe9ffa7ff60000000

def z496 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xf19e7e7e47ffffff 0xff19e7e7e47fffff

def z497 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0040008000600f2 0x0a0040008000600f

def z498 : W := mkw 0x00209082c602e150 0x400209082c602e15 0x8063b18f8601e3f5 0x08063b18f8601e3f

def z499 : W := mkw 0x0020800044028000 0x0002080004402800 0x006380000601c001 0x0006380000601c00

def z500 : W := mkw 0x108a063400d90c84 0x8108a063400d90c8 0x319a4e7007f9dc0b 0x7319a4e7007f9dc0

def z501 : W := mkw 0x2415800010268008 0x0241580001026800 0x0005800000060000 0x0000580000006000

def z502 : W := mkw 0x128a76360ad97ec4 0x8128a76360ad97ec 0xff9a7e767ff9ffcf 0xfff9a7e767ff9ffc

def z503 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0x91825e7607c1fcc5 0x091825e7607c1fcc

def z504 : W := mkw 0x0b6060006d001200 0x00b6060006d00120 0x4fe060007fc03f0d 0xf4fe060007fc03f0

def z505 : W := mkw 0x04140010102c0480 0x004140010102c048 0xee1c4070783e3cce 0xfee1c4070783e3cc

def z506 : W := mkw 0x008a000000910000 0x0008a00000091000 0x0198000001f80000 0x50198000001f8000

def z507 : W := mkw 0x8fdf6d6d00910000 0x08fdf6d6d0091000 0xbfffffff87f9c00f 0xfbfffffff87f9c00

def z508 : W := mkw 0x0000000000000000 0x0000000000000000 0x80002008000023f4 0x080002008000023f

def z509 : W := mkw 0x8941090100000000 0x0894109010000000 0x0061818180000000 0x0006181818000000

def z510 : W := mkw 0x2dff920077f7a80c 0x02dff920077f7a80 0x7fffde007ffffc0f 0xf7fffde007ffffc0

def z511 : W := mkw 0x869f646d00000000 0x0869f646d0000000 0x8e1fe07f80000006 0xe8e1fe07f8000000

def z512 : W := mkw 0x89cb0d2500000000 0x089cb0d250000000 0x91e7bf8f80000007 0xa91e7bf8f8000000

def z513 : W := mkw 0xbfffff7f77ffeccc 0x8bfffff7f77ffecc 0xfffffffffffffccf 0xffffffffffffffcc

def z514 : W := mkw 0x24bf800054b78008 0x024bf800054b7800 0x607f8000463fc00b 0xa607f8000463fc00

def z515 : W := mkw 0x0200600008001200 0x0020060000800120 0x4e00200078000300 0x84e0020007800030

def z516 : W := mkw 0x20aa800075b78008 0x020aa800075b7800 0x619a00007fffc00b 0x7619a00007fffc00

def z517 : W := mkw 0x8fdfed6f8002c050 0x48fdfed6f8002c05 0xbfffffff8007c0f7 0xebfffffff8007c0f

def z518 : W := mkw 0x2020800075b78008 0x02020800075b7800 0x606780007fffc00b 0xb606780007fffc00

def z519 : W := mkw 0x00209082c602e150 0x400209082c602e15 0x60639187c607e3f9 0x060639187c607e3f

def z520 : W := mkw 0x00aa9082c693e150 0x400aa9082c693e15 0xe1ffb18fc7ffe3ff 0xfe1ffb18fc7ffe3f

def z521 : W := mkw 0x4f7469c87d241323 0x04f7469c87d24132 0x4e64218878060330 0x84e6421887806033

def z522 : W := mkw 0x069e605818bd16a1 0x0069e605818bd16a 0xef9e60787fffffff 0xfef9e60787ffffff

def z523 : W := mkw 0x24bf800075b78008 0x024bf800075b7800 0x601f80007fffc00a 0x1601f80007fffc00

def z524 : W := mkw 0x249f800010b78008 0x0249f800010b7800 0x6e1f8000783fc00a 0xf6e1f8000783fc00

def z525 : W := mkw 0xdfff7fff6fd97fc6 0x8dfff7fff6fd97fc 0xfffffffffff9ffcf 0xffffffffffff9ffc

def z526 : W := mkw 0x4220fb82ce42fb56 0x44220fb82ce42fb5 0xf067ff8fc607ffff 0xaf067ff8fc607fff

def z527 : W := mkw 0x0000108282006150 0x4000010828200615 0x00000000000023f0 0x000000000000023f

def z528 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xb01a5e760039fcc6 0x0b01a5e760039fcc

def z529 : W := mkw 0x0fdf690000000000 0x00fdf69000000000 0x1fffff8000000007 0xe1fffff800000000

def z530 : W := mkw 0x00209092de2ef7f1 0x400209092de2ef7f 0x600000007e3ffff8 0x1600000007e3ffff

def z531 : W := mkw 0x0b60798046002100 0x00b6079804600210 0x5fe07f804600230d 0xe5fe07f804600230

def z532 : W := mkw 0x84bf94efc602e150 0x484bf94efc602e15 0xe07fb1ffc607e3ff 0xae07fb1ffc607e3f

def z533 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x1fe05f803fc01c01 0x51fe05f803fc01c0

def z534 : W := mkw 0x0000000000000000 0x0000000000000000 0x60000000400623f8 0x060000000400623f

def z535 : W := mkw 0x0000108002002100 0x0000010800200210 0x0000318000002304 0x0000031800000230

def z536 : W := mkw 0x0f54694800000000 0x00f5469480000000 0x9ffc7ff800000007 0xe9ffc7ff80000000

def z537 : W := mkw 0x19ea163667d96cc4 0x819ea163667d96cc 0xfffa5e767ff9fccf 0xffffa5e767ff9fcc

def z538 : W := mkw 0x4b40690029001202 0x04b4069002900120 0x0e00000038000000 0x00e0000003800000

def z539 : W := mkw 0x00000010182c16a1 0x000000010182c16a 0x0000000038381c00 0x10000000038381c0

def z540 : W := mkw 0x4f546b58396c1ea7 0x04f546b58396c1ea 0x1f984e7039f81c00 0x51f984e7039f81c0

def z541 : W := mkw 0x008a043400080480 0x0008a04340008048 0xb19a5e7600383ccf 0x7b19a5e7600383cc

def z542 : W := mkw 0x2d75800075268008 0x02d7580007526800 0x4fe580007fc60009 0xf4fe580007fc6000

def z543 : W := mkw 0x02006058080816a1 0x002006058080816a 0xce00607878003ffc 0xfce00607878003ff

def z544 : W := mkw 0x6fff7b807ff53b0e 0x06fff7b807ff53b0 0x5ff87f807ff83f0d 0xf5ff87f807ff83f0

def z545 : W := mkw 0x0020000065000000 0x0002000006500000 0x400000007fc00008 0x1400000007fc0000

def z546 : W := mkw 0x008a100202916040 0x0008a10020291604 0xa19a100607f9e0cf 0x7a19a100607f9e0c

def z547 : W := mkw 0x9fdf7f7f1afd7ee5 0x89fdf7f7f1afd7ee 0xffffffffffffffff 0xffffffffffffffff

def z548 : W := mkw 0x869f6d6d00000000 0x0869f6d6d0000000 0x901fffff80000006 0x0901fffff8000000

def z549 : W := mkw 0x0dff000065000000 0x00dff00006500000 0x4fff80007fc0000b 0xf4fff80007fc0000

def z550 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0x91985e7601f83cc4 0x591985e7601f83cc

def z551 : W := mkw 0x0200600008001200 0x0020060000800120 0xee04600878063ffe 0xfee04600878063ff

def z552 : W := mkw 0x422072806f403b06 0x0422072806f403b0 0x4e0060007fc03f0c 0xf4e0060007fc03f0

def z553 : W := mkw 0x2fffe90075b78008 0x02fffe90075b7800 0x7fffff807fffc00f 0xf7fffff807fffc00

def z554 : W := mkw 0x86146d6d00000000 0x086146d6d0000000 0x9e1c7fff80000006 0xe9e1c7fff8000000

def z555 : W := mkw 0x249f800290b7c058 0x4249f800290b7c05 0xa01f800f803fc0f2 0x0a01f800f803fc0f

def z556 : W := mkw 0x2dff800065938008 0x02dff80006593800 0x0fff800007c1c003 0xe0fff800007c1c00

def z557 : W := mkw 0x0200600000000000 0x0020060000000000 0x0e00600000000004 0xe0e0060000000000

def z558 : W := mkw 0x949f167f02d96cc4 0x8949f167f02d96cc 0xb19fde7f87f9fccf 0x7b19fde7f87f9fcc

def z559 : W := mkw 0x0414805a902ec4f1 0x40414805a902ec4f 0xa01f807f803fc0f2 0x0a01f807f803fc0f

def z560 : W := mkw 0x49601b806f403b06 0x049601b806f403b0 0x51e01f807fc03f09 0x151e01f807fc03f0

def z561 : W := mkw 0x0b40690000000000 0x00b4069000000000 0x0e60218000000000 0x80e6021800000000

def z562 : W := mkw 0x04140058182c16a1 0x004140058182c16a 0xe01c0078783e3ffa 0x1e01c0078783e3ff

def z563 : W := mkw 0x2fffe0587dbf96a9 0x02fffe0587dbf96a 0x6fffc0707fffdc0b 0xf6fffc0707fffdc0

def z564 : W := mkw 0x89eb9da7c602e150 0x489eb9da7c602e15 0xf1e7bf8fc607e3ff 0xaf1e7bf8fc607e3f

def z565 : W := mkw 0x108a162602d16844 0x8108a162602d1684 0xb1821e0607c1e0cf 0x2b1821e0607c1e0c

def z566 : W := mkw 0x000090028202e050 0x4000090028202e05 0xa007900f8607e0ff 0x2a007900f8607e0f

def z567 : W := mkw 0x8fffededc4028110 0x48fffededc402811 0xdfffffffc0060337 0xedfffffffc006033

def z568 : W := mkw 0x400012800a403b06 0x0400012800a403b0 0x0000000000003f00 0x00000000000003f0

def z569 : W := mkw 0x00209082c602e150 0x400209082c602e15 0xe000318fc607e3fc 0x0e000318fc607e3f

def z570 : W := mkw 0x000080028002c050 0x4000080028002c05 0xa067b18f8007c0f7 0xaa067b18f8007c0f

def z571 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x9f987fff80000004 0x49f987fff8000000

def z572 : W := mkw 0x2d75800075268008 0x02d7580007526800 0x6e6780007e07c00b 0xa6e6780007e07c00

def z573 : W := mkw 0x0414000010240000 0x0041400001024000 0x4e04000078060000 0x84e0400007806000

def z574 : W := mkw 0x39eb962667d3e84c 0x839eb962667d3e84 0x11e39e0607c1c001 0x011e39e0607c1c00

def z575 : W := mkw 0x0200690000000000 0x0020069000000000 0x10007f8000000004 0x010007f800000000

def z576 : W := mkw 0x3ddf163633fd6ccc 0x83ddf163633fd6cc 0xbf9a5e763ff9fccf 0x7bf9a5e763ff9fcc

def z577 : W := mkw 0x1000163602486cc4 0x81000163602486cc 0xb0025e760601fccf 0x2b0025e760601fcc

def z578 : W := mkw 0x1000121202d96cc4 0x81000121202d96cc 0xa002100607f9fccf 0x3a002100607f9fcc

def z579 : W := mkw 0x043490dad62ee5f1 0x4043490dad62ee5f 0xe07fb1ffc63fe3ff 0xae07fb1ffc63fe3f

def z580 : W := mkw 0x8fdf7f6d02402804 0x08fdf7f6d0240280 0x9fffffff87c03c0f 0xf9fffffff87c03c0

def z581 : W := mkw 0xcbeb7fa56f403b06 0x0cbeb7fa56f403b0 0x5fe3ff87ffc03f0d 0xf5fe3ff87ffc03f0

def z582 : W := mkw 0x108a121202d96cc4 0x8108a121202d96cc 0x219a000007f9fccb 0x7219a000007f9fcc

def z583 : W := mkw 0x0960000065000000 0x0096000006500000 0x01e0000007c00001 0x001e0000007c0000

def z584 : W := mkw 0x0000120002402804 0x0000012000240280 0x0000000007c03c08 0x10000000007c03c0

def z585 : W := mkw 0x000090828202e150 0x4000090828202e15 0xa007b18f8007e3f6 0x0a007b18f8007e3f

def z586 : W := mkw 0x0000000200004040 0x0000000020000404 0xa00200060001c0c2 0x0a00200060001c0c

def z587 : W := mkw 0x0000800080028010 0x4000080008002801 0x0005800980060030 0x0000580098006003

def z588 : W := mkw 0x0000800000028000 0x0000080000002800 0x200780000007c002 0x0200780000007c00

def z589 : W := mkw 0x0000000280004050 0x4000000028000405 0x8000000f800000f0 0x08000000f800000f

def z590 : W := mkw 0x0d55000000000000 0x00d5500000000000 0x0e65800000000000 0x80e6580000000000

def z591 : W := mkw 0x24bf9082d6b7e158 0x424bf9082d6b7e15 0xe07fb18fc63fe3ff 0xae07fb18fc63fe3f

def z592 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x4ffd800079fe0000 0xd4ffd800079fe000

def z593 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xb19a1e7607f9c0c3 0x0b19a1e7607f9c0c

def z594 : W := mkw 0x20209082f7b7e158 0x420209082f7b7e15 0xe067b18fffffe3ff 0xbe067b18fffffe3f

def z595 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x9f9fce7f80000002 0x49f9fce7f8000000

def z596 : W := mkw 0x502012926fd97fc6 0x8502012926fd97fc 0x600000007ff9ffc8 0x1600000007ff9ffc

def z597 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x1fe7bf8f80000001 0x81fe7bf8f8000000

def z598 : W := mkw 0x2961800065028008 0x0296180006502800 0x0061800000000000 0x0006180000000000

def z599 : W := mkw 0x6f75e9807d26930a 0x06f75e9807d26930 0x4e65a18078060300 0x84e65a1807806030

def z600 : W := mkw 0x849f846f8002c050 0x4849f846f8002c05 0xa01f807f8007c0f2 0x0a01f807f8007c0f

def z601 : W := mkw 0x8415004900000000 0x0841500490000000 0x0005800980000000 0x0000580098000000

def z602 : W := mkw 0x30aa963677ffeccc 0x830aa963677ffecc 0xf19a5e767ffffccf 0x7f19a5e767ffffcc

def z603 : W := mkw 0xcfdf6f6d29401a06 0x0cfdf6f6d29401a0 0x1f984e7039c01c00 0x51f984e7039c01c0

def z604 : W := mkw 0x02006058080816a1 0x002006058080816a 0x0000407000001c00 0x00000407000001c0

def z605 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000400000003c0c 0x70000400000003c0

def z606 : W := mkw 0x3dff962677f7e84c 0x83dff962677f7e84 0x7fff9e067fffc00b 0xf7fff9e067fffc00

def z607 : W := mkw 0x02006010182c16a1 0x002006010182c16a 0x6e006000783e3ffc 0xf6e006000783e3ff

def z608 : W := mkw 0x0200600008001200 0x0020060000800120 0x0000600000003f04 0x00000600000003f0

def z609 : W := mkw 0xafffed6d75268008 0x0afffed6d7526800 0xdffffffff8060007 0xedffffffff806000

def z610 : W := mkw 0x8fdf7def82006150 0x48fdf7def8200615 0x9fffffff800023f7 0xe9fffffff800023f

def z611 : W := mkw 0x849f046d00000000 0x0849f046d0000000 0x0018007000000000 0x0001800700000000

def z612 : W := mkw 0xafdf6d6d31b50008 0x0afdf6d6d31b5000 0x1f984e7039f80000 0x51f984e7039f8000

def z613 : W := mkw 0xcfff7ffd7f6c3fa7 0x0cfff7ffd7f6c3fa 0xfffffffffffe3fff 0xffffffffffffe3ff

def z614 : W := mkw 0x0000108282006150 0x4000010828200615 0x0000118780000000 0x0000011878000000

def z615 : W := mkw 0x0dff800044028000 0x00dff80004402800 0x6fff80004607c00b 0xe6fff80004607c00

def z616 : W := mkw 0x1000163602486cc4 0x81000163602486cc 0x91805e7607c03ccd 0x791805e7607c03cc

def z617 : W := mkw 0x249f000010b50008 0x0249f000010b5000 0x0018000000380000 0x0001800000038000

def z618 : W := mkw 0x4960098065000102 0x0496009806500010 0x0060018000000000 0x0006001800000000

def z619 : W := mkw 0x0220f0dace0af7f1 0x40220f0dace0af7f 0xe067f1ffc607ffff 0xae067f1ffc607fff

def z620 : W := mkw 0x6fdf6b0039f51a0e 0x06fdf6b0039f51a0 0x1f984e0039f81c00 0x51f984e0039f81c0

def z621 : W := mkw 0x09cb000000000000 0x009cb00000000000 0x01e3800000000001 0x001e380000000000

def z622 : W := mkw 0x59ea1fb667d96dc6 0x859ea1fb667d96dc 0xb1fa5ff607f9fccf 0x7b1fa5ff607f9fcc

def z623 : W := mkw 0x4b407b800a403b06 0x04b407b800a403b0 0x1fe07f8000003f05 0xe1fe07f8000003f0

def z624 : W := mkw 0x29eb800065938008 0x029eb80006593800 0x61e7800047c7c00b 0xa61e7800047c7c00

def z625 : W := mkw 0x00209082c602e150 0x400209082c602e15 0xe00210064607e3ff 0x2e00210064607e3f

def z626 : W := mkw 0x2000000031b50008 0x02000000031b5000 0x0000000039f80000 0x10000000039f8000

def z627 : W := mkw 0x169e767e02d96cc4 0x8169e767e02d96cc 0xbf9e7e7e07f9fccf 0xfbf9e7e7e07f9fcc

def z628 : W := mkw 0x0000108282006150 0x4000010828200615 0xa002318f8601e3ff 0x2a002318f8601e3f

def z629 : W := mkw 0x0000000000000000 0x0000000000000000 0x200200000601c00b 0x2200200000601c00

def z630 : W := mkw 0x50aa16b66fd97fc6 0x850aa16b66fd97fc 0xf19a5e767ff9ffcf 0x7f19a5e767ff9ffc

def z631 : W := mkw 0x8fdf6d7d182c16a1 0x08fdf6d7d182c16a 0xff9c6e78783e3ffe 0xfff9c6e78783e3ff

def z632 : W := mkw 0x4200698008001302 0x0420069800800130 0x0000218000000300 0x0000021800000030

def z633 : W := mkw 0xcfff7fed67402906 0x0cfff7fed6740290 0x9fffffff87c00007 0xe9fffffff87c0000

def z634 : W := mkw 0x849f046d00000000 0x0849f046d0000000 0x919fde7f80000007 0x6919fde7f8000000

def z635 : W := mkw 0x0960800065028000 0x0096080006502800 0x6fe780007fc7c00b 0xf6fe780007fc7c00

def z636 : W := mkw 0x0200604808001221 0x0020060480800122 0x0000200800000330 0x0000020080000033

def z637 : W := mkw 0x2020800075268008 0x0202080007526800 0x4000000078060000 0x0400000007806000

def z638 : W := mkw 0x10aa94b6c69be5d0 0xc10aa94b6c69be5d 0xe07fb1ffc63fe3ff 0xae07fb1ffc63fe3f

def z639 : W := mkw 0x8f556959182c16a1 0x08f556959182c16a 0xee7de1f9f83e3ffe 0xfee7de1f9f83e3ff

def z640 : W := mkw 0x00209082c602e150 0x400209082c602e15 0x606031804607e3fd 0xa606031804607e3f

def z641 : W := mkw 0x39eb963667dbeccc 0x839eb963667dbecc 0xb1fbde7607f9fccf 0x7b1fbde7607f9fcc

def z642 : W := mkw 0x29eb800075b78008 0x029eb800075b7800 0x61e380007fffc009 0x161e380007fffc00

def z643 : W := mkw 0x1000163602486cc4 0x81000163602486cc 0xb0185e7600383cce 0x7b0185e7600383cc

def z644 : W := mkw 0x849f047d102c04a1 0x0849f047d102c04a 0xa01f807f803e00f2 0x0a01f807f803e00f

def z645 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x6e7f8000783fc002 0x86e7f8000783fc00

def z646 : W := mkw 0x008a042400910000 0x0008a04240091000 0xb19a5e7607f9c00f 0x7b19a5e7607f9c00

def z647 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x11e07f8007c03f05 0x011e07f8007c03f0

def z648 : W := mkw 0x0ddf000010240000 0x00ddf00001024000 0x6fff8000783e000b 0xf6fff8000783e000

def z649 : W := mkw 0x00208080c4028110 0x400208080c402811 0x4000000040060330 0x0400000004006033

def z650 : W := mkw 0x00209082c602e150 0x400209082c602e15 0xa06391878601e0cf 0x2a06391878601e0c

def z651 : W := mkw 0x0000000000000000 0x0000000000000000 0x8002100600000007 0x2800210060000000

def z652 : W := mkw 0x0000008080000110 0x4000000808000011 0x0000218980000330 0x0000021898000033

def z653 : W := mkw 0x29eb9082e793e158 0x429eb9082e793e15 0x01e3918787c1c001 0x001e3918787c1c00

def z654 : W := mkw 0x008a000000910000 0x0008a00000091000 0x0182000007c1c001 0x00182000007c1c00

def z655 : W := mkw 0x528a7fb60ad97fc6 0x8528a7fb60ad97fc 0xb19a7ff607f9ffcf 0x7b19a7ff607f9ffc

def z656 : W := mkw 0x0414000010240000 0x0041400001024000 0x0e18000038380000 0x50e1800003838000

def z657 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x5e607f8078003f04 0x85e607f8078003f0

def z658 : W := mkw 0xaf75e94975268008 0x0af75e9497526800 0x4e65a189f8060000 0x84e65a189f806000

def z659 : W := mkw 0x89cb0d2500000000 0x089cb0d250000000 0x11800e0000000000 0x011800e000000000

def z660 : W := mkw 0x0000100002002000 0x0000010000200200 0x000010000600200d 0x2000010000600200

def z661 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0000000000020ce 0x2a0000000000020c

def z662 : W := mkw 0x0020128046402904 0x0002012804640290 0x51e07f8047c03f0d 0xf51e07f8047c03f0

def z663 : W := mkw 0x0000000000000000 0x0000000000000000 0x0060318000000005 0xa006031800000000

def z664 : W := mkw 0x00000010102c04a1 0x000000010102c04a 0x20000000003e00f0 0x020000000003e00f

def z665 : W := mkw 0x2000800010b78008 0x02000800010b7800 0x20000000003fc000 0x020000000003fc00

def z666 : W := mkw 0x108a063400d90c84 0x8108a063400d90c8 0x919a5e7601f81c07 0x7919a5e7601f81c0

def z667 : W := mkw 0x0000000000910000 0x0000000000091000 0x2000000007f9c008 0x12000000007f9c00

def z668 : W := mkw 0xcf7569c96d001302 0x0cf7569c96d00130 0x4e65a189f8000300 0x84e65a189f800030

def z669 : W := mkw 0x0634f0cade26f371 0x40634f0cade26f37 0xee67b18ffe07e3ff 0xaee67b18ffe07e3f

def z670 : W := mkw 0x04349082d626e150 0x404349082d626e15 0xee7fb18ffe3fe3ff 0xfee7fb18ffe3fe3f

def z671 : W := mkw 0x1000121202d96cc4 0x81000121202d96cc 0xa018407007f9fcce 0x7a018407007f9fcc

def z672 : W := mkw 0x00208080c4028110 0x400208080c402811 0x0061818180000000 0x0006181818000000

def z673 : W := mkw 0x10aa96a6c6d3e954 0xc10aa96a6c6d3e95 0x11e39f8787c1c001 0x011e39f8787c1c00

def z674 : W := mkw 0x108a162602d16844 0x8108a162602d1684 0x919a5e7607c1c007 0x6919a5e7607c1c00

def z675 : W := mkw 0x2d759082f726e158 0x42d759082f726e15 0xee67b18ffe07e3ff 0xaee67b18ffe07e3f

def z676 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0xee1c2078783e03f2 0x8ee1c2078783e03f

def z677 : W := mkw 0x402012806f403b06 0x0402012806f403b0 0x51805e007fc03f0d 0x751805e007fc03f0

def z678 : W := mkw 0x8ddf046d00000000 0x08ddf046d0000000 0x8fff807f80000003 0xe8fff807f8000000

def z679 : W := mkw 0x49601b8067402906 0x049601b806740290 0x51e03f8047c0230d 0xa51e03f8047c0230

def z680 : W := mkw 0x0b40690008001200 0x00b4069000800120 0x5fe07f8078003f0d 0xf5fe07f8078003f0

def z681 : W := mkw 0x2dff000075b50008 0x02dff000075b5000 0x4ff800007ff80009 0xf4ff800007ff8000

def z682 : W := mkw 0x4f747bc87f643b27 0x04f747bc87f643b2 0x5fe47f887fc63f3d 0xf5fe47f887fc63f3

def z683 : W := mkw 0xcf757bc96f403b06 0x0cf757bc96f403b0 0x5fe5ff89ffc03f0d 0xf5fe5ff89ffc03f0

def z684 : W := mkw 0x0614604808001200 0x0061460480800120 0xce1c607878003f0e 0xfce1c607878003f0

def z685 : W := mkw 0x0614604800000000 0x0061460480000000 0xee1c6078400623fe 0xeee1c6078400623f

def z686 : W := mkw 0x3020921277ffeccc 0x83020921277ffecc 0x600000007ffffcc8 0x1600000007ffffcc

def z687 : W := mkw 0x869f647d182c16a1 0x0869f647d182c16a 0xee1fe07ff83e3ffe 0xfee1fe07ff83e3ff

def z688 : W := mkw 0x40001b8002402906 0x040001b800240290 0x10001f8000000000 0x010001f800000000

def z689 : W := mkw 0x0b60690065000000 0x00b6069006500000 0x5fe07f807fc0000d 0xf5fe07f807fc0000

def z690 : W := mkw 0x0b40690000000000 0x00b4069000000000 0x9fe7ff8f80000007 0xe9fe7ff8f8000000

def z691 : W := mkw 0x108a16361afd7ee5 0x8108a16361afd7ee 0xf19a5e767fffffff 0x7f19a5e767ffffff

def z692 : W := mkw 0xafdfed6d10b78008 0x0afdfed6d10b7800 0xbfffffff803fc007 0xebfffffff803fc00

def z693 : W := mkw 0x0ddf000000000000 0x00ddf00000000000 0x0f98000000000000 0x40f9800000000000

def z694 : W := mkw 0x0000000000000000 0x0000000000000000 0xe067b18fc00623ff 0xae067b18fc00623f

def z695 : W := mkw 0x0614604818241221 0x0061460481824122 0xce1c607878060336 0xece1c60787806033

def z696 : W := mkw 0x463472d87f6c3fa7 0x0463472d87f6c3fa 0xee1c60787ffe3ffe 0xfee1c60787ffe3ff

def z697 : W := mkw 0x8ddf0d2500000000 0x08ddf0d250000000 0x1fff9f8780000003 0xe1fff9f878000000

def z698 : W := mkw 0x0000001000080480 0x0000000100008048 0xe01c6078403e3ffe 0xfe01c6078403e3ff

def z699 : W := mkw 0x000080028002c050 0x4000080028002c05 0x000380078001c000 0x0000380078001c00

def z700 : W := mkw 0x2d55000031240008 0x02d5500003124000 0x0e00000038000000 0x00e0000003800000

def z701 : W := mkw 0x808b042500000000 0x0808b04250000000 0x0003800780000000 0x0000380078000000

def z702 : W := mkw 0x0414000000000000 0x0041400000000000 0x0e1c000000000002 0xe0e1c00000000000

def z703 : W := mkw 0x0000042400000000 0x0000004240000000 0x90005e7600000004 0x090005e760000000

def z704 : W := mkw 0x022070804e003300 0x0022070804e00330 0x4e6071807e003f0d 0xf4e6071807e003f0

def z705 : W := mkw 0x0000120002402804 0x0000012000240280 0x10005e0000003c04 0x010005e0000003c0

def z706 : W := mkw 0x0614605800080480 0x0061460580008048 0xae1c607800383cce 0xfae1c607800383cc

def z707 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0xee1e60787e3fffff 0xfee1e60787e3ffff

def z708 : W := mkw 0x4b40eb02a942da56 0x44b40eb02a942da5 0xbf87ce0fb9c7dcf2 0x5bf87ce0fb9c7dcf

def z709 : W := mkw 0x42007bda8a487ff7 0x442007bda8a487ff 0x90007fff80003ff4 0x090007fff80003ff

def z710 : W := mkw 0x0000120002402804 0x0000012000240280 0x5f805e007fc03c0d 0xf5f805e007fc03c0

def z711 : W := mkw 0x049e000010b50000 0x0049e000010b5000 0x2f9a00003ff9c00b 0x72f9a00003ff9c00

def z712 : W := mkw 0x2d75800075b78008 0x02d75800075b7800 0x6e0000007fffc008 0x16e0000007fffc00

def z713 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0xee7de1f9f83e3ffe 0xfee7de1f9f83e3ff

def z714 : W := mkw 0x8ddf0d6d00000000 0x08ddf0d6d0000000 0x91ffdfff80000007 0x691ffdfff8000000

def z715 : W := mkw 0x10aa86b4c4db8d94 0xc10aa86b4c4db8d9 0x51fdeff9c1fe1f30 0xd51fdeff9c1fe1f3

def z716 : W := mkw 0x4b606b806d401b06 0x04b606b806d401b0 0x1fe04f8039c01c00 0x51fe04f8039c01c0

def z717 : W := mkw 0x8ddf0d2500000000 0x08ddf0d250000000 0x9fffdff780000007 0xe9fffdff78000000

def z718 : W := mkw 0x669ffb801af7bb0e 0x0669ffb801af7bb0 0x301fff80003fff06 0x0301fff80003fff0

def z719 : W := mkw 0x108a16b682d96dd4 0xc108a16b682d96dd 0xb19a5ff787f9fccf 0x7b19a5ff787f9fcc

def z720 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x9e7fffff80000006 0x89e7fffff8000000

def z721 : W := mkw 0x4b406b0029401a06 0x04b406b0029401a0 0x5fe07f8079c03f0d 0xf5fe07f8079c03f0

def z722 : W := mkw 0x0d74800075268000 0x00d7480007526800 0x6fff80007fffc00b 0xf6fff80007fffc00

def z723 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0xefff80087fffc0fb 0xfefff80087fffc0f

def z724 : W := mkw 0x4b607b006f403a06 0x04b607b006f403a0 0x5fe05e007fc03c0d 0xf5fe05e007fc03c0

def z725 : W := mkw 0x4b607bc86f403b27 0x04b607bc86f403b2 0x5fe07f887fc03f3d 0xf5fe07f887fc03f3

def z726 : W := mkw 0x89cb0d35182c16a1 0x089cb0d35182c16a 0x71e39f87f83e3ff9 0x171e39f87f83e3ff

def z727 : W := mkw 0x0634f0dade2ef7f1 0x40634f0dade2ef7f 0x0e7bd1f7be39dc01 0x50e7bd1f7be39dc0

def z728 : W := mkw 0x4b407b802b403b06 0x04b407b802b403b0 0x5f807f8079c03f0c 0xf5f807f8079c03f0

def z729 : W := mkw 0x4b406b0029401a06 0x04b406b0029401a0 0x1f804e0039c03c0c 0x71f804e0039c03c0

def z730 : W := mkw 0x8b416d6d00000000 0x08b416d6d0000000 0x9061ffff80000004 0x09061ffff8000000

def z731 : W := mkw 0xcb617b816f403b06 0x0cb617b816f403b0 0x5fe1ff81ffc03f0d 0xf5fe1ff81ffc03f0

def z732 : W := mkw 0x0f54694800000000 0x00f5469480000000 0x9fffffff80000007 0xe9fffffff8000000

def z733 : W := mkw 0x0dfe000075b50000 0x00dfe000075b5000 0x6ffe00007fffc00b 0xf6ffe00007fffc00

def z734 : W := mkw 0x0ddf000010b50000 0x00ddf000010b5000 0x6fff80007fffc00b 0xf6fff80007fffc00

def z735 : W := mkw 0x4b60fb82ef42fb56 0x44b60fb82ef42fb5 0xdfe5ff8fffc63ffd 0xfdfe5ff8fffc63ff

def z736 : W := mkw 0xcfdf6d6d29001202 0x0cfdf6d6d2900120 0x9fffffffb8000007 0xe9fffffffb800000

def z737 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x7fe47f807fc63f0f 0xf7fe47f807fc63f0

def z738 : W := mkw 0xafdf6d7d39bd16a9 0x0afdf6d7d39bd16a 0x1f984e7039f81c00 0x51f984e7039f81c0

def z739 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xb19a4e7607f9fcca 0x5b19a4e7607f9fcc

def z740 : W := mkw 0x4b607b826f407b46 0x04b607b826f407b4 0xffe7ff8fffc1ffcf 0xfffe7ff8fffc1ffc

def z741 : W := mkw 0xafdf6d6d21910008 0x0afdf6d6d2191000 0x9fffffff81c00007 0xe9fffffff81c0000

def z742 : W := mkw 0x008a121002d92c84 0x0008a121002d92c8 0xb19a5e7007f9fccf 0x7b19a5e7007f9fcc

def z743 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xb19e5e7e07fffcff 0x7b19e5e7e07fffcf

def z744 : W := mkw 0x4b406b0029401a06 0x04b406b0029401a0 0x1f807f8039c01c04 0x51f807f8039c01c0

def z745 : W := mkw 0x8f556d6d00000000 0x08f556d6d0000000 0x9e7dffff80000006 0xe9e7dffff8000000

def z746 : W := mkw 0x2d75800075b78008 0x02d75800075b7800 0x6fe580007fffc009 0xf6fe580007fffc00

def z747 : W := mkw 0x8fdf6d6d21000000 0x08fdf6d6d2100000 0x9fffffffb9c00007 0xf9fffffffb9c0000

def z748 : W := mkw 0x2dff842475b78008 0x02dff842475b7800 0xefff80767fffc00b 0xfefff80767fffc00

def z749 : W := mkw 0x4b407b022b407a46 0x04b407b022b407a4 0xbf825e063fc1fccf 0x7bf825e063fc1fcc

def z750 : W := mkw 0x4b60fb806f42bb06 0x04b60fb806f42bb0 0x7fe07f807fc7ff0d 0xf7fe07f807fc7ff0

def z751 : W := mkw 0x00209082c602e150 0x400209082c602e15 0xe067b18fc607c3f3 0x8e067b18fc607c3f

def z752 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0xdfffffffc000230f 0xedfffffffc000230

def z753 : W := mkw 0x24bf800075b78008 0x024bf800075b7800 0x6e1f80007fffc00a 0xf6e1f80007fffc00

def z754 : W := mkw 0x828a6d6d00000000 0x0828a6d6d0000000 0x91ffffff80000007 0xe91ffffff8000000

def z755 : W := mkw 0x2dff8080f5b78118 0x42dff8080f5b7811 0xefffa189ffffe3ff 0xfefffa189ffffe3f

def z756 : W := mkw 0x0414000010b50000 0x00414000010b5000 0x6e1c00007fffc00a 0xf6e1c00007fffc00

def z757 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x9ffbffff80000005 0x49ffbffff8000000

def z758 : W := mkw 0x349f843410bf8488 0x8349f843410bf848 0x201f8070003fc002 0x0201f8070003fc00

def z759 : W := mkw 0x8ddf0d6d00000000 0x08ddf0d6d0000000 0x11fb9ff780000001 0x011fb9ff78000000

def z760 : W := mkw 0x89cb0d6d00000000 0x089cb0d6d0000000 0x91e39fff80000001 0x091e39fff8000000

def z761 : W := mkw 0x4b407b002b403a06 0x04b407b002b403a0 0x1fe07f803fc03c0d 0xf1fe07f803fc03c0

def z762 : W := mkw 0x2ddf1082b3b56158 0x42ddf1082b3b5615 0x8f98318fb9f823f4 0x58f98318fb9f823f

def z763 : W := mkw 0x5bea6db66d9957c2 0x85bea6db66d9957c 0xee7a21f67839c3c2 0x8ee7a21f67839c3c

def z764 : W := mkw 0x108a163402d92c84 0x8108a163402d92c8 0x319a5e7007f9fc0f 0x7319a5e7007f9fc0

def z765 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x9fffffff80003c0f 0xf9fffffff80003c0

def z766 : W := mkw 0x00209082c602e150 0x400209082c602e15 0xe07ff1ffc607e3ff 0xee07ff1ffc607e3f

def z767 : W := mkw 0x2bebe0586d9b96a9 0x02bebe0586d9b96a 0x81e3e07807c1fff5 0x081e3e07807c1fff

def z768 : W := mkw 0x0b607b0067402804 0x00b607b006740280 0x5fe07f807fc03c0d 0xf5fe07f807fc03c0

def z769 : W := mkw 0x8fdf6d6d10240000 0x08fdf6d6d1024000 0xfffffffff83e23ff 0xffffffffff83e23f

def z770 : W := mkw 0xadff846d75b78008 0x0adff846d75b7800 0xefffb1ffffffc00f 0xfefffb1ffffffc00

def z771 : W := mkw 0x169e766e1af57a65 0x8169e766e1af57a6 0x5f863e0e7fc7c331 0x85f863e0e7fc7c33

def z772 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x6fff80007fffe3fb 0xf6fff80007fffe3f

def z773 : W := mkw 0x82006d6d00000000 0x082006d6d0000000 0x9065ffff80000004 0x89065ffff8000000

def z774 : W := mkw 0x0200620008401a04 0x00200620008401a0 0x1f804e0039c01c00 0x51f804e0039c01c0

def z775 : W := mkw 0x2dff842475b78008 0x02dff842475b7800 0x7fff9e067fffc00b 0xf7fff9e067fffc00

def z776 : W := mkw 0x4b406b0029401a06 0x04b406b0029401a0 0x1f806e0039c01c04 0xf1f806e0039c01c0

def z777 : W := mkw 0x0960000065910000 0x0096000006591000 0x6fe000007ff9c009 0xf6fe000007ff9c00

def z778 : W := mkw 0x2dff804875b78008 0x02dff804875b7800 0xefff80787fffc00b 0xfefff80787fffc00

def z779 : W := mkw 0xb49f847f10bfc4c8 0x8b49f847f10bfc4c 0xa01f807f803fc0c2 0x0a01f807f803fc0c

def z780 : W := mkw 0x008a162402d12804 0x0008a162402d1280 0xb19a5e7607f9fc0f 0x7b19a5e7607f9fc0

def z781 : W := mkw 0x1200725a0a487ee5 0x81200725a0a487ee 0x8000607800003ff4 0x08000607800003ff

def z782 : W := mkw 0x4b606b006d401a06 0x04b606b006d401a0 0x5fe07f807fc01c0d 0xf5fe07f807fc01c0

def z783 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x6fffb1807fffc00f 0xf6fffb1807fffc00

def z784 : W := mkw 0x149e047e10bd44e1 0x8149e047e10bd44e 0xa01a00760039c0c2 0x0a01a00760039c0c

def z785 : W := mkw 0x49601b8067402906 0x049601b806740290 0x5fe05f807fc03c0d 0xf5fe05f807fc03c0

def z786 : W := mkw 0xafdf6d6d10b50008 0x0afdf6d6d10b5000 0x9fffffff80380007 0xe9fffffff8038000

def z787 : W := mkw 0x2960800075b78008 0x02960800075b7800 0x6e6000007fffc008 0x96e6000007fffc00

def z788 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x6ffd80007fffc008 0xd6ffd80007fffc00

def z789 : W := mkw 0x4b407b002b403a06 0x04b407b002b403a0 0x1f805e003fc01c01 0x51f805e003fc01c0

def z790 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xb19a5e7607f9fcc7 0x0b19a5e7607f9fcc

def z791 : W := mkw 0xa220ed6d75b78008 0x0a220ed6d75b7800 0xf0007fffffffc00c 0x1f0007fffffffc00

def z792 : W := mkw 0x10209292defffff5 0xc10209292defffff 0x600000007ffffff8 0x1600000007ffffff

def z793 : W := mkw 0x0220f282ce42fb54 0x40220f282ce42fb5 0xffe7ff8fffc7ffff 0xfffe7ff8fffc7fff

def z794 : W := mkw 0x8bcb6d6d00000000 0x08bcb6d6d0000000 0x9fe3ffff80000005 0xe9fe3ffff8000000

def z795 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xb19a7fff87f9fccf 0x7b19a7fff87f9fcc

def z796 : W := mkw 0xadff846d75b78008 0x0adff846d75b7800 0xffffde7fffffc00f 0xfffffde7fffffc00

def z797 : W := mkw 0x9f557b5b02d96cc4 0x89f557b5b02d96cc 0x2e65a18987f9fcc8 0x92e65a18987f9fcc

def z798 : W := mkw 0xc4bf16ed6f403b06 0x0c4bf16ed6f403b0 0xc01f807fffc03f0a 0x1c01f807fffc03f0

def z799 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x1fe05f803fc03c0d 0x71fe05f803fc03c0

def z800 : W := mkw 0x8fdf6d6d08001221 0x08fdf6d6d0800122 0x9fffffff80000337 0xe9fffffff8000033

def z801 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0xee186078783e3ffc 0x5ee186078783e3ff

def z802 : W := mkw 0x4b60fb806f42bb06 0x04b60fb806f42bb0 0xffe7ff8fffc7ff0f 0xfffe7ff8fffc7ff0

def z803 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x4fff80007fffc001 0xd4fff80007fffc00

def z804 : W := mkw 0x6b61fb806f42bb0e 0x06b61fb806f42bb0 0x5fe1ff807fc03f0d 0xf5fe1ff807fc03f0

def z805 : W := mkw 0x89cb0d2500000000 0x089cb0d250000000 0x91ffffff80000007 0xe91ffffff8000000

def z806 : W := mkw 0x42007b800a403b06 0x042007b800a403b0 0x5f807f807fc03f0d 0xf5f807f807fc03f0

def z807 : W := mkw 0x52007fb68a487fd6 0xc52007fb68a487fd 0x90007fff80003ff4 0x090007fff80003ff

def z808 : W := mkw 0x89cb0d2500000000 0x089cb0d250000000 0x91fb9ff780000003 0x091fb9ff78000000

def z809 : W := mkw 0x4b407b002b403a06 0x04b407b002b403a0 0x1f804e003fc03c08 0x51f804e003fc03c0

def z810 : W := mkw 0x8b406d6d00000000 0x08b406d6d0000000 0x9fe7ffff80000007 0xe9fe7ffff8000000

def z811 : W := mkw 0x8fdf6d6d00910000 0x08fdf6d6d0091000 0xbfffffff8039c007 0xebfffffff8039c00

def z812 : W := mkw 0x096092026742e844 0x0096092026742e84 0xffe7de067fc7fccf 0xfffe7de067fc7fcc

def z813 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xf19e5e7647fffccf 0xff19e5e7647fffcc

def z814 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0x6e1c6078783e3ff8 0xd6e1c6078783e3ff

def z815 : W := mkw 0x39eb96a6e7d3e95c 0xc39eb96a6e7d3e95 0x11e39f8787c1c001 0x011e39f8787c1c00

def z816 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0xbfffffff800020cf 0xebfffffff800020c

def z817 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xb1984e7007f9fcce 0x7b1984e7007f9fcc

def z818 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0x6e1c4070783e3ffa 0xf6e1c4070783e3ff

def z819 : W := mkw 0x06146958182c16a1 0x006146958182c16a 0xfe1c7ff8783e3ffe 0xffe1c7ff8783e3ff

def z820 : W := mkw 0x2960800075b78008 0x02960800075b7800 0x6f8000007fffc008 0x56f8000007fffc00

def z821 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xff9a5e767ff9fccf 0xfff9a5e767ff9fcc

def z822 : W := mkw 0xafdf6d6d31b50008 0x0afdf6d6d31b5000 0xbfffffffbff9c00f 0xfbfffffffbff9c00

def z823 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x6fff80007fffc003 0x86fff80007fffc00

def z824 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xb1fbdff787f9fccf 0x7b1fbdff787f9fcc

def z825 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x6f9a00007fffc00b 0x76f9a00007fffc00

def z826 : W := mkw 0x0200620008401a04 0x00200620008401a0 0x5f806e0079c03f0c 0xf5f806e0079c03f0

def z827 : W := mkw 0x008a043400990480 0x0008a04340099048 0xb19a5e7607f9fccf 0x7b19a5e7607f9fcc

def z828 : W := mkw 0x2dff808075b78108 0x02dff808075b7810 0x6fffa1807fffc30b 0xf6fffa1807fffc30

def z829 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0xbfffffff8038000f 0xfbfffffff8038000

def z830 : W := mkw 0x4b606b006d401a06 0x04b606b006d401a0 0x5f804e007fc01c08 0x55f804e007fc01c0

def z831 : W := mkw 0x09ca000021910000 0x009ca00002191000 0x2f9a00003ff9c00b 0x72f9a00003ff9c00

def z832 : W := mkw 0x108a16b682d96dd4 0xc108a16b682d96dd 0xf19e7fffc7ffffff 0xff19e7fffc7fffff

def z833 : W := mkw 0x008a042400000000 0x0008a04240000000 0x91fbdff780000007 0x691fbdff78000000

def z834 : W := mkw 0x2ddf800031b78008 0x02ddf800031b7800 0x2f9f80003fffc00b 0x72f9f80003fffc00

def z835 : W := mkw 0x4b607b826f407b46 0x04b607b826f407b4 0x5fe27f867fc1ff0d 0xf5fe27f867fc1ff0

def z836 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0xee7fe078783e3fff 0xfee7fe078783e3ff

def z837 : W := mkw 0x4b60fb80ef42bb16 0x44b60fb80ef42bb1 0xffe5ff89ffc63fff 0xfffe5ff89ffc63ff

def z838 : W := mkw 0x4b60fb82ef42fb56 0x44b60fb82ef42fb5 0x5fe7ff8fffc7ff3d 0xf5fe7ff8fffc7ff3

def z839 : W := mkw 0x4b407b82ab407b56 0x44b407b82ab407b5 0x9f807f8fb9c03ff4 0x59f807f8fb9c03ff

def z840 : W := mkw 0x8bcb6d6d00000000 0x08bcb6d6d0000000 0x91fbffff80000007 0x691fbffff8000000

def z841 : W := mkw 0x4b406b0029401a06 0x04b406b0029401a0 0x5f804e0079c01c08 0xf5f804e0079c01c0

def z842 : W := mkw 0x89cb0d2500000000 0x089cb0d250000000 0x91e3dff780000005 0x091e3dff78000000

def z843 : W := mkw 0x4b406b0029401a06 0x04b406b0029401a0 0x1f806e0039c03f04 0x51f806e0039c03f0

def z844 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x2ffb80003ff9c00b 0x72ffb80003ff9c00

def z845 : W := mkw 0x8bcb6d2500000000 0x08bcb6d250000000 0x9ffbfff780000007 0xe9ffbfff78000000

def z846 : W := mkw 0x8f556d6d00000000 0x08f556d6d0000000 0x9fe5ffff80000005 0xe9fe5ffff8000000

def z847 : W := mkw 0x00208082c402c150 0x400208082c402c15 0xe067a18fc607c3fb 0xae067a18fc607c3f

def z848 : W := mkw 0x4b60fb82ef42fb56 0x44b60fb82ef42fb5 0xffe47f887fc7ffff 0xfffe47f887fc7fff

def z849 : W := mkw 0x108a16b602d96dc4 0x8108a16b602d96dc 0xb19a7ff607f9ffcf 0x7b19a7ff607f9ffc

def z850 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xb1fa7ff607f9fccf 0xfb1fa7ff607f9fcc

def z851 : W := mkw 0x8fdf6d6d18241221 0x08fdf6d6d1824122 0xdffffffff8063f3f 0xfdffffffff8063f3

def z852 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x5f807f807fc03f0c 0x55f807f807fc03f0

def z853 : W := mkw 0x2d74800075b78008 0x02d74800075b7800 0x6ffc00007fffc00b 0xf6ffc00007fffc00

def z854 : W := mkw 0x2dff8080f5b78118 0x42dff8080f5b7811 0xefffb18fffffc33f 0xfefffb18fffffc33

def z855 : W := mkw 0x949f047f10bd44e1 0x8949f047f10bd44e 0xa01f807f803fc0f2 0x0a01f807f803fc0f

def z856 : W := mkw 0xafdf6d6d31240008 0x0afdf6d6d3124000 0x9fffffffb8000007 0xe9fffffffb800000

def z857 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0x919a5e7607f9fcc5 0x5919a5e7607f9fcc

def z858 : W := mkw 0x020072000a403a04 0x0020072000a403a0 0x1f805e003fc03c0d 0x71f805e003fc03c0

def z859 : W := mkw 0x108a063400d90c84 0x8108a063400d90c8 0xb19a5e7607f9dc0f 0x7b19a5e7607f9dc0

def z860 : W := mkw 0x00209082c602e150 0x400209082c602e15 0xe067f18fc607ffff 0xfe067f18fc607fff

def z861 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0x319a5e7607f9dc0b 0x7319a5e7607f9dc0

def z862 : W := mkw 0x4b607b826f407b46 0x04b607b826f407b4 0xdfe07f867fc03fcd 0xfdfe07f867fc03fc

def z863 : W := mkw 0x4b406b0029401a06 0x04b406b0029401a0 0x1fe05f8039c01c01 0x51fe05f8039c01c0

def z864 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x91ffffff80000007 0x091ffffff8000000

def z865 : W := mkw 0x000080028002c050 0x4000080028002c05 0xe067b18fc007e3ff 0xae067b18fc007e3f

def z866 : W := mkw 0x00209082c602e150 0x400209082c602e15 0xa067b18f8607e3f7 0x0a067b18f8607e3f

def z867 : W := mkw 0x4b607b82ef407b56 0x44b607b82ef407b5 0x5fe07f807fc03ffd 0xf5fe07f807fc03ff

def z868 : W := mkw 0x52007f360a487ec6 0x852007f360a487ec 0x90005e7600003cc4 0x090005e7600003cc

def z869 : W := mkw 0x52007ffe0a487fe7 0x852007ffe0a487fe 0x90007ffe00003ff4 0x090007ffe00003ff

def z870 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0x11984e7007f9dc00 0x511984e7007f9dc0

def z871 : W := mkw 0xcb607bc96f403b06 0x0cb607bc96f403b0 0x5fe07f89ffc03f0d 0xf5fe07f89ffc03f0

def z872 : W := mkw 0x04140058182c16a1 0x004140058182c16a 0xee1c0078783e3ffa 0xfee1c0078783e3ff

def z873 : W := mkw 0x2960800075b78008 0x02960800075b7800 0x6fe780007fffc00b 0xf6fe780007fffc00

def z874 : W := mkw 0x4d741bd8776c2da7 0x04d741bd8776c2da 0xb1fc1ff807fe00f3 0x0b1fc1ff807fe00f

def z875 : W := mkw 0xef75e9c97d26930a 0x0ef75e9c97d26930 0x4e65a189f8060300 0x84e65a189f806030

def z876 : W := mkw 0x120076fe8a487ff5 0xc120076fe8a487ff 0x90007fff80003ff4 0x090007fff80003ff

def z877 : W := mkw 0x4b606b006d401a06 0x04b606b006d401a0 0x5fe06e007fc03f0d 0xf5fe06e007fc03f0

def z878 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0xdffffffff800000f 0xfdffffffff800000

def z879 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0xce1c6078783e3ff4 0xdce1c6078783e3ff

def z880 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0xee7c71f8783e3fff 0xfee7c71f8783e3ff

def z881 : W := mkw 0x0000121202486cc4 0x00000121202486cc 0xb19a5e7607f9fccf 0x7b19a5e7607f9fcc

def z882 : W := mkw 0x108a063400d90c84 0x8108a063400d90c8 0xb19a4e7007f9fccf 0x7b19a4e7007f9fcc

def z883 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x5f806e007fc03f0c 0xf5f806e007fc03f0

def z884 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0x319a4e7007f9fccb 0x7319a4e7007f9fcc

def z885 : W := mkw 0x52007b920a487fc6 0x852007b920a487fc 0x10007f8000003fc4 0x010007f8000003fc

def z886 : W := mkw 0x8ffffdefc602e150 0x48ffffdefc602e15 0x7f984e704607e3f8 0x47f984e704607e3f

def z887 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x9ffbdff780000007 0x69ffbdff78000000

def z888 : W := mkw 0x9fdf6f7d18fd1ea5 0x89fdf6f7d18fd1ea 0x1f984e7039f81c00 0x51f984e7039f81c0

def z889 : W := mkw 0x00209082c602e150 0x400209082c602e15 0xe07fb18fc63fe3ff 0xfe07fb18fc63fe3f

def z890 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0xbfffffff800600f7 0xebfffffff800600f

def z891 : W := mkw 0x29eb800065938008 0x029eb80006593800 0x6ffb80007ff9c00b 0xf6ffb80007ff9c00

def z892 : W := mkw 0x00209082c602e150 0x400209082c602e15 0xee67b18ffe07e3ff 0xfee67b18ffe07e3f

def z893 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x9ffdffff80000004 0xc9ffdffff8000000

def z894 : W := mkw 0x8bcb6d6d00000000 0x08bcb6d6d0000000 0x91e7ffff80000007 0xa91e7ffff8000000

def z895 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0xefff90067fffc00f 0xfefff90067fffc00

def z896 : W := mkw 0x4b60fb82ef42fb56 0x44b60fb82ef42fb5 0x7fe3ff87ffc7fffd 0xf7fe3ff87ffc7fff

def z897 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0xdfe47f887fc03f0f 0xfdfe47f887fc03f0

def z898 : W := mkw 0x4b60eb006d429a06 0x04b60eb006d429a0 0x7fe7ce007fc7dc0b 0xf7fe7ce007fc7dc0

def z899 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xf19a5e7647ffffff 0x7f19a5e7647fffff

def z900 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x5fe05f807fc01c09 0xf5fe05f807fc01c0

def z901 : W := mkw 0x8fdf6d6d18241221 0x08fdf6d6d1824122 0xfffffffff80623ff 0xefffffffff80623f

def z902 : W := mkw 0x4b406b0029401a06 0x04b406b0029401a0 0x5f804e0079c03f08 0x55f804e0079c03f0

def z903 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x1fe07f803fc03f05 0x51fe07f803fc03f0

def z904 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xb1ffde7607f9fccf 0xfb1ffde7607f9fcc

def z905 : W := mkw 0x149e047c10bd04a1 0x8149e047c10bd04a 0x0018007000380000 0x0001800700038000

def z906 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x6fff9187ffffc00b 0xf6fff9187ffffc00

def z907 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0xef9c60787ffe3fff 0xfef9c60787ffe3ff

def z908 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x7ff87f807ff83f0f 0xf7ff87f807ff83f0

def z909 : W := mkw 0x34bf94b6d6bfe5d8 0xc34bf94b6d6bfe5d 0xe07fb1ffc63fe3ff 0xae07fb1ffc63fe3f

def z910 : W := mkw 0x496012806f403b06 0x0496012806f403b0 0x5fe05e007fc03f0d 0xf5fe05e007fc03f0

def z911 : W := mkw 0x8fdf6d6d18241221 0x08fdf6d6d1824122 0xfffffffff83e033f 0xffffffffff83e033

def z912 : W := mkw 0x2ddf000031b50008 0x02ddf000031b5000 0x2f9800003ff9c008 0x52f9800003ff9c00

def z913 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0xee1c6078783e3ff6 0x8ee1c6078783e3ff

def z914 : W := mkw 0x0ddf042400000000 0x00ddf04240000000 0x9fffffff80000007 0xe9fffffff8000000

def z915 : W := mkw 0x4b407b802b403b06 0x04b407b802b403b0 0x1fe07f8039c03f05 0xf1fe07f8039c03f0

def z916 : W := mkw 0x09ea800065938000 0x009ea80006593800 0x6fff80007fffc00b 0xf6fff80007fffc00

def z917 : W := mkw 0xadff842575b78008 0x0adff842575b7800 0x6fff8007ffffc00b 0xf6fff8007ffffc00

def z918 : W := mkw 0x4b607b82ef407b56 0x44b607b82ef407b5 0xdfe7ff8fffc03fff 0xfdfe7ff8fffc03ff

def z919 : W := mkw 0x1200767e0a487ee5 0x81200767e0a487ee 0x90005e7600003cc4 0x090005e7600003cc

def z920 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x9fffbfff80000003 0x89fffbfff8000000

def z921 : W := mkw 0x4f74e9c8fd269333 0x44f74e9c8fd26933 0x4e65a189f8060330 0x84e65a189f806033

def z922 : W := mkw 0x2ddf000031b50008 0x02ddf000031b5000 0x0f9a00003ff9c001 0x50f9a00003ff9c00

def z923 : W := mkw 0x02006010182c16a1 0x002006010182c16a 0xee186070783e3ffe 0xfee186070783e3ff

def z924 : W := mkw 0x0bca6d2400000000 0x00bca6d240000000 0x9fffffff80000007 0xe9fffffff8000000

def z925 : W := mkw 0x3d759636776eeccc 0x83d759636776eecc 0xde65de7678063cc4 0x8de65de7678063cc

def z926 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x1ffbfff780000005 0xe1ffbfff78000000

def z927 : W := mkw 0x4b60fb82ef42fb56 0x44b60fb82ef42fb5 0xdfe3ff8fffc1fffd 0xfdfe3ff8fffc1fff

def z928 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0xefff80007fffe0cf 0xfefff80007fffe0c

def z929 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0xee184070783e3ffe 0x7ee184070783e3ff

def z930 : W := mkw 0x108a063400d90c84 0x8108a063400d90c8 0x119a4e7007f9dc01 0x5119a4e7007f9dc0

def z931 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xf1ffffffc7ffffff 0xff1ffffffc7fffff

def z932 : W := mkw 0x8fdf6d6d18241221 0x08fdf6d6d1824122 0x9fffffffb8000007 0xe9fffffffb800000

def z933 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x7fe27f807fc1ff0f 0xf7fe27f807fc1ff0

def z934 : W := mkw 0x6f75e9c87d26932b 0x06f75e9c87d26932 0x4e65a18878060330 0x84e65a1887806033

def z935 : W := mkw 0x4b606b806d401b06 0x04b606b806d401b0 0x5fe07f8079c01f05 0xf5fe07f8079c01f0

def z936 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x6f9f80007fffc00a 0x56f9f80007fffc00

def z937 : W := mkw 0x4b60fb80ef42bb16 0x44b60fb80ef42bb1 0x7fe7ff89ffc7ff3f 0xf7fe7ff89ffc7ff3

def z938 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0xefffc0707fffc00f 0xfefffc0707fffc00

def z939 : W := mkw 0x04140010182c16a1 0x004140010182c16a 0xee1c4070783e3ffe 0xfee1c4070783e3ff

def z940 : W := mkw 0xadff804975b78008 0x0adff804975b7800 0x6fff8009ffffc00b 0xf6fff8009ffffc00

def z941 : W := mkw 0x8fdf6d6d00910000 0x08fdf6d6d0091000 0x9fffffff87c1c007 0xe9fffffff87c1c00

def z942 : W := mkw 0x2dff842475b78008 0x02dff842475b7800 0xffffffffffffc00f 0xfffffffffffffc00

def z943 : W := mkw 0x49601b806f403b06 0x049601b806f403b0 0x5fe01f807fc03f09 0xf5fe01f807fc03f0

def z944 : W := mkw 0x120076360a487ec4 0x8120076360a487ec 0x90007e7600003fc4 0x090007e7600003fc

def z945 : W := mkw 0xadff8d6d75b78008 0x0adff8d6d75b7800 0xffff9fffffffc00b 0xfffff9fffffffc00

def z946 : W := mkw 0x6dff898075b7810a 0x06dff898075b7810 0x6fff81807fffc00b 0xf6fff81807fffc00

def z947 : W := mkw 0x04be800054b78000 0x004be800054b7800 0x6fff80007fffc00b 0xf6fff80007fffc00

def z948 : W := mkw 0x4b406b0029401a06 0x04b406b0029401a0 0x5f806e0079c01f00 0xd5f806e0079c01f0

def z949 : W := mkw 0x4b60eb80ed429b16 0x44b60eb80ed429b1 0x5fe5ef89f9c61f30 0xd5fe5ef89f9c61f3

def z950 : W := mkw 0x2434800075b78008 0x02434800075b7800 0x6e0400007fffc008 0x96e0400007fffc00

def z951 : W := mkw 0x8fdf6d6d08001200 0x08fdf6d6d0800120 0x9fffffff80003f07 0xe9fffffff80003f0

def z952 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x5fe3ff87ffc03f0d 0xf5fe3ff87ffc03f0

def z953 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x9fe7ffff80000005 0x89fe7ffff8000000

def z954 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0xdfffffffc0060337 0xedfffffffc006033

def z955 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x9fffffff87c0000f 0xf9fffffff87c0000

def z956 : W := mkw 0x24be800075b78008 0x024be800075b7800 0x6f9e00007fffc00b 0xf6f9e00007fffc00

def z957 : W := mkw 0x4b60fb806f42bb06 0x04b60fb806f42bb0 0xffe7ff887fc7ffff 0xfffe7ff887fc7fff

def z958 : W := mkw 0x09609282e742e954 0x409609282e742e95 0xffe7ff8fffc7ffff 0xfffe7ff8fffc7fff

def z959 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x7fffde007fffc00f 0xf7fffde007fffc00

def z960 : W := mkw 0x4b607b82ef407b56 0x44b607b82ef407b5 0xffe47f8fffc63fff 0xfffe47f8fffc63ff

def z961 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0xffe07f807fc03fcf 0xfffe07f807fc03fc

def z962 : W := mkw 0x4b407b802b403b06 0x04b407b802b403b0 0x1f804e0039c03f00 0x51f804e0039c03f0

def z963 : W := mkw 0x2dff000075b50008 0x02dff000075b5000 0x6ffa00007ff9c00b 0xf6ffa00007ff9c00

def z964 : W := mkw 0x86156059182c16a1 0x086156059182c16a 0xee1de079f83e3ffe 0xfee1de079f83e3ff

def z965 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x9fffdfff80000003 0x49fffdfff8000000

def z966 : W := mkw 0x108a163682d96cd4 0xc108a163682d96cd 0xb19a5e7f87f9fcff 0x7b19a5e7f87f9fcf

def z967 : W := mkw 0x50209292efdbffd6 0xc50209292efdbffd 0x600000007ffffff8 0x1600000007ffffff

def z968 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x5fe05f807fc03f09 0x55fe05f807fc03f0

def z969 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x1fe07f803fc01c05 0xf1fe07f803fc01c0

def z970 : W := mkw 0x00209082c602e150 0x400209082c602e15 0xe067a18fc607e3fa 0x8e067a18fc607e3f

def z971 : W := mkw 0x4b60fb82ef42fb56 0x44b60fb82ef42fb5 0xffe07f8fffc7fffd 0xfffe07f8fffc7fff

def z972 : W := mkw 0x34bf943656bfe4c8 0x834bf943656bfe4c 0xe07f9076463fe0cf 0xae07f9076463fe0c

def z973 : W := mkw 0x2020800075b78008 0x02020800075b7800 0x6e0000007fffc008 0xf6e0000007fffc00

def z974 : W := mkw 0x108a063600d94cc4 0x8108a063600d94cc 0xb19a4e7607f9dccb 0x7b19a4e7607f9dcc

def z975 : W := mkw 0x4b60fb82ef42fb56 0x44b60fb82ef42fb5 0x7fe7ff87ffc7ff0f 0xf7fe7ff87ffc7ff0

def z976 : W := mkw 0x349f843690bfc4d8 0xc349f843690bfc4d 0xa01f807f803fc0f2 0x0a01f807f803fc0f

def z977 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0xdff87ff07fc03f0f 0xfdff87ff07fc03f0

def z978 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xb19fde7f87f9fccf 0x7b19fde7f87f9fcc

def z979 : W := mkw 0x00209082c602e150 0x400209082c602e15 0xc067b18fc607e3f5 0x8c067b18fc607e3f

def z980 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x0f9800003ff9c000 0x50f9800003ff9c00

def z981 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x2fff80003fffc003 0x52fff80003fffc00

def z982 : W := mkw 0xadff846d75b78008 0x0adff846d75b7800 0x6fff80707fffc00b 0xf6fff80707fffc00

def z983 : W := mkw 0x0940020021400804 0x0094002002140080 0x1f804e0039c01c00 0x51f804e0039c01c0

def z984 : W := mkw 0x149e847e90bfc4f1 0xc149e847e90bfc4f 0xa01f807f803fc0f2 0x0a01f807f803fc0f

def z985 : W := mkw 0xafdf6d6d31b50008 0x0afdf6d6d31b5000 0xfffffffff9fe000f 0xffffffffff9fe000

def z986 : W := mkw 0x2d75800075b78008 0x02d75800075b7800 0x6e6780007fffc00b 0xb6e6780007fffc00

def z987 : W := mkw 0x349f043410bd0488 0x8349f043410bd048 0x0018007000380000 0x0001800700038000

def z988 : W := mkw 0xadff8d2575b78008 0x0adff8d2575b7800 0xffffbf8fffffc00f 0xfffffbf8fffffc00

def z989 : W := mkw 0x86146959182c16a1 0x086146959182c16a 0xee1c61f9f83e3ffe 0xfee1c61f9f83e3ff

def z990 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x6fffa0087fffc33b 0xf6fffa0087fffc33

def z991 : W := mkw 0x4b407b802b403b06 0x04b407b802b403b0 0x1f805f8039c01c00 0x51f805f8039c01c0

def z992 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x5fe04e007fc03f09 0xf5fe04e007fc03f0

def z993 : W := mkw 0x0000042400000000 0x0000004240000000 0x9067ffff80000007 0xa9067ffff8000000

def z994 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xb19e7e7e07f9fccf 0xfb19e7e7e07f9fcc

def z995 : W := mkw 0x10209292c6dbedd4 0xc10209292c6dbedd 0x2000000007f9fcc8 0x12000000007f9fcc

def z996 : W := mkw 0x849f046d00000000 0x0849f046d0000000 0x91ffffff80000007 0xe91ffffff8000000

def z997 : W := mkw 0x82006d6d00000000 0x082006d6d0000000 0x9063ffff80000005 0x09063ffff8000000

def z998 : W := mkw 0x4b60fb806f42bb06 0x04b60fb806f42bb0 0x5fe5ff807fc63f0d 0xf5fe5ff807fc63f0

def z999 : W := mkw 0x0960020065400804 0x0096002006540080 0x5fe04e007fc01c09 0xf5fe04e007fc01c0

def z1000 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x5fe07f807fc01f01 0xd5fe07f807fc01f0

def z1001 : W := mkw 0x0960128067402904 0x0096012806740290 0x5fe07f807fc03f0d 0xf5fe07f807fc03f0

def z1002 : W := mkw 0x30209292f7ffeddc 0xc30209292f7ffedd 0x600000007ffffff8 0x1600000007ffffff

def z1003 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0xee1fe07ff83e3ffe 0xfee1fe07ff83e3ff

def z1004 : W := mkw 0x4b606b006d401a06 0x04b606b006d401a0 0x1fe04e003fc01c01 0x51fe04e003fc01c0

def z1005 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x6f9c00007fffc00a 0xf6f9c00007fffc00

def z1006 : W := mkw 0x908b163702d96cc4 0x8908b163702d96cc 0xb19bde7787f9fccf 0x7b19bde7787f9fcc

def z1007 : W := mkw 0x4b406b8029401b06 0x04b406b8029401b0 0x1f806f8039c01f00 0x51f806f8039c01f0

def z1008 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x1f804e003fc01c00 0x51f804e003fc01c0

def z1009 : W := mkw 0x000090828202e150 0x4000090828202e15 0xa067b18f8007e3f7 0xaa067b18f8007e3f

def z1010 : W := mkw 0x4b407b002b403a06 0x04b407b002b403a0 0x5f807e007fc03f0d 0xf5f807e007fc03f0

def z1011 : W := mkw 0xadff8d2575b78008 0x0adff8d2575b7800 0xffffdff7ffffc00f 0xfffffdff7ffffc00

def z1012 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x9fffffff800023f7 0xe9fffffff800023f

def z1013 : W := mkw 0x108a16b682d96dd4 0xc108a16b682d96dd 0xb19a5e7607f9ffff 0x7b19a5e7607f9fff

def z1014 : W := mkw 0x4b406b0029401a06 0x04b406b0029401a0 0x1fe04e0039c01c01 0xf1fe04e0039c01c0

def z1015 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x4ffb80007ff9c009 0xf4ffb80007ff9c00

def z1016 : W := mkw 0x022072804e403b04 0x0022072804e403b0 0x5fe07f807fc03f0d 0xf5fe07f807fc03f0

def z1017 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x5fe07f807fc03f05 0x85fe07f807fc03f0

def z1018 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0xefffa0087fffc00f 0xfefffa0087fffc00

def z1019 : W := mkw 0x86146d6d00000000 0x086146d6d0000000 0x9e7fffff80000007 0xe9e7fffff8000000

def z1020 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0xdfe07f8fffc03f0d 0xfdfe07f8fffc03f0

def z1021 : W := mkw 0x89cb0d2500000000 0x089cb0d250000000 0x11fbdff780000001 0x411fbdff78000000

def z1022 : W := mkw 0x4b60fb82ef42fb56 0x44b60fb82ef42fb5 0x1fe3df87bfc1dc01 0x51fe3df87bfc1dc0

def z1023 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x6e7f80007fffc00a 0x96e7f80007fffc00

def z1024 : W := mkw 0x2434800075b78008 0x02434800075b7800 0x6e1800007fffc008 0x56e1800007fffc00

def z1025 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0xefffb18fffffe3ff 0xfefffb18fffffe3f

def z1026 : W := mkw 0x8fdf6d6d08001200 0x08fdf6d6d0800120 0xfffffffff8063fff 0xffffffffff8063ff

def z1027 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x6fffa189ffffc00b 0xf6fffa189ffffc00

def z1028 : W := mkw 0x00209282c642e954 0x400209282c642e95 0xf1e7bf8fc7c7e3ff 0xaf1e7bf8fc7c7e3f

def z1029 : W := mkw 0x8ddf0d6d00000000 0x08ddf0d6d0000000 0x91ffbfff80000007 0xa91ffbfff8000000

def z1030 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x0fff80003ff9c003 0xf0fff80003ff9c00

def z1031 : W := mkw 0x0b407b000a403a04 0x00b407b000a403a0 0x5fe07f807fc03f0d 0xf5fe07f807fc03f0

def z1032 : W := mkw 0x8fdf6d6d10240000 0x08fdf6d6d1024000 0xbfffffff803e0007 0xebfffffff803e000

def z1033 : W := mkw 0xaf75e9497d269229 0x0af75e9497d26922 0x4e65a189f8060330 0x84e65a189f806033

def z1034 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x5fe07f8079c03f04 0xd5fe07f8079c03f0

def z1035 : W := mkw 0x349f847e10bfc4e9 0x8349f847e10bfc4e 0xa01f807e003fc0f2 0x0a01f807e003fc0f

def z1036 : W := mkw 0x4b60fb82ef42fb56 0x44b60fb82ef42fb5 0xffe27f867fc7ffff 0xfffe27f867fc7fff

def z1037 : W := mkw 0x4b606b806d401b06 0x04b606b806d401b0 0x5fe06f807fc01f09 0xf5fe06f807fc01f0

def z1038 : W := mkw 0x249f800010b78008 0x0249f800010b7800 0x6f9f80007fffc00b 0xf6f9f80007fffc00

def z1039 : W := mkw 0x108a16b682d96dd4 0xc108a16b682d96dd 0xb1ffffff87f9ffff 0xfb1ffffff87f9fff

def z1040 : W := mkw 0x8fdf6d6d10b50000 0x08fdf6d6d10b5000 0xffffffffffffc00f 0xfffffffffffffc00

def z1041 : W := mkw 0x4b406b0029401a06 0x04b406b0029401a0 0x1fe06f8039c01c00 0xd1fe06f8039c01c0

def z1042 : W := mkw 0x4b60fb80ef42bb16 0x44b60fb80ef42bb1 0x5fe07f807fc63f3d 0xf5fe07f807fc63f3

def z1043 : W := mkw 0x00209082c602e150 0x400209082c602e15 0x6067b18fc607e3f9 0x86067b18fc607e3f

def z1044 : W := mkw 0x8fdf6d6d08001200 0x08fdf6d6d0800120 0xdffffffff8000307 0xedffffffff800030

def z1045 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xb19a5e7607f9dcc3 0x5b19a5e7607f9dcc

def z1046 : W := mkw 0x4b607b826f407b46 0x04b607b826f407b4 0x7fe07f807fc1ffcd 0xf7fe07f807fc1ffc

def z1047 : W := mkw 0x4b60fb82ef42fb56 0x44b60fb82ef42fb5 0x7fe5ff89ffc7fffd 0xf7fe5ff89ffc7fff

def z1048 : W := mkw 0x8fdf6d6d18241200 0x08fdf6d6d1824120 0xfffffffff83e3f0f 0xffffffffff83e3f0

def z1049 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0xee1c2078783e3ffa 0x9ee1c2078783e3ff

def z1050 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xb1985e7607f9fccc 0x5b1985e7607f9fcc

def z1051 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x6fffa0007fffe30f 0xf6fffa0007fffe30

def z1052 : W := mkw 0x00208082c402c150 0x400208082c402c15 0xe067b18fc007c3f7 0xae067b18fc007c3f

def z1053 : W := mkw 0x8fdf6d6d08001200 0x08fdf6d6d0800120 0x9fffffffb8001c07 0xf9fffffffb8001c0

def z1054 : W := mkw 0x008a000000910000 0x0008a00000091000 0x6f9a00007ff9c00b 0xf6f9a00007ff9c00

def z1055 : W := mkw 0x0000100202006040 0x0000010020200604 0xe067b18fc607e3ff 0xae067b18fc607e3f

def z1056 : W := mkw 0x40209292ff6efff7 0x440209292ff6efff 0x600000007ffffff8 0x1600000007ffffff

def z1057 : W := mkw 0x020072020a407a44 0x0020072020a407a4 0xff867e0e7fc7ffff 0xfff867e0e7fc7fff

def z1058 : W := mkw 0xd2007fff0a487fc6 0x8d2007fff0a487fc 0x90007fff80003fc4 0x090007fff80003fc

def z1059 : W := mkw 0x4b406b0029401a06 0x04b406b0029401a0 0x1f805e0039c01c05 0x71f805e0039c01c0

def z1060 : W := mkw 0x4b60fb80ef42bb16 0x44b60fb80ef42bb1 0x5fe1ff81ffc03f0d 0xf5fe1ff81ffc03f0

def z1061 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0xee1c4078783e3ffa 0x5ee1c4078783e3ff

def z1062 : W := mkw 0x4b606b806d401b06 0x04b606b806d401b0 0x5fe06f8079c03f0c 0xf5fe06f8079c03f0

def z1063 : W := mkw 0x2ddf000031b50008 0x02ddf000031b5000 0x6f9e00007fffc00b 0xf6f9e00007fffc00

def z1064 : W := mkw 0x4b607b826f407b46 0x04b607b826f407b4 0xffe67f8e7fc7ffff 0xfffe67f8e7fc7fff

def z1065 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0xbfffffff8601c00f 0xebfffffff8601c00

def z1066 : W := mkw 0x4b407b802b403b06 0x04b407b802b403b0 0x1f807f803fc03f0d 0x71f807f803fc03f0

def z1067 : W := mkw 0x2dff8080f5b78118 0x42dff8080f5b7811 0x6fff80007fffc33b 0xf6fff80007fffc33

def z1068 : W := mkw 0x00209082c602e150 0x400209082c602e15 0xf1e7ff8fc607e3ff 0xef1e7ff8fc607e3f

def z1069 : W := mkw 0x2434800075b78008 0x02434800075b7800 0x6e7f80007fffc00b 0xf6e7f80007fffc00

def z1070 : W := mkw 0x4b406b0029401a06 0x04b406b0029401a0 0x9fe7ff8fb9c01c07 0xf9fe7ff8fb9c01c0

def z1071 : W := mkw 0x8fdf6d6d10240000 0x08fdf6d6d1024000 0xdffffffff8060007 0xedffffffff806000

def z1072 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x5fe47f887fc63f3d 0xf5fe47f887fc63f3

def z1073 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xb19a7e7e07f9ffff 0x7b19a7e7e07f9fff

def z1074 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0x919a5e7607f9dc07 0x7919a5e7607f9dc0

def z1075 : W := mkw 0x0200601008081680 0x0020060100808168 0xee1c6078783e3ffe 0xfee1c6078783e3ff

def z1076 : W := mkw 0x4b60fb82ef42fb56 0x44b60fb82ef42fb5 0x5fe07f807fc1ff0d 0xf5fe07f807fc1ff0

def z1077 : W := mkw 0x2dff890075b78008 0x02dff890075b7800 0x7fff9f807fffc00b 0xf7fff9f807fffc00

def z1078 : W := mkw 0x00209282c642e954 0x400209282c642e95 0xf067ff8fc607ffff 0xaf067ff8fc607fff

def z1079 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x6ffb80007fffc009 0x56ffb80007fffc00

def z1080 : W := mkw 0x2ddf000031b50008 0x02ddf000031b5000 0x2fff80003ff9c00b 0xf2fff80003ff9c00

def z1081 : W := mkw 0x422072806f403b06 0x0422072806f403b0 0x5f807e007fc03f0d 0xf5f807e007fc03f0

def z1082 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0xdfe27f867fc03f0f 0xfdfe27f867fc03f0

def z1083 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x6fffc0007ffffc0f 0xf6fffc0007ffffc0

def z1084 : W := mkw 0x4b60fb80ef42bb16 0x44b60fb80ef42bb1 0xdfe7ff8fffc63f3f 0xfdfe7ff8fffc63f3

def z1085 : W := mkw 0x2dff804875b78029 0x02dff804875b7802 0x6fff80087fffc03b 0xf6fff80087fffc03

def z1086 : W := mkw 0x869f6d6d00000000 0x0869f6d6d0000000 0x907fffff80000007 0xa907fffff8000000

def z1087 : W := mkw 0x00209082e702e150 0x400209082e702e15 0xe067b18fffc7e3ff 0xbe067b18fffc7e3f

def z1088 : W := mkw 0x149e047c10bd04a1 0x8149e047c10bd04a 0xa01c0078003e00f2 0x0a01c0078003e00f

def z1089 : W := mkw 0x349f043610bd44c8 0x8349f043610bd44c 0xa01a00760039c0c2 0x0a01a00760039c0c

def z1090 : W := mkw 0x4b606b806d401b06 0x04b606b806d401b0 0x5f804e0079c01f00 0x55f804e0079c01f0

def z1091 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x5fe5ff89ffc03f0d 0xf5fe5ff89ffc03f0

def z1092 : W := mkw 0x92007f7f0a487ee5 0x892007f7f0a487ee 0x90007fff80003ff4 0x090007fff80003ff

def z1093 : W := mkw 0x0dff000065910000 0x00dff00006591000 0x6fff80007ff9c00b 0xf6fff80007ff9c00

def z1094 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0xffffffffc006000f 0xeffffffffc006000

def z1095 : W := mkw 0x8bcb6d6d00000000 0x08bcb6d6d0000000 0x11e3dff780000001 0x011e3dff78000000

def z1096 : W := mkw 0x0b6072006f403a04 0x00b6072006f403a0 0x5fe07e007fc03f0d 0xf5fe07e007fc03f0

def z1097 : W := mkw 0xa49f847d10bf84a9 0x0a49f847d10bf84a 0xa01f807f803fc0f2 0x0a01f807f803fc0f

def z1098 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x6fe780007fffc009 0x96fe780007fffc00

def z1099 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0x319a5e7607f9fcc9 0x5319a5e7607f9fcc

def z1100 : W := mkw 0x2dff8080f5b78118 0x42dff8080f5b7811 0x6fff8181ffffc00b 0xf6fff8181ffffc00

def z1101 : W := mkw 0x59ea9fa6e7d3e956 0xc59ea9fa6e7d3e95 0x11e39f8787c1c001 0x011e39f8787c1c00

def z1102 : W := mkw 0x149e147e12bd64e1 0x8149e147e12bd64e 0xe01e307e463fe3ff 0xae01e307e463fe3f

def z1103 : W := mkw 0x4b60fb826f42fb46 0x04b60fb826f42fb4 0xffe7ff867fc7ffcf 0xfffe7ff867fc7ffc

def z1104 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x1fffdff780000003 0xe1fffdff78000000

def z1105 : W := mkw 0x108a063400d90c84 0x8108a063400d90c8 0x31984e7007f9dc08 0x531984e7007f9dc0

def z1106 : W := mkw 0x4b60fb82ef42fb56 0x44b60fb82ef42fb5 0x7fe7ff807fc7ffff 0xf7fe7ff807fc7fff

def z1107 : W := mkw 0x8fdf6d6d00000000 0x08fdf6d6d0000000 0x1fffffff80000001 0xc1fffffff8000000

def z1108 : W := mkw 0x4b60fb82ef42fb56 0x44b60fb82ef42fb5 0xdfe7ff8fffc1ff0f 0xfdfe7ff8fffc1ff0

def z1109 : W := mkw 0x8ddf0d6d00000000 0x08ddf0d6d0000000 0x9fff9fff80000003 0xe9fff9fff8000000

def z1110 : W := mkw 0x4b60fb82ef42fb56 0x44b60fb82ef42fb5 0x7f804e007fc7fff8 0x57f804e007fc7fff

def z1111 : W := mkw 0x2d75800075b78008 0x02d75800075b7800 0x6e7d80007fffc00a 0xf6e7d80007fffc00

def z1112 : W := mkw 0x04140010102c0480 0x004140010102c048 0xee1c6078783e3ffe 0xfee1c6078783e3ff

def z1113 : W := mkw 0x1000121202d96cc4 0x81000121202d96cc 0xb1985e7007f9fccf 0x7b1985e7007f9fcc

def z1114 : W := mkw 0x4b606b006d401a06 0x04b606b006d401a0 0x5fe04e0079c01c00 0xd5fe04e0079c01c0

def z1115 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x7fe07f807fc63ffd 0xf7fe07f807fc63ff

def z1116 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0xefff800fffffc00b 0xfefff800fffffc00

def z1117 : W := mkw 0x4b607b82ef407b56 0x44b607b82ef407b5 0xffe27f8fffc1ffff 0xfffe27f8fffc1fff

def z1118 : W := mkw 0x0940120023402804 0x0094012002340280 0x1f805e003fc03c0d 0x71f805e003fc03c0

def z1119 : W := mkw 0x00208082c402c150 0x400208082c402c15 0xe067a18fc007e3fe 0xae067a18fc007e3f

def z1120 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0x119a5e7607f9fc0d 0x7119a5e7607f9fc0

def z1121 : W := mkw 0x069e646c00000000 0x0069e646c0000000 0x9fffffff80000007 0xe9fffffff8000000

def z1122 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x5fe03f807fc03f09 0x95fe03f807fc03f0

def z1123 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x5fe06f807fc03f08 0xd5fe06f807fc03f0

def z1124 : W := mkw 0x4b607b80ef403b16 0x44b607b80ef403b1 0x5fe07f89ffc03f3d 0xf5fe07f89ffc03f3

def z1125 : W := mkw 0x40209282e742e956 0x440209282e742e95 0xe067b18fc7c7e3ff 0xae067b18fc7c7e3f

def z1126 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0xf19a7e7647f9ffcf 0xff19a7e7647f9ffc

def z1127 : W := mkw 0xadff890175b78008 0x0adff890175b7800 0x6fff8181ffffc00b 0xf6fff8181ffffc00

def z1128 : W := mkw 0x149e043610bd44c0 0x8149e043610bd44c 0xa01e0076003fc0c2 0x0a01e0076003fc0c

def z1129 : W := mkw 0x8fdf6d6d10240000 0x08fdf6d6d1024000 0x9fffffffb8380007 0xf9fffffffb838000

def z1130 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0x6e186070783e3ffc 0xf6e186070783e3ff

def z1131 : W := mkw 0x2dff8000f5b78018 0x42dff8000f5b7801 0x6fff8009ffffc03b 0xf6fff8009ffffc03

def z1132 : W := mkw 0x8f556d6d00000000 0x08f556d6d0000000 0x9e67ffff80000007 0xa9e67ffff8000000

def z1133 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0xee1e707e783e3fff 0xfee1e707e783e3ff

def z1134 : W := mkw 0x00209082c602e150 0x400209082c602e15 0xe1e7b18fc7c7e3ff 0xfe1e7b18fc7c7e3f

def z1135 : W := mkw 0x14be94fed6bfe5f1 0xc14be94fed6bfe5f 0xe07fb1ffc63fe3ff 0xae07fb1ffc63fe3f

def z1136 : W := mkw 0x0b6069006d001200 0x00b6069006d00120 0x5fe07f807fc03f0d 0xf5fe07f807fc03f0

def z1137 : W := mkw 0x2dff842475b78008 0x02dff842475b7800 0x7fffce707fffc00b 0xf7fffce707fffc00

def z1138 : W := mkw 0x2dff800075b78008 0x02dff800075b7800 0x6ff800007fffc009 0xf6ff800007fffc00

def z1139 : W := mkw 0x00209282c642e954 0x400209282c642e95 0xe067b18fc7c7ffff 0xbe067b18fc7c7fff

def z1140 : W := mkw 0x8fdf6d6d00910000 0x08fdf6d6d0091000 0x9fffffff81f80007 0xf9fffffff81f8000

def z1141 : W := mkw 0x4b607bc86f403b06 0x04b607bc86f403b0 0xdfe07ff87fc03f0d 0xfdfe07ff87fc03f0

def z1142 : W := mkw 0x29ea800075b78008 0x029ea800075b7800 0x6ffa00007fffc00b 0xf6ffa00007fffc00

def z1143 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0xdfe07f887fc03ffd 0xfdfe07f887fc03ff

def z1144 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x5f805e007fc03f0d 0x75f805e007fc03f0

def z1145 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0xee1c71fff83e3ffe 0xfee1c71fff83e3ff

def z1146 : W := mkw 0x4b407b002b403a06 0x04b407b002b403a0 0x1f805e0039c03c04 0x51f805e0039c03c0

def z1147 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0x5fe7ff807fc03f0f 0xf5fe7ff807fc03f0

def z1148 : W := mkw 0x10209292c64aedd4 0xc10209292c64aedd 0x600000004607fff8 0x0600000004607fff

def z1149 : W := mkw 0x8fdf6d6d10240021 0x08fdf6d6d1024002 0x9fffffff80060037 0xe9fffffff8006003

def z1150 : W := mkw 0x4b406b0029401a06 0x04b406b0029401a0 0x1f804e003fc01c09 0x71f804e003fc01c0

def z1151 : W := mkw 0x00209082c602e150 0x400209082c602e15 0xe067b18fc007e3f6 0x8e067b18fc007e3f

def z1152 : W := mkw 0x06146058182c16a1 0x006146058182c16a 0xff9c7e78783e3fff 0xfff9c7e78783e3ff

def z1153 : W := mkw 0x4b607b806f403b06 0x04b607b806f403b0 0xffe7ff8fffc63fff 0xfffe7ff8fffc63ff

def z1154 : W := mkw 0x4b60fb82ef42fb56 0x44b60fb82ef42fb5 0xffe3ff87ffc1ffcf 0xfffe3ff87ffc1ffc

def z1155 : W := mkw 0x4b406b0029401a06 0x04b406b0029401a0 0xff846e0879c63ffe 0xfff846e0879c63ff

def z1156 : W := mkw 0x4b60fb806f42bb06 0x04b60fb806f42bb0 0x5fe3ff807fc1ff0d 0xf5fe3ff807fc1ff0

def z1157 : W := mkw 0x29eb800075b78008 0x029eb800075b7800 0x6fe380007fffc009 0xf6fe380007fffc00

def z1158 : W := mkw 0xadff8d2575b78008 0x0adff8d2575b7800 0x7fff8e007fffc00b 0xf7fff8e007fffc00

def z1159 : W := mkw 0x4b607b82ef407b56 0x44b607b82ef407b5 0x5fe07f87ffc03f0d 0xf5fe07f87ffc03f0

def z1160 : W := mkw 0x0020800044028000 0x0002080004402800 0xe067b18fc607e3ff 0xae067b18fc607e3f

def z1161 : W := mkw 0x108a163602d96cc4 0x8108a163602d96cc 0x31985e7007f9fccd 0x731985e7007f9fcc

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z7,z8,z6]),(1,[z9,z0,z2,z3,z7,z10])],[(0,[z0,z1,z2,z3,z7,z6,z11])],[(0,[z0,z12,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z13,z3,z7,z6]),(1,[z0,z1,z2,z7,z14,z6]),(0,[z0,z1,z2,z3,z7,z15,z6]),(0,[z0,z1,z2,z16,z3,z7,z6]),(0,[z0,z17,z1,z2,z3,z7,z6])],[(0,[z0,z1,z18,z19,z3,z7,z6]),(1,[z0,z1,z2,z3,z20,z6]),(1,[z0,z1,z21,z3,z7,z6]),(0,[z0,z1,z2,z3,z4,z7,z6]),(0,[z0,z1,z2,z3,z7,z22,z6]),(0,[z0,z1,z2,z23,z24,z7,z6])],[(0,[z25,z0,z1,z2,z3,z26,z6]),(0,[z0,z27,z1,z2,z3,z26,z6]),(0,[z0,z28,z1,z2,z3,z7,z6]),(0,[z29,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z30,z2,z3,z7,z6])],[(0,[z0,z1,z31,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z32])],[(0,[z0,z1,z2,z3,z26,z33,z6]),(0,[z0,z1,z2,z3,z34,z7,z6])],[(0,[z35,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z36,z18,z3,z7,z6]),(0,[z0,z1,z2,z37,z3,z26,z6]),(0,[z0,z1,z2,z3,z38,z7,z6]),(1,[z0,z39,z1,z2,z7,z6]),(1,[z0,z1,z2,z3,z7,z40]),(0,[z0,z41,z1,z2,z3,z7,z6])]],
   [[(0,[z0,z1,z2,z42,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z43,z6])],[(0,[z44,z0,z1,z2,z3,z7,z6]),(1,[z45,z1,z2,z37,z7,z6]),(0,[z0,z27,z1,z46,z2,z3,z6]),(0,[z0,z1,z47,z2,z3,z7,z6]),(0,[z48,z49,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z50]),(0,[z0,z1,z2,z3,z7,z51,z6])],[(0,[z0,z1,z2,z3,z26,z6,z52]),(0,[z53,z0,z1,z2,z3,z7,z54]),(0,[z0,z1,z55,z2,z3,z7,z6]),(0,[z0,z27,z56,z2,z3,z7,z6])],[(1,[z0,z1,z57,z3,z7,z6])],[(0,[z58,z0,z59,z2,z3,z7,z6]),(0,[z0,z1,z2,z60,z3,z26,z6]),(0,[z61,z0,z1,z2,z62,z7,z6]),(0,[z0,z1,z2,z63,z3,z7,z6]),(0,[z0,z1,z64,z2,z3,z7,z6]),(0,[z0,z1,z65,z2,z3,z6,z66])],[(0,[z67,z0,z1,z18,z3,z7,z6]),(0,[z0,z1,z2,z3,z68,z5,z6]),(0,[z0,z27,z2,z3,z7,z69,z6]),(0,[z9,z0,z1,z2,z3,z7,z10]),(1,[z0,z1,z70,z2,z3,z6])],[(0,[z0,z71,z1,z2,z3,z7,z6]),(0,[z61,z0,z72,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z73,z6]),(0,[z0,z1,z2,z3,z7,z6,z74])],[(0,[z0,z75,z1,z2,z3,z26,z6]),(0,[z0,z76,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z77,z6])]],
   [[(0,[z0,z1,z2,z78,z3,z7,z6]),(0,[z0,z1,z2,z3,z68,z7,z6]),(0,[z53,z0,z79,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z7,z69,z6]),(0,[z0,z1,z2,z3,z7,z6,z80]),(0,[z0,z1,z81,z2,z3,z7,z6])],[(0,[z82,z1,z2,z3,z68,z7,z6]),(0,[z0,z1,z2,z3,z7,z83,z6])],[(0,[z0,z84,z1,z2,z3,z7,z6]),(0,[z67,z1,z2,z18,z3,z7,z6]),(0,[z85,z0,z1,z2,z86,z7,z6]),(0,[z0,z1,z2,z3,z26,z87,z6]),(0,[z88,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z89,z2,z3,z7,z6])],[(0,[z90,z0,z1,z2,z3,z91,z6]),(0,[z0,z92,z1,z2,z3,z7,z93]),(0,[z0,z79,z1,z2,z3,z7,z10]),(0,[z0,z79,z1,z36,z3,z7,z6]),(1,[z0,z1,z2,z23,z24,z6]),(0,[z0,z1,z2,z3,z7,z6,z94]),(0,[z0,z1,z2,z95,z3,z7,z6]),(0,[z0,z1,z2,z3,z96,z7,z6])],[(0,[z0,z1,z2,z3,z26,z97,z6]),(1,[z0,z1,z2,z3,z98,z6]),(0,[z0,z1,z99,z2,z3,z7,z6]),(0,[z0,z100,z1,z2,z101,z7,z6])],[(0,[z0,z1,z36,z102,z3,z7,z6]),(0,[z0,z1,z2,z3,z103,z5,z6]),(0,[z104,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z105,z6]),(1,[z0,z1,z36,z3,z7,z33])],[(0,[z58,z0,z1,z2,z106,z7,z6]),(0,[z0,z1,z2,z107,z3,z7,z6]),(0,[z1,z2,z37,z3,z68,z7,z6]),(0,[z0,z108,z1,z2,z68,z7,z6]),(0,[z0,z1,z2,z3,z5,z109,z6]),(0,[z0,z1,z2,z3,z26,z110,z6]),(0,[z111,z0,z1,z2,z3,z7,z6]),(0,[z0,z92,z1,z112,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z113,z6]),(0,[z0,z1,z114,z2,z3,z7,z6])],[(0,[z58,z0,z115,z2,z3,z7,z6]),(0,[z90,z59,z1,z2,z3,z7,z6]),(0,[z0,z1,z102,z2,z3,z26,z6]),(0,[z0,z1,z2,z24,z7,z6,z32])]],
   [[(0,[z0,z1,z116,z2,z3,z7,z6]),(0,[z0,z1,z46,z3,z117,z7,z6])],[(0,[z0,z1,z118,z2,z3,z7,z6]),(0,[z0,z1,z119,z2,z3,z7,z6]),(0,[z0,z1,z2,z7,z109,z6,z120])],[(0,[z0,z1,z121,z2,z3,z5,z6]),(1,[z0,z27,z2,z3,z69,z6]),(0,[z0,z1,z2,z3,z122,z7,z6]),(0,[z0,z1,z2,z3,z7,z123,z6]),(0,[z0,z1,z36,z2,z3,z7,z10]),(0,[z124,z0,z1,z2,z3,z7,z6]),(0,[z125,z0,z1,z2,z3,z7,z6]),(0,[z0,z126,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z127,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z128])],[(0,[z129,z0,z1,z2,z3,z7,z6]),(0,[z67,z0,z1,z102,z3,z7,z6]),(0,[z0,z1,z2,z3,z130,z7,z6]),(0,[z61,z0,z1,z2,z3,z7,z54]),(0,[z0,z1,z46,z2,z3,z87,z6]),(0,[z131,z0,z1,z2,z3,z7,z6])],[(0,[z45,z1,z2,z37,z3,z7,z6]),(0,[z132,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z133,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z134,z10]),(0,[z0,z135,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z136])],[(0,[z45,z82,z1,z2,z3,z7,z6]),(0,[z0,z1,z137,z2,z3,z7,z6]),(0,[z0,z1,z121,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z138,z6])],[(0,[z0,z1,z2,z139,z3,z7,z6]),(0,[z0,z1,z2,z3,z5,z140,z6]),(0,[z0,z141,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z142])],[(0,[z143,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z101,z3,z26,z6]),(0,[z0,z1,z2,z144,z3,z7,z6]),(0,[z0,z1,z2,z3,z145,z7,z6]),(0,[z0,z1,z2,z101,z7,z134,z6])]],
   [[],[(0,[z0,z1,z2,z37,z3,z7,z146]),(0,[z0,z1,z147,z2,z3,z7,z6]),(0,[z0,z39,z1,z2,z3,z7,z6]),(1,[z0,z148,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z7,z6,z149])],[(0,[z0,z1,z2,z3,z150,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z151]),(0,[z152,z0,z1,z2,z3,z7,z6])],[(0,[z153,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z154,z2,z3,z26,z6]),(0,[z61,z0,z1,z2,z3,z7,z134]),(0,[z155,z0,z1,z2,z3,z7,z6]),(0,[z0,z108,z1,z89,z2,z7,z6]),(0,[z0,z1,z156,z2,z3,z7,z6])],[(0,[z0,z1,z2,z3,z157,z7,z6]),(0,[z9,z0,z59,z2,z3,z7,z6]),(0,[z158,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z159,z7,z6]),(0,[z0,z1,z160,z2,z3,z7,z6]),(0,[z0,z1,z2,z161,z3,z7,z6])],[(0,[z0,z148,z1,z2,z19,z3,z6]),(0,[z162,z0,z1,z2,z3,z7,z6])],[(0,[z0,z1,z1,z2,z3,z7,z6]),(0,[z0,z163,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z164,z7,z6])],[(0,[z0,z1,z2,z3,z165,z7,z6]),(0,[z61,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z4,z26,z6]),(1,[z0,z1,z2,z3,z7,z166])]],
   [[(0,[z0,z1,z167,z2,z3,z7,z6]),(0,[z168,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z169,z2,z3,z7,z6]),(0,[z0,z1,z170,z2,z3,z7,z6])],[(0,[z0,z1,z2,z3,z7,z7,z6]),(0,[z0,z1,z31,z2,z3,z26,z6]),(1,[z0,z171,z2,z3,z7,z6]),(0,[z53,z0,z1,z36,z2,z3,z7]),(0,[z0,z1,z89,z2,z3,z172,z6])],[(0,[z0,z173,z1,z2,z3,z7,z6]),(0,[z85,z0,z1,z2,z3,z174,z6]),(0,[z0,z1,z2,z3,z7,z174,z6]),(0,[z61,z0,z1,z2,z3,z7,z6])],[(0,[z0,z1,z2,z68,z7,z6,z32]),(1,[z0,z1,z2,z3,z175,z6]),(0,[z0,z1,z2,z176,z3,z7,z6]),(0,[z53,z1,z2,z3,z7,z97,z6]),(0,[z0,z1,z2,z7,z14,z87,z6])],[(1,[z0,z1,z2,z3,z7,z177]),(0,[z0,z1,z2,z3,z178,z7,z6])],[(0,[z0,z1,z2,z3,z179,z7,z6]),(1,[z180,z1,z2,z3,z7,z6])],[(0,[z0,z1,z2,z3,z5,z6,z32]),(0,[z0,z1,z2,z3,z7,z6,z181]),(0,[z0,z1,z182,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z183,z6]),(0,[z0,z27,z1,z2,z3,z7,z40]),(0,[z0,z1,z2,z3,z7,z6,z66]),(1,[z0,z1,z2,z7,z6,z120])],[(0,[z9,z0,z115,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z26,z134,z6]),(0,[z0,z100,z1,z2,z4,z7,z6])]],
   [[(0,[z0,z112,z2,z19,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z184]),(0,[z0,z1,z2,z3,z185,z186,z6]),(0,[z0,z1,z2,z3,z187,z7,z6])],[(0,[z0,z1,z2,z3,z188,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z189]),(0,[z0,z1,z2,z3,z26,z190,z6]),(0,[z0,z1,z2,z3,z7,z6,z191]),(0,[z0,z192,z1,z2,z3,z7,z6])],[(0,[z0,z1,z2,z193,z3,z7,z6])],[(0,[z0,z1,z194,z2,z3,z7,z6]),(1,[z0,z1,z195,z2,z3,z7]),(0,[z0,z1,z2,z196,z3,z5,z6]),(0,[z0,z1,z2,z197,z3,z7,z6]),(0,[z198,z0,z1,z2,z3,z7,z6]),(0,[z199,z0,z1,z2,z3,z7,z6]),(0,[z200,z0,z1,z2,z3,z7,z6])],[(1,[z1,z2,z18,z3,z5,z6]),(0,[z201,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z68,z26,z6]),(0,[z0,z1,z2,z202,z3,z7,z6]),(0,[z0,z1,z2,z3,z203,z7,z6])],[(1,[z0,z1,z2,z3,z91,z6]),(0,[z0,z204,z1,z2,z3,z7,z6]),(0,[z0,z205,z1,z2,z3,z7,z6])],[(0,[z0,z206,z1,z2,z3,z7,z6]),(0,[z0,z1,z89,z2,z3,z26,z6]),(0,[z0,z1,z2,z196,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z207]),(0,[z0,z1,z2,z3,z208,z7,z6])],[(0,[z0,z1,z2,z209,z3,z7,z6]),(0,[z0,z1,z2,z3,z5,z10,z6]),(1,[z0,z1,z2,z210,z7,z6]),(1,[z0,z1,z2,z3,z7,z211]),(0,[z0,z1,z212,z2,z3,z7,z6])]],
   [[(0,[z213,z1,z2,z18,z3,z7,z6])],[(0,[z0,z214,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z37,z7,z6,z32]),(0,[z215,z0,z1,z2,z3,z7,z6])],[(1,[z0,z1,z2,z3,z216,z6]),(0,[z90,z0,z59,z2,z3,z7,z6]),(1,[z0,z1,z2,z3,z7,z146]),(0,[z0,z1,z217,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z218,z6]),(0,[z219,z0,z1,z2,z3,z7,z6])],[(1,[z0,z1,z2,z220,z7,z6]),(0,[z82,z0,z1,z2,z37,z7,z6]),(0,[z221,z0,z1,z2,z3,z7,z6]),(0,[z222,z0,z1,z2,z3,z7,z6]),(0,[z223,z0,z1,z2,z3,z7,z6]),(0,[z0,z100,z1,z121,z2,z7,z6]),(0,[z0,z108,z1,z2,z3,z7,z224]),(0,[z0,z1,z89,z46,z2,z3,z6]),(0,[z0,z225,z1,z2,z3,z7,z6])],[(1,[z0,z1,z2,z226,z7,z6]),(0,[z227,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z228])],[(0,[z0,z1,z2,z229,z7,z109,z6])],[(0,[z0,z1,z2,z210,z19,z7,z6]),(0,[z0,z1,z2,z3,z230,z7,z6]),(0,[z231,z0,z1,z2,z3,z7,z6])],[(1,[z67,z1,z18,z3,z7,z6]),(0,[z0,z232,z1,z2,z3,z7,z6])]],
   [[(0,[z58,z0,z1,z194,z3,z7,z6]),(0,[z45,z0,z1,z2,z68,z7,z6]),(1,[z0,z1,z2,z233,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z234]),(1,[z0,z100,z2,z4,z7,z6]),(0,[z0,z1,z2,z3,z7,z235,z6]),(0,[z0,z1,z2,z3,z7,z172,z6]),(0,[z0,z1,z2,z3,z109,z6,z66])],[(0,[z0,z1,z121,z2,z3,z26,z6]),(0,[z236,z0,z1,z2,z3,z7,z6]),(0,[z0,z75,z1,z2,z7,z6,z32]),(0,[z0,z56,z2,z3,z237,z7,z6]),(0,[z0,z1,z238,z2,z3,z7,z6])],[(0,[z61,z0,z1,z2,z3,z239,z6]),(0,[z61,z0,z1,z2,z3,z98,z6]),(0,[z0,z1,z2,z3,z7,z240,z6]),(0,[z0,z108,z75,z1,z2,z7,z6])],[(0,[z241,z0,z1,z2,z3,z5,z6]),(0,[z0,z242,z1,z2,z3,z7,z6])],[(1,[z0,z1,z2,z3,z243,z6]),(0,[z0,z1,z244,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z245,z6])],[(0,[z90,z0,z115,z2,z3,z7,z6]),(0,[z0,z1,z195,z2,z18,z3,z7]),(0,[z0,z1,z2,z3,z186,z5,z6]),(0,[z246,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z247,z6])],[(0,[z241,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z150,z26,z6]),(0,[z248,z0,z1,z112,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z249,z6])],[(0,[z0,z1,z65,z2,z3,z5,z6]),(0,[z0,z250,z1,z2,z3,z7,z6]),(1,[z0,z1,z251,z3,z7,z6]),(0,[z252,z0,z1,z2,z3,z7,z6]),(0,[z0,z56,z1,z2,z3,z69,z6]),(0,[z0,z1,z2,z253,z3,z7,z6])]],
   [[(0,[z0,z1,z2,z3,z26,z6,z54]),(0,[z254,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z186,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z255])],[(0,[z0,z1,z2,z3,z7,z6,z256]),(0,[z0,z108,z1,z2,z37,z7,z6]),(0,[z0,z1,z257,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z258,z6]),(0,[z0,z1,z2,z3,z7,z259,z6])],[(0,[z0,z92,z1,z2,z3,z5,z6]),(0,[z0,z260,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z261,z3,z7,z6]),(0,[z48,z0,z1,z2,z3,z117,z6]),(0,[z0,z1,z2,z3,z7,z262,z6]),(0,[z0,z1,z2,z23,z3,z24,z6]),(0,[z0,z1,z65,z2,z3,z7,z6]),(1,[z0,z1,z65,z2,z3,z66])],[(0,[z0,z263,z1,z2,z18,z3,z7]),(0,[z0,z75,z1,z121,z2,z7,z6]),(0,[z0,z264,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z265])],[(0,[z241,z1,z2,z3,z7,z5,z6]),(0,[z0,z1,z2,z3,z266,z7,z6])],[(0,[z0,z267,z1,z2,z3,z7,z6]),(0,[z0,z92,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z268,z3,z7,z6]),(0,[z0,z1,z2,z269,z3,z7,z6]),(0,[z0,z56,z1,z2,z3,z237,z6])],[(0,[z0,z1,z2,z270,z3,z7,z6]),(0,[z61,z0,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z7,z271,z6]),(0,[z0,z1,z2,z3,z7,z272,z6]),(0,[z0,z108,z1,z2,z186,z7,z6])],[(0,[z0,z1,z273,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z274])]],
   [[(0,[z0,z1,z2,z3,z7,z275,z6])],[(0,[z82,z0,z1,z2,z3,z276,z6]),(0,[z45,z0,z1,z2,z3,z175,z6]),(0,[z277,z0,z1,z2,z3,z7,z6]),(0,[z48,z0,z1,z2,z23,z3,z6]),(0,[z278,z0,z1,z2,z3,z7,z6])],[(0,[z0,z279,z1,z2,z3,z7,z6]),(0,[z0,z1,z89,z2,z3,z5,z6]),(0,[z0,z92,z1,z19,z3,z7,z6]),(0,[z0,z108,z1,z3,z186,z7,z6]),(0,[z0,z280,z1,z2,z3,z7,z6])],[(0,[z0,z1,z2,z3,z96,z5,z6]),(0,[z0,z1,z2,z3,z281,z7,z6]),(0,[z0,z1,z2,z3,z7,z282,z6]),(0,[z0,z283,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z284,z6]),(0,[z0,z1,z2,z3,z285,z7,z6]),(0,[z286,z0,z1,z2,z3,z7,z6])],[(0,[z0,z1,z2,z287,z3,z7,z6])],[(0,[z0,z1,z2,z3,z86,z7,z6]),(0,[z0,z1,z288,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z289,z7,z6]),(0,[z0,z1,z290,z2,z3,z7,z6]),(0,[z0,z1,z2,z291,z3,z7,z6]),(0,[z0,z1,z292,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z52,z32])],[(0,[z0,z1,z2,z293,z3,z7,z6]),(0,[z0,z1,z2,z294,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z295])],[(0,[z296,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z5,z6,z66]),(0,[z0,z297,z1,z2,z3,z7,z6]),(0,[z0,z1,z298,z2,z3,z7,z6]),(0,[z48,z0,z1,z89,z2,z3,z6]),(1,[z0,z1,z299,z2,z7,z32])]],
   [[(0,[z0,z1,z2,z3,z300,z7,z6]),(1,[z48,z0,z1,z3,z87,z6]),(0,[z0,z1,z2,z3,z7,z301,z6]),(0,[z0,z1,z299,z2,z3,z7,z32]),(0,[z302,z0,z1,z2,z3,z7,z6])],[(0,[z0,z1,z2,z3,z7,z6,z303]),(0,[z0,z304,z1,z2,z3,z7,z6]),(0,[z0,z305,z2,z3,z7,z6,z52]),(0,[z0,z306,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z307,z7,z6]),(0,[z49,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z308,z2,z3,z7,z6]),(0,[z0,z1,z309,z2,z3,z7,z6])],[(0,[z58,z0,z1,z2,z3,z7,z310]),(0,[z0,z1,z2,z196,z3,z26,z6]),(0,[z0,z1,z2,z3,z7,z6,z311]),(0,[z0,z1,z2,z3,z7,z312,z6]),(0,[z0,z79,z1,z2,z3,z7,z255]),(0,[z0,z1,z313,z2,z3,z7,z6])],[(0,[z0,z1,z2,z314,z3,z7,z6]),(0,[z0,z1,z2,z3,z315,z7,z6]),(0,[z0,z1,z2,z3,z7,z10,z32]),(0,[z0,z1,z3,z117,z7,z87,z6]),(0,[z0,z1,z2,z3,z7,z316,z6])],[(0,[z0,z1,z2,z37,z3,z7,z189]),(0,[z0,z1,z2,z3,z26,z317,z6]),(0,[z318,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z319,z7,z6]),(1,[z0,z1,z2,z3,z185,z6]),(0,[z0,z1,z2,z3,z7,z320,z6]),(0,[z0,z1,z2,z321,z3,z7,z6])],[(0,[z0,z322,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z323,z6]),(0,[z0,z214,z1,z2,z3,z26,z6]),(0,[z0,z305,z1,z2,z3,z7,z10])],[(1,[z1,z2,z3,z26,z5,z6]),(0,[z0,z1,z2,z3,z7,z6,z324]),(0,[z0,z1,z2,z3,z7,z325,z6]),(0,[z0,z1,z326,z2,z3,z7,z6])],[(0,[z0,z1,z2,z327,z3,z7,z6]),(0,[z0,z148,z1,z2,z3,z7,z6]),(0,[z0,z2,z3,z7,z10,z6,z52]),(1,[z0,z1,z46,z3,z117,z6])]],
   [[(0,[z0,z0,z1,z2,z3,z5,z6]),(0,[z0,z56,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z328]),(0,[z0,z1,z329,z2,z3,z7,z6]),(0,[z330,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z331,z2,z3,z7,z6])],[(0,[z82,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z332,z7,z6]),(0,[z333,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z299,z2,z7,z6,z32])],[(0,[z334,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z335]),(0,[z213,z1,z2,z3,z26,z7,z6]),(0,[z336,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z337,z6])],[(0,[z0,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z338,z7,z6]),(0,[z0,z339,z1,z2,z3,z7,z6]),(0,[z0,z1,z70,z2,z3,z186,z6]),(0,[z0,z1,z2,z3,z7,z134,z255]),(0,[z0,z1,z2,z101,z24,z7,z6])],[(0,[z0,z1,z2,z3,z7,z6,z340]),(0,[z82,z0,z1,z2,z3,z7,z6]),(0,[z61,z0,z79,z1,z2,z3,z7]),(0,[z0,z1,z341,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z342,z7,z6]),(0,[z0,z1,z2,z3,z7,z343,z6])],[(0,[z0,z1,z344,z2,z3,z7,z6]),(1,[z0,z1,z345,z2,z7,z6]),(0,[z0,z1,z346,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z347,z7,z6])],[(0,[z58,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z348,z2,z3,z7,z6]),(0,[z1,z2,z3,z26,z7,z5,z6]),(0,[z53,z0,z1,z2,z3,z7,z32]),(1,[z0,z92,z112,z3,z7,z6])],[(0,[z0,z1,z2,z3,z7,z349,z6]),(0,[z0,z75,z1,z2,z101,z7,z6]),(0,[z0,z79,z1,z3,z7,z6,z255])]],
   [[(0,[z350,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z351,z3,z7,z6]),(0,[z0,z1,z2,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z352,z6]),(0,[z0,z353,z1,z2,z3,z7,z6])],[(0,[z58,z0,z1,z2,z3,z7,z6]),(0,[z354,z0,z1,z2,z3,z7,z6]),(0,[z85,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z7,z5,z6]),(0,[z9,z0,z2,z3,z7,z10,z6])],[(0,[z0,z1,z355,z2,z3,z7,z6]),(0,[z241,z0,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z19,z3,z5,z6]),(0,[z0,z1,z2,z3,z26,z10,z6]),(0,[z0,z1,z2,z3,z356,z7,z6]),(0,[z0,z1,z357,z2,z3,z7,z6]),(0,[z358,z0,z1,z2,z3,z7,z6])],[(0,[z0,z1,z2,z3,z7,z6,z359]),(0,[z0,z1,z2,z3,z7,z6,z52])],[(0,[z85,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z3,z7,z6]),(0,[z0,z1,z2,z68,z4,z7,z6]),(0,[z0,z1,z2,z3,z186,z26,z6]),(0,[z0,z360,z1,z2,z3,z7,z6]),(0,[z0,z361,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z362])],[(0,[z0,z1,z2,z363,z3,z7,z6]),(0,[z0,z364,z1,z2,z3,z7,z6]),(0,[z0,z365,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z19,z3,z7,z6]),(0,[z0,z2,z196,z3,z4,z7,z6]),(0,[z0,z366,z1,z2,z3,z7,z6])],[(0,[z0,z367,z1,z2,z3,z7,z6]),(0,[z67,z0,z1,z2,z3,z368,z6]),(0,[z0,z1,z2,z3,z20,z7,z6]),(0,[z0,z1,z369,z2,z3,z7,z6]),(0,[z0,z260,z1,z2,z3,z26,z6]),(0,[z0,z1,z65,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z370,z7,z6]),(0,[z0,z1,z2,z3,z7,z371,z6]),(0,[z0,z1,z2,z3,z7,z6,z372]),(0,[z0,z1,z373,z2,z3,z7,z6])],[(0,[z0,z108,z1,z2,z3,z5,z6]),(0,[z0,z1,z374,z2,z3,z7,z6]),(0,[z0,z1,z251,z2,z3,z7,z6]),(0,[z0,z1,z2,z23,z3,z172,z6]),(0,[z0,z1,z2,z375,z3,z7,z6]),(0,[z0,z1,z2,z376,z3,z7,z6])]],
   [[(0,[z377,z0,z1,z2,z3,z7,z6]),(0,[z61,z1,z2,z3,z7,z6,z54])],[(0,[z0,z92,z1,z2,z3,z26,z6]),(0,[z378,z0,z1,z2,z3,z7,z6]),(1,[z0,z1,z2,z101,z7,z134])],[(0,[z379,z0,z1,z2,z3,z7,z6]),(0,[z85,z1,z2,z3,z7,z5,z6]),(0,[z0,z108,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z380,z3,z7,z6]),(0,[z381,z0,z1,z2,z3,z7,z6])],[(0,[z0,z1,z102,z60,z3,z7,z6]),(0,[z45,z0,z1,z2,z37,z7,z6]),(0,[z0,z1,z2,z101,z60,z7,z6]),(0,[z0,z1,z2,z3,z7,z87,z6])],[(0,[z0,z1,z2,z3,z7,z382,z6]),(0,[z0,z1,z2,z3,z383,z7,z6]),(0,[z384,z0,z1,z2,z3,z7,z6])],[(0,[z90,z0,z1,z2,z3,z385,z6]),(0,[z0,z1,z2,z3,z7,z6,z386]),(0,[z0,z387,z1,z2,z3,z7,z6]),(1,[z0,z1,z2,z3,z7,z189]),(0,[z0,z1,z2,z3,z7,z6,z388]),(0,[z0,z1,z2,z3,z7,z6,z6]),(0,[z0,z100,z2,z3,z4,z7,z6]),(0,[z0,z1,z389,z2,z3,z7,z6])],[(0,[z390,z0,z1,z2,z3,z7,z6]),(1,[z49,z1,z2,z3,z7,z6]),(0,[z391,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z392,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z393,z6])],[(0,[z0,z1,z2,z3,z7,z394,z6]),(0,[z0,z1,z2,z3,z395,z7,z6]),(0,[z0,z1,z2,z3,z7,z110,z6]),(0,[z61,z0,z1,z2,z3,z7,z32]),(0,[z396,z0,z1,z2,z3,z7,z6]),(0,[z9,z0,z1,z2,z3,z7,z52]),(0,[z0,z397,z1,z2,z3,z7,z6])]],
   [[(0,[z0,z1,z398,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z98,z7,z6]),(0,[z0,z1,z2,z3,z399,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z400])],[(0,[z401,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z402,z7,z6]),(0,[z0,z1,z2,z3,z7,z109,z10]),(1,[z0,z108,z1,z186,z7,z6])],[(0,[z59,z1,z115,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z403]),(0,[z0,z1,z2,z37,z4,z7,z6]),(0,[z248,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z96,z26,z6]),(0,[z48,z0,z1,z46,z3,z7,z6]),(0,[z0,z404,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z405]),(0,[z0,z1,z406,z2,z3,z7,z6])],[(0,[z407,z0,z1,z2,z3,z7,z6]),(0,[z408,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z409,z3,z7,z6])],[(0,[z0,z1,z2,z3,z5,z69,z6]),(0,[z401,z0,z1,z2,z3,z7,z6]),(0,[z61,z0,z1,z57,z3,z7,z6]),(0,[z0,z410,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z411,z6]),(0,[z0,z1,z2,z3,z7,z6,z412])],[(0,[z61,z0,z1,z36,z2,z3,z7]),(0,[z248,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z413]),(0,[z0,z1,z2,z3,z7,z6,z414]),(0,[z0,z79,z1,z2,z3,z7,z52])],[(0,[z0,z1,z18,z60,z3,z7,z6]),(0,[z9,z0,z1,z2,z3,z5,z6]),(0,[z0,z108,z100,z1,z2,z7,z6]),(0,[z0,z1,z2,z3,z7,z52,z66]),(0,[z0,z415,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z416,z7,z6])],[(0,[z0,z417,z1,z2,z3,z7,z6]),(0,[z0,z72,z1,z2,z3,z7,z6]),(1,[z0,z1,z2,z3,z7,z93]),(0,[z0,z1,z2,z418,z3,z7,z6]),(0,[z0,z1,z419,z2,z3,z7,z6]),(0,[z0,z1,z65,z2,z3,z96,z6]),(1,[z0,z1,z2,z229,z7,z6])]],
   [[(0,[z0,z1,z2,z220,z3,z7,z6]),(0,[z0,z1,z2,z3,z420,z5,z6]),(0,[z0,z1,z421,z2,z3,z7,z6])],[(0,[z0,z422,z1,z2,z3,z7,z6]),(0,[z67,z85,z1,z2,z3,z7,z6]),(0,[z0,z1,z423,z2,z3,z7,z6]),(0,[z9,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z60,z7,z6,z32]),(0,[z0,z424,z1,z2,z3,z7,z6]),(1,[z0,z1,z89,z2,z172,z6])],[(0,[z0,z1,z2,z3,z7,z425,z6]),(0,[z0,z1,z2,z3,z7,z146,z6]),(0,[z248,z0,z1,z19,z3,z7,z6]),(0,[z0,z75,z1,z2,z4,z7,z6]),(1,[z0,z1,z2,z3,z7,z224]),(0,[z0,z1,z2,z3,z7,z426,z6]),(0,[z0,z1,z2,z3,z7,z6,z427])],[(0,[z0,z1,z2,z3,z428,z7,z6]),(0,[z0,z1,z2,z3,z420,z7,z6])],[(0,[z0,z79,z1,z2,z3,z5,z6]),(0,[z0,z56,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z7,z239,z6]),(0,[z0,z1,z2,z3,z7,z429,z6]),(0,[z0,z1,z2,z3,z7,z10,z66])],[(0,[z430,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z431,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z432,z7,z6]),(0,[z61,z53,z1,z2,z3,z7,z6]),(0,[z433,z0,z1,z2,z3,z7,z6]),(0,[z434,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z435,z3,z7,z6]),(0,[z0,z1,z121,z2,z24,z7,z6]),(0,[z0,z436,z1,z2,z3,z7,z6]),(0,[z437,z0,z1,z2,z3,z7,z6])],[(1,[z0,z263,z1,z2,z3,z7]),(0,[z0,z1,z2,z3,z7,z134,z52]),(0,[z0,z1,z2,z3,z7,z255,z32])],[(0,[z0,z1,z438,z2,z3,z5,z6]),(0,[z0,z0,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z338,z26,z6]),(0,[z0,z1,z2,z3,z7,z6,z439]),(0,[z0,z79,z1,z2,z3,z7,z6]),(0,[z0,z1,z299,z2,z101,z7,z6])]],
   [[(0,[z82,z0,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z440,z5,z6]),(0,[z0,z1,z2,z3,z7,z441,z6])],[(0,[z442,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z443,z3,z7,z6]),(0,[z0,z1,z2,z3,z444,z7,z6]),(0,[z0,z56,z1,z46,z2,z3,z6]),(0,[z0,z1,z2,z3,z7,z224,z6]),(0,[z0,z1,z2,z3,z7,z445,z6])],[(0,[z0,z1,z438,z2,z3,z7,z6]),(0,[z446,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z447,z7,z6])],[(0,[z0,z1,z2,z3,z7,z448,z6]),(0,[z0,z1,z2,z3,z7,z449,z6]),(0,[z0,z1,z2,z3,z5,z6,z335]),(0,[z0,z1,z2,z3,z440,z7,z6]),(0,[z0,z450,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z101,z3,z7,z32]),(0,[z0,z1,z2,z451,z3,z7,z6]),(0,[z0,z452,z1,z2,z3,z7,z6])],[(0,[z0,z1,z2,z3,z7,z453,z6]),(0,[z454,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z112,z2,z3,z5,z6]),(0,[z48,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z26,z109,z6]),(1,[z61,z1,z2,z3,z7,z54]),(0,[z0,z1,z2,z3,z7,z455,z6]),(0,[z0,z456,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z457,z7,z6]),(0,[z0,z27,z1,z2,z3,z7,z458]),(0,[z0,z1,z459,z2,z3,z7,z6])],[(0,[z58,z0,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z460,z7,z6]),(0,[z0,z1,z2,z3,z461,z7,z6]),(0,[z0,z1,z2,z3,z26,z462,z6]),(0,[z0,z39,z1,z2,z19,z7,z6])],[(0,[z0,z1,z2,z3,z463,z7,z6]),(0,[z464,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z465,z7,z6]),(0,[z0,z100,z1,z2,z196,z7,z6]),(0,[z0,z1,z2,z3,z466,z7,z6]),(0,[z0,z1,z65,z2,z3,z7,z109])],[(0,[z0,z1,z2,z3,z7,z467,z6]),(0,[z0,z1,z2,z468,z3,z7,z6]),(0,[z0,z1,z112,z2,z3,z7,z6]),(0,[z48,z0,z1,z2,z3,z7,z6])]],
   [[(0,[z85,z0,z1,z2,z3,z26,z6]),(0,[z0,z1,z469,z2,z3,z7,z6]),(0,[z0,z100,z1,z2,z3,z7,z249]),(0,[z470,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z3,z7,z33,z6,z255]),(0,[z0,z1,z2,z3,z7,z134,z6])],[(0,[z0,z1,z2,z19,z3,z26,z6]),(0,[z0,z1,z2,z471,z3,z7,z6]),(0,[z0,z1,z472,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z473,z7,z6]),(0,[z0,z1,z2,z3,z7,z474,z6]),(0,[z0,z1,z2,z3,z7,z475,z6])],[(0,[z0,z1,z2,z3,z5,z5,z6])],[(1,[z0,z1,z2,z3,z368,z6]),(0,[z0,z1,z374,z2,z3,z26,z6]),(0,[z0,z1,z46,z2,z23,z3,z6])],[(0,[z0,z1,z2,z3,z7,z476,z6]),(0,[z0,z1,z2,z3,z7,z477,z6]),(0,[z0,z1,z478,z2,z3,z7,z6]),(0,[z0,z180,z1,z2,z3,z7,z6])],[(0,[z0,z100,z1,z2,z3,z5,z6]),(0,[z0,z1,z121,z2,z60,z7,z6]),(0,[z0,z1,z2,z479,z3,z7,z6]),(0,[z0,z1,z2,z24,z7,z172,z6])],[(0,[z480,z0,z1,z2,z3,z7,z6]),(0,[z0,z108,z1,z2,z3,z26,z6]),(0,[z0,z1,z171,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z481,z6]),(0,[z0,z482,z1,z2,z3,z7,z6])],[(0,[z90,z0,z1,z2,z3,z7,z6]),(1,[z0,z1,z2,z3,z385,z6]),(0,[z0,z1,z2,z483,z3,z7,z6]),(0,[z0,z1,z2,z196,z68,z7,z6]),(1,[z0,z1,z2,z435,z7,z6])]],
   [[(0,[z0,z1,z2,z3,z7,z6,z484]),(0,[z0,z1,z2,z23,z3,z5,z6]),(0,[z0,z1,z485,z2,z3,z7,z6]),(0,[z0,z100,z1,z2,z3,z7,z6]),(0,[z0,z75,z100,z2,z3,z7,z6]),(0,[z486,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z487,z7,z6]),(0,[z0,z488,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z489,z7,z6])],[(0,[z0,z1,z2,z3,z7,z177,z6]),(0,[z1,z102,z2,z18,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z490,z6]),(0,[z45,z0,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z237,z7,z69,z6]),(0,[z0,z79,z1,z2,z416,z7,z6])],[(0,[z61,z0,z171,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z491,z7,z6]),(0,[z0,z1,z2,z3,z492,z7,z6]),(0,[z48,z0,z1,z3,z7,z87,z6]),(0,[z0,z79,z1,z2,z3,z7,z33]),(0,[z0,z1,z2,z3,z96,z7,z109])],[(0,[z0,z1,z2,z18,z3,z5,z6]),(1,[z82,z1,z2,z68,z7,z6]),(1,[z0,z1,z2,z62,z7,z6]),(0,[z0,z1,z2,z3,z7,z493,z6]),(0,[z0,z1,z2,z23,z3,z7,z6])],[(0,[z45,z0,z1,z2,z3,z7,z6]),(0,[z494,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z495,z2,z3,z7,z6])],[(0,[z0,z59,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z382,z6]),(1,[z0,z72,z2,z3,z7,z6]),(0,[z0,z1,z121,z60,z3,z7,z6])],[(0,[z0,z1,z2,z496,z3,z7,z6]),(0,[z497,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z18,z3,z7,z6]),(1,[z0,z1,z2,z3,z73,z6]),(0,[z498,z0,z1,z2,z3,z7,z6])],[(0,[z58,z0,z1,z496,z3,z7,z6]),(0,[z499,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z101,z68,z7,z6])]],
   [[(0,[z0,z59,z1,z2,z3,z7,z6]),(0,[z0,z1,z500,z2,z3,z7,z6]),(0,[z0,z56,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z501,z3,z7,z6])],[(0,[z248,z0,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z502,z3,z7,z6]),(0,[z0,z1,z36,z2,z3,z7,z33])],[(0,[z85,z0,z1,z18,z3,z7,z6]),(1,[z0,z1,z2,z86,z7,z6]),(0,[z0,z1,z503,z2,z3,z7,z6]),(0,[z0,z1,z504,z2,z3,z7,z6]),(0,[z0,z505,z1,z2,z3,z7,z6]),(0,[z0,z1,z345,z2,z3,z7,z6])],[(1,[z85,z1,z2,z3,z5,z6]),(0,[z0,z506,z1,z2,z3,z7,z6]),(1,[z0,z1,z2,z7,z6,z295]),(0,[z0,z108,z1,z2,z3,z7,z507]),(0,[z0,z1,z2,z3,z7,z134,z33])],[(0,[z508,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z26,z6,z32]),(0,[z248,z0,z92,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z509,z6]),(0,[z0,z1,z2,z3,z510,z7,z6]),(0,[z0,z1,z36,z2,z3,z7,z255])],[(0,[z0,z1,z2,z3,z7,z91,z6]),(0,[z9,z0,z1,z2,z3,z26,z6])],[(1,[z0,z1,z2,z3,z276,z6]),(1,[z0,z75,z2,z196,z7,z6]),(0,[z0,z1,z2,z3,z7,z511,z6]),(0,[z0,z1,z2,z3,z7,z6,z507])],[(0,[z0,z1,z2,z3,z7,z512,z6]),(0,[z213,z85,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z513])]],
   [[(0,[z0,z108,z1,z18,z3,z7,z6]),(0,[z0,z1,z2,z514,z3,z7,z6]),(0,[z0,z515,z1,z2,z3,z7,z6]),(1,[z0,z1,z2,z3,z7,z458]),(0,[z0,z1,z2,z516,z3,z7,z6])],[(0,[z58,z0,z1,z2,z226,z7,z6]),(1,[z0,z1,z2,z106,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z310]),(0,[z0,z1,z2,z3,z7,z6,z517]),(0,[z430,z0,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z7,z6,z54]),(0,[z0,z1,z2,z518,z3,z7,z6]),(0,[z519,z0,z1,z2,z3,z7,z6]),(0,[z0,z520,z1,z2,z3,z7,z6]),(0,[z0,z1,z345,z2,z7,z87,z6])],[(0,[z0,z1,z2,z3,z7,z33,z6])],[(0,[z85,z0,z1,z2,z220,z7,z6]),(0,[z0,z79,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z7,z521,z6]),(0,[z0,z1,z522,z2,z3,z7,z6]),(0,[z0,z1,z89,z2,z7,z6,z32]),(0,[z0,z1,z2,z523,z3,z7,z6])],[(0,[z0,z1,z2,z3,z117,z5,z6]),(0,[z0,z1,z2,z3,z5,z172,z6]),(0,[z0,z1,z2,z524,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z525]),(0,[z0,z1,z2,z3,z526,z7,z6])],[(0,[z527,z0,z1,z2,z3,z7,z6]),(1,[z0,z1,z121,z60,z7,z6]),(0,[z0,z1,z528,z2,z3,z7,z6]),(0,[z0,z1,z529,z2,z3,z7,z6])],[(0,[z0,z530,z1,z2,z3,z7,z6]),(0,[z0,z1,z531,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z97,z52]),(0,[z0,z1,z2,z3,z7,z532,z6])],[(0,[z58,z0,z1,z2,z3,z533,z6]),(0,[z534,z0,z1,z2,z3,z7,z6]),(0,[z535,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z26,z69,z6]),(0,[z0,z1,z536,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z117,z7,z6])]],
   [[(0,[z85,z0,z1,z102,z3,z7,z6]),(0,[z0,z1,z2,z537,z3,z7,z6])],[(0,[z0,z1,z2,z3,z538,z7,z6]),(0,[z61,z0,z1,z2,z233,z7,z6]),(1,[z0,z1,z2,z3,z7,z249])],[(0,[z539,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z140,z6]),(0,[z0,z1,z2,z21,z3,z7,z6]),(0,[z0,z1,z2,z3,z463,z26,z6]),(0,[z0,z1,z2,z3,z7,z10,z97]),(0,[z0,z1,z2,z3,z7,z93,z6])],[(0,[z0,z1,z112,z2,z3,z26,z6]),(0,[z48,z0,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z7,z540,z6])],[(0,[z0,z1,z2,z3,z7,z243,z6]),(0,[z0,z1,z2,z3,z5,z6,z255]),(0,[z0,z541,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z542,z3,z7,z6]),(0,[z0,z543,z1,z2,z3,z7,z6])],[(0,[z0,z1,z2,z3,z7,z544,z6]),(0,[z0,z1,z89,z121,z2,z7,z6]),(0,[z545,z0,z1,z2,z3,z7,z6])],[(0,[z85,z0,z1,z2,z3,z20,z6]),(0,[z0,z108,z1,z102,z3,z7,z6]),(0,[z0,z546,z1,z2,z3,z7,z6]),(1,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z7,z6,z547]),(0,[z0,z92,z112,z2,z3,z7,z6])],[(0,[z213,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z7,z548,z6])]],
   [[(1,[z241,z1,z2,z3,z5,z6]),(0,[z61,z0,z1,z251,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z97,z6]),(1,[z53,z1,z2,z3,z7,z97]),(0,[z0,z1,z549,z2,z3,z7,z6])],[(1,[z0,z1,z2,z3,z7,z6])],[(1,[z0,z1,z2,z3,z174,z6]),(0,[z213,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z57,z3,z7,z6])],[(0,[z0,z1,z550,z2,z3,z7,z6]),(0,[z53,z0,z1,z2,z3,z73,z6]),(0,[z0,z92,z1,z2,z3,z7,z166]),(0,[z9,z0,z305,z2,z3,z7,z6])],[(0,[z0,z1,z102,z112,z3,z7,z6]),(0,[z213,z241,z1,z2,z3,z7,z6]),(0,[z0,z551,z1,z2,z3,z5,z6]),(0,[z0,z100,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z7,z458,z6]),(0,[z0,z79,z1,z2,z16,z7,z6]),(1,[z0,z79,z1,z3,z7,z255])],[(0,[z0,z1,z2,z3,z276,z7,z6]),(0,[z0,z1,z2,z3,z7,z317,z6]),(0,[z53,z0,z1,z2,z3,z7,z97]),(0,[z0,z1,z2,z3,z552,z7,z6]),(0,[z0,z1,z89,z2,z23,z7,z6])],[(0,[z0,z1,z2,z62,z3,z7,z6]),(0,[z0,z1,z2,z3,z553,z7,z6])],[(0,[z0,z551,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z23,z3,z26,z6]),(0,[z0,z1,z2,z3,z7,z554,z6])]],
   [[(0,[z0,z1,z2,z555,z3,z7,z6]),(0,[z45,z0,z1,z500,z3,z7,z6]),(0,[z45,z0,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z556,z3,z7,z6]),(0,[z48,z180,z1,z2,z3,z7,z6]),(0,[z0,z1,z65,z2,z3,z7,z66])],[(0,[z0,z1,z121,z2,z68,z7,z6]),(0,[z0,z422,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z237,z5,z6]),(0,[z0,z557,z1,z2,z3,z7,z6]),(0,[z0,z1,z89,z2,z3,z24,z6]),(0,[z0,z1,z299,z2,z3,z7,z134]),(0,[z0,z1,z2,z3,z7,z6,z558])],[(0,[z0,z559,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z18,z3,z26,z6]),(0,[z0,z1,z2,z3,z560,z7,z6]),(0,[z0,z1,z561,z2,z3,z7,z6]),(0,[z0,z562,z1,z2,z3,z7,z6])],[(0,[z0,z1,z2,z3,z563,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z40]),(0,[z0,z1,z2,z3,z7,z564,z6])],[(0,[z0,z59,z1,z2,z3,z26,z6]),(0,[z0,z1,z565,z2,z3,z7,z6]),(0,[z248,z0,z2,z19,z3,z7,z6]),(0,[z0,z1,z2,z3,z237,z7,z6]),(0,[z566,z0,z1,z2,z3,z7,z6])],[(0,[z0,z1,z112,z18,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z567]),(0,[z82,z0,z1,z2,z68,z7,z6]),(0,[z0,z1,z2,z3,z26,z5,z6]),(0,[z0,z1,z2,z3,z432,z5,z6]),(0,[z0,z1,z299,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z402,z6]),(0,[z0,z1,z2,z3,z568,z7,z6]),(0,[z569,z0,z1,z2,z3,z7,z6]),(0,[z570,z0,z1,z2,z3,z7,z6])],[(0,[z0,z1,z2,z106,z3,z7,z6]),(0,[z0,z1,z2,z3,z368,z7,z6]),(0,[z0,z1,z2,z3,z7,z571,z6]),(0,[z0,z1,z2,z3,z26,z117,z6])],[(0,[z0,z27,z1,z2,z3,z69,z6]),(0,[z0,z305,z1,z2,z3,z7,z52]),(0,[z0,z1,z36,z2,z3,z7,z52])]],
   [[(0,[z0,z1,z2,z572,z3,z7,z6]),(0,[z0,z1,z2,z3,z26,z7,z6]),(0,[z0,z1,z2,z186,z7,z6,z32]),(0,[z0,z1,z299,z2,z3,z7,z6])],[(0,[z0,z573,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z574,z7,z6]),(0,[z0,z575,z1,z2,z3,z7,z6])],[(0,[z1,z2,z18,z3,z7,z5,z6]),(0,[z0,z1,z2,z196,z37,z7,z6]),(0,[z0,z1,z2,z3,z576,z7,z6]),(0,[z0,z1,z577,z2,z3,z7,z6]),(0,[z0,z1,z578,z2,z3,z7,z6]),(0,[z0,z579,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z580])],[(0,[z0,z1,z2,z3,z7,z10,z6]),(0,[z0,z1,z2,z3,z7,z6,z581]),(1,[z0,z1,z2,z416,z7,z6]),(0,[z0,z1,z582,z2,z3,z7,z6])],[(0,[z0,z1,z2,z514,z3,z26,z6]),(0,[z0,z1,z583,z2,z3,z7,z6]),(0,[z584,z0,z1,z2,z3,z7,z6]),(0,[z585,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z96,z7,z66])],[(0,[z586,z0,z1,z2,z3,z7,z6]),(0,[z587,z0,z1,z2,z3,z7,z6]),(0,[z588,z0,z1,z2,z3,z7,z6]),(0,[z589,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z26,z6,z181]),(0,[z0,z1,z2,z3,z26,z6,z66]),(0,[z0,z27,z1,z2,z3,z237,z6])],[(0,[z0,z305,z1,z2,z3,z5,z6]),(0,[z0,z1,z36,z2,z3,z5,z6]),(0,[z0,z1,z46,z2,z3,z5,z6]),(0,[z61,z0,z1,z2,z3,z7,z97]),(0,[z0,z1,z590,z2,z3,z7,z6]),(0,[z0,z1,z2,z591,z3,z7,z6])],[(0,[z0,z1,z2,z592,z3,z7,z6]),(0,[z53,z0,z1,z2,z3,z7,z134]),(0,[z0,z1,z593,z2,z3,z7,z6]),(0,[z0,z1,z46,z2,z3,z117,z6]),(0,[z0,z1,z2,z7,z134,z6,z32]),(0,[z0,z1,z2,z594,z3,z7,z6])]],
   [[(0,[z0,z1,z2,z3,z7,z595,z6]),(1,[z0,z56,z2,z3,z237,z6]),(0,[z0,z1,z2,z3,z7,z596,z6]),(0,[z0,z1,z36,z3,z7,z33,z6])],[(0,[z0,z1,z115,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z24,z5,z6]),(1,[z0,z1,z2,z3,z239,z6]),(0,[z0,z1,z2,z3,z7,z597,z6]),(0,[z0,z1,z2,z598,z3,z7,z6]),(0,[z0,z305,z1,z2,z3,z7,z6]),(0,[z0,z1,z46,z2,z3,z7,z6]),(0,[z0,z1,z36,z2,z3,z7,z6]),(0,[z0,z1,z89,z2,z101,z7,z6]),(0,[z0,z1,z2,z3,z7,z599,z6])],[(0,[z0,z1,z2,z101,z37,z7,z6]),(0,[z0,z1,z2,z3,z5,z6,z54]),(0,[z0,z1,z2,z3,z7,z600,z6]),(0,[z0,z1,z2,z210,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z601,z6]),(0,[z0,z1,z2,z3,z602,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z603])],[(1,[z0,z1,z194,z3,z7,z6]),(0,[z0,z604,z1,z2,z3,z7,z6]),(0,[z67,z0,z1,z2,z3,z352,z6]),(0,[z0,z1,z102,z3,z7,z6,z255]),(0,[z45,z0,z1,z2,z3,z395,z6]),(0,[z53,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z33,z6]),(0,[z605,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z606,z7,z6]),(0,[z0,z100,z1,z2,z3,z7,z211]),(0,[z0,z607,z1,z2,z3,z7,z6])],[(0,[z0,z1,z115,z2,z3,z7,z6]),(0,[z67,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z195,z2,z3,z7,z6]),(0,[z0,z608,z1,z2,z3,z7,z6]),(0,[z0,z1,z60,z3,z186,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z609]),(0,[z0,z1,z2,z3,z24,z7,z6])],[(0,[z0,z1,z2,z3,z7,z6,z610]),(0,[z0,z1,z2,z3,z7,z611,z6]),(1,[z213,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z538,z26,z6]),(0,[z0,z1,z2,z3,z7,z190,z6]),(0,[z0,z1,z2,z3,z7,z6,z612])],[(1,[z90,z59,z2,z3,z7,z6]),(0,[z53,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z613])],[(0,[z90,z0,z1,z2,z3,z5,z6]),(0,[z67,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z5,z6,z52]),(0,[z0,z1,z2,z7,z10,z6,z295]),(0,[z0,z1,z2,z101,z186,z7,z6]),(0,[z0,z1,z2,z3,z96,z109,z6])]],
   [[(0,[z614,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z615,z2,z3,z7,z6]),(0,[z0,z1,z616,z2,z3,z7,z6])],[(0,[z0,z1,z2,z617,z3,z5,z6]),(0,[z0,z1,z2,z3,z618,z7,z6]),(0,[z0,z619,z1,z2,z3,z7,z6]),(0,[z48,z0,z1,z2,z3,z87,z6]),(0,[z0,z1,z2,z3,z7,z620,z6])],[(0,[z58,z1,z115,z2,z3,z7,z6]),(0,[z0,z263,z1,z2,z3,z7,z6]),(0,[z0,z108,z1,z2,z24,z7,z6])],[(0,[z0,z1,z621,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z622,z6]),(0,[z0,z1,z2,z3,z623,z7,z6])],[(0,[z58,z0,z1,z2,z3,z7,z177]),(0,[z0,z1,z2,z624,z3,z7,z6]),(0,[z0,z1,z2,z617,z3,z7,z6]),(0,[z625,z0,z1,z2,z3,z7,z6])],[(1,[z0,z1,z500,z3,z7,z6]),(0,[z0,z1,z2,z626,z3,z7,z6]),(1,[z0,z1,z2,z3,z26,z6]),(0,[z25,z0,z1,z2,z3,z5,z6]),(0,[z0,z27,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z627,z3,z7,z6]),(0,[z628,z0,z1,z2,z3,z7,z6])],[(0,[z629,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z18,z3,z7,z6,z255]),(0,[z0,z1,z2,z3,z7,z175,z6]),(0,[z213,z0,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z7,z630,z6])],[(0,[z0,z1,z2,z3,z5,z87,z6]),(0,[z0,z1,z2,z3,z26,z172,z6]),(0,[z0,z1,z2,z3,z7,z6,z631]),(0,[z0,z1,z2,z3,z632,z7,z6])]],
   [[(0,[z25,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z37,z3,z5,z6]),(0,[z0,z27,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z633]),(0,[z0,z1,z2,z3,z7,z634,z6])],[(0,[z0,z1,z2,z3,z5,z97,z6]),(0,[z0,z1,z635,z2,z3,z5,z6]),(0,[z0,z636,z1,z2,z3,z7,z6]),(0,[z0,z75,z1,z2,z196,z7,z6]),(0,[z0,z1,z2,z637,z3,z7,z6]),(0,[z0,z1,z2,z638,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z639,z6]),(0,[z640,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z120])],[(0,[z53,z0,z1,z2,z3,z402,z6]),(0,[z0,z1,z2,z3,z641,z7,z6]),(0,[z0,z1,z2,z642,z3,z7,z6])],[(0,[z58,z90,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z37,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z166]),(0,[z0,z1,z643,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z109,z52]),(0,[z0,z1,z2,z3,z7,z644,z6]),(0,[z0,z1,z2,z645,z3,z7,z6]),(0,[z0,z646,z1,z2,z3,z7,z6])],[(0,[z0,z1,z635,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z647,z7,z6]),(0,[z0,z1,z648,z2,z3,z7,z6]),(0,[z0,z1,z2,z435,z7,z10,z6])],[(0,[z0,z59,z2,z3,z7,z6,z52]),(0,[z649,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z60,z3,z5,z6]),(0,[z0,z1,z2,z3,z7,z103,z6]),(0,[z0,z1,z2,z144,z19,z3,z6]),(0,[z650,z0,z1,z2,z3,z7,z6])],[(0,[z651,z0,z1,z2,z3,z7,z6]),(0,[z652,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z653,z3,z7,z6]),(0,[z45,z0,z1,z21,z3,z7,z6]),(0,[z0,z654,z1,z2,z3,z7,z6]),(0,[z0,z1,z89,z2,z7,z172,z6]),(0,[z0,z1,z2,z3,z7,z655,z6])],[(1,[z58,z115,z2,z3,z7,z6]),(0,[z0,z656,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z26,z6,z255]),(0,[z0,z1,z2,z3,z657,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z658])]],
   [[(0,[z0,z75,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z237,z26,z6]),(0,[z0,z1,z2,z60,z3,z7,z6])],[(1,[z0,z305,z2,z3,z7,z52])],[(0,[z58,z0,z1,z2,z3,z216,z6]),(0,[z0,z1,z2,z3,z7,z659,z6]),(0,[z660,z0,z1,z2,z3,z7,z6]),(1,[z85,z1,z102,z3,z7,z6]),(0,[z0,z108,z1,z2,z60,z7,z6]),(1,[z0,z1,z2,z3,z7,z507])],[(0,[z661,z0,z1,z2,z3,z7,z6]),(0,[z0,z115,z2,z3,z7,z6,z52]),(0,[z662,z0,z1,z2,z3,z7,z6]),(0,[z663,z0,z1,z2,z3,z7,z6]),(0,[z0,z75,z1,z2,z3,z7,z6]),(0,[z664,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z665,z3,z7,z6])],[(0,[z0,z1,z2,z3,z26,z26,z6]),(0,[z0,z1,z299,z2,z3,z26,z6]),(0,[z0,z1,z666,z2,z3,z7,z6]),(1,[z0,z1,z2,z144,z3,z6]),(0,[z48,z0,z56,z1,z2,z3,z6]),(0,[z667,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z668])],[(0,[z0,z1,z2,z3,z7,z216,z6]),(1,[z0,z1,z2,z3,z7,z310]),(0,[z0,z1,z669,z2,z3,z7,z6]),(0,[z0,z670,z1,z2,z3,z7,z6]),(0,[z0,z1,z671,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z109,z6])],[(0,[z672,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z673,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z462,z6]),(0,[z0,z100,z1,z2,z7,z6,z32]),(0,[z0,z1,z674,z2,z3,z7,z6]),(0,[z0,z108,z1,z121,z3,z7,z6]),(0,[z0,z1,z70,z2,z3,z7,z6]),(0,[z0,z1,z2,z675,z3,z7,z6]),(0,[z0,z676,z1,z2,z3,z7,z6]),(1,[z0,z1,z2,z16,z7,z6]),(0,[z0,z1,z2,z3,z677,z7,z6]),(0,[z0,z1,z2,z3,z7,z678,z6])],[(1,[z0,z1,z496,z3,z7,z6]),(0,[z0,z1,z2,z3,z226,z7,z6]),(0,[z0,z1,z2,z3,z679,z7,z6]),(0,[z82,z0,z1,z2,z3,z243,z6]),(0,[z0,z1,z680,z2,z3,z7,z6])]],
   [[(0,[z0,z1,z102,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z395,z6]),(0,[z0,z1,z2,z681,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z682,z6]),(0,[z0,z1,z2,z3,z7,z6,z683]),(0,[z0,z684,z1,z2,z3,z7,z6])],[],[],[(0,[z0,z1,z2,z3,z385,z7,z6]),(0,[z0,z1,z102,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z233,z7,z6]),(0,[z0,z685,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z6,z211])],[(0,[z0,z1,z121,z2,z37,z7,z6]),(0,[z1,z2,z3,z7,z97,z6,z54]),(0,[z0,z1,z2,z101,z3,z7,z134])],[(0,[z0,z305,z1,z2,z3,z26,z6]),(0,[z0,z1,z36,z2,z3,z26,z6]),(0,[z0,z1,z46,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z686,z7,z6])],[(0,[z0,z1,z2,z3,z7,z687,z6])],[(0,[z0,z1,z2,z3,z688,z7,z6]),(0,[z0,z1,z2,z3,z7,z33,z32]),(0,[z0,z1,z689,z2,z3,z7,z6])]],
   [[(0,[z0,z1,z115,z2,z3,z26,z6]),(1,[z0,z1,z2,z3,z352,z6]),(0,[z0,z1,z102,z19,z3,z7,z6]),(0,[z0,z1,z2,z3,z5,z453,z6]),(0,[z0,z1,z2,z101,z3,z5,z6]),(0,[z0,z1,z690,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z24,z26,z6]),(0,[z0,z1,z2,z691,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z14,z6]),(0,[z0,z1,z2,z3,z7,z6,z692])],[(0,[z0,z1,z693,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z52,z54]),(0,[z48,z0,z27,z1,z2,z3,z6]),(0,[z694,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z121,z2,z186,z7,z6]),(0,[z0,z695,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z696,z7,z6])],[(0,[z53,z0,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z7,z697,z6])],[(0,[z67,z0,z1,z2,z3,z26,z6]),(0,[z698,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z690,z2,z3,z7,z6]),(0,[z0,z75,z2,z196,z3,z7,z6]),(0,[z0,z1,z2,z101,z3,z7,z6])],[(0,[z699,z0,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z700,z3,z7,z6]),(0,[z85,z1,z102,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z5,z134,z6]),(0,[z0,z1,z2,z3,z7,z701,z6])],[(1,[z248,z0,z19,z3,z7,z6]),(0,[z0,z702,z1,z2,z3,z7,z6]),(0,[z703,z0,z1,z2,z3,z7,z6])],[(0,[z0,z1,z2,z3,z533,z7,z6]),(0,[z0,z704,z1,z2,z3,z7,z6]),(0,[z90,z0,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z5,z611,z6]),(0,[z0,z1,z2,z3,z185,z7,z6]),(0,[z705,z0,z1,z2,z3,z7,z6]),(0,[z0,z706,z1,z2,z3,z7,z6])],[(1,[z0,z1,z2,z3,z533,z6]),(0,[z0,z1,z154,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z10,z54]),(0,[z0,z1,z2,z229,z3,z7,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z106,z7,z177]),(0,[z0,z1,z2,z7,z146,z32]),(0,[z0,z1,z2,z62,z7,z146]),(0,[z48,z0,z1,z537,z3,z6])],[(0,[z0,z707,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z708,z6]),(0,[z0,z1,z2,z709,z5,z6]),(0,[z710,z0,z1,z2,z3,z6])],[(0,[z0,z711,z1,z2,z7,z6]),(0,[z0,z263,z1,z2,z712,z7]),(0,[z0,z713,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z714]),(0,[z0,z100,z2,z451,z7,z6])],[(1,[z1,z2,z3,z708,z6]),(0,[z53,z1,z2,z3,z26,z97])],[(0,[z0,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z709,z7,z6]),(0,[z0,z1,z18,z3,z7,z507]),(0,[z85,z1,z715,z3,z7,z6]),(0,[z104,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z716,z6]),(0,[z0,z1,z2,z3,z7,z717]),(0,[z0,z1,z2,z718,z172,z6])],[(0,[z0,z1,z719,z3,z7,z6]),(0,[z9,z0,z2,z435,z7,z10]),(0,[z0,z1,z2,z3,z7,z720])],[(0,[z0,z1,z2,z3,z721,z6]),(0,[z0,z1,z722,z2,z5,z6]),(0,[z0,z171,z2,z3,z7,z134]),(0,[z48,z0,z1,z502,z3,z6])],[(0,[z0,z1,z496,z3,z7,z310]),(0,[z0,z1,z2,z723,z7,z6]),(0,[z0,z1,z2,z3,z724,z6]),(0,[z1,z2,z3,z5,z6,z142]),(0,[z0,z79,z1,z3,z26,z255]),(0,[z0,z1,z57,z3,z239,z6]),(0,[z0,z1,z2,z3,z725,z6]),(0,[z0,z1,z2,z7,z249,z32]),(0,[z0,z2,z3,z7,z10,z726]),(0,[z0,z1,z2,z101,z7,z548])]],
   [[(0,[z727,z115,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z728,z6]),(0,[z0,z1,z2,z3,z5,z166]),(0,[z0,z1,z2,z3,z729,z6]),(0,[z0,z1,z2,z3,z7,z730]),(0,[z0,z1,z2,z3,z6,z731])],[(0,[z0,z1,z722,z2,z7,z6]),(0,[z85,z1,z2,z220,z5,z6]),(0,[z0,z1,z732,z2,z3,z5]),(0,[z0,z1,z733,z2,z7,z6]),(0,[z0,z1,z734,z2,z7,z6])],[(0,[z82,z1,z2,z68,z243,z6]),(0,[z0,z1,z2,z3,z735,z6])],[(0,[z58,z115,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z7,z736]),(0,[z0,z1,z21,z3,z26,z6]),(0,[z0,z1,z2,z3,z7,z166]),(0,[z0,z148,z39,z1,z2,z6]),(0,[z0,z1,z2,z435,z7,z32])],[(0,[z0,z1,z2,z3,z737,z6]),(0,[z694,z115,z2,z3,z7,z6]),(0,[z0,z365,z2,z4,z7,z6]),(0,[z401,z0,z1,z3,z87,z6]),(0,[z61,z0,z1,z2,z416,z7]),(0,[z1,z2,z3,z7,z6,z738]),(0,[z0,z1,z70,z2,z101,z6])],[(0,[z0,z171,z2,z3,z7,z6]),(0,[z0,z1,z739,z3,z7,z6]),(0,[z0,z305,z2,z3,z5,z52]),(0,[z391,z1,z2,z3,z5,z6]),(0,[z200,z1,z2,z3,z5,z6]),(0,[z0,z404,z2,z3,z7,z10]),(0,[z0,z1,z345,z46,z2,z6]),(0,[z0,z1,z2,z3,z740,z6])],[(0,[z0,z1,z2,z106,z216,z6]),(0,[z0,z1,z2,z3,z7,z741]),(0,[z180,z1,z2,z3,z5,z6]),(0,[z0,z1,z36,z3,z7,z449]),(0,[z0,z685,z2,z3,z7,z52]),(0,[z0,z108,z1,z418,z7,z6]),(0,[z0,z742,z1,z3,z7,z6]),(0,[z0,z2,z3,z7,z726,z52]),(0,[z48,z49,z1,z3,z87,z6]),(0,[z0,z1,z2,z23,z718,z6])],[(0,[z0,z1,z743,z3,z7,z6]),(0,[z0,z1,z2,z3,z26,z40]),(0,[z0,z1,z2,z62,z7,z32]),(0,[z0,z108,z1,z70,z2,z6]),(0,[z0,z1,z89,z238,z2,z6]),(0,[z180,z1,z2,z3,z117,z6]),(0,[z0,z1,z2,z3,z744,z6])]],
   [[(0,[z662,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z7,z745]),(0,[z0,z1,z2,z746,z7,z6])],[(0,[z180,z1,z2,z3,z7,z6]),(0,[z45,z1,z500,z37,z7,z6])],[(0,[z152,z1,z102,z3,z7,z6]),(0,[z0,z1,z102,z3,z7,z507]),(0,[z0,z1,z2,z3,z7,z747]),(0,[z0,z1,z2,z748,z7,z6]),(0,[z0,z1,z2,z7,z6,z120])],[(0,[z0,z1,z496,z3,z5,z6]),(0,[z88,z1,z18,z3,z7,z6]),(0,[z85,z1,z2,z3,z749,z6]),(0,[z0,z1,z2,z3,z750,z6]),(0,[z0,z1,z57,z3,z26,z6]),(0,[z0,z260,z2,z3,z237,z6]),(0,[z751,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z144,z3,z6]),(1,[z0,z2,z3,z7,z726])],[(0,[z0,z1,z2,z3,z7,z752]),(0,[z698,z0,z19,z3,z7,z6]),(0,[z0,z1,z2,z753,z7,z6]),(0,[z0,z1,z89,z2,z718,z6])],[(0,[z0,z1,z2,z3,z7,z754]),(0,[z0,z1,z2,z755,z7,z6]),(0,[z0,z756,z1,z2,z7,z6])],[(0,[z0,z1,z496,z3,z7,z6])],[(0,[z0,z1,z2,z3,z7,z757]),(0,[z0,z1,z2,z3,z533,z310]),(0,[z0,z1,z195,z2,z3,z7]),(0,[z0,z1,z2,z3,z758,z6]),(0,[z0,z1,z2,z3,z5,z759]),(0,[z0,z1,z2,z3,z7,z760])]],
   [[(0,[z1,z2,z18,z3,z5,z6]),(0,[z85,z1,z102,z3,z20,z6]),(0,[z0,z1,z2,z3,z761,z6]),(0,[z0,z1,z2,z762,z7,z6]),(0,[z0,z1,z2,z3,z5,z211]),(0,[z0,z2,z3,z7,z726,z6]),(0,[z0,z1,z3,z763,z87,z6])],[(0,[z0,z695,z2,z3,z7,z52])],[(1,[z1,z2,z762,z7,z6]),(0,[z0,z1,z764,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z759]),(0,[z486,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z7,z765]),(0,[z766,z1,z2,z3,z7,z6]),(0,[z0,z100,z2,z767,z7,z6]),(0,[z0,z1,z768,z2,z3,z6])],[(0,[z0,z1,z195,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z146]),(0,[z1,z406,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z7,z211])],[(0,[z0,z1,z2,z220,z5,z6]),(0,[z0,z1,z2,z3,z7,z769]),(0,[z381,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z7,z6,z770]),(1,[z0,z771,z3,z7,z6]),(0,[z0,z100,z2,z4,z7,z249])],[(0,[z0,z1,z2,z226,z5,z6]),(0,[z0,z1,z2,z772,z7,z6]),(0,[z0,z1,z2,z220,z7,z773]),(0,[z0,z774,z1,z2,z3,z6]),(0,[z0,z1,z2,z775,z7,z6]),(0,[z9,z0,z2,z3,z7,z726])],[(0,[z0,z1,z2,z3,z7,z146]),(0,[z0,z1,z21,z3,z395,z6]),(0,[z0,z1,z2,z210,z144,z6]),(1,[z0,z2,z767,z7,z6]),(0,[z0,z1,z2,z3,z776,z6]),(0,[z0,z1,z777,z2,z7,z6])],[(0,[z0,z1,z2,z220,z7,z6]),(0,[z0,z1,z2,z778,z7,z6]),(0,[z0,z1,z2,z3,z7,z726]),(0,[z0,z1,z2,z3,z6,z779]),(0,[z0,z780,z1,z3,z7,z6])]],
   [[(0,[z0,z1,z2,z226,z7,z6]),(0,[z67,z1,z18,z3,z5,z6]),(0,[z0,z1,z2,z220,z174,z6]),(0,[z0,z1,z2,z7,z718,z6])],[(0,[z67,z263,z1,z18,z3,z7]),(0,[z0,z263,z1,z2,z3,z26]),(0,[z248,z0,z19,z3,z5,z6]),(0,[z0,z100,z2,z4,z5,z6]),(0,[z0,z75,z2,z767,z7,z6]),(0,[z0,z1,z2,z781,z7,z6])],[(0,[z213,z1,z2,z3,z20,z6]),(0,[z0,z1,z2,z3,z782,z6]),(0,[z0,z1,z2,z783,z7,z6]),(0,[z0,z1,z2,z471,z7,z32]),(0,[z0,z148,z1,z2,z210,z6])],[(0,[z0,z1,z2,z784,z3,z6]),(0,[z67,z1,z18,z3,z7,z6]),(0,[z520,z1,z2,z3,z5,z6]),(0,[z0,z1,z438,z3,z103,z6]),(0,[z0,z1,z2,z3,z785,z6])],[(0,[z45,z1,z2,z37,z395,z6]),(0,[z9,z0,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z786]),(0,[z0,z1,z635,z2,z172,z6]),(0,[z248,z0,z19,z3,z7,z6]),(0,[z0,z100,z2,z4,z7,z6])],[(0,[z0,z1,z2,z24,z259,z6]),(0,[z0,z1,z2,z787,z7,z6])],[(0,[z0,z1,z2,z3,z533,z6]),(0,[z0,z1,z2,z788,z7,z6]),(0,[z0,z1,z2,z3,z749,z6]),(0,[z85,z1,z147,z3,z7,z6]),(0,[z0,z1,z2,z26,z6,z295]),(0,[z0,z1,z2,z3,z789,z6]),(0,[z0,z1,z790,z3,z7,z6]),(0,[z0,z108,z1,z186,z7,z224]),(0,[z0,z1,z2,z3,z7,z791])],[(0,[z0,z1,z792,z2,z3,z7]),(0,[z0,z1,z2,z3,z7,z786]),(0,[z9,z0,z2,z3,z7,z10])]],
   [[(0,[z0,z1,z2,z3,z243,z6]),(0,[z0,z1,z154,z3,z538,z6]),(0,[z0,z793,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z7,z794])],[(0,[z0,z1,z795,z3,z7,z6]),(0,[z0,z1,z2,z7,z14,z6]),(0,[z0,z1,z2,z7,z6,z796]),(1,[z0,z1,z3,z7,z797]),(0,[z0,z1,z2,z3,z6,z798])],[(0,[z0,z1,z2,z3,z799,z6]),(0,[z0,z1,z194,z3,z7,z177]),(0,[z0,z1,z2,z3,z20,z6]),(0,[z0,z1,z2,z3,z7,z800]),(0,[z0,z1,z648,z2,z7,z32])],[(0,[z59,z727,z2,z3,z7,z6]),(0,[z0,z801,z2,z3,z7,z6]),(0,[z0,z39,z1,z2,z5,z6]),(0,[z640,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z802,z6])],[(0,[z0,z1,z2,z803,z7,z6]),(0,[z498,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z117,z763,z6])],[(0,[z1,z102,z715,z3,z7,z6]),(0,[z45,z1,z2,z37,z5,z6]),(0,[z0,z1,z36,z468,z3,z7]),(0,[z0,z1,z2,z3,z804,z6])],[(0,[z0,z1,z2,z3,z7,z805]),(0,[z0,z39,z1,z2,z7,z6]),(0,[z0,z1,z2,z3,z806,z6])],[(0,[z0,z1,z2,z7,z807,z6]),(0,[z0,z1,z2,z3,z26,z166]),(0,[z0,z1,z2,z3,z26,z736]),(0,[z0,z1,z2,z7,z6,z791])]],
   [[(0,[z45,z1,z2,z37,z7,z6]),(0,[z0,z1,z2,z3,z7,z808]),(0,[z0,z1,z2,z3,z809,z6]),(1,[z0,z1,z2,z718,z6])],[(0,[z0,z1,z2,z3,z5,z810]),(0,[z0,z171,z2,z3,z26,z6])],[(0,[z58,z115,z2,z3,z26,z6]),(0,[z0,z422,z2,z3,z432,z6]),(0,[z0,z1,z2,z3,z7,z811])],[(1,[z727,z2,z3,z7,z6]),(0,[z0,z1,z812,z2,z3,z6]),(0,[z0,z1,z3,z7,z797,z255])],[(0,[z0,z1,z813,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z810]),(0,[z0,z1,z299,z2,z7,z791])],[(0,[z0,z814,z2,z3,z7,z6]),(0,[z0,z2,z3,z815,z7,z6]),(0,[z180,z1,z2,z3,z26,z6])],[(0,[z0,z1,z2,z3,z7,z816]),(0,[z90,z59,z2,z3,z91,z6]),(0,[z0,z1,z817,z3,z7,z6]),(0,[z0,z818,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z26,z747]),(0,[z0,z1,z2,z24,z7,z507]),(0,[z0,z819,z2,z3,z7,z6])],[(0,[z45,z1,z21,z37,z7,z6]),(0,[z0,z1,z2,z820,z7,z6]),(0,[z0,z1,z821,z3,z7,z6])]],
   [[(0,[z0,z1,z194,z3,z216,z6]),(0,[z0,z1,z2,z3,z7,z822]),(0,[z0,z1,z2,z823,z7,z6])],[(0,[z0,z1,z824,z3,z7,z6]),(0,[z0,z1,z2,z825,z7,z6]),(0,[z0,z826,z1,z2,z3,z6]),(0,[z0,z1,z36,z3,z5,z33]),(0,[z0,z1,z374,z2,z3,z181]),(0,[z0,z827,z1,z3,z7,z6])],[(0,[z0,z1,z496,z3,z26,z6]),(0,[z0,z1,z194,z226,z7,z6]),(0,[z0,z1,z2,z828,z7,z6]),(0,[z0,z1,z2,z3,z7,z829]),(0,[z0,z2,z196,z767,z7,z6]),(0,[z0,z1,z2,z3,z830,z6])],[(0,[z0,z1,z831,z2,z7,z6]),(0,[z0,z75,z2,z7,z6,z94]),(0,[z0,z1,z832,z3,z7,z6]),(0,[z0,z1,z2,z416,z7,z10])],[(0,[z0,z833,z1,z2,z3,z7]),(0,[z0,z1,z2,z834,z7,z6]),(0,[z48,z0,z1,z3,z87,z6]),(0,[z0,z1,z36,z3,z7,z33])],[(0,[z0,z84,z2,z3,z7,z52]),(0,[z0,z1,z2,z3,z835,z6]),(0,[z0,z836,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z837,z6])],[(0,[z58,z115,z2,z3,z7,z177]),(0,[z0,z1,z2,z3,z838,z6]),(0,[z0,z1,z313,z60,z7,z6])],[(0,[z1,z112,z18,z3,z5,z6]),(0,[z0,z1,z2,z3,z839,z6]),(0,[z0,z1,z2,z3,z26,z211]),(0,[z566,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z7,z840]),(0,[z0,z1,z2,z3,z841,z6]),(0,[z0,z1,z2,z3,z7,z842])]],
   [[(0,[z0,z1,z194,z3,z533,z6]),(0,[z0,z1,z2,z3,z843,z6])],[(0,[z0,z1,z2,z844,z7,z6]),(0,[z1,z2,z3,z5,z493,z6]),(0,[z0,z171,z2,z3,z7,z54]),(0,[z0,z1,z2,z3,z7,z845]),(0,[z0,z27,z2,z3,z69,z6]),(0,[z0,z1,z2,z3,z7,z846])],[(0,[z0,z1,z2,z3,z26,z146]),(0,[z1,z2,z3,z26,z5,z6])],[(0,[z0,z1,z2,z220,z26,z6]),(0,[z430,z0,z1,z3,z317,z6]),(0,[z470,z1,z2,z3,z7,z97]),(0,[z847,z1,z2,z3,z7,z6])],[(0,[z58,z115,z496,z3,z7,z6]),(0,[z0,z1,z2,z226,z26,z6]),(0,[z579,z1,z2,z3,z5,z6]),(0,[z0,z1,z46,z3,z103,z6]),(0,[z0,z79,z1,z57,z3,z7]),(0,[z0,z1,z2,z3,z848,z6])],[(0,[z0,z1,z849,z3,z7,z6]),(0,[z0,z1,z850,z3,z7,z6]),(0,[z0,z27,z160,z2,z3,z6]),(0,[z0,z1,z2,z3,z7,z851])],[(0,[z0,z108,z1,z188,z7,z6]),(0,[z0,z1,z2,z3,z852,z6]),(0,[z0,z1,z345,z2,z5,z6]),(0,[z0,z1,z2,z60,z7,z507]),(0,[z0,z108,z1,z70,z186,z6])],[(0,[z67,z1,z18,z3,z26,z6]),(0,[z0,z1,z2,z853,z7,z6]),(0,[z0,z1,z2,z854,z7,z6])]],
   [[(0,[z0,z1,z732,z2,z3,z7]),(0,[z125,z1,z2,z3,z5,z6]),(0,[z1,z2,z591,z3,z5,z6]),(0,[z248,z0,z19,z3,z26,z6]),(0,[z0,z100,z2,z4,z26,z6]),(0,[z0,z148,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z855]),(0,[z48,z0,z1,z14,z87,z6])],[(0,[z0,z1,z345,z2,z7,z6])],[(0,[z0,z1,z2,z3,z7,z856]),(0,[z0,z1,z57,z3,z98,z6]),(0,[z0,z2,z767,z4,z7,z6]),(0,[z0,z1,z2,z7,z134,z791])],[(0,[z0,z1,z857,z3,z7,z6]),(0,[z0,z858,z1,z2,z3,z6]),(0,[z0,z1,z859,z3,z7,z6]),(0,[z9,z0,z2,z3,z26,z10]),(0,[z0,z72,z2,z233,z7,z6]),(0,[z860,z1,z2,z3,z7,z6])],[(0,[z0,z1,z861,z3,z7,z6]),(0,[z0,z1,z2,z3,z862,z6]),(0,[z0,z27,z2,z3,z69,z40]),(0,[z0,z1,z2,z3,z863,z6])],[(0,[z0,z171,z2,z3,z5,z6]),(0,[z585,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z7,z864]),(0,[z865,z1,z2,z3,z7,z6])],[(0,[z58,z115,z2,z226,z7,z6]),(0,[z437,z1,z2,z3,z5,z6]),(0,[z866,z1,z2,z3,z7,z6])],[(0,[z0,z1,z2,z3,z867,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z177]),(0,[z85,z1,z102,z220,z7,z6]),(0,[z0,z1,z2,z7,z868,z6]),(0,[z0,z1,z251,z62,z7,z6]),(0,[z0,z1,z2,z7,z869,z6]),(0,[z0,z1,z870,z3,z7,z6])],[(0,[z0,z1,z431,z2,z7,z32]),(0,[z0,z1,z2,z3,z6,z871]),(0,[z0,z872,z2,z3,z7,z6])],[(0,[z0,z1,z2,z3,z216,z310]),(0,[z0,z1,z2,z3,z175,z6]),(0,[z0,z1,z2,z101,z5,z134]),(0,[z0,z1,z2,z873,z5,z6]),(0,[z0,z1,z2,z5,z14,z6]),(0,[z0,z39,z1,z2,z26,z6]),(0,[z0,z72,z251,z3,z7,z6]),(0,[z61,z1,z2,z62,z7,z54]),(0,[z0,z2,z3,z237,z874,z6]),(0,[z0,z1,z3,z7,z6,z875])],[(0,[z0,z1,z2,z3,z7,z177]),(0,[z0,z1,z2,z876,z7,z6]),(0,[z0,z1,z2,z3,z877,z6]),(0,[z0,z92,z112,z3,z7,z93]),(0,[z0,z1,z2,z3,z7,z878])],[(0,[z0,z1,z2,z226,z7,z310]),(0,[z58,z115,z2,z3,z533,z6]),(0,[z0,z879,z2,z3,z7,z6]),(0,[z45,z1,z2,z37,z26,z6]),(0,[z0,z880,z2,z3,z7,z6]),(0,[z881,z0,z1,z3,z5,z6]),(0,[z219,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z532,z6]),(0,[z61,z72,z2,z3,z7,z54])],[(0,[z0,z1,z882,z3,z7,z6]),(0,[z0,z1,z2,z3,z883,z6]),(0,[z0,z1,z18,z220,z7,z6]),(0,[z0,z1,z2,z873,z7,z6]),(0,[z0,z1,z119,z2,z7,z32]),(0,[z0,z1,z2,z101,z7,z134])],[(0,[z0,z1,z884,z3,z7,z6]),(0,[z0,z1,z2,z3,z5,z189]),(0,[z0,z39,z1,z2,z7,z730]),(0,[z0,z1,z2,z7,z885,z6])],[(0,[z881,z0,z1,z3,z7,z6]),(0,[z49,z1,z2,z3,z5,z6]),(0,[z61,z1,z2,z3,z7,z886])]],
   [[(0,[z0,z1,z2,z3,z7,z887]),(0,[z53,z1,z2,z3,z7,z612]),(0,[z1,z2,z3,z7,z6,z888])],[(0,[z227,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z7,z189]),(0,[z889,z1,z2,z3,z7,z6]),(0,[z0,z305,z2,z3,z7,z726]),(0,[z180,z1,z2,z3,z538,z6])],[(0,[z0,z1,z2,z3,z7,z890]),(0,[z49,z1,z2,z3,z7,z6]),(0,[z1,z2,z18,z3,z352,z6]),(0,[z0,z1,z715,z3,z7,z6]),(0,[z0,z108,z1,z186,z5,z6]),(0,[z0,z1,z2,z891,z7,z6]),(0,[z892,z1,z2,z3,z7,z6])],[(0,[z0,z1,z2,z210,z5,z6]),(0,[z1,z2,z638,z3,z5,z6]),(0,[z0,z1,z2,z820,z26,z6]),(0,[z180,z1,z2,z3,z87,z6]),(0,[z0,z1,z2,z24,z6,z228])],[(0,[z0,z1,z2,z3,z91,z6]),(0,[z0,z1,z496,z3,z533,z6]),(1,[z1,z715,z3,z7,z6])],[(0,[z0,z1,z2,z3,z7,z893]),(0,[z0,z1,z36,z57,z3,z7]),(0,[z0,z108,z1,z186,z7,z6])],[(0,[z0,z1,z2,z3,z7,z894]),(0,[z0,z1,z2,z895,z7,z6]),(0,[z628,z1,z18,z3,z7,z6]),(0,[z0,z1,z2,z210,z7,z6]),(0,[z0,z1,z2,z3,z896,z6])],[(0,[z0,z1,z2,z3,z897,z6]),(0,[z1,z2,z715,z3,z7,z6]),(0,[z0,z1,z2,z3,z898,z6]),(0,[z0,z1,z831,z2,z26,z6]),(0,[z0,z171,z57,z3,z7,z6]),(0,[z0,z75,z2,z42,z7,z6])]],
   [[(0,[z0,z1,z899,z3,z7,z6]),(0,[z396,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z229,z5,z6]),(0,[z0,z1,z36,z3,z26,z33])],[(0,[z0,z1,z2,z3,z216,z6]),(0,[z0,z1,z2,z3,z900,z6]),(0,[z277,z59,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z901]),(0,[z0,z1,z2,z3,z902,z6])],[(0,[z0,z1,z2,z3,z903,z6]),(0,[z67,z1,z18,z3,z352,z6]),(0,[z0,z1,z121,z294,z7,z6])],[(0,[z0,z1,z102,z220,z7,z6]),(0,[z381,z1,z102,z3,z7,z6]),(0,[z0,z1,z904,z3,z7,z6]),(0,[z0,z1,z2,z905,z3,z6]),(0,[z0,z72,z2,z62,z7,z6]),(0,[z0,z1,z2,z516,z7,z134]),(0,[z0,z1,z2,z229,z7,z6]),(0,[z0,z1,z2,z3,z718,z6])],[(0,[z0,z1,z2,z906,z7,z6]),(0,[z0,z1,z2,z233,z5,z6]),(0,[z0,z907,z2,z3,z7,z6])],[(0,[z108,z1,z18,z3,z5,z6]),(0,[z0,z1,z500,z68,z7,z6]),(0,[z0,z1,z2,z3,z908,z6]),(1,[z0,z2,z3,z874,z6]),(0,[z0,z1,z2,z3,z909,z6]),(0,[z0,z1,z2,z3,z910,z6]),(0,[z0,z1,z2,z3,z7,z911]),(0,[z0,z1,z2,z912,z7,z6]),(0,[z0,z1,z89,z2,z172,z6])],[(0,[z1,z2,z3,z26,z708,z6]),(0,[z1,z2,z3,z26,z262,z6]),(0,[z0,z913,z2,z3,z7,z6])],[(0,[z67,z1,z715,z3,z7,z6]),(0,[z0,z1,z914,z2,z3,z7]),(0,[z0,z1,z2,z3,z915,z6]),(0,[z0,z1,z2,z233,z7,z6]),(0,[z670,z1,z2,z3,z5,z6]),(0,[z0,z1,z916,z2,z5,z6]),(0,[z0,z1,z2,z7,z6,z917]),(0,[z0,z1,z36,z3,z7,z22]),(0,[z0,z1,z2,z3,z918,z6])]],
   [[(0,[z90,z727,z2,z3,z7,z6]),(0,[z0,z171,z2,z3,z239,z6]),(0,[z0,z171,z2,z3,z98,z6]),(0,[z0,z1,z2,z7,z10,z120])],[(0,[z0,z1,z2,z220,z20,z6]),(0,[z286,z1,z2,z68,z7,z6])],[(0,[z0,z1,z2,z919,z7,z6]),(0,[z0,z1,z916,z2,z7,z6]),(0,[z0,z1,z2,z3,z7,z920])],[(0,[z1,z18,z3,z103,z5,z6]),(0,[z0,z1,z251,z3,z5,z6]),(0,[z0,z1,z3,z5,z921,z6]),(0,[z0,z1,z771,z3,z7,z6]),(0,[z0,z1,z2,z922,z7,z6]),(0,[z0,z923,z2,z3,z7,z6])],[(0,[z0,z1,z924,z2,z3,z7]),(0,[z198,z1,z2,z3,z5,z6]),(0,[z199,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z7,z678,z32])],[(0,[z61,z1,z2,z3,z5,z54]),(0,[z0,z1,z345,z2,z26,z6]),(0,[z0,z1,z2,z767,z7,z6]),(0,[z0,z1,z121,z925,z7,z6])],[(0,[z0,z1,z2,z3,z7,z926]),(0,[z58,z727,z2,z3,z7,z6]),(0,[z0,z1,z251,z3,z7,z6]),(0,[z1,z2,z3,z538,z5,z6]),(0,[z0,z263,z1,z2,z3,z5]),(0,[z0,z1,z2,z712,z7,z6]),(0,[z45,z1,z2,z37,z7,z146]),(0,[z0,z1,z2,z3,z927,z6]),(0,[z180,z56,z1,z2,z3,z6])],[(0,[z0,z1,z2,z928,z7,z6]),(0,[z0,z929,z2,z3,z7,z6]),(0,[z0,z1,z930,z3,z7,z6]),(0,[z0,z1,z931,z3,z7,z6])]],
   [[(0,[z0,z1,z2,z3,z7,z932]),(0,[z0,z1,z2,z3,z933,z6]),(0,[z85,z1,z2,z86,z5,z6]),(0,[z0,z1,z924,z2,z3,z5]),(0,[z61,z1,z2,z3,z7,z54]),(0,[z0,z1,z3,z7,z934,z6]),(0,[z0,z1,z46,z3,z399,z6])],[(0,[z0,z1,z2,z3,z935,z6]),(0,[z0,z1,z2,z936,z7,z6]),(0,[z0,z1,z65,z2,z3,z181]),(0,[z0,z1,z2,z3,z874,z6]),(0,[z0,z1,z2,z3,z937,z6]),(0,[z0,z1,z60,z925,z7,z6]),(0,[z0,z1,z65,z2,z3,z66])],[(0,[z0,z1,z2,z68,z7,z507]),(0,[z0,z1,z2,z938,z7,z6]),(0,[z0,z939,z2,z3,z7,z6])],[(0,[z0,z56,z2,z3,z432,z6]),(0,[z0,z1,z2,z7,z6,z940])],[(0,[z0,z59,z2,z3,z7,z310]),(0,[z0,z1,z2,z3,z7,z941]),(0,[z0,z1,z2,z435,z7,z134])],[(0,[z0,z1,z2,z942,z7,z6]),(0,[z0,z1,z2,z3,z7,z886]),(0,[z0,z1,z2,z3,z943,z6]),(0,[z0,z1,z2,z944,z7,z6]),(0,[z0,z1,z2,z7,z6,z945])],[(0,[z131,z1,z18,z3,z7,z6]),(0,[z0,z263,z1,z3,z7,z255]),(0,[z0,z1,z500,z3,z175,z6]),(0,[z0,z1,z57,z233,z7,z6]),(0,[z0,z1,z2,z7,z946,z6])],[(0,[z0,z1,z2,z3,z26,z177]),(0,[z0,z947,z1,z2,z7,z6]),(0,[z0,z1,z2,z3,z948,z6])]],
   [[(0,[z0,z1,z2,z3,z949,z6]),(0,[z0,z1,z2,z62,z7,z134]),(0,[z0,z1,z2,z950,z7,z93]),(0,[z0,z1,z2,z3,z7,z951]),(0,[z0,z1,z46,z202,z3,z6])],[(0,[z0,z1,z2,z3,z952,z6]),(0,[z0,z1,z2,z101,z26,z134]),(0,[z0,z1,z2,z3,z7,z953]),(0,[z0,z108,z1,z342,z7,z6])],[(0,[z0,z1,z121,z193,z7,z6])],[(0,[z0,z1,z2,z3,z385,z6]),(0,[z0,z1,z2,z3,z7,z954]),(0,[z0,z1,z299,z2,z5,z32]),(0,[z29,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z7,z955])],[(0,[z1,z18,z19,z3,z5,z6]),(0,[z0,z1,z2,z3,z26,z189]),(0,[z0,z1,z2,z956,z7,z6]),(0,[z0,z1,z2,z3,z957,z6]),(0,[z0,z1,z958,z2,z3,z6]),(0,[z0,z1,z2,z959,z7,z6])],[(0,[z0,z1,z2,z5,z6,z120]),(0,[z49,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z960,z6]),(0,[z0,z1,z299,z2,z7,z32])],[(0,[z0,z1,z2,z3,z961,z6]),(0,[z0,z115,z2,z3,z7,z310]),(0,[z1,z715,z18,z3,z7,z6]),(0,[z0,z1,z2,z62,z7,z6]),(0,[z0,z1,z57,z3,z7,z32]),(0,[z0,z1,z2,z233,z239,z6]),(0,[z0,z1,z2,z233,z98,z6]),(0,[z0,z1,z89,z2,z7,z507]),(0,[z0,z1,z2,z23,z285,z6]),(0,[z0,z1,z2,z3,z962,z6])]],
   [[(0,[z0,z1,z2,z963,z7,z6])],[(0,[z1,z36,z18,z3,z5,z6]),(0,[z0,z108,z1,z186,z26,z6]),(0,[z0,z2,z3,z7,z964,z6]),(0,[z0,z1,z89,z2,z320,z6])],[(0,[z0,z1,z2,z3,z7,z965]),(0,[z0,z1,z966,z3,z7,z6]),(0,[z0,z1,z2,z3,z5,z967]),(0,[z0,z551,z2,z3,z69,z6]),(0,[z0,z1,z2,z210,z26,z6]),(0,[z0,z1,z2,z416,z7,z255])],[(0,[z0,z1,z2,z3,z968,z6]),(0,[z0,z1,z2,z3,z969,z6]),(0,[z1,z195,z2,z18,z3,z5]),(0,[z0,z1,z2,z86,z5,z6]),(0,[z0,z1,z2,z3,z185,z6]),(0,[z0,z1,z2,z3,z7,z797])],[(0,[z970,z1,z2,z3,z7,z6])],[(0,[z0,z1,z2,z3,z7,z967]),(0,[z0,z1,z2,z3,z971,z6])],[(0,[z0,z1,z2,z86,z7,z6]),(0,[z1,z2,z762,z3,z7,z6]),(0,[z0,z1,z2,z3,z972,z6]),(0,[z48,z0,z1,z3,z317,z6]),(0,[z0,z1,z251,z3,z239,z6]),(0,[z0,z1,z251,z3,z98,z6]),(0,[z0,z1,z2,z973,z7,z458]),(0,[z0,z1,z46,z3,z117,z6])],[(0,[z85,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z86,z174,z6]),(0,[z0,z1,z974,z3,z7,z6]),(0,[z0,z75,z2,z196,z5,z6]),(0,[z0,z1,z2,z229,z26,z6])]],
   [[(0,[z61,z1,z2,z3,z239,z54]),(0,[z0,z1,z2,z3,z975,z6]),(0,[z0,z108,z1,z185,z186,z6]),(0,[z0,z1,z344,z2,z7,z32])],[(0,[z0,z1,z496,z3,z7,z177]),(0,[z0,z1,z2,z3,z976,z6]),(0,[z0,z1,z2,z3,z5,z458]),(0,[z0,z1,z2,z3,z977,z6])],[(0,[z0,z1,z2,z106,z5,z6]),(0,[z0,z92,z112,z3,z5,z6]),(0,[z0,z1,z978,z3,z7,z6]),(0,[z979,z1,z2,z3,z7,z6]),(0,[z0,z75,z2,z196,z7,z6]),(0,[z0,z1,z2,z980,z7,z6])],[(0,[z0,z1,z2,z981,z7,z6]),(0,[z0,z1,z195,z2,z3,z26]),(0,[z0,z1,z2,z7,z6,z982]),(0,[z0,z1,z2,z233,z26,z6]),(0,[z0,z1,z983,z2,z3,z6]),(0,[z223,z0,z2,z3,z7,z10]),(1,[z0,z1,z3,z763,z6])],[(0,[z0,z1,z2,z984,z3,z6]),(0,[z0,z1,z2,z3,z7,z985]),(0,[z0,z1,z2,z986,z7,z6]),(0,[z0,z1,z2,z3,z987,z6]),(0,[z1,z2,z594,z3,z5,z6]),(0,[z0,z1,z2,z3,z7,z458]),(0,[z0,z1,z2,z101,z7,z411])],[(0,[z0,z1,z2,z106,z7,z6]),(0,[z0,z92,z112,z3,z7,z6])],[(0,[z0,z1,z2,z7,z6,z988]),(0,[z0,z1,z121,z60,z5,z6]),(0,[z0,z771,z19,z3,z7,z6]),(0,[z0,z108,z1,z186,z7,z507]),(0,[z48,z0,z1,z345,z2,z6])],[(0,[z58,z115,z2,z3,z216,z6]),(0,[z0,z1,z31,z2,z110,z6]),(0,[z0,z2,z3,z7,z989,z6])]],
   [[(0,[z1,z2,z3,z526,z26,z6]),(0,[z0,z1,z70,z121,z2,z6]),(0,[z0,z1,z3,z7,z6,z797])],[(0,[z0,z1,z2,z990,z7,z6]),(0,[z45,z1,z2,z762,z7,z6]),(0,[z0,z1,z2,z3,z991,z6]),(0,[z0,z1,z121,z60,z7,z6])],[(0,[z0,z1,z2,z3,z992,z6]),(0,[z0,z1,z251,z3,z26,z6]),(0,[z694,z1,z2,z3,z7,z54]),(0,[z0,z92,z771,z3,z7,z6])],[(0,[z0,z1,z2,z226,z7,z177]),(0,[z0,z1,z121,z7,z655,z6])],[(0,[z401,z1,z18,z3,z5,z6]),(0,[z61,z1,z2,z3,z26,z54]),(0,[z0,z171,z2,z233,z7,z6])],[(0,[z0,z39,z1,z18,z7,z6]),(0,[z993,z0,z1,z2,z3,z7])],[(0,[z0,z1,z994,z3,z7,z6]),(0,[z0,z1,z635,z2,z140,z6])],[(0,[z0,z1,z496,z3,z216,z6]),(0,[z0,z1,z995,z2,z3,z7]),(0,[z401,z1,z18,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z996]),(0,[z168,z1,z2,z68,z7,z6]),(0,[z0,z1,z2,z101,z7,z249]),(0,[z0,z100,z1,z2,z7,z507]),(1,[z0,z1,z925,z7,z6])]],
   [[(0,[z0,z1,z2,z3,z7,z997]),(0,[z90,z59,z2,z3,z385,z6]),(0,[z0,z1,z2,z3,z998,z6]),(0,[z0,z1,z999,z2,z3,z6]),(0,[z0,z1,z500,z37,z7,z6]),(0,[z1,z2,z37,z762,z7,z6]),(0,[z1,z2,z139,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1000,z6]),(0,[z0,z1,z496,z226,z7,z6]),(0,[z0,z1,z2,z3,z533,z177]),(0,[z0,z1,z1001,z2,z3,z6]),(0,[z0,z1,z2,z3,z1002,z7]),(0,[z82,z1,z2,z762,z7,z6]),(0,[z358,z1,z2,z3,z5,z6]),(0,[z0,z1003,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z1004,z6])],[(0,[z0,z1,z2,z1005,z7,z6]),(0,[z0,z1,z3,z7,z6,z1006]),(0,[z0,z1,z2,z3,z1007,z6]),(0,[z48,z0,z1,z345,z87,z6])],[(0,[z0,z1,z2,z5,z807,z6]),(0,[z0,z1,z2,z3,z1008,z6]),(0,[z1009,z1,z2,z3,z7,z6])],[(0,[z0,z1,z21,z3,z175,z6]),(0,[z241,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z540,z6]),(0,[z0,z1,z89,z2,z110,z6]),(0,[z248,z0,z144,z19,z3,z6])],[(0,[z0,z1,z2,z3,z1010,z6]),(0,[z0,z171,z2,z3,z7,z32]),(0,[z0,z1,z2,z7,z6,z1011])],[(0,[z0,z1,z2,z3,z7,z1012]),(0,[z0,z1,z2,z3,z174,z6]),(0,[z0,z1,z1013,z3,z7,z6]),(0,[z333,z1,z2,z37,z7,z6]),(0,[z694,z1,z2,z3,z5,z6]),(0,[z0,z75,z1,z2,z7,z507]),(0,[z0,z1,z2,z3,z1014,z6])],[(0,[z0,z1,z2,z1015,z7,z6]),(0,[z0,z1016,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1017,z6])]],
   [[(0,[z0,z1,z2,z1018,z7,z6]),(0,[z0,z1,z2,z3,z7,z1019]),(0,[z0,z1,z2,z3,z1020,z6]),(0,[z0,z1,z2,z3,z798,z66])],[(0,[z0,z1,z2,z226,z216,z6]),(0,[z0,z1,z2,z3,z7,z1021]),(0,[z0,z2,z3,z874,z69,z6]),(0,[z0,z1,z680,z2,z3,z66])],[(0,[z0,z1,z2,z3,z1022,z6]),(0,[z0,z108,z1,z461,z7,z6]),(0,[z45,z1,z2,z37,z175,z6]),(0,[z0,z1,z299,z2,z26,z32]),(0,[z0,z100,z2,z4,z7,z211]),(0,[z0,z56,z2,z380,z3,z6]),(0,[z0,z1,z2,z1023,z7,z6])],[(0,[z0,z1,z2,z1024,z7,z6]),(0,[z0,z1,z2,z3,z5,z93]),(0,[z434,z1,z2,z3,z26,z6]),(0,[z0,z171,z36,z2,z3,z7])],[(0,[z49,z1,z2,z3,z20,z6]),(0,[z0,z1,z2,z1025,z7,z6])],[(0,[z152,z1,z2,z37,z7,z6]),(0,[z0,z1,z2,z37,z7,z507]),(0,[z0,z1,z2,z3,z5,z1026]),(0,[z0,z1,z2,z416,z7,z52]),(0,[z0,z1,z2,z7,z52,z120]),(0,[z48,z180,z1,z3,z87,z6])],[(0,[z0,z1,z2,z1027,z7,z6]),(0,[z1,z2,z3,z5,z317,z6]),(0,[z0,z1,z2,z3,z5,z224]),(0,[z0,z1,z2,z514,z24,z6]),(0,[z0,z1,z2,z3,z7,z93]),(0,[z1028,z1,z2,z3,z7,z6]),(0,[z0,z1,z3,z7,z763,z6]),(0,[z0,z1,z582,z3,z7,z33])],[(0,[z0,z1,z194,z106,z7,z6]),(0,[z0,z1,z2,z3,z7,z1029]),(0,[z396,z1,z102,z3,z7,z6])]],
   [[(0,[z0,z1,z2,z1030,z7,z6]),(0,[z1,z2,z3,z749,z5,z6]),(0,[z0,z1,z2,z3,z7,z1026]),(0,[z53,z1,z2,z3,z402,z97]),(0,[z0,z1,z1031,z2,z3,z6]),(0,[z0,z1,z2,z3,z7,z1032])],[(0,[z0,z1,z2,z226,z533,z6]),(0,[z45,z1,z2,z37,z7,z189]),(0,[z0,z1,z2,z3,z402,z6]),(0,[z248,z0,z148,z19,z3,z6]),(0,[z0,z1,z3,z7,z6,z1033]),(0,[z0,z79,z1,z3,z7,z74]),(0,[z0,z1,z2,z3,z7,z224])],[(0,[z0,z1,z2,z3,z1034,z6]),(0,[z0,z1,z2,z86,z26,z6]),(0,[z248,z0,z771,z3,z7,z6]),(0,[z0,z1,z2,z3,z1035,z6]),(0,[z0,z1,z2,z186,z7,z507])],[(0,[z0,z39,z1,z2,z144,z6])],[(0,[z0,z1,z2,z416,z5,z6]),(0,[z0,z1,z2,z23,z420,z6]),(0,[z0,z1,z2,z3,z1036,z6])],[(0,[z0,z1,z2,z3,z1037,z6]),(0,[z0,z263,z1,z2,z3,z7]),(0,[z0,z2,z771,z3,z7,z6]),(0,[z0,z1,z2,z1038,z7,z6]),(0,[z0,z1,z1039,z3,z7,z6])],[(0,[z1,z2,z3,z708,z5,z6]),(0,[z0,z75,z2,z196,z26,z6])],[(0,[z82,z1,z2,z68,z276,z6]),(0,[z0,z1,z2,z3,z7,z1040]),(0,[z0,z1,z2,z416,z7,z6]),(0,[z0,z1,z2,z3,z1041,z6])]],
   [[(0,[z0,z1,z2,z3,z1042,z6]),(0,[z0,z1,z2,z3,z26,z458])],[(0,[z0,z1,z2,z106,z26,z6]),(0,[z0,z364,z2,z3,z7,z52]),(0,[z1,z2,z3,z708,z7,z6]),(0,[z0,z92,z112,z3,z26,z6]),(0,[z1,z81,z2,z3,z26,z6]),(0,[z0,z1,z2,z26,z6,z120]),(0,[z1043,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z1044])],[(0,[z0,z1,z1045,z3,z7,z6]),(0,[z0,z1,z2,z3,z1046,z6]),(0,[z0,z1,z2,z950,z7,z6]),(0,[z0,z79,z1,z416,z7,z255])],[(0,[z278,z1,z2,z3,z26,z6]),(0,[z0,z2,z767,z3,z7,z6]),(0,[z0,z1,z2,z3,z1047,z6]),(0,[z0,z79,z1,z3,z7,z797]),(0,[z0,z205,z1,z89,z2,z6]),(0,[z0,z1,z2,z3,z7,z1048])],[(0,[z0,z1,z194,z3,z5,z6]),(0,[z9,z0,z2,z3,z7,z512]),(0,[z0,z1,z2,z5,z6,z982]),(0,[z0,z1049,z2,z3,z7,z6])],[(0,[z0,z1,z1050,z3,z7,z6]),(0,[z225,z1,z2,z3,z5,z6]),(0,[z0,z1,z121,z60,z26,z6]),(0,[z0,z684,z2,z3,z7,z52])],[(0,[z0,z1,z2,z1051,z7,z6]),(0,[z0,z1,z2,z435,z7,z249]),(0,[z0,z1,z70,z2,z6,z32]),(0,[z1052,z1,z2,z3,z7,z6])],[(0,[z0,z1,z194,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z1053]),(0,[z85,z1,z102,z86,z7,z6]),(0,[z0,z1054,z1,z2,z7,z6]),(0,[z0,z2,z3,z7,z874,z6])]],
   [[(0,[z1055,z1,z2,z3,z7,z6]),(0,[z0,z92,z112,z3,z7,z166])],[],[(0,[z90,z59,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z1056,z7]),(0,[z0,z1,z2,z3,z368,z6]),(0,[z0,z1,z2,z220,z7,z822]),(0,[z0,z1057,z1,z2,z3,z6]),(1,[z1,z2,z3,z7,z886]),(0,[z0,z1,z2,z7,z6,z1058])],[(0,[z58,z115,z2,z106,z7,z6]),(0,[z0,z551,z2,z3,z453,z6]),(0,[z0,z1,z2,z435,z5,z6]),(0,[z1,z2,z3,z5,z6,z603]),(0,[z0,z1,z2,z3,z26,z996]),(0,[z0,z1,z2,z26,z6,z770]),(0,[z0,z1,z2,z7,z697,z32]),(0,[z0,z1,z89,z2,z481,z6]),(0,[z0,z108,z1,z537,z7,z6]),(0,[z0,z1,z2,z3,z1059,z6])],[(0,[z0,z1,z2,z3,z1060,z6]),(0,[z0,z1061,z2,z3,z7,z6]),(0,[z0,z1,z2,z7,z458,z945]),(0,[z0,z64,z2,z3,z7,z52])],[(0,[z85,z1,z18,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1062,z6]),(0,[z0,z1,z2,z1063,z7,z6]),(0,[z0,z1,z500,z3,z5,z6]),(0,[z0,z1,z2,z3,z1056,z5]),(0,[z0,z1,z2,z3,z1064,z6]),(0,[z0,z1,z2,z435,z7,z6]),(0,[z180,z27,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z7,z1065]),(0,[z82,z1,z2,z68,z5,z6]),(0,[z0,z1,z2,z62,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z1066,z6]),(0,[z0,z1,z2,z1067,z7,z6]),(0,[z241,z1,z2,z3,z708,z6]),(0,[z0,z214,z2,z3,z462,z6]),(0,[z1068,z1,z2,z3,z7,z6])],[(0,[z0,z1,z2,z106,z7,z310]),(0,[z0,z1,z2,z1069,z7,z6]),(0,[z0,z1,z500,z3,z7,z6]),(0,[z0,z72,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1070,z6]),(0,[z0,z1,z2,z3,z7,z1071])],[(0,[z0,z1,z2,z3,z1072,z6]),(0,[z0,z1,z1073,z3,z7,z6]),(0,[z0,z1,z1074,z3,z7,z6]),(0,[z0,z163,z112,z3,z7,z6]),(0,[z82,z1,z2,z68,z7,z6]),(0,[z0,z1075,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z620,z6]),(0,[z61,z1,z57,z3,z7,z54]),(0,[z0,z1,z2,z416,z7,z33])],[(0,[z0,z1,z496,z106,z7,z6]),(0,[z0,z1,z2,z3,z1076,z6]),(0,[z0,z1,z2,z1077,z7,z6]),(0,[z0,z280,z2,z3,z7,z10]),(0,[z1078,z1,z2,z3,z7,z6])],[(0,[z0,z72,z2,z3,z7,z6]),(0,[z53,z1,z2,z3,z73,z97]),(0,[z0,z607,z2,z3,z7,z10])],[(0,[z0,z1,z2,z1079,z7,z6]),(0,[z0,z1075,z2,z3,z7,z6]),(0,[z0,z1,z2,z3,z73,z6]),(0,[z0,z1,z3,z7,z33,z797])],[(0,[z0,z1,z2,z1080,z7,z6]),(0,[z0,z1,z2,z3,z1081,z6])],[(0,[z0,z1,z2,z3,z1082,z6]),(0,[z1,z18,z3,z5,z6,z255]),(0,[z1,z2,z269,z3,z5,z6]),(0,[z0,z1,z2,z1083,z7,z6])]],
   [[(0,[z0,z39,z1,z102,z7,z6]),(0,[z0,z1,z2,z26,z14,z6]),(0,[z53,z0,z1,z2,z416,z7]),(0,[z0,z1,z2,z3,z1084,z6])],[(0,[z85,z1,z2,z3,z352,z6]),(0,[z0,z1,z2,z1085,z7,z6])],[(0,[z0,z1,z2,z3,z7,z1086]),(0,[z401,z0,z1,z3,z382,z6]),(0,[z0,z1,z2,z3,z26,z93]),(0,[z1,z2,z3,z7,z6,z886]),(0,[z1,z2,z3,z7,z97,z886]),(0,[z0,z1,z2,z7,z6,z295]),(0,[z1087,z1,z2,z3,z7,z6]),(0,[z0,z1,z2,z376,z7,z32])],[(0,[z58,z115,z2,z3,z7,z6]),(0,[z85,z1,z102,z3,z5,z6]),(0,[z0,z1,z2,z1088,z3,z6]),(0,[z0,z1,z2,z3,z1089,z6]),(0,[z152,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z507]),(0,[z0,z1,z2,z3,z26,z1029]),(0,[z61,z1,z2,z3,z98,z54]),(0,[z61,z225,z1,z2,z3,z7]),(0,[z0,z100,z522,z2,z7,z6]),(0,[z0,z1,z2,z24,z718,z6])],[(0,[z263,z1,z2,z18,z3,z5]),(0,[z0,z1,z2,z3,z1090,z6]),(0,[z0,z1,z36,z3,z7,z797])],[(0,[z0,z1,z2,z3,z276,z6]),(0,[z0,z1,z2,z3,z26,z224]),(0,[z0,z305,z2,z3,z7,z52])],[(0,[z0,z1,z2,z3,z5,z310]),(0,[z85,z1,z102,z3,z7,z6]),(0,[z67,z1,z195,z18,z3,z7]),(0,[z0,z1,z2,z3,z1091,z6]),(0,[z302,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z7,z6,z1092]),(0,[z0,z1,z2,z3,z7,z507]),(0,[z0,z1,z1093,z2,z7,z6])],[(0,[z85,z1,z102,z3,z174,z6]),(0,[z0,z1,z2,z16,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z7,z1094]),(0,[z0,z263,z1,z36,z3,z7]),(0,[z0,z1,z2,z86,z20,z6]),(0,[z53,z1,z2,z3,z7,z886]),(0,[z0,z1,z46,z3,z763,z6])],[(0,[z0,z1,z2,z3,z7,z310]),(0,[z0,z1,z2,z3,z7,z1095]),(0,[z1,z2,z3,z187,z26,z6]),(0,[z0,z1,z57,z62,z7,z6]),(0,[z0,z1,z590,z2,z7,z32])],[(0,[z0,z1,z2,z16,z7,z6])],[(0,[z0,z1,z2,z106,z533,z6]),(0,[z0,z1,z2,z416,z26,z6]),(0,[z0,z72,z57,z3,z7,z6]),(0,[z0,z1,z1096,z2,z3,z6]),(0,[z0,z1,z2,z3,z6,z1097]),(0,[z180,z1,z2,z23,z3,z6])],[(0,[z0,z1,z2,z3,z216,z177]),(0,[z0,z1,z2,z3,z395,z6]),(0,[z0,z1,z2,z1098,z7,z6]),(0,[z0,z112,z771,z3,z7,z6]),(0,[z0,z1,z2,z7,z791,z32])],[(0,[z0,z1,z1099,z3,z7,z6]),(0,[z0,z1,z2,z1100,z7,z6]),(0,[z0,z1,z2,z3,z5,z249]),(0,[z0,z108,z1,z925,z7,z6]),(0,[z0,z79,z1,z16,z7,z255])],[(0,[z0,z2,z3,z7,z1101,z6]),(0,[z0,z1,z2,z1102,z3,z6])],[(0,[z0,z263,z1,z57,z3,z7]),(0,[z0,z1,z2,z3,z1103,z6])]],
   [[(0,[z0,z1,z2,z3,z7,z249])],[(0,[z0,z1,z2,z3,z7,z1104]),(0,[z180,z1,z89,z2,z3,z6]),(0,[z0,z1,z1105,z3,z7,z6])],[(0,[z1,z329,z2,z3,z5,z6]),(0,[z1,z331,z2,z3,z5,z6]),(0,[z0,z79,z171,z2,z3,z7]),(0,[z0,z1,z2,z62,z239,z6]),(0,[z0,z1,z2,z62,z98,z6]),(0,[z0,z1,z2,z7,z93,z1011]),(0,[z0,z1,z2,z973,z7,z6]),(0,[z0,z1,z2,z3,z1106,z6])],[(0,[z0,z1,z2,z3,z7,z1107]),(0,[z0,z1,z194,z3,z26,z6]),(0,[z0,z1,z423,z60,z7,z6]),(0,[z0,z1,z2,z3,z26,z1053]),(0,[z0,z1,z2,z3,z1108,z6]),(0,[z9,z0,z2,z7,z10,z295])],[(0,[z0,z1,z2,z3,z352,z6]),(0,[z53,z1,z2,z3,z5,z97]),(0,[z0,z27,z2,z3,z462,z6]),(0,[z0,z72,z2,z3,z239,z6]),(0,[z0,z72,z2,z3,z98,z6]),(0,[z0,z1,z2,z3,z7,z1109])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z101,z7,z146]),(0,[z0,z1,z2,z3,z1110,z6]),(0,[z339,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z514,z150,z6]),(0,[z0,z1,z2,z3,z7,z798])],[(0,[z90,z59,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z7,z773]),(0,[z0,z1,z154,z3,z117,z6]),(0,[z0,z171,z251,z3,z7,z6]),(0,[z0,z1,z2,z1111,z7,z6]),(0,[z0,z56,z2,z3,z874,z6])],[(0,[z0,z1112,z2,z3,z7,z6]),(0,[z0,z108,z1,z576,z7,z6]),(0,[z53,z1,z2,z3,z7,z97]),(0,[z248,z0,z39,z19,z7,z6])]],
   [[(0,[z0,z1,z2,z3,z7,z6]),(0,[z0,z79,z1,z3,z5,z255]),(0,[z232,z1,z2,z3,z26,z6]),(0,[z61,z171,z2,z3,z7,z54])],[(0,[z0,z1,z1113,z3,z7,z6]),(0,[z0,z1,z2,z3,z1114,z6])],[(0,[z0,z1,z2,z3,z1115,z6]),(0,[z0,z1,z2,z1116,z7,z6]),(0,[z0,z1,z2,z435,z26,z6]),(0,[z0,z1,z2,z3,z1117,z6])],[(0,[z0,z1,z1118,z2,z3,z6]),(0,[z0,z79,z1,z3,z7,z255])],[(0,[z0,z1,z21,z3,z5,z6]),(0,[z1119,z1,z2,z3,z7,z6])],[(0,[z58,z115,z194,z3,z7,z6]),(0,[z0,z1,z1120,z3,z7,z6]),(0,[z0,z1,z1121,z2,z3,z7]),(0,[z0,z1,z500,z3,z26,z6]),(0,[z0,z1,z2,z3,z1122,z6]),(0,[z0,z1,z2,z3,z763,z6]),(0,[z0,z1,z2,z101,z7,z791])],[(0,[z0,z1,z2,z3,z1123,z6]),(0,[z0,z1,z2,z3,z1124,z6]),(0,[z82,z1,z2,z68,z26,z6]),(0,[z0,z1,z2,z62,z26,z6]),(0,[z1,z2,z3,z1125,z7,z6]),(0,[z0,z1,z89,z2,z510,z6])],[(0,[z0,z1,z1126,z3,z7,z6]),(0,[z0,z1,z21,z3,z7,z6]),(0,[z1,z2,z762,z68,z7,z6]),(0,[z0,z1,z2,z7,z6,z1127]),(0,[z0,z1,z2,z1128,z3,z6])]],
   [[(0,[z0,z1,z2,z3,z7,z1129]),(0,[z1,z2,z3,z20,z5,z6]),(0,[z0,z1,z2,z3,z5,z40]),(0,[z0,z1130,z2,z3,z7,z6]),(0,[z0,z72,z2,z3,z26,z6]),(0,[z0,z1,z57,z3,z7,z134])],[(0,[z0,z1,z2,z1131,z7,z6]),(0,[z0,z1,z2,z3,z7,z1132]),(0,[z0,z361,z2,z3,z7,z52])],[],[(0,[z0,z1,z194,z3,z7,z310]),(0,[z0,z1133,z2,z3,z7,z6]),(0,[z219,z1,z2,z37,z7,z6]),(0,[z0,z1,z2,z3,z7,z40]),(0,[z0,z27,z2,z3,z874,z6]),(0,[z1134,z1,z2,z3,z7,z6])],[(0,[z0,z263,z1,z2,z942,z7]),(0,[z0,z1,z57,z3,z5,z6])],[(0,[z0,z1,z2,z1135,z3,z6]),(0,[z0,z1,z1136,z2,z3,z6]),(0,[z0,z27,z2,z3,z69,z458])],[(0,[z0,z727,z2,z3,z7,z6]),(0,[z0,z1,z2,z1137,z7,z6]),(0,[z0,z1,z690,z2,z3,z335]),(0,[z0,z1,z2,z1138,z7,z6]),(0,[z0,z1,z2,z3,z26,z1086]),(0,[z1139,z1,z2,z3,z7,z6])],[(0,[z0,z1,z57,z3,z7,z6]),(0,[z0,z1,z2,z3,z7,z1140]),(0,[z0,z1,z2,z617,z420,z6]),(0,[z0,z1,z2,z26,z868,z6]),(0,[z570,z1,z2,z3,z26,z6]),(0,[z0,z171,z2,z62,z7,z6])]],
   [[(0,[z0,z1,z2,z3,z1141,z6]),(0,[z0,z1,z2,z1142,z7,z6])],[(0,[z0,z260,z2,z3,z463,z6]),(0,[z0,z305,z2,z3,z26,z52]),(0,[z61,z1,z2,z3,z7,z316]),(0,[z0,z1,z2,z925,z7,z6]),(0,[z0,z1,z70,z2,z3,z6]),(0,[z0,z646,z1,z3,z7,z255])],[(0,[z0,z1,z2,z3,z1143,z6]),(0,[z0,z1,z2,z3,z1144,z6]),(0,[z85,z1,z102,z3,z26,z6]),(0,[z0,z1,z2,z3,z26,z507])],[(0,[z0,z1145,z2,z3,z7,z6]),(0,[z0,z1,z2,z5,z6,z295]),(0,[z53,z1,z331,z2,z3,z7]),(1,[z0,z1,z2,z7,z791])],[(0,[z1,z727,z2,z3,z7,z6]),(0,[z0,z171,z2,z3,z7,z97]),(0,[z0,z1,z2,z3,z1146,z6])],[(0,[z0,z1,z2,z3,z26,z310]),(0,[z0,z1,z2,z3,z1147,z6]),(0,[z0,z1,z251,z233,z7,z6]),(0,[z248,z0,z210,z19,z7,z6]),(0,[z0,z1,z3,z925,z7,z6]),(0,[z0,z1,z1148,z2,z3,z7])],[(0,[z0,z1,z2,z16,z26,z6])],[(0,[z61,z1,z2,z233,z7,z54]),(0,[z0,z1,z2,z3,z7,z1149]),(0,[z0,z56,z2,z3,z237,z6]),(0,[z0,z1,z2,z3,z1150,z6]),(0,[z1151,z1,z2,z3,z7,z6]),(0,[z48,z0,z1,z3,z763,z6]),(0,[z0,z1,z2,z23,z24,z6])]],
   [[(0,[z1,z18,z60,z3,z5,z6]),(0,[z0,z1,z500,z3,z395,z6]),(0,[z0,z1,z2,z3,z98,z6]),(0,[z0,z1,z2,z3,z239,z6]),(0,[z0,z1,z65,z2,z3,z798])],[(0,[z213,z1,z2,z3,z708,z6]),(0,[z0,z1152,z2,z3,z7,z6])],[(0,[z90,z59,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1153,z6]),(0,[z0,z646,z1,z186,z7,z6])],[(0,[z0,z1,z2,z3,z1154,z6])],[(0,[z0,z1,z2,z3,z1155,z6]),(0,[z0,z1,z2,z3,z1156,z6]),(0,[z213,z1,z2,z3,z26,z6]),(0,[z0,z1,z2,z3,z26,z249]),(0,[z1,z2,z3,z315,z26,z6]),(0,[z0,z1,z2,z1157,z7,z6])],[(0,[z0,z1,z2,z7,z6,z1158]),(0,[z0,z1,z2,z3,z1159,z6]),(0,[z67,z1,z18,z3,z368,z6]),(0,[z358,z1,z2,z68,z7,z6]),(0,[z0,z1,z690,z2,z3,z66]),(0,[z0,z39,z1,z2,z7,z1040]),(0,[z1160,z1,z2,z3,z7,z6])],[(0,[z336,z1,z2,z3,z5,z6]),(0,[z0,z1,z1161,z3,z7,z6]),(0,[z61,z1,z251,z3,z7,z54])],[(0,[z58,z115,z2,z3,z7,z310]),(0,[z0,z1,z3,z7,z921,z6]),(0,[z0,z304,z2,z196,z7,z6]),(0,[z0,z2,z3,z5,z1101,z6]),(0,[z1,z2,z3,z7,z886,z54]),(0,[z0,z1,z925,z186,z7,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 530) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 530).take 531) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1061).take 160) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1221)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [530, 531, 160] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 113).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 113).take 125).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 238).take 18).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [113, 125, 18] = true :=
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

end PEqualNP.Outside.L_meta_40517

theorem PEqualNP.Outside.L_meta_40517 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4243120288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4243120288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_40517.solve