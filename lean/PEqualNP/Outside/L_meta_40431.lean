import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40431

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
  Nat.testBit (4276809448 * 2 ^ 32 + 4240501952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x08115831bc661e62#64 ++ 0x21022b06378cc3cc#64 ++ 0xe833fa73fc663e67#64 ++ 0xdd067f4e7f8cc7cc#64 : BitVec 256),
   (0x0044c084502a82a8#64 ++ 0x400898108a055055#64 ++ 0xf8ccc58c707fc7ff#64 ++ 0xbf1998b18e0ff8ff#64 : BitVec 256),
   (0x030b060a85856850#64 ++ 0x806160c150b0ad0a#64 ++ 0xbf0f060f8f87f87f#64 ++ 0x77e1e0c1f1f0ff0f#64 : BitVec 256),
   (0x05b007500ad07503#64 ++ 0x00b600ea015a0ea0#64 ++ 0xdff007f00ff87f86#64 ++ 0xfbfe00fe01ff0ff0#64 : BitVec 256),
   (0x16ffe8000f7f8004#64 ++ 0x02dffd0001eff000#64 ++ 0x97fff8000fff8005#64 ++ 0xf2ffff0001fff000#64 : BitVec 256),
   (0x27eeb7ef60000000#64 ++ 0x04fdd6fdec000000#64 ++ 0xe7fffffff0000003#64 ++ 0xfcfffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 5]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [10, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [9, 7]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00c040c00000003 0x3401808180000000

def z1 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0xf8ccc58c707fc7ff 0xbf1998b18e0ff8ff

def z2 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0xbf0f060f8f87f87f 0x77e1e0c1f1f0ff0f

def z3 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0xdff007f00ff87f86 0xfbfe00fe01ff0ff0

def z4 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0xe833fa73fc663e67 0xdd067f4e7f8cc7cc

def z5 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x97fff8000fff8005 0xf2ffff0001fff000

def z6 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0xe7fffffff0000003 0xfcfffffffe000000

def z7 : W := mkw 0x04b000000a500000 0x00960000014a0000 0x073000000f800000 0x40e6000001f00000

def z8 : W := mkw 0x16bb28000f550004 0x02d7650001eaa000 0x073338000f800000 0x40e6670001f00000

def z9 : W := mkw 0x0001000084040840 0x0000200010808108 0xa80302038c063867 0x550060407180c70c

def z10 : W := mkw 0x081148109c661e62 0x21022902138cc3cc 0x080000000c663e64 0x01000000018cc7cc

def z11 : W := mkw 0x0010401018621622 0x00020802030c42c4 0xe830c2707c663e67 0xdd06184e0f8cc7cc

def z12 : W := mkw 0x024fc084552f82a8 0x4049f8108aa5f055 0xffcfc58c7fffc7ff 0xfff9f8b18ffff8ff

def z13 : W := mkw 0x0044808440000000 0x0008901088000000 0xf8ccc58c7007c07f 0xbf1998b18e00f80f

def z14 : W := mkw 0x0100075000807503 0x002000ea00100ea0 0x480007f000007f82 0x090000fe00000ff0

def z15 : W := mkw 0x04b000000a500000 0x00960000014a0000 0x97f000000ff80004 0xf2fe000001ff0000

def z16 : W := mkw 0x08001031b0001e62 0x21000206360003cc 0x68000273f0003e62 0x0d00004e7e0007cc

def z17 : W := mkw 0x210017ff60807503 0x042002ffec100ea0 0x680007fff0007f82 0x0d0000fffe000ff0

def z18 : W := mkw 0x001148000c660000 0x00022900018cc000 0x000000000c660004 0x00000000018cc000

def z19 : W := mkw 0x0db15f71bef67f63 0x21b62bee37decfec 0xfff3fff3fffe7fe7 0xfffe7ffe7fffcffc

def z20 : W := mkw 0x16ffe8845f7f82ac 0x42dffd108beff055 0xfffffd8c7fffc7ff 0xffffffb18ffff8ff

def z21 : W := mkw 0x0db01771bad07f63 0x21b602ee375a0fec 0xfff007f3fff87fe6 0xfffe00fe7fff0ffc

def z22 : W := mkw 0x0110075008c07503 0x002200ea01180ea0 0xc83007f00c607f86 0xd90600fe018c0ff0

def z23 : W := mkw 0x0010001008401402 0x0002000201080280 0xc83002700c603e06 0xd906004e018c07c0

def z24 : W := mkw 0x06eea00000000000 0x00ddd40000000000 0x87fff80000000001 0xf0ffff0000000000

def z25 : W := mkw 0x0100060a80806850 0x802000c150100d0a 0x2800060f8000787a 0x050000c1f0000f0f

def z26 : W := mkw 0x124fe800052f8004 0x0249fd0000a5f000 0x000ff80000078001 0x0001ff000000f000

def z27 : W := mkw 0x030a060a00000000 0x006140c140000000 0xa70f060f80000003 0x74e1e0c1f0000000

def z28 : W := mkw 0x001000000a500000 0x00020000014a0000 0x100000000ff80004 0x0200000001ff0000

def z29 : W := mkw 0x0844d0b5f02a9eea 0x61089a16be0553dd 0xf8ccc7fff07fffff 0xbf1998fffe0fffff

def z30 : W := mkw 0x16ffa8000f5d8004 0x02dff50001ebb000 0x17ff38000f998000 0x62ffe70001f33000

def z31 : W := mkw 0x020b000005050000 0x0041600000a0a000 0xbf0f040c0f87c07f 0x77e1e08181f0f80f

def z32 : W := mkw 0x0a1b583bbd671e72 0xa1436b0777ace3ce 0xe83ffa7ffc67be7f 0xdd07ff4fff8cf7cf

def z33 : W := mkw 0x0001000085050850 0x8000200010a0a10a 0x0000000000078078 0x000000000000f00f

def z34 : W := mkw 0x05b0075a8ad07d53 0x80b600eb515a0faa 0xfff007ff8ff87ffe 0xfffe00fff1ff0fff

def z35 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0x30ccc58c701fc1f9 0x261998b18e03f83f

def z36 : W := mkw 0x030b075a85857d53 0x806160eb50b0afaa 0xff0f07ff8f87ffff 0x7fe1e0fff1f0ffff

def z37 : W := mkw 0x2a5ff8bffc661e62 0x254bff17ff8cc3cc 0xe83ffa7ffc663e67 0xdd07ff4fff8cc7cc

def z38 : W := mkw 0x0044c084402a8088 0x4008981088055011 0x90ccc58c007fc19d 0xb21998b1800ff833

def z39 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0x4033fa73fc603e00 0xc8067f4e7f8c07c0

def z40 : W := mkw 0x0854d8b5786a96aa 0x610a9b16af0d52d5 0x40f0f9f070780780 0x881e1f3e0e0f00f0

def z41 : W := mkw 0x17ffef500ffff507 0x02fffdea01fffea0 0xdffffff00fffff87 0xfbfffffe01fffff0

def z42 : W := mkw 0x1efff831bf7f9e66 0x23dfff0637eff3cc 0xfffffa73ffffbe67 0xffffff4e7ffff7cc

def z43 : W := mkw 0x14f4e8845a7a82ac 0x429e9d108b4f5055 0xf8fcfd8c707fc7ff 0xbf1f9fb18e0ff8ff

def z44 : W := mkw 0x210017ef60000000 0x042002fdec000000 0x600007fff0000002 0x0c0000fffe000000

def z45 : W := mkw 0x0001400095afeaf8 0xc000280012b5fd5f 0x180000000ffffffc 0x0300000001ffffff

def z46 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0x200cc00c70078079 0x040198018e00f00f

def z47 : W := mkw 0x0044808440088088 0x4008901088011011 0x10cc058c0019c198 0x221980b180033833

def z48 : W := mkw 0x04b001500a501503 0x0096002a014a02a0 0x40f001f000780780 0x881e003e000f00f0

def z49 : W := mkw 0x07bb075a8fd57d53 0x80f760eb51faafaa 0xffff07ff8fffffff 0xffffe0fff1ffffff

def z50 : W := mkw 0x05a0074002906101 0x00b400e800520c20 0x17c0058003984180 0x22f800b000730830

def z51 : W := mkw 0x031b4e0a8de76850 0x806369c151bced0a 0xbf3ffe0f8fe7f87f 0xf7e7ffc1f1fcff0f

def z52 : W := mkw 0x0000000000000000 0x0000000000000000 0xd8c0058000784786 0xbb1800b0000f08f0

def z53 : W := mkw 0x034fc68ed5afeaf8 0xc069f8d1dab5fd5f 0xbf0fc60fff87f87f 0x77e1f8c1fff0ff0f

def z54 : W := mkw 0x27aa376b20000000 0x04f546ed64000000 0x07333a7380000000 0x40e6674e70000000

def z55 : W := mkw 0x224eb0af60000000 0x0449d615ec000000 0x200ff80ff0000001 0x0401ff01fe000000

def z56 : W := mkw 0x27eef7ef702a82a8 0x44fddefdee055055 0xfffffffff07fc7ff 0xfffffffffe0ff8ff

def z57 : W := mkw 0x0000000000000000 0x0000000000000000 0xb80c040c0007c07f 0x370180818000f80f

def z58 : W := mkw 0x00000084500002a8 0x400000108a000055 0x6800058c700047fa 0x0d0000b18e0008ff

def z59 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0xd8c0c58070784786 0xbb1818b00e0f08f0

def z60 : W := mkw 0x030a060a01816010 0x806140c140302c02 0x170c040c0381c018 0x22e1808180703803

def z61 : W := mkw 0x27eeb7ef61816010 0x84fdd6fdec302c02 0xf7fffffff381c01b 0xfefffffffe703803

def z62 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0xe0ccc58c7007807b 0xbc1998b18e00f00f

def z63 : W := mkw 0x0000000000000000 0x0000000000000000 0xe000c00070000003 0x9c0018000e000000

def z64 : W := mkw 0x0000102120000000 0x0000020424000000 0xe033fa73f0000003 0xdc067f4e7e000000

def z65 : W := mkw 0x081148109c661e62 0x21022902138cc3cc 0x8833f8000c663e65 0xd1067f00018cc7cc

def z66 : W := mkw 0x0db15f71bef67f63 0x21b62bee37decfec 0xef33fa73ffe63e67 0xdde67f4e7ffcc7cc

def z67 : W := mkw 0x001148000c660000 0x00022900018cc000 0x8033f8000c660005 0xd0067f00018cc000

def z68 : W := mkw 0x08015821b4260a60 0x21002b043684c14c 0x2003f803f0060061 0x04007f007e00c00c

def z69 : W := mkw 0x030a060a00000000 0x006140c140000000 0x070c040c00000000 0x20e1808180000000

def z70 : W := mkw 0x081148109c661e62 0x21022902138cc3cc 0xa80302038c663e67 0x55006040718cc7cc

def z71 : W := mkw 0x16eea00003198004 0x02ddd40000633000 0x17cc000003998000 0x22f9800000733000

def z72 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0x1fc005800ff87f84 0x23f800b001ff0ff0

def z73 : W := mkw 0x27eea7ce40000000 0x04fdd4f9c8000000 0x07cc058c00000000 0x20f980b180000000

def z74 : W := mkw 0x37eea7ce43198004 0x06fdd4f9c8633000 0x17cc058c03998000 0x22f980b180733000

def z75 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0x47f3fbf3f0000000 0xc8fe7f7e7e000000

def z76 : W := mkw 0x06fea0000a500000 0x00dfd400014a0000 0x97fff8000ff80005 0xf2ffff0001ff0000

def z77 : W := mkw 0x0044808440088088 0x4008901088011011 0x000c000c00018018 0x0001800180003003

def z78 : W := mkw 0x080010b5f0001eea 0x61000216be0003dd 0x680007fff0007ffa 0x0d0000fffe000fff

def z79 : W := mkw 0x04b000000a500000 0x00960000014a0000 0xdff005800ff84786 0xfbfe00b001ff08f0

def z80 : W := mkw 0x0100060000806000 0x002000c000100c00 0x9f0006000f807806 0x73e000c001f00f00

def z81 : W := mkw 0x07bb075a8fd57d53 0x80f760eb51faafaa 0x073302738f803800 0x40e6604e71f00700

def z82 : W := mkw 0x2ffffffffef67f63 0x25ffffffffdecfec 0xfffffffffffe7fe7 0xffffffffffffcffc

def z83 : W := mkw 0x05f4c7d45afaf7ab 0x40be98fa8b5f5ef5 0xfffcc7fc7fffffff 0xffff98ff8fffffff

def z84 : W := mkw 0x05b047501af27723 0x00b608ea035e4ee4 0xfff0c7f07ffe7fe7 0xfffe18fe0fffcffc

def z85 : W := mkw 0x001000100ad07503 0x00020002015a0ea0 0x180000000ff87f84 0x0300000001ff0ff0

def z86 : W := mkw 0x27feb7ff6ad07503 0x04ffd6ffed5a0ea0 0xfffffffffff87f87 0xffffffffffff0ff0

def z87 : W := mkw 0x27aa37ef60000000 0x04f546fdec000000 0x67333ffff0000002 0x4ce667fffe000000

def z88 : W := mkw 0x2100176b20000000 0x042002ed64000000 0x0000027380000000 0x0000004e70000000

def z89 : W := mkw 0x16ffe8100ffff507 0x02dffd0201fffea0 0x9ffff8000fffff85 0xf3ffff0001fffff0

def z90 : W := mkw 0x230b17efe5856850 0x846162fdfcb0ad0a 0xff0f07ffff87f87f 0x7fe1e0fffff0ff0f

def z91 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x073ff8000f878001 0x40e7ff0001f0f000

def z92 : W := mkw 0x0044800000000000 0x0008900000000000 0x80ccc00000000001 0xb019980000000000

def z93 : W := mkw 0x021b48000d670000 0x0043690001ace000 0x973ff8000fe78005 0xf2e7ff0001fcf000

def z94 : W := mkw 0x08001031a0001c42 0x2100020634000388 0x0000027380003800 0x0000004e70000700

def z95 : W := mkw 0x06bb00000f550000 0x00d7600001eaa000 0x97ff00000fff8005 0xf2ffe00001fff000

def z96 : W := mkw 0x16fee8000b7b8004 0x02dfdd00016f7000 0x17fcf80003f98000 0xa2ff9f00007f3000

def z97 : W := mkw 0x020b000005050000 0x0041600000a0a000 0x970f00000f878005 0x72e1e00001f0f000

def z98 : W := mkw 0x17ffee0a8fffe854 0x82fffdc151fffd0a 0xbffffe0f8ffff87f 0xf7ffffc1f1ffff0f

def z99 : W := mkw 0x210017ef60000000 0x042002fdec000000 0xe033fffff0000003 0xdc067ffffe000000

def z100 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0x073002700f803800 0x40e6004e01f00700

def z101 : W := mkw 0x0855d8b5fc6e9eea 0x610abb16bf8dd3dd 0xf8fffffffc7fffff 0xff1fffffff8fffff

def z102 : W := mkw 0x27aa274a00000000 0x04f544e940000000 0x0700000000000000 0x00e0000000000000

def z103 : W := mkw 0x0000000000000000 0x0000000000000000 0xf8cc058c007fc7ff 0xbf1980b1800ff8ff

def z104 : W := mkw 0x0001000085856850 0x8000200010b0ad0a 0x180000000f87f87c 0x0300000001f0ff0f

def z105 : W := mkw 0x24e4b1e560000000 0x049c963cac000000 0x40f0f9f070000000 0x881e1f3e0e000000

def z106 : W := mkw 0x0db11f71aed47d43 0x21b623ee35da8fa8 0xdff33ff38ff87f86 0xfbfe67fe71ff0ff0

def z107 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0x970f02038f87b805 0x72e1e04071f0f700

def z108 : W := mkw 0x08005031b0221e62 0x21000a06360443cc 0xe800c273f0663e67 0x9d00184e7e0cc7cc

def z109 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0xffcf078f8fffffff 0xfff9e0f1f1ffffff

def z110 : W := mkw 0x0000001000001402 0x0000000200000280 0x4800027000003e02 0x0900004e000007c0

def z111 : W := mkw 0x0001480004260000 0x000029000084c000 0x0003f80000060001 0x00007f000000c000

def z112 : W := mkw 0x06eea00000000000 0x00ddd40000000000 0x07cc000000000000 0x20f9800000000000

def z113 : W := mkw 0x0044c084402a8000 0x0008981088055000 0xf0ccc58c707f8007 0xbe1998b18e0ff000

def z114 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0x2033fa73fc063861 0x44067f4e7f80c70c

def z115 : W := mkw 0x0000000000088088 0x4000000000011011 0x100000000019c198 0x0200000000033833

def z116 : W := mkw 0x031b061a8fd57d53 0x806360c351faafaa 0xbf0f060f8fffffff 0x77e1e0c1f1ffffff

def z117 : W := mkw 0x1fffff71bfffff67 0x23ffffee37ffffec 0xfffffff3ffffffe7 0xfffffffe7ffffffc

def z118 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0x9f3006700f807806 0x73e600ce01f00f00

def z119 : W := mkw 0x0b1b5e3bbde77e72 0xa1636bc777bcefce 0xef33fa73ffe63e67 0xdde67f4e7ffcc7cc

def z120 : W := mkw 0x001000100ad07503 0x00020002015a0ea0 0xd8c005800ff87f86 0xbb1800b001ff0ff0

def z121 : W := mkw 0x09001771b0807f63 0x212002ee36100fec 0x680007f3f0007fe2 0x0d0000fe7e000ffc

def z122 : W := mkw 0x0100068ed0806af8 0xc02000d1da100d5f 0x6800078ff0007ffa 0x0d0000f1fe000fff

def z123 : W := mkw 0x17ffef5a8ffffd57 0x82fffdeb51ffffaa 0xffffffff8fffffff 0xfffffffff1ffffff

def z124 : W := mkw 0x05a0074000000000 0x00b400e800000000 0xc7f007f000000002 0xf8fe00fe00000000

def z125 : W := mkw 0x0100060000806000 0x002000c000100c00 0xbf0c060c0f87f87f 0x77e180c181f0ff0f

def z126 : W := mkw 0x07bb07500fd57503 0x00f760ea01faaea0 0xdfff07f00fffff87 0xfbffe0fe01fffff0

def z127 : W := mkw 0x27eeb7efe0806850 0x84fdd6fdfc100d0a 0xeffffffff000787b 0xfdfffffffe000f0f

def z128 : W := mkw 0x00004000102a82a8 0x4000080002055055 0x18000000007fc7fc 0x03000000000ff8ff

def z129 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0x27cffd8ff0000001 0x24f9ffb1fe000000

def z130 : W := mkw 0x37ffffef6f7f8004 0x06fffffdedeff000 0xf7ffffffffff8007 0xfefffffffffff000

def z131 : W := mkw 0x0000000000000000 0x0000000000000000 0x180000000007c07c 0x030000000000f80f

def z132 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0x070302038f803800 0x40e0604071f00700

def z133 : W := mkw 0x0001000084040840 0x0000200010808108 0xb80f060f8c07f87f 0x7701e0c1f180ff0f

def z134 : W := mkw 0x101108000f550004 0x0202210001eaa000 0x000000000f800000 0x0000000001f00000

def z135 : W := mkw 0x0000000000806000 0x0000000000100c00 0x180000000f807804 0x0300000001f00f00

def z136 : W := mkw 0x27eea7ce41816010 0x84fdd4f9c8302c02 0x17cc058c0381c018 0x22f980b180703803

def z137 : W := mkw 0x06efa00005050000 0x00ddf40000a0a000 0x97fff8000f878005 0xf2ffff0001f0f000

def z138 : W := mkw 0x06eeb02120000000 0x00ddd60424000000 0xe7fffa73f0000003 0xfcffff4e7e000000

def z139 : W := mkw 0x16fff8212f7f8004 0x02dfff0425eff000 0xf7fffa73ffff8007 0xfeffff4e7ffff000

def z140 : W := mkw 0x101148000f7f8004 0x0202290001eff000 0x100000000fff8004 0x0200000001fff000

def z141 : W := mkw 0x0000000000000000 0x0000000000000000 0x900c000000078005 0x320180000000f000

def z142 : W := mkw 0x0855d8b5fc6e9eea 0x610abb16bf8dd3dd 0xe8f3fbf3fc7e3fe7 0xdd1e7f7e7f8fc7fc

def z143 : W := mkw 0x27eef7ef602a8000 0x04fddefdec055000 0xf7fffffff07f8007 0xfefffffffe0ff000

def z144 : W := mkw 0x0001000085856850 0x8000200010b0ad0a 0xb80c040c0f87f87f 0x3701808181f0ff0f

def z145 : W := mkw 0x020b000a85856850 0x8041600150b0ad0a 0x380f000f8f87f87d 0x0701e001f1f0ff0f

def z146 : W := mkw 0x125fe8000f7f8004 0x024bfd0001eff000 0x100ff8000fff8005 0x0201ff0001fff000

def z147 : W := mkw 0x0010103128401402 0x0002020625080280 0xe833fa73fc603e07 0xdd067f4e7f8c07c0

def z148 : W := mkw 0x27ffffef6c660000 0x04fffffded8cc000 0xe7fffffffc660007 0xfcffffffff8cc000

def z149 : W := mkw 0x17fea7500bd9f507 0x02ffd4ea017b3ea0 0xdffc07f00ff9ff86 0xfbff80fe01ff3ff0

def z150 : W := mkw 0x020b000a85050850 0x8041600150a0a10a 0xb80f040f8007c07f 0x3701e081f000f80f

def z151 : W := mkw 0x05b047501afaf7ab 0x40b608ea035f5ef5 0xdff007f00ffffffe 0xfbfe00fe01ffffff

def z152 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0x47fcfdfc70000000 0xa8ff9fbf8e000000

def z153 : W := mkw 0x16aa200003110004 0x02d5440000622000 0x0700000003800000 0x00e0000000700000

def z154 : W := mkw 0x37ffbfef6f550004 0x06fff7fdedeaa000 0xe7ffffffff800003 0xfcfffffffff00000

def z155 : W := mkw 0x14f5e8000f7f8004 0x029ebd0001eff000 0x10f0f8000fff8004 0x821e1f0001fff000

def z156 : W := mkw 0x0db14f509ef67f63 0x21b629ea13decfec 0xdff007f00ffe7fe6 0xfbfe00fe01ffcffc

def z157 : W := mkw 0x020b000085856850 0x8041600010b0ad0a 0x9f0f00000f87f87d 0x73e1e00001f0ff0f

def z158 : W := mkw 0x05e487c44298e189 0x40bc90f888531c31 0x17cc058c0399c198 0x22f980b180733833

def z159 : W := mkw 0x1055c8000f7f8004 0x020ab90001eff000 0x90ccc0000fff8005 0xb219980001fff000

def z160 : W := mkw 0x17bb2e0a8fd56854 0x82f765c151faad0a 0x07333a038f803800 0x40e6674071f00700

def z161 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0x280f060f8007f87b 0x0501e0c1f000ff0f

def z162 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0x40c0c18070780780 0x881818300e0f00f0

def z163 : W := mkw 0x16bb28000f550004 0x02d7650001eaa000 0x973f38000f878005 0x72e7e70001f0f000

def z164 : W := mkw 0x0845d8a5f42e8ae8 0x6108bb14be85d15d 0x200ff80ff0078079 0x0401ff01fe00f00f

def z165 : W := mkw 0x1efff8b5ff7f9eee 0x63dfff16bfeff3dd 0xffffffffffffffff 0xffffffffffffffff

def z166 : W := mkw 0x27feb7ff6ad07503 0x04ffd6ffed5a0ea0 0xe7ffffffff803803 0xfcfffffffff00700

def z167 : W := mkw 0x2fefffeff4260a60 0x25fdfffdfe84c14c 0xe7fffffff0060063 0xfcfffffffe00c00c

def z168 : W := mkw 0x27eea7ce42906101 0x04fdd4f9c8520c20 0x17cc058c03984180 0x22f980b180730830

def z169 : W := mkw 0x0044c000102a8220 0x0008980002055044 0xf8ccc000707f8667 0xbf1998000e0ff0cc

def z170 : W := mkw 0x001108000c440000 0x0002210001888000 0x003338000c000000 0x4006670001800000

def z171 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0x6033f873f0660661 0x8c067f0e7e0cc0cc

def z172 : W := mkw 0x0900163bb0807e72 0xa12002c776100fce 0x6800067ff0007e7a 0x0d0000cffe000fcf

def z173 : W := mkw 0x07ba075a0bd17513 0x80f740eb417a2ea2 0xdffc07fc0ff9ff9e 0xfbff80ff81ff3ff3

def z174 : W := mkw 0x0810583138621622 0x21020b06270c42c4 0xe033fa73f0600603 0xdc067f4e7e0c00c0

def z175 : W := mkw 0x0000400010220220 0x0000080002044044 0x0800000000660664 0x01000000000cc0cc

def z176 : W := mkw 0x08001031b0001e62 0x21000206360003cc 0xe833fa73f0003e63 0xdd067f4e7e0007cc

def z177 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0x07ff3fff80000000 0x60ffe7fff0000000

def z178 : W := mkw 0x16eee000033b8004 0x02dddc0000677000 0x97ccc00003ff8005 0xb2f99800007ff000

def z179 : W := mkw 0x034fc60a85afe850 0x8069f8c150b5fd0a 0xbfcfc60f8ffff87f 0xf7f9f8c1f1ffff0f

def z180 : W := mkw 0x08015831b4261e62 0x21002b063684c3cc 0x6803fa73f0063e63 0x0d007f4e7e00c7cc

def z181 : W := mkw 0x37eeb7ef63198004 0x06fdd6fdec633000 0xf7fffffff3998003 0xfefffffffe733000

def z182 : W := mkw 0x16eea00003198004 0x02ddd40000633000 0x97fff80003998001 0xf2ffff0000733000

def z183 : W := mkw 0x030a060a80806850 0x806140c150100d0a 0xaf0f060f8000787b 0x75e1e0c1f0000f0f

def z184 : W := mkw 0x07ffc7dedffffffb 0xc0fff8fbdbffffff 0xffffc7ffffffffff 0xfffff8ffffffffff

def z185 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0xf8f3fff3fc7e7fe7 0xff1e7ffe7f8fcffc

def z186 : W := mkw 0x030b460a95a76a70 0x806168c152b4ed4e 0xff0fc60fffe7fe7f 0xffe1f8c1fffcffcf

def z187 : W := mkw 0x004490a560000000 0x00089214ac000000 0xe0fffffff0000003 0xfc1ffffffe000000

def z188 : W := mkw 0x27eeb7ef62906101 0x04fdd6fdec520c20 0xf7fffffff3984183 0xfefffffffe730830

def z189 : W := mkw 0x26eeb1ef60000000 0x04ddd63dec000000 0x60fff9fff0000001 0x8c1fff3ffe000000

def z190 : W := mkw 0x16efe800073f8004 0x02ddfd0000e7f000 0x17cff800039f8001 0x22f9ff000073f000

def z191 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x07f3f8000ff80000 0xc0fe7f0001ff0000

def z192 : W := mkw 0x27efb7efe5856850 0x84fdf6fdfcb0ad0a 0xe7ffffffff803803 0xfcfffffffff00700

def z193 : W := mkw 0x14f4e8000a7a8004 0x029e9d00014f5000 0x00f0f80000780000 0x801e1f00000f0000

def z194 : W := mkw 0x020a000a00000000 0x0041400140000000 0x200f000f80000001 0x0401e001f0000000

def z195 : W := mkw 0x2144d7ef702a82a8 0x44289afdee055055 0xf8ccc7fff07fc7ff 0xbf1998fffe0ff8ff

def z196 : W := mkw 0x224eb0af60000000 0x0449d615ec000000 0xe03ffa7ff0000003 0xdc07ff4ffe000000

def z197 : W := mkw 0x0000102120000000 0x0000020424000000 0x00333a7380000000 0x4006674e70000000

def z198 : W := mkw 0x020a000000000000 0x0041400000000000 0x870f000000000001 0x70e1e00000000000

def z199 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0x47f003f00ff83f80 0xc8fe007e01ff07f0

def z200 : W := mkw 0x27eef7ef702a82a8 0x44fddefdee055055 0xe7fffffff007807b 0xfcfffffffe00f00f

def z201 : W := mkw 0x05a0074002906101 0x00b400e800520c20 0x0700000003800000 0x00e0000000700000

def z202 : W := mkw 0x0045c084d42e8ae8 0x4008b8109a85d15d 0xf8cfc78ffc7fffff 0xff19f8f1ff8fffff

def z203 : W := mkw 0x0044c000002a8000 0x0008980000055000 0x90ccc000007f8005 0xb2199800000ff000

def z204 : W := mkw 0x27eeb7ef700002a8 0x44fdd6fdee000055 0xeffffffff00047fb 0xfdfffffffe0008ff

def z205 : W := mkw 0x27feb7ff68401402 0x04ffd6ffed080280 0xeffffffffc603e07 0xfdffffffff8c07c0

def z206 : W := mkw 0x0cb15831be761e62 0x21962b0637cec3cc 0xfff3fa73fffe3e67 0xfffe7f4e7fffc7cc

def z207 : W := mkw 0x00000084500002a8 0x400000108a000055 0x2000000c70000078 0x040000018e00000f

def z208 : W := mkw 0x124fe884552f82ac 0x4249fd108aa5f055 0x200ff80c70078079 0x0401ff018e00f00f

def z209 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0x2803f803fc663e65 0x05007f007f8cc7cc

def z210 : W := mkw 0x081148109c661e62 0x21022902138cc3cc 0xc83002700c663e66 0xd906004e018cc7cc

def z211 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0xf83ffe7ffc67fe7f 0xff07ffcfff8cffcf

def z212 : W := mkw 0x0000400010220220 0x0000080002044044 0xe800c00070660667 0x9d0018000e0cc0cc

def z213 : W := mkw 0x27aa376b20000000 0x04f546ed64000000 0xe733fa73f0000003 0xdce67f4e7e000000

def z214 : W := mkw 0x00004000002a8000 0x0000080000055000 0x10000000007f8004 0x02000000000ff000

def z215 : W := mkw 0x214497ef60000000 0x042892fdec000000 0xe0ccc7fff0000003 0xbc1998fffe000000

def z216 : W := mkw 0x1ffffe3bbffffe76 0xa3ffffc777ffffce 0xfffffe7ffffffe7f 0xffffffcfffffffcf

def z217 : W := mkw 0x0000000002906101 0x0000000000520c20 0x1000000003984180 0x0200000000730830

def z218 : W := mkw 0x181148109f7f9e66 0x2302290213eff3cc 0x180000000fffbe64 0x0300000001fff7cc

def z219 : W := mkw 0x2fffbfffec441c42 0x25fff7fffd888388 0xe7fffffffc003803 0xfcffffffff800700

def z220 : W := mkw 0x0100060000806000 0x002000c000100c00 0x1700040003804000 0x22e0008000700800

def z221 : W := mkw 0x37bb3f6b2f550004 0x06f767ed65eaa000 0x07333a738f800000 0x40e6674e71f00000

def z222 : W := mkw 0x0810583138621622 0x21020b06270c42c4 0x4030f87070600600 0x88061f0e0e0c00c0

def z223 : W := mkw 0x0b1b5e3bbde77e72 0xa1636bc777bcefce 0xff3ffe7fffe7fe7f 0xffe7ffcffffcffcf

def z224 : W := mkw 0x081148109c6e9eea 0x61022902138dd3dd 0x180000000c7ffffc 0x03000000018fffff

def z225 : W := mkw 0x05a0074000000000 0x00b400e800000000 0xdff007f000784786 0xfbfe00fe000f08f0

def z226 : W := mkw 0x101148008fffe854 0x8202290011fffd0a 0x180000000ffff87c 0x0300000001ffff0f

def z227 : W := mkw 0x101148001f7f82ac 0x4202290003eff055 0x180000000fffc7fc 0x0300000001fff8ff

def z228 : W := mkw 0x030b060005856000 0x006160c000b0ac00 0x9f0f06000f87f807 0x73e1e0c001f0ff00

def z229 : W := mkw 0x27eeb7ef60806000 0x04fdd6fdec100c00 0xffffffffff807807 0xfffffffffff00f00

def z230 : W := mkw 0x0001000005050000 0x0000200000a0a000 0x100000000f878004 0x0200000001f0f000

def z231 : W := mkw 0x124fe80a852f8854 0x8249fd0150a5f10a 0x200ff80f80078079 0x0401ff01f000f00f

def z232 : W := mkw 0x0101060084846840 0x002020c010908d08 0xbf0306038f867867 0x77e060c071f0cf0c

def z233 : W := mkw 0x07ab074a87956951 0x80f560e950f2ad2a 0xbfcf078f8f9ff9ff 0x77f9e0f1f1f3ff3f

def z234 : W := mkw 0x125fe8000d6f8004 0x024bfd0001adf000 0x803ff8000c678005 0xd007ff00018cf000

def z235 : W := mkw 0x18115831bf7f9e66 0x23022b0637eff3cc 0xf833fa73ffffbe67 0xdf067f4e7ffff7cc

def z236 : W := mkw 0x030b460a95afeaf8 0xc06168c152b5fd5f 0xbf0f060f8fffffff 0x77e1e0c1f1ffffff

def z237 : W := mkw 0x27efb7efe5856850 0x84fdf6fdfcb0ad0a 0xffffffffff87f87f 0xfffffffffff0ff0f

def z238 : W := mkw 0x17ffef400fffe105 0x02fffde801fffc20 0x97fffd800fffc185 0xf2ffffb001fff830

def z239 : W := mkw 0x1efff821bf7f8a64 0x23dfff0437eff14c 0xb7fff803ffff8065 0xf6ffff007ffff00c

def z240 : W := mkw 0x020b000a85050850 0x8041600150a0a10a 0x200f000f80078079 0x0401e001f000f00f

def z241 : W := mkw 0x034fc68ed5afeaf8 0xc069f8d1dab5fd5f 0xffcfc78fffffffff 0xfff9f8f1ffffffff

def z242 : W := mkw 0x0000000000000000 0x0000000000000000 0x4800058000004782 0x090000b0000008f0

def z243 : W := mkw 0x0b1b1e3badc57c52 0xa16363c775b8af8a 0xbf3f3e7f8f87f87f 0x77e7e7cff1f0ff0f

def z244 : W := mkw 0x001148001c660220 0x00022900038cc044 0xe833f8007c660667 0xdd067f000f8cc0cc

def z245 : W := mkw 0x1effe8109f7f9e66 0x23dffd0213eff3cc 0x9ffff8000fffbe65 0xf3ffff0001fff7cc

def z246 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0xfffc07fc0fffffff 0xffff80ff81ffffff

def z247 : W := mkw 0x08115831bef67f63 0x21022b0637decfec 0xf833fa73fffe7fe7 0xdf067f4e7fffcffc

def z248 : W := mkw 0x030b060a05050000 0x006160c140a0a000 0xb70f060f8f878007 0x76e1e0c1f1f0f000

def z249 : W := mkw 0x15b14f500ffff507 0x02b629ea01fffea0 0xdff007f00fffff86 0xfbfe00fe01fffff0

def z250 : W := mkw 0x16ffe8845f7f82ac 0x42dffd108beff055 0xb7fff80c7fff807d 0xf6ffff018ffff00f

def z251 : W := mkw 0x27eea7ce40088088 0x44fdd4f9c8011011 0x17cc058c0019c198 0x22f980b180033833

def z252 : W := mkw 0x020a000a01010010 0x8041400140202002 0x000c000c00018018 0x0001800180003003

def z253 : W := mkw 0x04e4a00000000000 0x009c940000000000 0x00f0f80000000000 0x801e1f0000000000

def z254 : W := mkw 0x05b107508ed47d43 0x00b620ea11da8fa8 0xfff307f38ffe7fe7 0xfffe60fe71ffcffc

def z255 : W := mkw 0x27eea7ce40000000 0x04fdd4f9c8000000 0xa7cf078f80000003 0x74f9e0f1f0000000

def z256 : W := mkw 0x1cf5f831be7e9e66 0x239ebf0637cfd3cc 0xe8f3fa73fc7e3e67 0xdd1e7f4e7f8fc7cc

def z257 : W := mkw 0x04b000100a501402 0x00960002014a0280 0xdff002700ff83e06 0xfbfe004e01ff07c0

def z258 : W := mkw 0x0044808440088088 0x4008901088011011 0xd8cc058c0079c79e 0xbb1980b1800f38f3

def z259 : W := mkw 0x27eeb7ef60088088 0x44fdd6fdec011011 0xf7fffffff019c19b 0xfefffffffe033833

def z260 : W := mkw 0x0a0b582bb5270a70 0xa1416b0576a4e14e 0x200ff80ff0078079 0x0401ff01fe00f00f

def z261 : W := mkw 0x0000102120000000 0x0000020424000000 0x60000273f0000002 0x0c00004e7e000000

def z262 : W := mkw 0x0000000000000000 0x0000000000000000 0x2800040c0000407a 0x050000818000080f

def z263 : W := mkw 0x16ffe8100f7f9406 0x02dffd0201eff280 0xdffffa700fffbe07 0xfbffff4e01fff7c0

def z264 : W := mkw 0x27eea7ce40000000 0x04fdd4f9c8000000 0xc7fc07fc00000002 0xf8ff80ff80000000

def z265 : W := mkw 0x08111831ac441c42 0x2102230635888388 0xe033fa73fc003803 0xdc067f4e7f800700

def z266 : W := mkw 0x0010480008620000 0x00020900010c4000 0x0030f80000600000 0x80061f00000c0000

def z267 : W := mkw 0x020b000a85050850 0x8041600150a0a10a 0xa80f020f8c07b87f 0x5501e041f180f70f

def z268 : W := mkw 0x030a060a01816010 0x806140c140302c02 0xb70f060f8381c01b 0x76e1e0c1f0703803

def z269 : W := mkw 0x001000100ad07503 0x00020002015a0ea0 0xd83002700ff87f86 0xdb06004e01ff0ff0

def z270 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0xfffffffff007c07f 0xfffffffffe00f80f

def z271 : W := mkw 0x030a060a01816010 0x806140c140302c02 0x0700000003800000 0x00e0000000700000

def z272 : W := mkw 0x0010000008400000 0x0002000001080000 0x803000000c600004 0xd0060000018c0000

def z273 : W := mkw 0x234fb6afe5856850 0x8469f6d5fcb0ad0a 0xbf0ffe0fff87f87f 0x77e1ffc1fff0ff0f

def z274 : W := mkw 0x0044808440000000 0x0008901088000000 0xe0ccc58c70000003 0xbc1998b18e000000

def z275 : W := mkw 0x00004000102a82a8 0x4000080002055055 0xb80c040c007fc7ff 0x37018081800ff8ff

def z276 : W := mkw 0x0810481018621622 0x21020902030c42c4 0x0000000000600600 0x00000000000c00c0

def z277 : W := mkw 0x27ba377b2ad07503 0x04f746ef655a0ea0 0x07333a738f803800 0x40e6674e71f00700

def z278 : W := mkw 0x0010001008401402 0x0002000201080280 0x080000000c603e04 0x01000000018c07c0

def z279 : W := mkw 0x07bb075a8fd57d53 0x80f760eb51faafaa 0xdff307f38ff87f86 0xfbfe60fe71ff0ff0

def z280 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0x273ffa7ff0000001 0x44e7ff4ffe000000

def z281 : W := mkw 0x0055c8000c6e8000 0x000ab900018dd000 0x90fff8000c7f8005 0xf21fff00018ff000

def z282 : W := mkw 0x0044808440000000 0x0008901088000000 0x00cc058c00000000 0x201980b180000000

def z283 : W := mkw 0x16ffe8844f7f8004 0x02dffd1089eff000 0xf7fffd8c7fff8007 0xfeffffb18ffff000

def z284 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0xfffffffff0784787 0xfffffffffe0f08f0

def z285 : W := mkw 0x030a162b20000000 0x006142c564000000 0xe73ffe7ff0000003 0xfce7ffcffe000000

def z286 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0xaf0302038f863867 0x55e0604071f0c70c

def z287 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x00fff800007f8001 0x801fff00000ff000

def z288 : W := mkw 0x27efb7efe4040840 0x04fdf6fdfc808108 0xeffffffffc063867 0xfdffffffff80c70c

def z289 : W := mkw 0x0000000000000000 0x0000000000000000 0x8033f80000000001 0xd0067f0000000000

def z290 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0xdffffd800fffc787 0xfbffffb001fff8f0

def z291 : W := mkw 0x08111831ac441c42 0x2102230635888388 0x00333a738c003800 0x4006674e71800700

def z292 : W := mkw 0x081148109c661e62 0x21022902138cc3cc 0xe800c0007c663e67 0x9d0018000f8cc7cc

def z293 : W := mkw 0x14e4a00002188004 0x029c940000431000 0x00c0000000180000 0x0018000000030000

def z294 : W := mkw 0x0044808440088088 0x4008901088011011 0xb8cc058c001fc1ff 0x371980b18003f83f

def z295 : W := mkw 0x031b061a8dc57c52 0x806360c351b8af8a 0xff3f067f8fe7fe7f 0xffe7e0cff1fcffcf

def z296 : W := mkw 0x1ebb3831af551c46 0x23d7670635eaa388 0x07333a738f803800 0x40e6674e71f00700

def z297 : W := mkw 0x04f4c0000a7a8000 0x009e9800014f5000 0x97fcc0000fff8005 0xf2ff980001fff000

def z298 : W := mkw 0x04b148000e760000 0x0096290001cec000 0x97f3f8000ffe0005 0xf2fe7f0001ffc000

def z299 : W := mkw 0x0001400094260a60 0x000028001284c14c 0xe803c203fc663e67 0xdd0078407f8cc7cc

def z300 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z301 : W := mkw 0x27efa7cec5856850 0x84fdf4f9d8b0ad0a 0xbfcf078f8f87f87f 0x77f9e0f1f1f0ff0f

def z302 : W := mkw 0x37ffff6b2f7f8004 0x06ffffed65eff000 0x97fffa738fff8005 0xf2ffff4e71fff000

def z303 : W := mkw 0x27feb7ff6a501503 0x04ffd6ffed4a02a0 0xe7fffffff0780783 0xfcfffffffe0f00f0

def z304 : W := mkw 0x0000000000000000 0x0000000000000000 0x10c0058000184180 0x221800b000030830

def z305 : W := mkw 0x06aa200000000000 0x00d5440000000000 0x0733380000000000 0x40e6670000000000

def z306 : W := mkw 0x200011e560000000 0x0400023cac000000 0x400001f070000000 0x0800003e0e000000

def z307 : W := mkw 0x0044808440000000 0x0008901088000000 0x200cc00c70000001 0x040198018e000000

def z308 : W := mkw 0x27ffb7ffefd57d53 0x84fff6fffdfaafaa 0xffffffffffffffff 0xffffffffffffffff

def z309 : W := mkw 0x14f4e9500a7a9507 0x029e9d2a014f52a0 0x40f0f9f000780780 0x881e1f3e000f00f0

def z310 : W := mkw 0x05e4c7c4502a82a8 0x40bc98f88a055055 0xfffcc7fc707fc7ff 0xffff98ff8e0ff8ff

def z311 : W := mkw 0x00011021a4040840 0x0000220434808108 0xe833fa73fc063867 0xdd067f4e7f80c70c

def z312 : W := mkw 0x234eb7ef60000000 0x0469d6fdec000000 0x600ffffff0000003 0x0c01fffffe000000

def z313 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0xc7f007f00f803802 0xf8fe00fe01f00700

def z314 : W := mkw 0x0810583138621622 0x21020b06270c42c4 0xc830fa707c603e06 0xd9061f4e0f8c07c0

def z315 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0x4830f8707c663e64 0x89061f0e0f8cc7cc

def z316 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0x380cc00c707fc7fd 0x070198018e0ff8ff

def z317 : W := mkw 0x2ffffffffc661e62 0x25ffffffff8cc3cc 0xeffffffffc663e67 0xfdffffffff8cc7cc

def z318 : W := mkw 0x17eea60a0399e014 0x82fdd4c140733c02 0x17cc040c0399c018 0x22f9808180733803

def z319 : W := mkw 0x05b14f500ef67503 0x00b629ea01decea0 0xdff3fff00ffe7f87 0xfbfe7ffe01ffcff0

def z320 : W := mkw 0x00004084502202a8 0x400008108a044055 0xe800c58c706647ff 0x9d0018b18e0cc8ff

def z321 : W := mkw 0x34f4f9e56a7a8004 0x069e9f3cad4f5000 0x40f0f9f070780000 0x881e1f3e0e0f0000

def z322 : W := mkw 0x16bb28000f550004 0x02d7650001eaa000 0x97f338000ff80004 0xf2fe670001ff0000

def z323 : W := mkw 0x17ffefd45ffff7af 0x42fffdfa8bfffef5 0xfffffffc7fffffff 0xffffffff8fffffff

def z324 : W := mkw 0x120b280005050004 0x0241650000a0a000 0x0003380000000000 0x0000670000000000

def z325 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0x08333a738c663e64 0x4106674e718cc7cc

def z326 : W := mkw 0x0044c000102a82a8 0x4008980002055055 0x98ccc000007fc7fd 0xb3199800000ff8ff

def z327 : W := mkw 0x05b007500a501503 0x00b600ea014a02a0 0xc7f007f000780782 0xf8fe00fe000f00f0

def z328 : W := mkw 0x081148109ef67f63 0x2102290213decfec 0x180000000ffe7fe4 0x0300000001ffcffc

def z329 : W := mkw 0x0100074000000000 0x002000e800000000 0x400007f000000002 0x080000fe00000000

def z330 : W := mkw 0x05b017712ad07503 0x00b602ee255a0ea0 0xfff3fff3fff87f87 0xfffe7ffe7fff0ff0

def z331 : W := mkw 0x024fc000052f8000 0x0049f80000a5f000 0x97cfc0000fff8005 0xf2f9f80001fff000

def z332 : W := mkw 0x27ab376ba5856850 0x84f566ed74b0ad0a 0xbf3f3e7f8f87f87f 0x77e7e7cff1f0ff0f

def z333 : W := mkw 0x0001000004040000 0x0000200000808000 0x800300000c060005 0x500060000180c000

def z334 : W := mkw 0x0cb059713a721723 0x21960b2e274e42e4 0x40f0f9f070780780 0x881e1f3e0e0f00f0

def z335 : W := mkw 0x2cf4f9f578621622 0x259e9f3eaf0c42c4 0x40f0f9f070600600 0x881e1f3e0e0c00c0

def z336 : W := mkw 0x200010af60000000 0x04000215ec000000 0x2000000ff0000000 0x04000001fe000000

def z337 : W := mkw 0x14f4e8000a7a8004 0x029e9d00014f5000 0x97f0f8000ff80004 0xf2fe1f0001ff0000

def z338 : W := mkw 0x1a5ff831bd6f9e66 0x234bff0637adf3cc 0xe83ffa73fc67be67 0xdd07ff4e7f8cf7cc

def z339 : W := mkw 0x16ffe9500f7f9507 0x02dffd2a01eff2a0 0xd7fff9f00fff8785 0xfaffff3e01fff0f0

def z340 : W := mkw 0x07ba075a0ad07503 0x00f740eb415a0ea0 0xffff07ff8ff87f87 0xffffe0fff1ff0ff0

def z341 : W := mkw 0x08015821b4260a60 0x21002b043684c14c 0xe033fa73f0060063 0xdc067f4e7e00c00c

def z342 : W := mkw 0x210017ef700002a8 0x442002fdee000055 0x680007fff00047fa 0x0d0000fffe0008ff

def z343 : W := mkw 0x08011031b4041e62 0x21002206368083cc 0xe8030273fc063e67 0x5d00604e7f80c7cc

def z344 : W := mkw 0x25e4b7e560000000 0x04bc96fcac000000 0xc7f0fff070000002 0xf8fe1ffe0e000000

def z345 : W := mkw 0x0b0b163bb5857e72 0xa16162c776b0afce 0xff0f067fff87fe7f 0x7fe1e0cffff0ffcf

def z346 : W := mkw 0x37ffffef7f7f82ac 0x46fffffdefeff055 0xffffffffffffc7ff 0xfffffffffffff8ff

def z347 : W := mkw 0x00000084500002a8 0x400000108a000055 0xf8c0058c707847fe 0xbf1800b18e0f08ff

def z348 : W := mkw 0x0845d8a5f42e8ae8 0x6108bb14be85d15d 0xf8cffd8ff07fc7ff 0xbf19ffb1fe0ff8ff

def z349 : W := mkw 0x324ff8af652f8004 0x0649ff15eca5f000 0x200ff80ff0078001 0x0401ff01fe00f000

def z350 : W := mkw 0x0df5dff5fefeffeb 0x61bebbfebfdfdffd 0xffffffffffffffff 0xffffffffffffffff

def z351 : W := mkw 0x0010001008401402 0x0002000201080280 0xd8f007f00c787f86 0xfb1e00fe018f0ff0

def z352 : W := mkw 0x05a0074002906101 0x00b400e800520c20 0xdfc0058003f84786 0xbbf800b0007f08f0

def z353 : W := mkw 0x08115831bde77e72 0xa1022b0637bcefce 0xf833fa73ffe7fe7f 0xdf067f4e7ffcffcf

def z354 : W := mkw 0x081108108c441c42 0x2102210211888388 0x000000000c003800 0x0000000001800700

def z355 : W := mkw 0x16bb68000f7f8004 0x02d76d0001eff000 0x173338000fff8004 0x42e6670001fff000

def z356 : W := mkw 0x101048000a7a8004 0x02020900014f5000 0x0000000000780000 0x00000000000f0000

def z357 : W := mkw 0x0000000000000000 0x0000000000000000 0xa003020380000003 0x5400604070000000

def z358 : W := mkw 0x16ffe8001f7f8224 0x02dffd0003eff044 0xfffff8007fff8667 0xffffff000ffff0cc

def z359 : W := mkw 0x25f4b7f56ad07503 0x04be96fead5a0ea0 0xdff0fff07ff87f86 0xfbfe1ffe0fff0ff0

def z360 : W := mkw 0x0044c000002a8000 0x0008980000055000 0x00c0c00000780000 0x80181800000f0000

def z361 : W := mkw 0x00004000102a82a8 0x4000080002055055 0x0000000000078078 0x000000000000f00f

def z362 : W := mkw 0x0100060a80806850 0x802000c150100d0a 0xb80c060f8007f87f 0x370180c1f000ff0f

def z363 : W := mkw 0x27efb7efe5050850 0x84fdf6fdfca0a10a 0xe7fffffff007807b 0xfcfffffffe00f00f

def z364 : W := mkw 0x08015821b4260a60 0x21002b043684c14c 0xa803fa03fc063867 0x55007f407f80c70c

def z365 : W := mkw 0x0044808440088088 0x4008901088011011 0xf0ccc58c7019c19b 0xbe1998b18e033833

def z366 : W := mkw 0x16ffe80a8f7f8854 0x82dffd0151eff10a 0xb7fff80f8fff807d 0xf6ffff01f1fff00f

def z367 : W := mkw 0x001000100a501503 0x00020002014a02a0 0x0000000000780780 0x00000000000f00f0

def z368 : W := mkw 0x24e4b1e560000000 0x049c963cac000000 0xe0f3fbf3f0000003 0xdc1e7f7e7e000000

def z369 : W := mkw 0x16bb68000f770004 0x02d76d0001eee000 0x8733f8000fe60005 0xd0e67f0001fcc000

def z370 : W := mkw 0x29115ffffc661e62 0x25222bffff8cc3cc 0xe833fffffc663e67 0xdd067fffff8cc7cc

def z371 : W := mkw 0x00000084500002a8 0x400000108a000055 0x4000018070000780 0x080000300e0000f0

def z372 : W := mkw 0x14f4e8845a7a82ac 0x429e9d108b4f5055 0x40f0f98070780780 0x881e1f300e0f00f0

def z373 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0x1f3002700ff87f84 0x43e6004e01ff0ff0

def z374 : W := mkw 0x001148100c661402 0x00022902018cc280 0xc833fa700c663e07 0xd9067f4e018cc7c0

def z375 : W := mkw 0x17ffef400f7f8004 0x02fffde801eff000 0xd7fffff00fff8007 0xfafffffe01fff000

def z376 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0x60ccc18c707f87f9 0x8c1998318e0ff0ff

def z377 : W := mkw 0x27eea7ce40000000 0x04fdd4f9c8000000 0x87fffd8c00000001 0xf0ffffb180000000

def z378 : W := mkw 0x0000000000000000 0x0000000000000000 0xc030027000000002 0xd806004e00000000

def z379 : W := mkw 0x0000000000000000 0x0000000000000000 0x100c040c0001c018 0x2201808180003803

def z380 : W := mkw 0x2cf5f9f5fc661e62 0x259ebf3ebf8cc3cc 0xe8f3fbf3fc663e67 0xdd1e7f7e7f8cc7cc

def z381 : W := mkw 0x27fea7de4ad07503 0x04ffd4fbc95a0ea0 0xdffc07fc0ff87f86 0xfbff80ff81ff0ff0

def z382 : W := mkw 0x124fe884552f82ac 0x4249fd108aa5f055 0xf8cffd8c707fc7ff 0xbf19ffb18e0ff8ff

def z383 : W := mkw 0x1000000003198004 0x0200000000633000 0x1000000003998000 0x0200000000733000

def z384 : W := mkw 0x16ffe8845f7f82ac 0x42dffd108beff055 0xd7fff9807fff8785 0xfaffff300ffff0f0

def z385 : W := mkw 0x0100060a80806850 0x802000c150100d0a 0x0000020380003800 0x0000004070000700

def z386 : W := mkw 0x24e4f1e5702a82a8 0x449c9e3cae055055 0xf8fcfdfc707fc7ff 0xbf1f9fbf8e0ff8ff

def z387 : W := mkw 0x0855c894dc6e9eea 0x610ab9129b8dd3dd 0xf8ccc58c7c7fffff 0xbf1998b18f8fffff

def z388 : W := mkw 0x0b5fdebffdeffefa 0xe16bfbd7ffbdffdf 0xffffffffffffffff 0xffffffffffffffff

def z389 : W := mkw 0x05f487d44ad07503 0x00be90fa895a0ea0 0xfffcc7fc7ff87f87 0xffff98ff8fff0ff0

def z390 : W := mkw 0x1044e800002a8004 0x02089d0000055000 0x0000f80000000000 0x00001f0000000000

def z391 : W := mkw 0x0cb15971be761f63 0x21962b2e37cec3ec 0xe8f3fbf3fc7e3fe7 0xdd1e7f7e7f8fc7fc

def z392 : W := mkw 0x27aa376b20000000 0x04f546ed64000000 0xc7f33ff380000002 0xf8fe67fe70000000

def z393 : W := mkw 0x16ffe8008f7f8844 0x02dffd0011eff108 0xbffffa038fffb867 0xf7ffff4071fff70c

def z394 : W := mkw 0x07eea74000000000 0x00fdd4e800000000 0xc7fffff000000003 0xf8fffffe00000000

def z395 : W := mkw 0x011007500ad07503 0x002200ea015a0ea0 0x580007f00ff87f86 0x0b0000fe01ff0ff0

def z396 : W := mkw 0x0000102120000000 0x0000020424000000 0x2003f803f0000001 0x04007f007e000000

def z397 : W := mkw 0x0010001008401402 0x0002000201080280 0x003002700c003800 0x4006004e01800700

def z398 : W := mkw 0x24f4b1f56a501503 0x049e963ead4a02a0 0x40f0f9f070780780 0x881e1f3e0e0f00f0

def z399 : W := mkw 0x034e868e40000000 0x0069d0d1c8000000 0xe7cfc78ff0000003 0xfcf9f8f1fe000000

def z400 : W := mkw 0x17ffee0a0f7f8004 0x02fffdc141eff000 0xb7fffe0f8fff8007 0xf6ffffc1f1fff000

def z401 : W := mkw 0x0100074000806101 0x002000e800100c20 0x0000058000004180 0x000000b000000830

def z402 : W := mkw 0x14b028000a500004 0x02960500014a0000 0x0030380000000000 0x0006070000000000

def z403 : W := mkw 0x0045c084d5afeaf8 0xc008b8109ab5fd5f 0xf8ccc58c7fffffff 0xbf1998b18fffffff

def z404 : W := mkw 0x00448084500002a8 0x400890108a000055 0xe8ccc58c700047fb 0xbd1998b18e0008ff

def z405 : W := mkw 0x16ffe8001f7f82ac 0x42dffd0003eff055 0x9ffff8000fffc7fd 0xf3ffff0001fff8ff

def z406 : W := mkw 0x0000000000000000 0x0000000000000000 0x880002000c003806 0x5100004001800700

def z407 : W := mkw 0x05a0176120000000 0x00b402ec24000000 0xe7f3fff3f0000003 0xfcfe7ffe7e000000

def z408 : W := mkw 0x1a4ff821b52f8a64 0x2349ff0436a5f14c 0x200ff803f0078061 0x0401ff007e00f00c

def z409 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x17cc00000fff8004 0x22f9800001fff000

def z410 : W := mkw 0x16eea0844319808c 0x42ddd41088633011 0x17cc058c0399c198 0x22f980b180733833

def z411 : W := mkw 0x27ba377b2ad07503 0x04f746ef655a0ea0 0xdff33ff38ff87f86 0xfbfe67fe71ff0ff0

def z412 : W := mkw 0x08115831bc6e9eea 0x61022b06378dd3dd 0xf833fa73fc7fffff 0xdf067f4e7f8fffff

def z413 : W := mkw 0x05b007400ad06101 0x00b600e8015a0c20 0x97f005800ff84184 0xf2fe00b001ff0830

def z414 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0xbffffc0c0fffc07f 0xf7ffff8181fff80f

def z415 : W := mkw 0x24e4b1e560000000 0x049c963cac000000 0xe0fcfdfc70000003 0xbc1f9fbf8e000000

def z416 : W := mkw 0x030a060a00000000 0x006140c140000000 0xbf0f060f8007c07f 0x77e1e0c1f000f80f

def z417 : W := mkw 0x030a060a00806000 0x006140c140100c00 0xbf0f060f8f807807 0x77e1e0c1f1f00f00

def z418 : W := mkw 0x0000102120000000 0x0000020424000000 0x4030f87070000000 0x88061f0e0e000000

def z419 : W := mkw 0x14f4e8000a7a8004 0x029e9d00014f5000 0x90fcf800007f8005 0xb21f9f00000ff000

def z420 : W := mkw 0x0001000084040840 0x0000200010808108 0x2003000380060061 0x040060007000c00c

def z421 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0xe8c0c180707e07e7 0x9d1818300e0fc0fc

def z422 : W := mkw 0x09115e31bce67e62 0x21222bc6379ccfcc 0xff33fe73ffe67e67 0xffe67fce7ffccfcc

def z423 : W := mkw 0x09115f71bce67f63 0x21222bee379ccfec 0xe833fff3fc667fe7 0xdd067ffe7f8ccffc

def z424 : W := mkw 0x0000000000000000 0x0000000000000000 0x9800040000004006 0x3300008000000800

def z425 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0xcf3002700fe03e06 0xd9e6004e01fc07c0

def z426 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0x2f03060f8f80787a 0x45e060c1f1f00f0f

def z427 : W := mkw 0x17ffef500ffff507 0x02fffdea01fffea0 0x97fffa700fffb805 0xf2ffff4e01fff700

def z428 : W := mkw 0x0100075a80807d53 0x802000eb50100faa 0x680007ff80007ffa 0x0d0000fff0000fff

def z429 : W := mkw 0x37ffffefefffe854 0x86fffffdfdfffd0a 0xfffffffffffff87f 0xffffffffffffff0f

def z430 : W := mkw 0x07aa074a03916111 0x80f540e940722c22 0x17cc058c0399c198 0x22f980b180733833

def z431 : W := mkw 0x0044c000002a8000 0x0008980000055000 0xb8ccc40c007fc07f 0xb7199881800ff80f

def z432 : W := mkw 0x0100075000807503 0x002000ea00100ea0 0x0000027000003800 0x0000004e00000700

def z433 : W := mkw 0x0fbb5f7bbff77f73 0xa1f76bef77feefee 0xffffffffffffffff 0xffffffffffffffff

def z434 : W := mkw 0x0000015000001503 0x0000002a000002a0 0x400001f000000780 0x0800003e000000f0

def z435 : W := mkw 0x05f487d44ad8f58b 0x40be90fa895b1eb1 0xdffc07fc0ff9ff9e 0xfbff80ff81ff3ff3

def z436 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0x4f3007f00f807f82 0x49e600fe01f00ff0

def z437 : W := mkw 0x2fbb3f7bac441c42 0x25f767ef75888388 0x07333a738c003800 0x40e6674e71800700

def z438 : W := mkw 0x08111831ac441c42 0x2102230635888388 0xc8333a738c603e06 0xd906674e718c07c0

def z439 : W := mkw 0x27efb7ef65050000 0x04fdf6fdeca0a000 0xf7ffffffff878007 0xfefffffffff0f000

def z440 : W := mkw 0x00000084500002a8 0x400000108a000055 0xf80c058c7007c7ff 0x3f0180b18e00f8ff

def z441 : W := mkw 0x024ea00000000000 0x0049d40000000000 0x000ff80000000001 0x0001ff0000000000

def z442 : W := mkw 0x0044808440000000 0x0008901088000000 0xf8ccc58c70784787 0xbf1998b18e0f08f0

def z443 : W := mkw 0x290017fff0001e62 0x252002fffe0003cc 0x680007fff0003e62 0x0d0000fffe0007cc

def z444 : W := mkw 0x020b000005050000 0x0041600000a0a000 0x070300000f800000 0x40e0600001f00000

def z445 : W := mkw 0x0054c094586a96aa 0x400a98128b0d52d5 0xf8fcc7fc7c7fffff 0xff1f98ff8f8fffff

def z446 : W := mkw 0x05a0074000000000 0x00b400e800000000 0x07c0058000000000 0x20f800b000000000

def z447 : W := mkw 0x0100060000806000 0x002000c000100c00 0xdfc007800ff87f86 0xfbf800f001ff0ff0

def z448 : W := mkw 0x16fee8000a7a8004 0x02dfdd00014f5000 0x87fff80000780001 0xf0ffff00000f0000

def z449 : W := mkw 0x001100108fd57d53 0x8002200211faafaa 0x180000000ffffffc 0x0300000001ffffff

def z450 : W := mkw 0x020a000001010000 0x0041400000202000 0x170c000003818000 0x22e1800000703000

def z451 : W := mkw 0x16efa000071d8004 0x02ddf40000e3b000 0x97cf00000f9f8005 0x72f9e00001f3f000

def z452 : W := mkw 0x16ffe8844f7f808c 0x42dffd1089eff011 0x97fffd8c0fffc19d 0xf2ffffb181fff833

def z453 : W := mkw 0x0044c000002a8000 0x0008980000055000 0x000cc00000078001 0x000198000000f000

def z454 : W := mkw 0x09115e3bbce67e72 0xa1222bc7779ccfce 0xe833fe7ffc667e7f 0xdd067fcfff8ccfcf

def z455 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0x170f060f8f81f818 0x62e1e0c1f1f03f03

def z456 : W := mkw 0x06eea08440000000 0x00ddd41088000000 0xe7fffd8c70000003 0xfcffffb18e000000

def z457 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0xe0ccc58c70780783 0xbc1998b18e0f00f0

def z458 : W := mkw 0x020b000085050840 0x0041600010a0a108 0xbf0f02038f87b867 0x77e1e04071f0f70c

def z459 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0x18cc058c007fc7fc 0x231980b1800ff8ff

def z460 : W := mkw 0x0101060a85856850 0x802020c150b0ad0a 0x3800060f8f87f87e 0x070000c1f1f0ff0f

def z461 : W := mkw 0x27ab376ba5856850 0x84f566ed74b0ad0a 0x07333a738f803800 0x40e6674e71f00700

def z462 : W := mkw 0x030b060a05856010 0x806160c140b0ac02 0x970f040c0f87c01d 0x72e1e08181f0f803

def z463 : W := mkw 0x131b4e0a8fffe854 0x826369c151fffd0a 0xbf0f060f8ffff87f 0x77e1e0c1f1ffff0f

def z464 : W := mkw 0x030a060a01816010 0x806140c140302c02 0x9f0c060c0f81f81e 0x73e180c181f03f03

def z465 : W := mkw 0x07bb060a8fd56850 0x80f760c151faad0a 0xbfff060f8ffff87f 0xf7ffe0c1f1ffff0f

def z466 : W := mkw 0x0101060085856850 0x802020c010b0ad0a 0x9f0006000f87f87e 0x73e000c001f0ff0f

def z467 : W := mkw 0x001100108c441c42 0x0002200211888388 0xe83302738c663e67 0xdd06604e718cc7cc

def z468 : W := mkw 0x0100060000806000 0x002000c000100c00 0x0800060000007802 0x010000c000000f00

def z469 : W := mkw 0x0100060a80806850 0x802000c150100d0a 0xbf00060f8f80787e 0x77e000c1f1f00f0f

def z470 : W := mkw 0x0000000a80000850 0x800000015000010a 0x2000000f80000078 0x04000001f000000f

def z471 : W := mkw 0x27feb7ef6a500000 0x04ffd6fded4a0000 0xf7fffffffff80007 0xfeffffffffff0000

def z472 : W := mkw 0x030b162ba5856850 0x806162c574b0ad0a 0xff3ffe7fff87f87f 0xffe7ffcffff0ff0f

def z473 : W := mkw 0x0efff831bc661e62 0x21dfff06378cc3cc 0xeffffa73fc663e67 0xfdffff4e7f8cc7cc

def z474 : W := mkw 0x08111831ac441c42 0x2102230635888388 0xa8333a738c063867 0x5506674e7180c70c

def z475 : W := mkw 0x0100075000807503 0x002000ea00100ea0 0xdf0007f00f807f86 0x7be000fe01f00ff0

def z476 : W := mkw 0x0000008440000000 0x0000001088000000 0x6000058c70000002 0x0c0000b18e000000

def z477 : W := mkw 0x0855d8b5fc661e62 0x210abb16bf8cc3cc 0xe8fffffffc663e67 0xfd1fffffff8cc7cc

def z478 : W := mkw 0x17ffee0a0fffe014 0x82fffdc141fffc02 0x97fffc0c0fffc01d 0xf2ffff8181fff803

def z479 : W := mkw 0x224fb0afe5050850 0x8449f615fca0a10a 0x200ff80ff0078079 0x0401ff01fe00f00f

def z480 : W := mkw 0x0001000085856850 0x8000200010b0ad0a 0xb80302038f87f87f 0x5700604071f0ff0f

def z481 : W := mkw 0x0044800000088000 0x0008900000011000 0x10cc000000198000 0x2219800000033000

def z482 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0c0058000000002 0xb81800b000000000

def z483 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0x48f007f000787f82 0x891e00fe000f0ff0

def z484 : W := mkw 0x0100060a00000000 0x002000c140000000 0x2000060f80000002 0x040000c1f0000000

def z485 : W := mkw 0x3fffffffff7f9e66 0x27ffffffffeff3cc 0xffffffffffffbe67 0xfffffffffffff7cc

def z486 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0x68000273fc663e66 0x0d00004e7f8cc7cc

def z487 : W := mkw 0x24a0316120000000 0x0494062c24000000 0x0030387000000000 0x0006070e00000000

def z488 : W := mkw 0x0100060000806000 0x002000c000100c00 0x070002000f803800 0x40e0004001f00700

def z489 : W := mkw 0x04f4c1d45a7a97ab 0x409e983a8b4f52f5 0x40f0c1f070780780 0x881e183e0e0f00f0

def z490 : W := mkw 0x08001021b0000a60 0x210002043600014c 0x20000003f0000060 0x040000007e00000c

def z491 : W := mkw 0x134fee0a85afe854 0x8269fdc150b5fd0a 0xbf0ffe0f8f87f87f 0x77e1ffc1f1f0ff0f

def z492 : W := mkw 0x00004000102a82a8 0x4000080002055055 0xd8c00580007fc7fe 0xbb1800b0000ff8ff

def z493 : W := mkw 0x0100060000000000 0x002000c000000000 0x8700060000000002 0x70e000c000000000

def z494 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0xe80cc00c7067867f 0x9d0198018e0cf0cf

def z495 : W := mkw 0x05a0075000807503 0x00b400ea00100ea0 0xcff007f000007f82 0xf9fe00fe00000ff0

def z496 : W := mkw 0x0000000080000840 0x0000000010000108 0x2800020380003862 0x050000407000070c

def z497 : W := mkw 0x081148109de77e72 0xa102290213bcefce 0x180000000fe7fe7c 0x0300000001fcffcf

def z498 : W := mkw 0x37ffffff6ffff507 0x06ffffffedfffea0 0xffffffffffffff87 0xfffffffffffffff0

def z499 : W := mkw 0x04a0014002100101 0x0094002800420020 0x00c0018000180180 0x0018003000030030

def z500 : W := mkw 0x25e4b7ef60000000 0x04bc96fdec000000 0x60f0fffff0000002 0x8c1e1ffffe000000

def z501 : W := mkw 0x020b000a85050850 0x8041600150a0a10a 0x0003000380000000 0x0000600070000000

def z502 : W := mkw 0x0000000000000000 0x0000000000000000 0x1800000000784784 0x03000000000f08f0

def z503 : W := mkw 0x0000400010220220 0x0000080002044044 0x4000c00070600600 0x880018000e0c00c0

def z504 : W := mkw 0x04b000000a500000 0x00960000014a0000 0x00f0000000780000 0x801e0000000f0000

def z505 : W := mkw 0x0b1b1e3badc57c52 0xa16363c775b8af8a 0x07333a738f803800 0x40e6674e71f00700

def z506 : W := mkw 0x121b48000f7f8004 0x0243690001eff000 0x970f00000fff8005 0x72e1e00001fff000

def z507 : W := mkw 0x0b0b5e2bb5a76a70 0xa1616bc576b4ed4e 0xbf0ffe0fff87f87f 0x77e1ffc1fff0ff0f

def z508 : W := mkw 0x0000000010000220 0x0000000002000044 0x6800000070000662 0x0d0000000e0000cc

def z509 : W := mkw 0x0854d8b5786a96aa 0x610a9b16af0d52d5 0xf8fcfdfc707fc7ff 0xbf1f9fbf8e0ff8ff

def z510 : W := mkw 0x07eea60a00000000 0x00fdd4c140000000 0xa7fffe0f80000003 0xf4ffffc1f0000000

def z511 : W := mkw 0x04a0000000000000 0x0094000000000000 0x87f0000000000000 0xf0fe000000000000

def z512 : W := mkw 0x14b148000f7f8004 0x0296290001eff000 0x97f000000fff8004 0xf2fe000001fff000

def z513 : W := mkw 0x00004000102a82a8 0x4000080002055055 0xf800c000707fc7ff 0x9f0018000e0ff8ff

def z514 : W := mkw 0x05b007d45ad077ab 0x40b600fa8b5a0ef5 0xfff007fc7ff87ffe 0xfffe00ff8fff0fff

def z515 : W := mkw 0x24e4f1e5702a82a8 0x449c9e3cae055055 0x40f0f9f070780780 0x881e1f3e0e0f00f0

def z516 : W := mkw 0x05a0074002906101 0x00b400e800520c20 0xd7f007f003984182 0xfafe00fe00730830

def z517 : W := mkw 0x0044808440000000 0x0008901088000000 0x40c0c18070000000 0x881818300e000000

def z518 : W := mkw 0x034ec68e502a82a8 0x4069d8d1ca055055 0xffcfc78ff07fc7ff 0xfff9f8f1fe0ff8ff

def z519 : W := mkw 0x081158b5fc661eea 0x61022b16bf8cc3dd 0xe833fffffc667fff 0xdd067fffff8ccfff

def z520 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0x57f005f003f84780 0xaafe00be007f08f0

def z521 : W := mkw 0x230a17ef60000000 0x046142fdec000000 0xe70f07fff0000003 0x7ce1e0fffe000000

def z522 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0x1f0c040c0f87f87c 0x23e1808181f0ff0f

def z523 : W := mkw 0x034e868e4189e098 0xc069d0d1c8313c13 0x17cc058c0399c198 0x22f980b180733833

def z524 : W := mkw 0x17ffee000fffe004 0x02fffdc001fffc00 0x9ffffe000ffff807 0xf3ffffc001ffff00

def z525 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0xd0ccc180707f8785 0xba1998300e0ff0f0

def z526 : W := mkw 0x08115821bc660a60 0x21022b04378cc14c 0xa033f803fc660065 0xd4067f007f8cc00c

def z527 : W := mkw 0x27eeb76b20000000 0x04fdd6ed64000000 0x87fffa7380000001 0xf0ffff4e70000000

def z528 : W := mkw 0x224ea08e40000000 0x0449d411c8000000 0x000c000c00000000 0x0001800180000000

def z529 : W := mkw 0x17ffee0a8fffe854 0x82fffdc151fffd0a 0x97fffa038fffb805 0xf2ffff4071fff700

def z530 : W := mkw 0x0000400010220220 0x0000080002044044 0x2000c00070060061 0x040018000e00c00c

def z531 : W := mkw 0x1055c8845f7f82ac 0x420ab9108beff055 0xf8ccc58c7fffc7ff 0xbf1998b18ffff8ff

def z532 : W := mkw 0x124fe800052f8004 0x0249fd0000a5f000 0x970ff8000f878005 0x72e1ff0001f0f000

def z533 : W := mkw 0x27eee7ce502a82a8 0x44fddcf9ca055055 0xffccc58c707fc7ff 0xbff998b18e0ff8ff

def z534 : W := mkw 0x27aa376b20000000 0x04f546ed64000000 0xa73f3e7f80000003 0x74e7e7cff0000000

def z535 : W := mkw 0x0055c8845c6e82a8 0x400ab9108b8dd055 0xf8fffd8c7c7fc7ff 0xff1fffb18f8ff8ff

def z536 : W := mkw 0x36fff8af6f7f8004 0x06dfff15edeff000 0xb7fff80fffff8005 0xf6ffff01fffff000

def z537 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0x67cc07fff0000002 0x2cf980fffe000000

def z538 : W := mkw 0x16eee084533b82ac 0x42dddc108a677055 0xffccc58c73ffc7ff 0xbff998b18e7ff8ff

def z539 : W := mkw 0x0100075000807503 0x002000ea00100ea0 0xd8c007f000787f86 0xbb1800fe000f0ff0

def z540 : W := mkw 0x14f5e8000e7e8004 0x029ebd0001cfd000 0x80f3f8000c7e0005 0xd01e7f00018fc000

def z541 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0xb0ccc00c707f807d 0xb61998018e0ff00f

def z542 : W := mkw 0x37efffef652f8004 0x06fdfffdeca5f000 0xe7fffffff0078003 0xfcfffffffe00f000

def z543 : W := mkw 0x224ef0af702a82a8 0x4449de15ee055055 0xf8cffd8ff07fc7ff 0xbf19ffb1fe0ff8ff

def z544 : W := mkw 0x17bb2f500fd57507 0x02f765ea01faaea0 0x07333a700f803800 0x40e6674e01f00700

def z545 : W := mkw 0x0db15f71bc661e62 0x21b62bee378cc3cc 0xeff3fff3fc663e67 0xfdfe7ffe7f8cc7cc

def z546 : W := mkw 0x1cf4f8313a7a9626 0x239e9f06274f52c4 0x40f0f87070780600 0x881e1f0e0e0f00c0

def z547 : W := mkw 0x0810583138621622 0x21020b06270c42c4 0xe830f87070660667 0x9d061f0e0e0cc0cc

def z548 : W := mkw 0x0000000000000000 0x0000000000000000 0x970000000f800004 0x72e0000001f00000

def z549 : W := mkw 0x04f4c1d45a7a97ab 0x409e983a8b4f52f5 0xf8fcc5fc707fc7ff 0xbf1f98bf8e0ff8ff

def z550 : W := mkw 0x081158313c661622 0x21022b06278cc2c4 0xc033f8707c660605 0xd8067f0e0f8cc0c0

def z551 : W := mkw 0x011006100ad07503 0x002200c2015a0ea0 0x9f0006000ff87f86 0x73e000c001ff0ff0

def z552 : W := mkw 0x0a1b5831bd671e62 0x21436b0637ace3cc 0xff3ffa73ffe7be67 0xffe7ff4e7ffcf7cc

def z553 : W := mkw 0x0000000000000000 0x0000000000000000 0x40c0018000780780 0x88180030000f00f0

def z554 : W := mkw 0x05e4c7c452bae3a9 0x40bc98f88a575c75 0xffccc58c73ffc7ff 0xbff998b18e7ff8ff

def z555 : W := mkw 0x05f4c7d45afaf7ab 0x40be98fa8b5f5ef5 0xdff0c7f07ff87f86 0xfbfe18fe0fff0ff0

def z556 : W := mkw 0x08015821b4260a60 0x21002b043684c14c 0xe803f803f0660667 0x9d007f007e0cc0cc

def z557 : W := mkw 0x05a0074002906101 0x00b400e800520c20 0x9fc007800f987986 0x73f800f001f30f30

def z558 : W := mkw 0x10014800052f8004 0x0200290000a5f000 0x0000000000078000 0x000000000000f000

def z559 : W := mkw 0x04b001500a501503 0x0096002a014a02a0 0x0030007000000000 0x0006000e00000000

def z560 : W := mkw 0x0000502130220220 0x00000a0426044044 0xe833fa73f0660667 0xdd067f4e7e0cc0cc

def z561 : W := mkw 0x034f868ec5856850 0x8069f0d1d8b0ad0a 0xffcfc78fff87f87f 0xfff9f8f1fff0ff0f

def z562 : W := mkw 0x04b001500a501503 0x0096002a014a02a0 0xd7f001f00ff80784 0xfafe003e01ff00f0

def z563 : W := mkw 0x0044c000002a8000 0x0008980000055000 0xd8ccc580007fc787 0xbb1998b0000ff8f0

def z564 : W := mkw 0x0054c0945afaf7ab 0x400a98128b5f5ef5 0xf8ccc58c7fffffff 0xbf1998b18fffffff

def z565 : W := mkw 0x224eb0af60000000 0x0449d615ec000000 0xe0cffd8ff0000003 0xbc19ffb1fe000000

def z566 : W := mkw 0x16fea0000b598004 0x02dfd400016b3000 0x97fc00000ff98004 0xf2ff800001ff3000

def z567 : W := mkw 0x0110061008c07402 0x002200c201180e80 0xdf3006700fe07e06 0xfbe600ce01fc0fc0

def z568 : W := mkw 0x034ec68e51abe2b8 0xc069d8d1ca357c57 0xffccc58c73ffc7ff 0xbff998b18e7ff8ff

def z569 : W := mkw 0x0001000084040840 0x0000200010808108 0x000302038c003800 0x4000604071800700

def z570 : W := mkw 0x37feffef6a7a8004 0x06ffdffded4f5000 0xe7fffffff0780003 0xfcfffffffe0f0000

def z571 : W := mkw 0x0801480094260a60 0x210029001284c14c 0x0000000000060060 0x000000000000c00c

def z572 : W := mkw 0x224ef0af702a82a8 0x4449de15ee055055 0x200ff80ff0078079 0x0401ff01fe00f00f

def z573 : W := mkw 0x0001000085856850 0x8000200010b0ad0a 0x000000000f803800 0x0000000001f00700

def z574 : W := mkw 0x08105831b8621e62 0x21020b06370c43cc 0x6830fa73f0603e62 0x8d061f4e7e0c07cc

def z575 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0x370f040f8387c079 0x26e1e081f070f80f

def z576 : W := mkw 0x0b1b4e1a9de77e72 0xa16369c353bcefce 0xbf0f060f8fe7fe7f 0x77e1e0c1f1fcffcf

def z577 : W := mkw 0x05b107508fd57d53 0x80b620ea11faafaa 0xdff007f00ffffffe 0xfbfe00fe01ffffff

def z578 : W := mkw 0x0000001000807503 0x0000000200100ea0 0x0800000000007f80 0x0100000000000ff0

def z579 : W := mkw 0x030a060a81816850 0x806140c150302d0a 0x3f0c060f8381f87a 0x27e180c1f0703f0f

def z580 : W := mkw 0x08111831bc441e62 0x21022306378883cc 0x68333a73fc003e62 0x4d06674e7f8007cc

def z581 : W := mkw 0x2ffeffff78621622 0x25ffdfffef0c42c4 0xe7fffffff0600603 0xfcfffffffe0c00c0

def z582 : W := mkw 0x030a060a01816010 0x806140c140302c02 0xbf0c040c0387c07f 0x37e180818070f80f

def z583 : W := mkw 0x17ffee8edfffeafc 0xc2fffdd1dbfffd5f 0xffffff8fffffffff 0xfffffff1ffffffff

def z584 : W := mkw 0x2ffffffffde77e72 0xa5ffffffffbcefce 0xffffffffffe7fe7f 0xfffffffffffcffcf

def z585 : W := mkw 0x0000008440000088 0x4000001088000011 0x0000058c00004198 0x000000b180000833

def z586 : W := mkw 0x2044b0a560000000 0x04089614ac000000 0x0000f80070000000 0x00001f000e000000

def z587 : W := mkw 0x04f4c0845a7a82a8 0x409e98108b4f5055 0xfffcc58c7fffc7ff 0xffff98b18ffff8ff

def z588 : W := mkw 0x101148100ffff507 0x0202290201fffea0 0x180000000fffff84 0x0300000001fffff0

def z589 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0x270f020f8f87b879 0x44e1e041f1f0f70f

def z590 : W := mkw 0x04b000100ad07503 0x00960002015a0ea0 0x9ff000000ff87f84 0xf3fe000001ff0ff0

def z591 : W := mkw 0x034f868ec58de8d8 0xc069f0d1d8b1bd1b 0xbfcf078f8f9ff9ff 0x77f9e0f1f1f3ff3f

def z592 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0x68c0c58c707847fa 0x8d1818b18e0f08ff

def z593 : W := mkw 0x030b068ed5856af8 0xc06160d1dab0ad5f 0xff0f078fff87ffff 0x7fe1e0f1fff0ffff

def z594 : W := mkw 0x030b060a84040840 0x006160c150808108 0xaf0f060f8c063867 0x75e1e0c1f180c70c

def z595 : W := mkw 0x0044d0a5702a82a8 0x40089a14ae055055 0xf8fffffff07fc7ff 0xff1ffffffe0ff8ff

def z596 : W := mkw 0x04a0014000000000 0x0094002800000000 0x40f001f000000000 0x881e003e00000000

def z597 : W := mkw 0x16ffa8000f550004 0x02dff50001eaa000 0x87fff8000f800001 0xf0ffff0001f00000

def z598 : W := mkw 0x210007ce40000000 0x042000f9c8000000 0x0000058c00000000 0x000000b180000000

def z599 : W := mkw 0x0144c68450aae2a8 0x402898d08a155c55 0xffccc78c7fffffff 0xfff998f18fffffff

def z600 : W := mkw 0x07aa074a00000000 0x00f540e940000000 0xe7ff07ff80000003 0xfcffe0fff0000000

def z601 : W := mkw 0x210017efe0806850 0x842002fdfc100d0a 0x680007fff000787a 0x0d0000fffe000f0f

def z602 : W := mkw 0x124ea00001098004 0x0249d40000213000 0x000c000000018000 0x0001800000003000

def z603 : W := mkw 0x27fef7ff7afaf7ab 0x44ffdeffef5f5ef5 0xffffffffffffffff 0xffffffffffffffff

def z604 : W := mkw 0x0db11f71aed47d43 0x21b623ee35da8fa8 0x07333a738f803800 0x40e6674e71f00700

def z605 : W := mkw 0x0044c08450220220 0x000898108a044044 0xe8ccc58c70660667 0xbd1998b18e0cc0cc

def z606 : W := mkw 0x2a4ff8aff4260a60 0x2549ff15fe84c14c 0x200ff80ff0060061 0x0401ff01fe00c00c

def z607 : W := mkw 0x101148000f7f8004 0x0202290001eff000 0x9033f8000fff8005 0xd2067f0001fff000

def z608 : W := mkw 0x1efff831af7f9c46 0x23dfff0635eff388 0x97fffa738fffb805 0xf2ffff4e71fff700

def z609 : W := mkw 0x08115831ac661c42 0x21022b06358cc388 0x8033fa738c663805 0xd0067f4e718cc700

def z610 : W := mkw 0x00000000100002a8 0x4000000002000055 0x08000000000047f8 0x01000000000008ff

def z611 : W := mkw 0x05b0075008401402 0x00b600ea01080280 0xcff007f00c603e06 0xf9fe00fe018c07c0

def z612 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0x0000c00070000000 0x000018000e000000

def z613 : W := mkw 0x27eef7ef702a82a8 0x44fddefdee055055 0xe7fffffff0780783 0xfcfffffffe0f00f0

def z614 : W := mkw 0x2fbb7f7bbc661e62 0x25f76fef778cc3cc 0xef33fa73fc663e67 0xdde67f4e7f8cc7cc

def z615 : W := mkw 0x024fc08ed52f8af8 0xc049f811daa5f15f 0xf8cfc58ff07fc7ff 0xbf19f8b1fe0ff8ff

def z616 : W := mkw 0x07ab074a85856850 0x80f560e950b0ad0a 0xffff07ff8f87f87f 0xffffe0fff1f0ff0f

def z617 : W := mkw 0x16efe800052f8004 0x02ddfd0000a5f000 0x87fff80000078001 0xf0ffff000000f000

def z618 : W := mkw 0x07bb075a8fd57d53 0x80f760eb51faafaa 0xbf3f067f8f87f87f 0x77e7e0cff1f0ff0f

def z619 : W := mkw 0x00004084502a82a8 0x400008108a055055 0x7800058c707fc7fe 0x0f0000b18e0ff8ff

def z620 : W := mkw 0x001158212c660000 0x00022b04258cc000 0xe033fa73fc660007 0xdc067f4e7f8cc000

def z621 : W := mkw 0x27eff7eff5afeaf8 0xc4fdfefdfeb5fd5f 0xffffffffffffffff 0xffffffffffffffff

def z622 : W := mkw 0x220a302b20000000 0x0441460564000000 0x0003380380000000 0x0000670070000000

def z623 : W := mkw 0x0810183128401402 0x2102030625080280 0x0030387000000000 0x0006070e00000000

def z624 : W := mkw 0x234eb6af60000000 0x0469d6d5ec000000 0xa70ffe0ff0000003 0x74e1ffc1fe000000

def z625 : W := mkw 0x27eef7ef70220220 0x04fddefdee044044 0xeffffffff0660667 0xfdfffffffe0cc0cc

def z626 : W := mkw 0x0b1b5e3bbc661e62 0x21636bc7778cc3cc 0xef3ffe7ffc663e67 0xfde7ffcfff8cc7cc

def z627 : W := mkw 0x0000400010220220 0x0000080002044044 0xf8c0c580707e47e7 0xbf1818b00e0fc8fc

def z628 : W := mkw 0x08011821a4040840 0x2100230434808108 0x0003380380000000 0x0000670070000000

def z629 : W := mkw 0x17efa60a879de854 0x82fdf4c150f3bd0a 0xbfcf060f8f9ff87f 0x77f9e0c1f1f3ff0f

def z630 : W := mkw 0x17bb2f500fd57507 0x02f765ea01faaea0 0xdff33ff00ff87f86 0xfbfe67fe01ff0ff0

def z631 : W := mkw 0x0000000000000000 0x0000000000000000 0x200c000c00078079 0x040180018000f00f

def z632 : W := mkw 0x0855d831bc6e9e62 0x210abb06378dd3cc 0xf8fffa73fc7fbe67 0xff1fff4e7f8ff7cc

def z633 : W := mkw 0x0010001008401402 0x0002000201080280 0x4030007000600600 0x8806000e000c00c0

def z634 : W := mkw 0x36fff9e56f7f8004 0x06dfff3cadeff000 0xd7fff9f07fff8005 0xfaffff3e0ffff000

def z635 : W := mkw 0x06ffe8000c660000 0x00dffd00018cc000 0x87fff8000c660005 0xf0ffff00018cc000

def z636 : W := mkw 0x2ffffffffc6e9eea 0x65ffffffff8dd3dd 0xfffffffffc7fffff 0xffffffffff8fffff

def z637 : W := mkw 0x020b000005050000 0x0041600000a0a000 0x000f000000078001 0x0001e0000000f000

def z638 : W := mkw 0x020b000a85050850 0x8041600150a0a10a 0xb70f000f8f87807d 0x76e1e001f1f0f00f

def z639 : W := mkw 0x0000000000000000 0x0000000000000000 0xc800000000600606 0x99000000000c00c0

def z640 : W := mkw 0x124fe800052f8004 0x0249fd0000a5f000 0x90cff800007f8005 0xb219ff00000ff000

def z641 : W := mkw 0x05a0075002907503 0x00b400ea00520ea0 0x5fc007f003987f82 0x2bf800fe00730ff0

def z642 : W := mkw 0x001000100ad07503 0x00020002015a0ea0 0x000000000f803800 0x0000000001f00700

def z643 : W := mkw 0x010007d4508077ab 0x402000fa8a100ef5 0x680007fc70007ffa 0x0d0000ff8e000fff

def z644 : W := mkw 0x0855d8b5fc6e9eea 0x610abb16bf8dd3dd 0xe83ffa7ffc67be7f 0xdd07ff4fff8cf7cf

def z645 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0xa70f060f8f803803 0x74e1e0c1f1f00700

def z646 : W := mkw 0x24e4a1c440000000 0x049c943888000000 0x00c0018000000000 0x0018003000000000

def z647 : W := mkw 0x0000000001816010 0x8000000000302c02 0x100000000381c018 0x0200000000703803

def z648 : W := mkw 0x030b060a85050850 0x806160c150a0a10a 0xa70f060f8007807b 0x74e1e0c1f000f00f

def z649 : W := mkw 0x05e487c440000000 0x00bc90f888000000 0xe7fcc7fc70000003 0xfcff98ff8e000000

def z650 : W := mkw 0x001040101afaf7ab 0x40020802035f5ef5 0x180000000ffffffc 0x0300000001ffffff

def z651 : W := mkw 0x17bb2e0a8fd56854 0x82f765c151faad0a 0xbf3f3e0f8f87f87f 0x77e7e7c1f1f0ff0f

def z652 : W := mkw 0x0800103130001622 0x21000206260002c4 0x4000007070000600 0x0800000e0e0000c0

def z653 : W := mkw 0x00004000102a82a8 0x4000080002055055 0x0000000000780780 0x00000000000f00f0

def z654 : W := mkw 0x0100060a00806010 0x802000c140100c02 0x0000040c00004018 0x0000008180000803

def z655 : W := mkw 0x0000000080806850 0x8000000010100d0a 0x0800000000007878 0x0100000000000f0f

def z656 : W := mkw 0x0001000084040840 0x0000200010808108 0x080000000c063864 0x010000000180c70c

def z657 : W := mkw 0x1efff8313f7f9626 0x23dfff0627eff2c4 0xd7fff8707fff8605 0xfaffff0e0ffff0c0

def z658 : W := mkw 0x26eeb1e560000000 0x04ddd63cac000000 0xc7fff9f070000001 0xf8ffff3e0e000000

def z659 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0x58c0c180707fc7fc 0x8b1818300e0ff8ff

def z660 : W := mkw 0x07efa60a85856850 0x80fdf4c150b0ad0a 0xbffffe0f8f87f87f 0xf7ffffc1f1f0ff0f

def z661 : W := mkw 0x0800001090001e62 0x21000002120003cc 0x0800000000003e60 0x01000000000007cc

def z662 : W := mkw 0x024fc08ed52f8af8 0xc049f811daa5f15f 0x200fc00ff0078079 0x0401f801fe00f00f

def z663 : W := mkw 0x05f4c7500afaf503 0x00be98ea015f5ea0 0xdffcc7f00fffff87 0xfbff98fe01fffff0

def z664 : W := mkw 0x04b001500a501503 0x0096002a014a02a0 0xc8f003f00c783f86 0xd91e007e018f07f0

def z665 : W := mkw 0x0144c68ed0aaeaf8 0xc02898d1da155d5f 0xf8ccc78ff07fffff 0xbf1998f1fe0fffff

def z666 : W := mkw 0x05a0074000806000 0x00b400e800100c00 0xdff007f00f807806 0xfbfe00fe01f00f00

def z667 : W := mkw 0x04a0000002100000 0x0094000000420000 0x17c0000003980000 0x22f8000000730000

def z668 : W := mkw 0x05b007400a500000 0x00b600e8014a0000 0xd7f007f00ff80006 0xfafe00fe01ff0000

def z669 : W := mkw 0x0000400000220000 0x0000080000044000 0x8000c00000660005 0x90001800000cc000

def z670 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0x1f0302038f87f87c 0x43e0604071f0ff0f

def z671 : W := mkw 0x0044808440088088 0x4008901088011011 0x00c0018000180180 0x0018003000030030

def z672 : W := mkw 0x04b001500a501503 0x0096002a014a02a0 0xd8f005f000784786 0xbb1e00be000f08f0

def z673 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0x9f0306038f807806 0x73e060c071f00f00

def z674 : W := mkw 0x06eee000002a8000 0x00dddc0000055000 0x97fff800007f8005 0xf2ffff00000ff000

def z675 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0x680cc58c7007c7fb 0x0d0198b18e00f8ff

def z676 : W := mkw 0x0101060a84846850 0x802020c150908d0a 0xa803060f8c06787f 0x550060c1f180cf0f

def z677 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0xb80cc40c7007c07f 0x370198818e00f80f

def z678 : W := mkw 0x2feeb7fff0001e62 0x25fdd6fffe0003cc 0xeffffffff0003e63 0xfdfffffffe0007cc

def z679 : W := mkw 0x0000000000000000 0x0000000000000000 0xa800000000060067 0x150000000000c00c

def z680 : W := mkw 0x001148008c660840 0x00022900118cc108 0xa833fa038c663867 0xd5067f40718cc70c

def z681 : W := mkw 0x37ffefce4f7f8004 0x06fffdf9c9eff000 0x97fffd8c0fff8005 0xf2ffffb181fff000

def z682 : W := mkw 0x0800582130220220 0x21000b0426044044 0x0000f80070000000 0x00001f000e000000

def z683 : W := mkw 0x25a017ef60000000 0x04b402fdec000000 0xe7f007fff0000002 0xfcfe00fffe000000

def z684 : W := mkw 0x1ebb7831bf771e66 0x23d76f0637eee3cc 0xef33fa73ffe63e67 0xdde67f4e7ffcc7cc

def z685 : W := mkw 0x27eeb7ff60807503 0x04fdd6ffec100ea0 0xeffffffff0007f83 0xfdfffffffe000ff0

def z686 : W := mkw 0x16ffe8008fffe854 0x82dffd0011fffd0a 0x9ffff8000ffff87d 0xf3ffff0001ffff0f

def z687 : W := mkw 0x26eeb0af60000000 0x04ddd615ec000000 0xa7fff80ff0000001 0xf4ffff01fe000000

def z688 : W := mkw 0x06eee084502a82a8 0x40dddc108a055055 0xfffffd8c707fc7ff 0xffffffb18e0ff8ff

def z689 : W := mkw 0x27eea7ce40000000 0x04fdd4f9c8000000 0xe7ccc58c70000003 0xbcf998b18e000000

def z690 : W := mkw 0x15f4ef500afaf507 0x02be9dea015f5ea0 0xdff0fff00ff87f86 0xfbfe1ffe01ff0ff0

def z691 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0x97f002700ff83804 0xf2fe004e01ff0700

def z692 : W := mkw 0x17eea7400399e105 0x02fdd4e800733c20 0x17cc05800399c180 0x22f980b000733830

def z693 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0x50ccc58c7079c798 0xaa1998b18e0f38f3

def z694 : W := mkw 0x25b017ff6ad07503 0x04b602ffed5a0ea0 0xfff007fffff87f86 0xfffe00ffffff0ff0

def z695 : W := mkw 0x030a060a00000000 0x006140c140000000 0x0703020380000000 0x40e0604070000000

def z696 : W := mkw 0x04b001500ad07503 0x0096002a015a0ea0 0x58f001f00ff87f84 0x8b1e003e01ff0ff0

def z697 : W := mkw 0x08101031b8401e62 0x21020206370803cc 0xe8300273fc603e66 0xdd06004e7f8c07cc

def z698 : W := mkw 0x0000000000000000 0x0000000000000000 0x90c0000000780004 0xb2180000000f0000

def z699 : W := mkw 0x0000400010220220 0x0000080002044044 0xf80cc40c7067c67f 0xbf0198818e0cf8cf

def z700 : W := mkw 0x07fea7500ad07503 0x00ffd4ea015a0ea0 0xdffffff00ff87f87 0xfbfffffe01ff0ff0

def z701 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0x17f007f00f987980 0x62fe00fe01f30f30

def z702 : W := mkw 0x00448084500882a8 0x400890108a011055 0x78cc058c7019c7fa 0x2f1980b18e0338ff

def z703 : W := mkw 0x0db05f713af27723 0x21b60bee275e4ee4 0xdff0fff07ff87f86 0xfbfe1ffe0fff0ff0

def z704 : W := mkw 0x05a0074000000000 0x00b400e800000000 0x0730027000000000 0x40e6004e00000000

def z705 : W := mkw 0x05b006000ad06000 0x00b600c0015a0c00 0x9ff006000ff87806 0xf3fe00c001ff0f00

def z706 : W := mkw 0x0144c7d450aaf7ab 0x402898fa8a155ef5 0xf8ccc7fc707fffff 0xbf1998ff8e0fffff

def z707 : W := mkw 0x27aa376b20000000 0x04f546ed64000000 0xe73ffe7ff0000003 0xfce7ffcffe000000

def z708 : W := mkw 0x16ffe8008f7f8844 0x02dffd0011eff108 0x9ffff8000fffb865 0xf3ffff0001fff70c

def z709 : W := mkw 0x31115fef6f7f8004 0x06222bfdedeff000 0x700007ffffff8006 0x0e0000fffffff000

def z710 : W := mkw 0x210017efe0806850 0x842002fdfc100d0a 0x600007fff0003802 0x0c0000fffe000700

def z711 : W := mkw 0x121b48000f7f8004 0x0243690001eff000 0x973ff8000fff8005 0xf2e7ff0001fff000

def z712 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0xfffffffff0004007 0xfffffffffe000800

def z713 : W := mkw 0x0044808440000000 0x0008901088000000 0xf8ccc58c707fc7ff 0xbf1998b18e0ff8ff

def z714 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0x4833fa73fc663e64 0xc9067f4e7f8cc7cc

def z715 : W := mkw 0x05f4c7d45afaf7ab 0x40be98fa8b5f5ef5 0x273cc27c7f87b879 0x44e7984f8ff0f70f

def z716 : W := mkw 0x27eeb7ef60806000 0x04fdd6fdec100c00 0xf7fffffff3804003 0xfefffffffe700800

def z717 : W := mkw 0x15f4ef500afaf507 0x02be9dea015f5ea0 0x48f0fff000787f82 0x891e1ffe000f0ff0

def z718 : W := mkw 0x224ff0aff52f8af8 0xc449fe15fea5f15f 0x200ff80ff0078079 0x0401ff01fe00f00f

def z719 : W := mkw 0x09001631b0807e62 0x212002c636100fcc 0x68000673f0007e62 0x0d0000ce7e000fcc

def z720 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0xfff307f38ff87f87 0xfffe60fe71ff0ff0

def z721 : W := mkw 0x16ffa8000f5d8004 0x02dff50001ebb000 0x07f338000f980000 0x40fe670001f30000

def z722 : W := mkw 0x16bb28000f550004 0x02d7650001eaa000 0xdff33d800ff84786 0xfbfe67b001ff08f0

def z723 : W := mkw 0x27eea7ce4189e098 0xc4fdd4f9c8313c13 0x17cc058c0399c198 0x22f980b180733833

def z724 : W := mkw 0x27eeb7ef60806000 0x04fdd6fdec100c00 0xffffffffff87f87f 0xfffffffffff0ff0f

def z725 : W := mkw 0x16ffe8100f7f9406 0x02dffd0201eff280 0x97fffa700fffb805 0xf2ffff4e01fff700

def z726 : W := mkw 0x08115831bc6e9e62 0x21022b06378dd3cc 0xf833fa73fc7fbe67 0xdf067f4e7f8ff7cc

def z727 : W := mkw 0x0900163ba0807c52 0xa12002c774100f8a 0x0000027380003800 0x0000004e70000700

def z728 : W := mkw 0x020b480005270000 0x0041690000a4e000 0x970ff8000f878005 0x72e1ff0001f0f000

def z729 : W := mkw 0x37eeb7ef6399e105 0x06fdd6fdec733c20 0xf7fffffff399c183 0xfefffffffe733830

def z730 : W := mkw 0x16efe800052f8004 0x02ddfd0000a5f000 0x97fff8000f878005 0xf2ffff0001f0f000

def z731 : W := mkw 0x06fee0845a7a82a8 0x40dfdc108b4f5055 0xfffffd8c7fffc7ff 0xffffffb18ffff8ff

def z732 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0x3f0f040f8f87f87d 0x27e1e081f1f0ff0f

def z733 : W := mkw 0x0100075000807503 0x002000ea00100ea0 0xdfc007f00ff87f86 0xfbf800fe01ff0ff0

def z734 : W := mkw 0x08111831ac441c42 0x2102230635888388 0xe833fa73fc063867 0xdd067f4e7f80c70c

def z735 : W := mkw 0x14f4e8000a7a8004 0x029e9d00014f5000 0x07f0f8000ff80000 0xc0fe1f0001ff0000

def z736 : W := mkw 0x27eea7ce40806101 0x04fdd4f9c8100c20 0x07cc058c00004180 0x20f980b180000830

def z737 : W := mkw 0x16ffe8844f7f808c 0x42dffd1089eff011 0xf7fffd8c7fffc19f 0xfeffffb18ffff833

def z738 : W := mkw 0x06bb015a8f551d53 0x80d7602b51eaa3aa 0x60ff01ff807f87f9 0x8c1fe03ff00ff0ff

def z739 : W := mkw 0x04a0102120000000 0x0094020424000000 0xe7f3fa73f0000003 0xfcfe7f4e7e000000

def z740 : W := mkw 0x16fee8000b7b8004 0x02dfdd00016f7000 0x07f0f80003f80000 0x80fe1f00007f0000

def z741 : W := mkw 0x1effe8101f7f9626 0x23dffd0203eff2c4 0x97fff8000fff8605 0xf2ffff0001fff0c0

def z742 : W := mkw 0x07eeb76120000000 0x00fdd6ec24000000 0xe7fffff3f0000003 0xfcfffffe7e000000

def z743 : W := mkw 0x16ffe8008f7f8844 0x02dffd0011eff108 0x97fffa038fffb805 0xf2ffff4071fff700

def z744 : W := mkw 0x16efe884573f82ac 0x42ddfd108ae7f055 0xffcffd8c73ffc7ff 0xbff9ffb18e7ff8ff

def z745 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0xc7f007f00ff83f82 0xf8fe00fe01ff07f0

def z746 : W := mkw 0x16ffe8001f7f8224 0x02dffd0003eff044 0x9ffff8000fff8665 0xf3ffff0001fff0cc

def z747 : W := mkw 0x16ffa8000f550004 0x02dff50001eaa000 0x07f3f8000f800000 0xc0fe7f0001f00000

def z748 : W := mkw 0x1effe894df7f9eee 0x63dffd129beff3dd 0xfffffd8c7fffffff 0xffffffb18fffffff

def z749 : W := mkw 0x27aa776b302a82a8 0x44f54eed66055055 0x1f333a73807fc7fc 0x43e6674e700ff8ff

def z750 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0x67fffdfff0000001 0xacffffbffe000000

def z751 : W := mkw 0x025fc8000d6f8000 0x004bf90001adf000 0x97fff8000fff8005 0xf2ffff0001fff000

def z752 : W := mkw 0x27eeb7ef60000088 0x44fdd6fdec000011 0xe7fffffff000419b 0xfcfffffffe000833

def z753 : W := mkw 0x27eeb7ef61816010 0x84fdd6fdec302c02 0xe7fffffff3800003 0xfcfffffffe700000

def z754 : W := mkw 0x224eb0af60000000 0x0449d615ec000000 0xe0fffffff0000003 0xfc1ffffffe000000

def z755 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0x67fffbfff0000001 0xccffff7ffe000000

def z756 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0xdffc07fc0ff9ff9e 0xfbff80ff81ff3ff3

def z757 : W := mkw 0x18115831bf771e66 0x23022b0637eee3cc 0xe833fa73ffe63e67 0xdd067f4e7ffcc7cc

def z758 : W := mkw 0x24e5b1e5e5856850 0x849cb63cbcb0ad0a 0x58f0f9f07f87f87c 0x8b1e1f3e0ff0ff0f

def z759 : W := mkw 0x16ffe8845f7f82ac 0x42dffd108beff055 0xbffff80c7fffc7fd 0xf7ffff018ffff8ff

def z760 : W := mkw 0x09001771b0807f63 0x212002ee36100fec 0x68000273f0003e62 0x0d00004e7e0007cc

def z761 : W := mkw 0x0100060a80806850 0x802000c150100d0a 0xbf0c060f8f87f87f 0x77e180c1f1f0ff0f

def z762 : W := mkw 0x16ffa8000f550004 0x02dff50001eaa000 0x073ff8000f800001 0x40e7ff0001f00000

def z763 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0x58ccc58c707fc7fc 0xab1998b18e0ff8ff

def z764 : W := mkw 0x1cf4f8b57a7a96ae 0x639e9f16af4f52d5 0x40f0f9f070780780 0x881e1f3e0e0f00f0

def z765 : W := mkw 0x16bb28845f5502ac 0x42d765108beaa055 0x6f333d8c7f8047fa 0x4de667b18ff008ff

def z766 : W := mkw 0x16fee8845b7b82ac 0x42dfdd108b6f7055 0xfffcfd8c73ffc7ff 0xbfff9fb18e7ff8ff

def z767 : W := mkw 0x16ffe8845f7f82ac 0x42dffd108beff055 0x47f3f9807ff80780 0xc8fe7f300fff00f0

def z768 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0xf8f3fa73fc7e3e67 0xff1e7f4e7f8fc7cc

def z769 : W := mkw 0x16efe800073f8004 0x02ddfd0000e7f000 0x97fff800039f8001 0xf2ffff000073f000

def z770 : W := mkw 0x16ffe8844f7f808c 0x42dffd1089eff011 0xbffffd8c0fffc1ff 0xf7ffffb181fff83f

def z771 : W := mkw 0x081148109d671e62 0x2102290213ace3cc 0x180000000fe7be64 0x0300000001fcf7cc

def z772 : W := mkw 0x05a0176122906101 0x00b402ec24520c20 0xf7f3fff3f3984183 0xfefe7ffe7e730830

def z773 : W := mkw 0x0da15f61b6b66b61 0x21b42bec36d6cd6c 0x37c3fd83f39e41e1 0x26f87fb07e73c83c

def z774 : W := mkw 0x2100177b20807503 0x042002ef64100ea0 0x0000027380003800 0x0000004e70000700

def z775 : W := mkw 0x134fef5005aff507 0x0269fdea00b5fea0 0x480ffff00007ff83 0x0901fffe0000fff0

def z776 : W := mkw 0x081148109c661e62 0x21022902138cc3cc 0x000000000c063860 0x000000000180c70c

def z777 : W := mkw 0x16ffe8845f7f82ac 0x42dffd108beff055 0xf7fff98c7fff87fd 0xfeffff318ffff0ff

def z778 : W := mkw 0x0b1a5e3b39e37632 0xa1634bc7673c6ec6 0x573cfc7c73e1c618 0xaae79f8f8e7c38c3

def z779 : W := mkw 0x16ffe80a8f7f8854 0x82dffd0151eff10a 0x97fff8038fff8005 0xf2ffff0071fff000

def z780 : W := mkw 0x06ffe8000e760000 0x00dffd0001cec000 0x97fff8000ffe0005 0xf2ffff0001ffc000

def z781 : W := mkw 0x16bb28000f550004 0x02d7650001eaa000 0x97ff38000fff8005 0xf2ffe70001fff000

def z782 : W := mkw 0x06eea00001010000 0x00ddd40000202000 0x97fff80003818001 0xf2ffff0000703000

def z783 : W := mkw 0x16ffa8000f5d8004 0x02dff50001ebb000 0x97fff8000f998001 0xf2ffff0001f33000

def z784 : W := mkw 0x200011e560000000 0x0400023cac000000 0xe033fbf3f0000003 0xdc067f7e7e000000

def z785 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0x1ff007f00ff87f84 0x63fe00fe01ff0ff0

def z786 : W := mkw 0x081148109ef67f63 0x2102290213decfec 0x080000000fe63e64 0x0100000001fcc7cc

def z787 : W := mkw 0x081148109ce67e72 0xa1022902139ccfce 0x080000000c667e7c 0x01000000018ccfcf

def z788 : W := mkw 0x1eeeb031b3199e66 0x23ddd606366333cc 0x7fcc0273f399be62 0x2ff9804e7e7337cc

def z789 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0x57f007f00ff87f80 0xeafe00fe01ff0ff0

def z790 : W := mkw 0x16bb29500f551507 0x02d7652a01eaa2a0 0x073338700f800000 0x40e6670e01f00000

def z791 : W := mkw 0x0000102120000000 0x0000020424000000 0xe0f3fff3f0000003 0xfc1e7ffe7e000000

def z792 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0x60fffffff0000003 0x8c1ffffffe000000

def z793 : W := mkw 0x08115831bc6e9eea 0x61022b06378dd3dd 0xf83ffe7ffc7fffff 0xff07ffcfff8fffff

def z794 : W := mkw 0x37eea7ce4399e014 0x86fdd4f9c8733c02 0x17cc058c0399c018 0x22f980b180733803

def z795 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0x38ccc58c707fc7fd 0x271998b18e0ff8ff

def z796 : W := mkw 0x021b48000d670000 0x0043690001ace000 0x8733f8000fe60005 0xd0e67f0001fcc000

def z797 : W := mkw 0x16ffe8001f7f8224 0x02dffd0003eff044 0xfffffc0c7fffc67f 0xffffff818ffff8cf

def z798 : W := mkw 0x1effe8109f7f9e66 0x23dffd0213eff3cc 0xbffffa038fffbe67 0xf7ffff4071fff7cc

def z799 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0x2833fa73fc663e65 0x45067f4e7f8cc7cc

def z800 : W := mkw 0x08115831bc6e9eea 0x61022b06378dd3dd 0xe833fa73fc67be7f 0xdd067f4e7f8cf7cf

def z801 : W := mkw 0x0855c894dc6e9eea 0x610ab9129b8dd3dd 0x18cc058c0c7ffffc 0x231980b1818fffff

def z802 : W := mkw 0x0100162120000000 0x002002c424000000 0xe733fe73f0000003 0xfce67fce7e000000

def z803 : W := mkw 0x030a162b21816010 0x806142c564302c02 0xf73ffe7ff381c01b 0xfee7ffcffe703803

def z804 : W := mkw 0x26eeb0af60000000 0x04ddd615ec000000 0xe7fffa7ff0000003 0xfcffff4ffe000000

def z805 : W := mkw 0x27eeb7ef60088088 0x44fdd6fdec011011 0xe7fffffff0180183 0xfcfffffffe030030

def z806 : W := mkw 0x1effe8109f7f9e66 0x23dffd0213eff3cc 0x1fcc00000fffbe64 0x23f9800001fff7cc

def z807 : W := mkw 0x0900563bb0a27e72 0xa1200ac776144fce 0xf80cc67ff067fe7f 0xbf0198cffe0cffcf

def z808 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0xc7f3fff3f0000002 0xf8fe7ffe7e000000

def z809 : W := mkw 0x225eb0bf6ad07503 0x044bd617ed5a0ea0 0x380ff80ffff87f85 0x0701ff01ffff0ff0

def z810 : W := mkw 0x16ffe8001f7f8224 0x02dffd0003eff044 0xfffffd807fffc7e7 0xffffffb00ffff8fc

def z811 : W := mkw 0x16ffe8845f7f82ac 0x42dffd108beff055 0xd7fffd8c7fffc79d 0xfaffffb18ffff8f3

def z812 : W := mkw 0x06eeb0a560000000 0x00ddd614ac000000 0xe7fffffff0000003 0xfcfffffffe000000

def z813 : W := mkw 0x09114e109ce67e62 0x212229c2139ccfcc 0x9f0006000fe67e66 0x73e000c001fccfcc

def z814 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x17fcf8000fff8004 0xa2ff9f0001fff000

def z815 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0xa73ffe7ff0000003 0x74e7ffcffe000000

def z816 : W := mkw 0x27eea7ce42906101 0x04fdd4f9c8520c20 0x07cc058c03800000 0x20f980b180700000

def z817 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0xff0fc60fff87f87f 0xffe1f8c1fff0ff0f

def z818 : W := mkw 0x27eea7ce40806000 0x04fdd4f9c8100c00 0x17cc058c03804000 0x22f980b180700800

def z819 : W := mkw 0x08005031b0221e62 0x21000a06360443cc 0xe833fa73f0663e67 0xdd067f4e7e0cc7cc

def z820 : W := mkw 0x26eeb1ef60000000 0x04ddd63dec000000 0xe7fff9fff0000001 0xfcffff3ffe000000

def z821 : W := mkw 0x14f4e8000a7a8004 0x029e9d00014f5000 0x17f0f80003f80000 0xa2fe1f00007f0000

def z822 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0xf7fffffff001c01b 0xfefffffffe003803

def z823 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0xf8fffd8c707fc7ff 0xff1fffb18e0ff8ff

def z824 : W := mkw 0x27eeb7ef60088088 0x44fdd6fdec011011 0xe7fffffff001801b 0xfcfffffffe003003

def z825 : W := mkw 0x05b0075a0ad07503 0x00b600eb415a0ea0 0xfff007ff8ff87f86 0xfffe00fff1ff0ff0

def z826 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x0733f8000f800000 0x40e67f0001f00000

def z827 : W := mkw 0x16ffe8845f7f82ac 0x42dffd108beff055 0xfffff9807fff87e7 0xffffff300ffff0fc

def z828 : W := mkw 0x001148000c660000 0x00022900018cc000 0x9733f8000fe60005 0xf2e67f0001fcc000

def z829 : W := mkw 0x08115831ac661c42 0x21022b06358cc388 0xe033fa73fc663807 0xdc067f4e7f8cc700

def z830 : W := mkw 0x27aa376b20000000 0x04f546ed64000000 0x2733fa73f0000001 0x44e67f4e7e000000

def z831 : W := mkw 0x004490a560000000 0x00089214ac000000 0xe0f3fbf3f0000003 0xdc1e7f7e7e000000

def z832 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0xf8ccc78c7c7fffff 0xff1998f18f8fffff

def z833 : W := mkw 0x08115831be761f63 0x21022b0637cec3ec 0xe833fa73fc7e3fe7 0xdd067f4e7f8fc7fc

def z834 : W := mkw 0x16efa000071d8004 0x02ddf40000e3b000 0x97fff8000f9f8005 0xf2ffff0001f3f000

def z835 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0xc833fa73fc603e06 0xd9067f4e7f8c07c0

def z836 : W := mkw 0x085598b5ec4c9cca 0x610ab316bd899399 0x10ff3fff8c19f998 0x621fe7fff1833f33

def z837 : W := mkw 0x0900177130807723 0x212002ee26100ee4 0x480007f070007f82 0x090000fe0e000ff0

def z838 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0xd7f003f00ff83f84 0xfafe007e01ff07f0

def z839 : W := mkw 0x16bb68000f7f8004 0x02d76d0001eff000 0x97f338000fff8004 0xf2fe670001fff000

def z840 : W := mkw 0x27eeb76b20000000 0x04fdd6ed64000000 0xe7fffa73f0000003 0xfcffff4e7e000000

def z841 : W := mkw 0x16ffe8945f7f96ae 0x42dffd128beff2d5 0xfffffffc7fffffff 0xffffffff8fffffff

def z842 : W := mkw 0x021b08000d450000 0x0043610001a8a000 0x073338000f800000 0x40e6670001f00000

def z843 : W := mkw 0x090016bff0807efa 0xe12002d7fe100fdf 0x680007fff0007ffa 0x0d0000fffe000fff

def z844 : W := mkw 0x00015021b4260a60 0x00002a043684c14c 0xe833fa73fc663e67 0xdd067f4e7f8cc7cc

def z845 : W := mkw 0x124fe884552f82ac 0x4249fd108aa5f055 0xbf0ffc0c7f87c07f 0x77e1ff818ff0f80f

def z846 : W := mkw 0x26eeb1ef60000000 0x04ddd63dec000000 0xe0fffdfff0000003 0xbc1fffbffe000000

def z847 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0x68ccc58c707fc7fb 0x8d1998b18e0ff8ff

def z848 : W := mkw 0x16bb68000f7f8004 0x02d76d0001eff000 0x973f38000fff8005 0x72e7e70001fff000

def z849 : W := mkw 0x26eeb1ef60000000 0x04ddd63dec000000 0xe0fffbfff0000003 0xdc1fff7ffe000000

def z850 : W := mkw 0x15f4ee0a8afae854 0x82be9dc1515f5d0a 0x28f0fe0f8078787a 0x851e1fc1f00f0f0f

def z851 : W := mkw 0x04b001500ad07503 0x0096002a015a0ea0 0xdff001f00ff87f84 0xfbfe003e01ff0ff0

def z852 : W := mkw 0x001158312c661402 0x00022b06258cc280 0xe833fa73fc663e07 0xdd067f4e7f8cc7c0

def z853 : W := mkw 0x27eeb7ef61010010 0x84fdd6fdec202002 0xe7fffffff001801b 0xfcfffffffe003003

def z854 : W := mkw 0x081148109de77e72 0xa102290213bcefce 0x080000000fe63e64 0x0100000001fcc7cc

def z855 : W := mkw 0x16ffe884df7f8aec 0x42dffd109beff15d 0xffffff8fffffffff 0xfffffff1ffffffff

def z856 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0x5ff005f00ff87f84 0xabfe00be01ff0ff0

def z857 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0xfff007f00ffe7fe7 0xfffe00fe01ffcffc

def z858 : W := mkw 0x27aa37ef60000000 0x04f546fdec000000 0xe733fffff0000003 0xdce67ffffe000000

def z859 : W := mkw 0x0900177bb0807f73 0xa12002ef76100fee 0x680007fff0007ffa 0x0d0000fffe000fff

def z860 : W := mkw 0x0a4fd8aff52f8af8 0xe149fb15fea5f15f 0x200ff80ff0078079 0x0401ff01fe00f00f

def z861 : W := mkw 0x16bb28100f551406 0x02d7650201eaa280 0xcf333a700fe03e06 0xd9e6674e01fc07c0

def z862 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0x370f060f8f87f879 0x66e1e0c1f1f0ff0f

def z863 : W := mkw 0x05a0176120000000 0x00b402ec24000000 0xe733fa73f0000003 0xdce67f4e7e000000

def z864 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x9ffff8000fffc07d 0xf3ffff0001fff80f

def z865 : W := mkw 0x081148109c661e62 0x21022902138cc3cc 0xd8c005800c7e7fe6 0xbb1800b0018fcffc

def z866 : W := mkw 0x16ffe8845f7f82ac 0x42dffd108beff055 0xdffffd807fffc787 0xfbffffb00ffff8f0

def z867 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0xe8f3fbf3fc7e3fe7 0xdd1e7f7e7f8fc7fc

def z868 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0x70ccc58c707fc7f9 0xae1998b18e0ff8ff

def z869 : W := mkw 0x0000102120000000 0x0000020424000000 0xe03ffe7ff0000003 0xfc07ffcffe000000

def z870 : W := mkw 0x081148109d671e72 0xa102290213ace3ce 0x080000000c67be7c 0x01000000018cf7cf

def z871 : W := mkw 0x0cf4d9f57a7a97ab 0x619e9b3eaf4f52f5 0x40f0f9f070780780 0x881e1f3e0e0f00f0

def z872 : W := mkw 0x210017ef60806101 0x042002fdec100c20 0x600007fff0004182 0x0c0000fffe000830

def z873 : W := mkw 0x2fffefdedc661e62 0x25fffdfbdb8cc3cc 0x0fcc058c0c663e64 0x21f980b1818cc7cc

def z874 : W := mkw 0x081148109ff77f73 0xa102290213feefee 0x180000000ffffffc 0x0300000001ffffff

def z875 : W := mkw 0x14f5e8000e7e8004 0x029ebd0001cfd000 0x97f3f8000ffe0005 0xf2fe7f0001ffc000

def z876 : W := mkw 0x16bb68000f770004 0x02d76d0001eee000 0x973ff8000fe78005 0xf2e7ff0001fcf000

def z877 : W := mkw 0x16ffe8001f7f8224 0x02dffd0003eff044 0xb7fff8007fff8065 0xf6ffff000ffff00c

def z878 : W := mkw 0x06eea00000000000 0x00ddd40000000000 0x97fff8000f800005 0xf2ffff0001f00000

def z879 : W := mkw 0x081148109c661e62 0x21022902138cc3cc 0x180000000c67fe7c 0x03000000018cffcf

def z880 : W := mkw 0x210017ff708077ab 0x442002ffee100ef5 0x680007fff0007ffa 0x0d0000fffe000fff

def z881 : W := mkw 0x290017fff0807e72 0xa52002fffe100fce 0x680007fff0007e7a 0x0d0000fffe000fcf

def z882 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0x1f0f060f8f87f87c 0x63e1e0c1f1f0ff0f

def z883 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0x78cc058c707fc7fe 0x2f1980b18e0ff8ff

def z884 : W := mkw 0x16ffe88edf7f8afc 0xc2dffd11dbeff15f 0xfffffd8fffffc7ff 0xffffffb1fffff8ff

def z885 : W := mkw 0x16ffe8000f7f808c 0x42dffd0001eff011 0x97fff8000fffc19d 0xf2ffff0001fff833

def z886 : W := mkw 0x16ffe9400f7f8004 0x02dffd2801eff000 0xd7fff9f00fff8005 0xfaffff3e01fff000

def z887 : W := mkw 0x16ffe8001f7f82ac 0x42dffd0003eff055 0xdffffd800fffc7ff 0xfbffffb001fff8ff

def z888 : W := mkw 0x081148109c661e62 0x21022902138cc3cc 0x000000000c603e00 0x00000000018c07c0

def z889 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0xf7fffffff0184183 0xfefffffffe030830

def z890 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0xfffffffff07fc7ff 0xfffffffffe0ff8ff

def z891 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x87f3f8000ffe0005 0xd0fe7f0001ffc000

def z892 : W := mkw 0x16ffe80a0f7f8014 0x82dffd0141eff002 0x97fff80c0fff801d 0xf2ffff0181fff003

def z893 : W := mkw 0x0cb01031ba501e62 0x21960206374a03cc 0xfff00273fff83e66 0xfffe004e7fff07cc

def z894 : W := mkw 0x130b2e0a85856854 0x826165c150b0ad0a 0xbf0f3e0f8f87f87f 0x77e1e7c1f1f0ff0f

def z895 : W := mkw 0x00115821ac660840 0x00022b04358cc108 0xe833fa73fc663867 0xdd067f4e7f8cc70c

def z896 : W := mkw 0x16ffa8000f550004 0x02dff50001eaa000 0x97fff8000ff80005 0xf2ffff0001ff0000

def z897 : W := mkw 0x181148109ffffe76 0xa302290213ffffce 0x180000000ffffe7c 0x0300000001ffffcf

def z898 : W := mkw 0x1effe8009f7f8a64 0x23dffd0013eff14c 0x97fff8000fff8065 0xf2ffff0001fff00c

def z899 : W := mkw 0x210017ef60806010 0x842002fdec100c02 0x600007fff000401a 0x0c0000fffe000803

def z900 : W := mkw 0x0db14f509ef67f63 0x21b629ea13decfec 0x1fc005800ffe7fe4 0x23f800b001ffcffc

def z901 : W := mkw 0x27eea7ce43916111 0x84fdd4f9c8722c22 0x17cc058c0399c198 0x22f980b180733833

def z902 : W := mkw 0x06fea0844a500000 0x00dfd410894a0000 0xfffffd8c7ff84787 0xffffffb18fff08f0

def z903 : W := mkw 0x16ffe8845f7f82ac 0x42dffd108beff055 0xfffff80c7fff867f 0xffffff018ffff0cf

def z904 : W := mkw 0x16ffe9500f7f9507 0x02dffd2a01eff2a0 0xdffffdf00fffc787 0xfbffffbe01fff8f0

def z905 : W := mkw 0x04b148000e760000 0x0096290001cec000 0x8733f8000fe60005 0xd0e67f0001fcc000

def z906 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x9ffffa000fffb807 0xf3ffff4001fff700

def z907 : W := mkw 0x0000103120001402 0x0000020624000280 0xe833fa73f0003e03 0xdd067f4e7e0007c0

def z908 : W := mkw 0x214497ff60807503 0x042892ffec100ea0 0xf8ccc7fff0787f87 0xbf1998fffe0f0ff0

def z909 : W := mkw 0x08115831be761e62 0x21022b0637cec3cc 0xf833fa73fffe3e67 0xdf067f4e7fffc7cc

def z910 : W := mkw 0x27eeb7ef60806101 0x04fdd6fdec100c20 0xe7fffffff0004183 0xfcfffffffe000830

def z911 : W := mkw 0x04b108000e540000 0x0096210001ca8000 0x97f338000ff80004 0xf2fe670001ff0000

def z912 : W := mkw 0x08011031b4041e62 0x21002206368083cc 0xe833fa73fc063e67 0xdd067f4e7f80c7cc

def z913 : W := mkw 0x37eeb7ef6399e014 0x86fdd6fdec733c02 0xf7fffffff399c01b 0xfefffffffe733803

def z914 : W := mkw 0x16ffe8845f7f82ac 0x42dffd108beff055 0x97fff8007fff8005 0xf2ffff000ffff000

def z915 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0xffcf078f8f87f87f 0xfff9e0f1f1f0ff0f

def z916 : W := mkw 0x16bb28000f550004 0x02d7650001eaa000 0x8733f8000f800001 0xd0e67f0001f00000

def z917 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0x6833fa73fc603e62 0xcd067f4e7f8c07cc

def z918 : W := mkw 0x16ffe80a8f7f8854 0x82dffd0151eff10a 0xbffffa0f8fffb87f 0xf7ffff41f1fff70f

def z919 : W := mkw 0x16bb28000f550004 0x02d7650001eaa000 0xbf3f3c0c0f87c07f 0x77e7e78181f0f80f

def z920 : W := mkw 0x16ffe8844f7f8004 0x02dffd1089eff000 0xd7fff9807fff8005 0xfaffff300ffff000

def z921 : W := mkw 0x034fc68ed5afeaf8 0xc069f8d1dab5fd5f 0x47c3c383fff83f80 0xc8f878707fff07f0

def z922 : W := mkw 0x16ffe8844f7f8004 0x02dffd1089eff000 0xfffffd8c7fffc787 0xffffffb18ffff8f0

def z923 : W := mkw 0x0000102120000000 0x0000020424000000 0x4033fa73f0000000 0xc8067f4e7e000000

def z924 : W := mkw 0x16ffe88edf7f8afc 0xc2dffd11dbeff15f 0xb7fff80fffff807d 0xf6ffff01fffff00f

def z925 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0xf7fff8007fff8007 0xfeffff000ffff000

def z926 : W := mkw 0x27eeb7ef61816010 0x84fdd6fdec302c02 0xffffffffff81f81f 0xfffffffffff03f03

def z927 : W := mkw 0x16ffe8845f7f82ac 0x42dffd108beff055 0x9ffffd8c0fffc7fd 0xf3ffffb181fff8ff

def z928 : W := mkw 0x27eeb7ef60088000 0x04fdd6fdec011000 0xf7fffffff0198003 0xfefffffffe033000

def z929 : W := mkw 0x16bb28000f550004 0x02d7650001eaa000 0x07f338000ff80000 0xc0fe670001ff0000

def z930 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0xeffffffff0004783 0xfdfffffffe0008f0

def z931 : W := mkw 0x16ffe8001f7f82ac 0x42dffd0003eff055 0xbffffc0c0fffc7ff 0xf7ffff8181fff8ff

def z932 : W := mkw 0x16bb28000f550004 0x02d7650001eaa000 0x87f338000f800000 0xf0fe670001f00000

def z933 : W := mkw 0x16bb68000f770004 0x02d76d0001eee000 0x0733f8000fe00000 0xc0e67f0001fc0000

def z934 : W := mkw 0x08111831ac441c42 0x2102230635888388 0xe833fa73fc603e07 0xdd067f4e7f8c07c0

def z935 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0xf8cfc78ff07fc7ff 0xff19f8f1fe0ff8ff

def z936 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x97f3f8000ff80004 0xf2fe7f0001ff0000

def z937 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0xfffffd8c0fffc7ff 0xffffffb181fff8ff

def z938 : W := mkw 0x00001021a0000840 0x0000020434000108 0xe833fa73f0003863 0xdd067f4e7e00070c

def z939 : W := mkw 0x16bb28000f550004 0x02d7650001eaa000 0x873f38000f800001 0x70e7e70001f00000

def z940 : W := mkw 0x08015831b4261e62 0x21002b063684c3cc 0xe833fa73f0063e63 0xdd067f4e7e00c7cc

def z941 : W := mkw 0x09001771a0807d43 0x212002ee34100fa8 0x480007f380007f82 0x090000fe70000ff0

def z942 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0xe7f3fbf3f0000003 0xdcfe7f7e7e000000

def z943 : W := mkw 0x16ffe9500f7f9507 0x02dffd2a01eff2a0 0x97fff8700fff8005 0xf2ffff0e01fff000

def z944 : W := mkw 0x081148109c661e62 0x21022902138cc3cc 0x180000000c7e7fe4 0x03000000018fcffc

def z945 : W := mkw 0x16ffe8845f7f82ac 0x42dffd108beff055 0x273ff80c7f878079 0x44e7ff018ff0f00f

def z946 : W := mkw 0x27eeb7ef60088088 0x44fdd6fdec011011 0xfffffffff079c79f 0xfffffffffe0f38f3

def z947 : W := mkw 0x2100176ba0806850 0x842002ed74100d0a 0x0000027380003800 0x0000004e70000700

def z948 : W := mkw 0x16bb28000f550004 0x02d7650001eaa000 0x17f338000f980000 0x62fe670001f30000

def z949 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0x0033fa73fc003800 0x40067f4e7f800700

def z950 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0xff0f060f8fe7fe7f 0xffe1e0c1f1fcffcf

def z951 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0xbfcf078f8f9ff9ff 0x77f9e0f1f1f3ff3f

def z952 : W := mkw 0x16ffe8100f7f9406 0x02dffd0201eff280 0x9ffff8000fffbe05 0xf3ffff0001fff7c0

def z953 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0x3f0c060f8f87f87e 0x27e180c1f1f0ff0f

def z954 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x97fffd800fffc185 0xf2ffffb001fff830

def z955 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0xf7fffffff0780007 0xfefffffffe0f0000

def z956 : W := mkw 0x08015821b4260a60 0x21002b043684c14c 0xe833fa73fc063867 0xdd067f4e7f80c70c

def z957 : W := mkw 0x05a0074000806000 0x00b400e800100c00 0xdff007f00ff87f86 0xfbfe00fe01ff0ff0

def z958 : W := mkw 0x16bb68001f7f82ac 0x42d76d0003eff055 0x1f3338000fffc7fc 0x43e6670001fff8ff

def z959 : W := mkw 0x16aa200003110004 0x02d5440000622000 0x0733380003800000 0x40e6670000700000

def z960 : W := mkw 0x16bb68000f770004 0x02d76d0001eee000 0x073338000fe60004 0x40e6670001fcc000

def z961 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0xd7fffa700fff8007 0xfaffff4e01fff000

def z962 : W := mkw 0x000010a560000000 0x00000214ac000000 0xe033fffff0000003 0xdc067ffffe000000

def z963 : W := mkw 0x16bb28000f5d8004 0x02d7650001ebb000 0x173338000f998000 0x42e6670001f33000

def z964 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0xf7fffffff0078007 0xfefffffffe00f000

def z965 : W := mkw 0x0100177120807503 0x002002ee24100ea0 0x680007f3f0007f82 0x0d0000fe7e000ff0

def z966 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0x6833fa73f0663e63 0x8d067f4e7e0cc7cc

def z967 : W := mkw 0x16bb68000f770004 0x02d76d0001eee000 0x0733f8000f860001 0x40e67f0001f0c000

def z968 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x07fff8000fff8001 0xc0ffff0001fff000

def z969 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x87fff8000f878001 0xf0ffff0001f0f000

def z970 : W := mkw 0x16ffe8844f7f8004 0x02dffd1089eff000 0xb7fff80c7fff8005 0xf6ffff018ffff000

def z971 : W := mkw 0x1effe8109f7f9eee 0x63dffd0213eff3dd 0x9ffff8000ffffffd 0xf3ffff0001ffffff

def z972 : W := mkw 0x16ffe8008f7f8844 0x02dffd0011eff108 0xb7fff8038fff8065 0xf6ffff0071fff00c

def z973 : W := mkw 0x16ffe8845f7f8224 0x02dffd108beff044 0xfffffd8c7fff8667 0xffffffb18ffff0cc

def z974 : W := mkw 0x00000084500002a8 0x400000108a000055 0xf8cc058c707fc7ff 0xbf1980b18e0ff8ff

def z975 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0xff3f067f8f87f87f 0xffe7e0cff1f0ff0f

def z976 : W := mkw 0x2044b0a560000000 0x04089614ac000000 0xe033fa73f0000003 0xdc067f4e7e000000

def z977 : W := mkw 0x05e497e560000000 0x00bc92fcac000000 0xe7fffffff0000003 0xfcfffffffe000000

def z978 : W := mkw 0x1044e884502a82ac 0x42089d108a055055 0xf8ccfd8c707fc7ff 0xbf199fb18e0ff8ff

def z979 : W := mkw 0x020a102b20000000 0x0041420564000000 0xe03ffa7ff0000003 0xdc07ff4ffe000000

def z980 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0x27fffffff0000001 0x64fffffffe000000

def z981 : W := mkw 0x230a17ef60000000 0x046142fdec000000 0xe73ffffff0000003 0xfce7fffffe000000

def z982 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x17ff38000fff8004 0x62ffe70001fff000

def z983 : W := mkw 0x16eea00003198004 0x02ddd40000633000 0x17ff380003998000 0x62ffe70000733000

def z984 : W := mkw 0x210017ef60806000 0x042002fdec100c00 0x680007fff0007802 0x0d0000fffe000f00

def z985 : W := mkw 0x16ffe8844f7f808c 0x42dffd1089eff011 0xdffffd8c0fffc79f 0xfbffffb181fff8f3

def z986 : W := mkw 0x25a017ef60000000 0x04b402fdec000000 0xe7f3fffff0000003 0xfcfe7ffffe000000

def z987 : W := mkw 0x120b280005050004 0x0241650000a0a000 0x970f38000f878005 0x72e1e70001f0f000

def z988 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0x67f3fffff0000002 0xccfe7ffffe000000

def z989 : W := mkw 0x26eeb1e560000000 0x04ddd63cac000000 0xe7fffbf3f0000003 0xfcffff7e7e000000

def z990 : W := mkw 0x16bb68000f7f8004 0x02d76d0001eff000 0x073338000ff80000 0x40e6670001ff0000

def z991 : W := mkw 0x04e4b02120000000 0x009c960424000000 0xe0f3fa73f0000003 0xdc1e7f4e7e000000

def z992 : W := mkw 0x08115831bc6e9eea 0x61022b06378dd3dd 0xf8f3fff3fc7fffff 0xff1e7ffe7f8fffff

def z993 : W := mkw 0x16eea0844319808c 0x42ddd41088633011 0xf7fffd8c7399c19b 0xfeffffb18e733833

def z994 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x17fff8000f9f8001 0x62ffff0001f3f000

def z995 : W := mkw 0x27eeb7ef61816010 0x84fdd6fdec302c02 0xfffffffff387c07f 0xfffffffffe70f80f

def z996 : W := mkw 0x0944d6bff0aafefa 0xe1289ad7fe155fdf 0xf8ccc7fff07fffff 0xbf1998fffe0fffff

def z997 : W := mkw 0x081148109c661eea 0x61022902138cc3dd 0x080000000c667ffc 0x01000000018ccfff

def z998 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0xb7fff80c0fff807d 0xf6ffff0181fff00f

def z999 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0xf83ffa73fc67be67 0xff07ff4e7f8cf7cc

def z1000 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0xffccc58c7fffc7ff 0xfff998b18ffff8ff

def z1001 : W := mkw 0x16ffe8845f7f82ac 0x42dffd108beff055 0xf7fffd8c7fff8787 0xfeffffb18ffff0f0

def z1002 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0xaf0f020f8f87b87f 0x55e1e041f1f0f70f

def z1003 : W := mkw 0x020b000085050840 0x0041600010a0a108 0xbf0f060f8f87f87f 0x77e1e0c1f1f0ff0f

def z1004 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0xbf0f060f8fffffff 0x77e1e0c1f1ffffff

def z1005 : W := mkw 0x09001771a0807d43 0x212002ee34100fa8 0x0000027380003800 0x0000004e70000700

def z1006 : W := mkw 0x08111831ac441c42 0x2102230635888388 0x4033fa73fc003800 0xc8067f4e7f800700

def z1007 : W := mkw 0x020b000a85050850 0x8041600150a0a10a 0xbf0f020f8f87b87f 0x77e1e041f1f0f70f

def z1008 : W := mkw 0x16ffe8001f7f82ac 0x42dffd0003eff055 0x97fff8000fff807d 0xf2ffff0001fff00f

def z1009 : W := mkw 0x27aa376b20000000 0x04f546ed64000000 0xe7f3fff3f0000003 0xfcfe7ffe7e000000

def z1010 : W := mkw 0x24e4b1e560000000 0x049c963cac000000 0x40f3fbf3f0000000 0xc81e7f7e7e000000

def z1011 : W := mkw 0x15b02f500ad07507 0x02b605ea015a0ea0 0xdff03ff00ff87f86 0xfbfe07fe01ff0ff0

def z1012 : W := mkw 0x14f5e8000f7f8004 0x029ebd0001eff000 0x97f0f8000fff8004 0xf2fe1f0001fff000

def z1013 : W := mkw 0x04b001500a501503 0x0096002a014a02a0 0xdff003f00ff83f86 0xfbfe007e01ff07f0

def z1014 : W := mkw 0x27eeb7ef6298e189 0x44fdd6fdec531c31 0xf7fffffff399c19b 0xfefffffffe733833

def z1015 : W := mkw 0x020a102120000000 0x0041420424000000 0xe73ffa73f0000003 0xfce7ff4e7e000000

def z1016 : W := mkw 0x00011021a4040840 0x0000220434808108 0xe033fa73fc003803 0xdc067f4e7f800700

def z1017 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0xff33fa73ffe63e67 0xffe67f4e7ffcc7cc

def z1018 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x17cff8000fff8005 0x22f9ff0001fff000

def z1019 : W := mkw 0x16eea00003198004 0x02ddd40000633000 0x17cff80003998001 0x22f9ff0000733000

def z1020 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0xeffffffff000407b 0xfdfffffffe00080f

def z1021 : W := mkw 0x16bb28000f550004 0x02d7650001eaa000 0x173338000f878004 0x42e6670001f0f000

def z1022 : W := mkw 0x0000102120000000 0x0000020424000000 0x2033fa73f0000001 0x44067f4e7e000000

def z1023 : W := mkw 0x36ffe88e4f7f8004 0x06dffd11c9eff000 0x97fff80c0fff8005 0xf2ffff0181fff000

def z1024 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0xfff0c7f07ff87f87 0xfffe18fe0fff0ff0

def z1025 : W := mkw 0x2144d7ff70aaf7ab 0x44289affee155ef5 0xf8ccc7fff07fffff 0xbf1998fffe0fffff

def z1026 : W := mkw 0x081148109c6e9e62 0x21022902138dd3cc 0x180000000c7fbe64 0x03000000018ff7cc

def z1027 : W := mkw 0x01114f500ce67503 0x002229ea019ccea0 0xc833fff00c667f87 0xd9067ffe018ccff0

def z1028 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x97fffc0c0fffc01d 0xf2ffff8181fff803

def z1029 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0xf833fa73fc67fe7f 0xdf067f4e7f8cffcf

def z1030 : W := mkw 0x16ffa8844f5d808c 0x42dff51089ebb011 0x17ff3d8c0f99c198 0x62ffe7b181f33833

def z1031 : W := mkw 0x1ebb28108f551c46 0x23d7650211eaa388 0x073338000f803800 0x40e6670001f00700

def z1032 : W := mkw 0x08115831bc6e9eea 0x61022b06378dd3dd 0xe833fa73fc7e3fe7 0xdd067f4e7f8fc7fc

def z1033 : W := mkw 0x224eb0af60000000 0x0449d615ec000000 0x603ff87ff0000001 0x8c07ff0ffe000000

def z1034 : W := mkw 0x0900162bb0806a70 0xa12002c576100d4e 0x2800060ff000787a 0x050000c1fe000f0f

def z1035 : W := mkw 0x030a060a00806000 0x006140c140100c00 0xbf0f060f8f87f87f 0x77e1e0c1f1f0ff0f

def z1036 : W := mkw 0x27eeb7ef60088088 0x44fdd6fdec011011 0xfffffffff01fc1ff 0xfffffffffe03f83f

def z1037 : W := mkw 0x1effe8109f7f9e66 0x23dffd0213eff3cc 0xfffff8007fffbe67 0xffffff000ffff7cc

def z1038 : W := mkw 0x081148109e761f63 0x2102290213cec3ec 0x080000000c7e3fe4 0x01000000018fc7fc

def z1039 : W := mkw 0x210017f560807503 0x042002feac100ea0 0x480007f070007f82 0x090000fe0e000ff0

def z1040 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x17fff8000ff98000 0xe2ffff0001ff3000

def z1041 : W := mkw 0x030b074a85856951 0x806160e950b0ad2a 0xbf0f078f8f87f9ff 0x77e1e0f1f1f0ff3f

def z1042 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0x673ffffff0000003 0x4ce7fffffe000000

def z1043 : W := mkw 0x14b028000a500004 0x02960500014a0000 0x073038000f800000 0x40e6070001f00000

def z1044 : W := mkw 0x16ffe9d45f7f97af 0x42dffd3a8beff2f5 0xfffffdfc7fffc7ff 0xffffffbf8ffff8ff

def z1045 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x17fff80003ff8001 0xa2ffff00007ff000

def z1046 : W := mkw 0x18115831be7e9e66 0x23022b0637cfd3cc 0xe833fa73fc7e3e67 0xdd067f4e7f8fc7cc

def z1047 : W := mkw 0x16eea00003198004 0x02ddd40000633000 0x17fcf80003998000 0xa2ff9f0000733000

def z1048 : W := mkw 0x210017eff0806af8 0xc42002fdfe100d5f 0x680007fff0007ffa 0x0d0000fffe000fff

def z1049 : W := mkw 0x27eeb7ef63916111 0x84fdd6fdec722c22 0xf7fffffff399c19b 0xfefffffffe733833

def z1050 : W := mkw 0x06ffe8000d670000 0x00dffd0001ace000 0x97fff8000fe78005 0xf2ffff0001fcf000

def z1051 : W := mkw 0x24a0316120000000 0x0494062c24000000 0xe033fa73f0000003 0xdc067f4e7e000000

def z1052 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0xbffff8000fff8067 0xf7ffff0001fff00c

def z1053 : W := mkw 0x06fea0000a500000 0x00dfd400014a0000 0x87fff8000f800001 0xf0ffff0001f00000

def z1054 : W := mkw 0x16ffe8844f7f808c 0x42dffd1089eff011 0x97fff80c0fff801d 0xf2ffff0181fff003

def z1055 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0xfffc07fc0ff87f87 0xffff80ff81ff0ff0

def z1056 : W := mkw 0x210017ffe0807d53 0x842002fffc100faa 0x680007fff0007ffa 0x0d0000fffe000fff

def z1057 : W := mkw 0x0100162ba0806850 0x802002c574100d0a 0x6800067ff000787a 0x0d0000cffe000f0f

def z1058 : W := mkw 0x16eee084533b82ac 0x42dddc108a677055 0xfffffd8c73ffc7ff 0xffffffb18e7ff8ff

def z1059 : W := mkw 0x27aa376b20000000 0x04f546ed64000000 0x4733fa73f0000000 0xc8e67f4e7e000000

def z1060 : W := mkw 0x27eeb7ef62100000 0x04fdd6fdec420000 0xf7fffffff3980003 0xfefffffffe730000

def z1061 : W := mkw 0x16eea00003110004 0x02ddd40000622000 0x87fff80003800001 0xf0ffff0000700000

def z1062 : W := mkw 0x0900163ba0807c52 0xa12002c774100f8a 0x2800067f8000787a 0x050000cff0000f0f

def z1063 : W := mkw 0x16ffe8844f7f808c 0x42dffd1089eff011 0x97fff9800fff8185 0xf2ffff3001fff030

def z1064 : W := mkw 0x08111831ac441c42 0x2102230635888388 0x2033fa73fc003801 0x44067f4e7f800700

def z1065 : W := mkw 0x081148109deffefa 0xe102290213bdffdf 0x180000000ffffffc 0x0300000001ffffff

def z1066 : W := mkw 0x04b000100a501402 0x00960002014a0280 0xdff007f00ff87f86 0xfbfe00fe01ff0ff0

def z1067 : W := mkw 0x120b280005050004 0x0241650000a0a000 0x070338000f800000 0x40e0670001f00000

def z1068 : W := mkw 0x081148109c661e62 0x21022902138cc3cc 0x0000000000660660 0x00000000000cc0cc

def z1069 : W := mkw 0x16ffe8008f7f8844 0x02dffd0011eff108 0xbffffe0f8ffff87f 0xf7ffffc1f1ffff0f

def z1070 : W := mkw 0x181148109e7e9e66 0x2302290213cfd3cc 0x080000000c7e3e64 0x01000000018fc7cc

def z1071 : W := mkw 0x0000400010220220 0x0000080002044044 0xf8ccc58c707fc7ff 0xbf1998b18e0ff8ff

def z1072 : W := mkw 0x16ffe9400f7f8105 0x02dffd2801eff020 0x97fff9800fff8185 0xf2ffff3001fff030

def z1073 : W := mkw 0x1ebb68109f771e66 0x23d76d0213eee3cc 0x0f3338000fe63e64 0x41e6670001fcc7cc

def z1074 : W := mkw 0x08101031b8401e62 0x21020206370803cc 0xe833fa73fc603e67 0xdd067f4e7f8c07cc

def z1075 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x9ffffc000fffc007 0xf3ffff8001fff800

def z1076 : W := mkw 0x0000102120000000 0x0000020424000000 0xe833fa73fc003807 0xdd067f4e7f800700

def z1077 : W := mkw 0x0fbb1f7bafd57d53 0xa1f763ef75faafaa 0x07333a738f803800 0x40e6674e71f00700

def z1078 : W := mkw 0x1effe8109f7f9e66 0x23dffd0213eff3cc 0xdffffa700fffbe67 0xfbffff4e01fff7cc

def z1079 : W := mkw 0x210017ff60807503 0x042002ffec100ea0 0x600007fff0003802 0x0c0000fffe000700

def z1080 : W := mkw 0x081148109c6e9eea 0x61022902138dd3dd 0x080000000c67be7c 0x01000000018cf7cf

def z1081 : W := mkw 0x16ffe8001f7f8224 0x02dffd0003eff044 0xd7fff8007fff8605 0xfaffff000ffff0c0

def z1082 : W := mkw 0x04f5c8000e7e8000 0x009eb90001cfd000 0x97fff8000fff8005 0xf2ffff0001fff000

def z1083 : W := mkw 0x081148109efeffeb 0x6102290213dfdffd 0x180000000ffffffc 0x0300000001ffffff

def z1084 : W := mkw 0x04b048000a720000 0x00960900014e4000 0x97f0f8000ff80004 0xf2fe1f0001ff0000

def z1085 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0xdff007f00ffffffe 0xfbfe00fe01ffffff

def z1086 : W := mkw 0x0000102120000000 0x0000020424000000 0xe833fa73f0600607 0xdd067f4e7e0c00c0

def z1087 : W := mkw 0x1a4ff8a5f52f8aec 0x6349ff14bea5f15d 0x200ff80ff0078079 0x0401ff01fe00f00f

def z1088 : W := mkw 0x0000102120000000 0x0000020424000000 0xf83ffe7ff007c07f 0xff07ffcffe00f80f

def z1089 : W := mkw 0x08115831bd671e62 0x21022b0637ace3cc 0xf833fa73ffe7be67 0xdf067f4e7ffcf7cc

def z1090 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0xe83ffa7ffc67be7f 0xdd07ff4fff8cf7cf

def z1091 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0xe83ffe7ffc663e67 0xfd07ffcfff8cc7cc

def z1092 : W := mkw 0x16efe884573f82ac 0x42ddfd108ae7f055 0x37cffd8c739fc1f9 0x26f9ffb18e73f83f

def z1093 : W := mkw 0x181148109f771e66 0x2302290213eee3cc 0x080000000fe63e64 0x0100000001fcc7cc

def z1094 : W := mkw 0x37eeb7ef62188004 0x06fdd6fdec431000 0xe7fffffff0180003 0xfcfffffffe030000

def z1095 : W := mkw 0x16ffa8000f550004 0x02dff50001eaa000 0x07ff38000f800000 0x60ffe70001f00000

def z1096 : W := mkw 0x16ffe80a8f7f8854 0x82dffd0151eff10a 0xbffffc0f8fffc07f 0xf7ffff81f1fff80f

def z1097 : W := mkw 0x16bb68000f770004 0x02d76d0001eee000 0x97f3f8000ffe0005 0xf2fe7f0001ffc000

def z1098 : W := mkw 0x18115831bf7f9eee 0x63022b0637eff3dd 0xf833fa73ffffffff 0xdf067f4e7fffffff

def z1099 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0xc7fffbf3f0000001 0xf8ffff7e7e000000

def z1100 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0xe033fa73fc063863 0xdc067f4e7f80c70c

def z1101 : W := mkw 0x090017f5f0807feb 0x612002febe100ffd 0x680007fff0007ffa 0x0d0000fffe000fff

def z1102 : W := mkw 0x0100162120806000 0x002002c424100c00 0xff33fe73ff807807 0xffe67fce7ff00f00

def z1103 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0xc033fa73fc663e05 0xd8067f4e7f8cc7c0

def z1104 : W := mkw 0x06efa00005050000 0x00ddf40000a0a000 0x87fff8000f800001 0xf0ffff0001f00000

def z1105 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0xfff007fc0ff87ffe 0xfffe00ff81ff0fff

def z1106 : W := mkw 0x27eea7ce41816010 0x84fdd4f9c8302c02 0x07cc058c03800000 0x20f980b180700000

def z1107 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0xeffffffff0600607 0xfdfffffffe0c00c0

def z1108 : W := mkw 0x081148109c661e62 0x21022902138cc3cc 0x880002000c663e66 0x51000040018cc7cc

def z1109 : W := mkw 0x14b148000f7f8004 0x0296290001eff000 0x97f3f8000fff8005 0xf2fe7f0001fff000

def z1110 : W := mkw 0x04f4a0000a500000 0x009e9400014a0000 0x97f0f8000ff80004 0xf2fe1f0001ff0000

def z1111 : W := mkw 0x004490a560088088 0x40089214ac011011 0xf0fffffff019c19b 0xfe1ffffffe033833

def z1112 : W := mkw 0x16ab280007150004 0x02d5650000e2a000 0x0703380003800000 0x00e0670000700000

def z1113 : W := mkw 0x06bb48000f770000 0x00d7690001eee000 0x97fff8000fff8005 0xf2ffff0001fff000

def z1114 : W := mkw 0x16bb28100f551406 0x02d7650201eaa280 0x07333a700f803800 0x40e6674e01f00700

def z1115 : W := mkw 0x0110061008c07402 0x002200c201180e80 0xdff007f00ff87f86 0xfbfe00fe01ff0ff0

def z1116 : W := mkw 0x030a162b20000000 0x006142c564000000 0xe733fa73f0000003 0xdce67f4e7e000000

def z1117 : W := mkw 0x0010503138621622 0x00020a06270c42c4 0xe833fa73fc663e67 0xdd067f4e7f8cc7cc

def z1118 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0xf833fe73fc667e67 0xff067fce7f8ccfcc

def z1119 : W := mkw 0x16ffe8101f7f9626 0x02dffd0203eff2c4 0xfffffa707fffbe67 0xffffff4e0ffff7cc

def z1120 : W := mkw 0x16ffe8100f7f9406 0x02dffd0201eff280 0xd7fff8700fff8605 0xfaffff0e01fff0c0

def z1121 : W := mkw 0x0b1b4e1a9de77e72 0xa16369c353bcefce 0x1f0c040c0fe7fe7c 0x23e1808181fcffcf

def z1122 : W := mkw 0x16ffa8000f5d8004 0x02dff50001ebb000 0x073f38000f818000 0x40e7e70001f03000

def z1123 : W := mkw 0x081148109e761e62 0x2102290213cec3cc 0x180000000ffe3e64 0x0300000001ffc7cc

def z1124 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0x5fc007f00ff87f86 0x2bf800fe01ff0ff0

def z1125 : W := mkw 0x0900163bb0807e72 0xa12002c776100fce 0x68000273f0003e62 0x0d00004e7e0007cc

def z1126 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0xeffffffffc003807 0xfdffffffff800700

def z1127 : W := mkw 0x16bb68000f7f8004 0x02d76d0001eff000 0x9733f8000fff8005 0xd2e67f0001fff000

def z1128 : W := mkw 0x06aa302120000000 0x00d5460424000000 0xe733fa73f0000003 0xdce67f4e7e000000

def z1129 : W := mkw 0x124fe800052f8004 0x0249fd0000a5f000 0x070ff8000f878001 0x40e1ff0001f0f000

def z1130 : W := mkw 0x0000102120000000 0x0000020424000000 0x6033f873f0000001 0x8c067f0e7e000000

def z1131 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0xdffc07f00fffff87 0xfbff80fe01fffff0

def z1132 : W := mkw 0x37eeb7ef63110004 0x06fdd6fdec622000 0xe7fffffff3800003 0xfcfffffffe700000

def z1133 : W := mkw 0x27eeb7ef61010000 0x04fdd6fdec202000 0xf7fffffff3818003 0xfefffffffe703000

def z1134 : W := mkw 0x08105831b8621e62 0x21020b06370c43cc 0xe833fa73f0603e63 0xdd067f4e7e0c07cc

def z1135 : W := mkw 0x04b148001e760220 0x0096290003cec044 0xfff3fd807ffe47e7 0xfffe7fb00fffc8fc

def z1136 : W := mkw 0x06eea00002100000 0x00ddd40000420000 0x97fff80003980001 0xf2ffff0000730000

def z1137 : W := mkw 0x16ba28000b510004 0x02d74500016a2000 0x0730380003800000 0x00e6070000700000

def z1138 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0xe833fe7ffc667e7f 0xdd067fcfff8ccfcf

def z1139 : W := mkw 0x16fea0000b598004 0x02dfd400016b3000 0x97fff8000ff98005 0xf2ffff0001ff3000

def z1140 : W := mkw 0x06efa08445050000 0x00ddf41088a0a000 0xfffffd8c7f87c07f 0xffffffb18ff0f80f

def z1141 : W := mkw 0x16fee8000a7a8004 0x02dfdd00014f5000 0x97fff8000ff80005 0xf2ffff0001ff0000

def z1142 : W := mkw 0x181148109d6f9e66 0x2302290213adf3cc 0x080000000c67be64 0x01000000018cf7cc

def z1143 : W := mkw 0x37eeb7ef6319808c 0x46fdd6fdec633011 0xf7fffffff399c19b 0xfefffffffe733833

def z1144 : W := mkw 0x16efa800071d8004 0x02ddf50000e3b000 0x17cf380003998000 0x22f9e70000733000

def z1145 : W := mkw 0x16eee000033b8004 0x02dddc0000677000 0x97fff80003ff8005 0xf2ffff00007ff000

def z1146 : W := mkw 0x27eea7ce4298e189 0x44fdd4f9c8531c31 0x17cc058c0399c198 0x22f980b180733833

def z1147 : W := mkw 0x04b108000e540000 0x0096210001ca8000 0x073338000f800000 0x40e6670001f00000

def z1148 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0xa7fffa7ff0000001 0xf4ffff4ffe000000

def z1149 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0x4ff007f00ff87f82 0xc9fe00fe01ff0ff0

def z1150 : W := mkw 0x16fea8000b598004 0x02dfd500016b3000 0x17fc380003998000 0x22ff870000733000

def z1151 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x9ffff8000fffc785 0xf3ffff0001fff8f0

def z1152 : W := mkw 0x214497ef60000000 0x042892fdec000000 0xe0fffffff0000003 0xfc1ffffffe000000

def z1153 : W := mkw 0x020b000005050000 0x0041600000a0a000 0x973ff8000f878005 0xf2e7ff0001f0f000

def z1154 : W := mkw 0x27eeb7ef60806010 0x84fdd6fdec100c02 0xe7fffffff000401b 0xfcfffffffe000803

def z1155 : W := mkw 0x030b074a85856850 0x806160e950b0ad0a 0xff0f07ff8f87f87f 0x7fe1e0fff1f0ff0f

def z1156 : W := mkw 0x081148109c661e62 0x21022902138cc3cc 0xb80c040c0c67fe7f 0x37018081818cffcf

def z1157 : W := mkw 0x36ffe9c44f7f8004 0x06dffd3889eff000 0x97fff9800fff8005 0xf2ffff3001fff000

def z1158 : W := mkw 0x16fee8000b7b8004 0x02dfdd00016f7000 0x97fff80003f98001 0xf2ffff00007f3000

def z1159 : W := mkw 0x16ffe8108f7f9c46 0x02dffd0211eff388 0xfffffa738fffbe67 0xffffff4e71fff7cc

def z1160 : W := mkw 0x0044c084502a82a8 0x400898108a055055 0xf8fcc7fc707fc7ff 0xff1f98ff8e0ff8ff

def z1161 : W := mkw 0x37eeb7ef61098004 0x06fdd6fdec213000 0xe7fffffff0018003 0xfcfffffffe003000

def z1162 : W := mkw 0x16efe800073f8004 0x02ddfd0000e7f000 0x070ff80003878001 0x00e1ff000070f000

def z1163 : W := mkw 0x0100176120000000 0x002002ec24000000 0xe033fff3f0000003 0xdc067ffe7e000000

def z1164 : W := mkw 0x04b000000a500000 0x00960000014a0000 0x97f3f8000ff80005 0xf2fe7f0001ff0000

def z1165 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0x3f0f020f8f87f87d 0x47e1e041f1f0ff0f

def z1166 : W := mkw 0x06ab200005050000 0x00d5640000a0a000 0x073338000f800000 0x40e6670001f00000

def z1167 : W := mkw 0x24e4b1e560000000 0x049c963cac000000 0x60f3f9f3f0000001 0x8c1e7f3e7e000000

def z1168 : W := mkw 0x14b028000a500004 0x02960500014a0000 0x97f038000ff80004 0xf2fe070001ff0000

def z1169 : W := mkw 0x27eeb7ef60806000 0x04fdd6fdec100c00 0xeffffffff0007803 0xfdfffffffe000f00

def z1170 : W := mkw 0x06efe000052f8000 0x00ddfc0000a5f000 0x97fff8000fff8005 0xf2ffff0001fff000

def z1171 : W := mkw 0x25e4b7ef60000000 0x04bc96fdec000000 0xe0f3fffff0000003 0xdc1e7ffffe000000

def z1172 : W := mkw 0x08001031a0001c42 0x2100020634000388 0xe033fa73f0003803 0xdc067f4e7e000700

def z1173 : W := mkw 0x16eeb02123198004 0x02ddd60424633000 0xf7fffa73f3998003 0xfeffff4e7e733000

def z1174 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0xd7fffd800fff8007 0xfaffffb001fff000

def z1175 : W := mkw 0x0810583138621622 0x21020b06270c42c4 0xe833fa73fc603e07 0xdd067f4e7f8c07c0

def z1176 : W := mkw 0x16bb28000f550004 0x02d7650001eaa000 0x873338000f860005 0x50e6670001f0c000

def z1177 : W := mkw 0x27eea7ce40806010 0x84fdd4f9c8100c02 0x07cc058c00004018 0x20f980b180000803

def z1178 : W := mkw 0x04f5c8845e7e82a8 0x409eb9108bcfd055 0xfffffd8c7fffc7ff 0xffffffb18ffff8ff

def z1179 : W := mkw 0x27eeb7ef62906101 0x04fdd6fdec520c20 0xe7fffffff3800003 0xfcfffffffe700000

def z1180 : W := mkw 0x021b48001d670220 0x0043690003ace044 0xff3ffc0c7fe7c67f 0xffe7ff818ffcf8cf

def z1181 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0xbf3ffe0f8f87f87f 0xf7e7ffc1f1f0ff0f

def z1182 : W := mkw 0x08115831bd671e72 0xa1022b0637ace3ce 0xe833fa73fc67be7f 0xdd067f4e7f8cf7cf

def z1183 : W := mkw 0x124fe800052f8004 0x0249fd0000a5f000 0x170ff80003878001 0x22e1ff000070f000

def z1184 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x87fff8000ff80001 0xf0ffff0001ff0000

def z1185 : W := mkw 0x224eb0af60000000 0x0449d615ec000000 0x203ffa7ff0000001 0x4407ff4ffe000000

def z1186 : W := mkw 0x16eee800033b8004 0x02dddd0000677000 0x17ccf80003998000 0x22f99f0000733000

def z1187 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0xeffffffff0060067 0xfdfffffffe00c00c

def z1188 : W := mkw 0x06ba20000a500000 0x00d74400014a0000 0x073338000f800000 0x40e6670001f00000

def z1189 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0xdff3fff00ff87f87 0xfbfe7ffe01ff0ff0

def z1190 : W := mkw 0x181148109f7f9eee 0x6302290213eff3dd 0x180000000ffffffc 0x0300000001ffffff

def z1191 : W := mkw 0x16bb68001f770224 0x02d76d0003eee044 0xef33f8007fe60667 0xdde67f000ffcc0cc

def z1192 : W := mkw 0x200010af60000000 0x04000215ec000000 0xe033fa7ff0000003 0xdc067f4ffe000000

def z1193 : W := mkw 0x16ffe80a0f7f8004 0x02dffd0141eff000 0xb7fff80f8fff8005 0xf6ffff01f1fff000

def z1194 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0x6033fa73fc663e61 0xcc067f4e7f8cc7cc

def z1195 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0xcff003f00ff83f86 0xd9fe007e01ff07f0

def z1196 : W := mkw 0x06fee0000a7a8000 0x00dfdc00014f5000 0x97fff8000fff8005 0xf2ffff0001fff000

def z1197 : W := mkw 0x024fa00005050000 0x0049f40000a0a000 0x970ff8000f878005 0x72e1ff0001f0f000

def z1198 : W := mkw 0x27eeb7ef60806000 0x04fdd6fdec100c00 0xe7ffffffff803803 0xfcfffffffff00700

def z1199 : W := mkw 0x16ffe8845f7f82ac 0x42dffd108beff055 0xb7fffd8c7fffc1fd 0xf6ffffb18ffff83f

def z1200 : W := mkw 0x234eb6af60000000 0x0469d6d5ec000000 0xe73ffe7ff0000003 0xfce7ffcffe000000

def z1201 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0xe833fff3fc667fe7 0xdd067ffe7f8ccffc

def z1202 : W := mkw 0x214497efe0806850 0x842892fdfc100d0a 0xf8ccc7fff007f87f 0xbf1998fffe00ff0f

def z1203 : W := mkw 0x16bb28008f550844 0x02d7650011eaa108 0x07333a038f803800 0x40e6674071f00700

def z1204 : W := mkw 0x16ffe8008f7f8854 0x82dffd0011eff10a 0x97fff8000fff807d 0xf2ffff0001fff00f

def z1205 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0xb70f020f8f87b87d 0x76e1e041f1f0f70f

def z1206 : W := mkw 0x16ffe8009f7f8a64 0x02dffd0013eff14c 0xfffffa03ffffbe67 0xffffff407ffff7cc

def z1207 : W := mkw 0x14f4e8000a7a8004 0x029e9d00014f5000 0x97fcf8000fff8005 0xf2ff9f0001fff000

def z1208 : W := mkw 0x16bb28000f550004 0x02d7650001eaa000 0x873338000fe00004 0xd0e6670001fc0000

def z1209 : W := mkw 0x08111831bc441e62 0x21022306378883cc 0xe833fa73fc003e63 0xdd067f4e7f8007cc

def z1210 : W := mkw 0x2144d7eff0aaeaf8 0xc4289afdfe155d5f 0xf8ccc7fff07fffff 0xbf1998fffe0fffff

def z1211 : W := mkw 0x16ffa8000f550004 0x02dff50001eaa000 0x97fff8000f878005 0xf2ffff0001f0f000

def z1212 : W := mkw 0x24e4b1e560000000 0x049c963cac000000 0xe0fffffff0000003 0xfc1ffffffe000000

def z1213 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0xbfcf060f8ffff87f 0xf7f9e0c1f1ffff0f

def z1214 : W := mkw 0x025fc8845d6f82a8 0x404bf9108badf055 0xfffffd8c7fffc7ff 0xffffffb18ffff8ff

def z1215 : W := mkw 0x16ffe8100f7f9406 0x02dffd0201eff280 0xdffffff00fffff87 0xfbfffffe01fffff0

def z1216 : W := mkw 0x07eeb62b20000000 0x00fdd6c564000000 0xe7fffe7ff0000003 0xfcffffcffe000000

def z1217 : W := mkw 0x0010103128401402 0x0002020625080280 0xe033fa73fc003803 0xdc067f4e7f800700

def z1218 : W := mkw 0x27eeb7ef6189e098 0xc4fdd6fdec313c13 0xf7fffffff399c19b 0xfefffffffe733833

def z1219 : W := mkw 0x05b007500ad07503 0x00b600ea015a0ea0 0x5ff003f00ff87f84 0xcbfe007e01ff0ff0

def z1220 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0x0733fa73f0000000 0x40e67f4e7e000000

def z1221 : W := mkw 0x16ffe8844f7f8004 0x02dffd1089eff000 0x97fffd8c0fff8005 0xf2ffffb181fff000

def z1222 : W := mkw 0x16bb280a8f550854 0x82d7650151eaa10a 0x073338038f800000 0x40e6670071f00000

def z1223 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0x47fffffff0000000 0xe8fffffffe000000

def z1224 : W := mkw 0x021b08000d450000 0x0043610001a8a000 0x973f38000f878005 0x72e7e70001f0f000

def z1225 : W := mkw 0x2100176b20000000 0x042002ed64000000 0xe033fa73f0000003 0xdc067f4e7e000000

def z1226 : W := mkw 0x18115831bd6f9e66 0x23022b0637adf3cc 0xe833fa73fc67be67 0xdd067f4e7f8cf7cc

def z1227 : W := mkw 0x16ffe8001f7f82ac 0x42dffd0003eff055 0x97fff8000fff8785 0xf2ffff0001fff0f0

def z1228 : W := mkw 0x09005771b0a27f63 0x21200aee36144fec 0xf8c0c7f3f07e7fe7 0xbf1818fe7e0fcffc

def z1229 : W := mkw 0x16ffe8845f7f82ac 0x42dffd108beff055 0xbffffc0c7fffc07f 0xf7ffff818ffff80f

def z1230 : W := mkw 0x16bb28000f550004 0x02d7650001eaa000 0x173338000ff80004 0x42e6670001ff0000

def z1231 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0xb7fffc0c0fff8007 0xf6ffff8181fff000

def z1232 : W := mkw 0x16bb28000f550004 0x02d7650001eaa000 0x973338000f800004 0x72e6670001f00000

def z1233 : W := mkw 0x16efe800073f8004 0x02ddfd0000e7f000 0x97cff8000f9f8005 0x72f9ff0001f3f000

def z1234 : W := mkw 0x16ffa8000f5d8004 0x02dff50001ebb000 0x97ff38000ff98004 0xf2ffe70001ff3000

def z1235 : W := mkw 0x081148109ce67f63 0x21022902139ccfec 0x080000000c667fe4 0x01000000018ccffc

def z1236 : W := mkw 0x27eeb7ef62100101 0x04fdd6fdec420020 0xe7fffffff0180183 0xfcfffffffe030030

def z1237 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0xa033fa73fc663865 0xd4067f4e7f8cc70c

def z1238 : W := mkw 0x14f4e8845a7a82ac 0x429e9d108b4f5055 0xdff0fd807ff84786 0xfbfe1fb00fff08f0

def z1239 : W := mkw 0x125fe8000f7f8004 0x024bfd0001eff000 0x970ff8000fff8005 0x72e1ff0001fff000

def z1240 : W := mkw 0x16ffe8100f7f9507 0x02dffd0201eff2a0 0x97fff8000fff8785 0xf2ffff0001fff0f0

def z1241 : W := mkw 0x124fe800052f8004 0x0249fd0000a5f000 0x97cff8000fff8005 0xf2f9ff0001fff000

def z1242 : W := mkw 0x16ffe8845f7f82ac 0x42dffd108beff055 0xdffff9807fffc7fd 0xfbffff300ffff8ff

def z1243 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0xd7fff9800fff8785 0xfaffff3001fff0f0

def z1244 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0xff0f078f8f87ffff 0x7fe1e0f1f1f0ffff

def z1245 : W := mkw 0x16ffe8000f770004 0x02dffd0001eee000 0x87fff8000fe60005 0xf0ffff0001fcc000

def z1246 : W := mkw 0x37eea7ce4399e105 0x06fdd4f9c8733c20 0x17cc058c0399c180 0x22f980b180733830

def z1247 : W := mkw 0x16ffe8844f7f8004 0x02dffd1089eff000 0xfffffd8c7fffc07f 0xffffffb18ffff80f

def z1248 : W := mkw 0x0101060084846840 0x002020c010908d08 0xbf0f060f8f87f87f 0x77e1e0c1f1f0ff0f

def z1249 : W := mkw 0x081148109c6e9eea 0x61022902138dd3dd 0x080000000c7e3fe4 0x01000000018fc7fc

def z1250 : W := mkw 0x234eb7ef60000000 0x0469d6fdec000000 0xe03ffffff0000003 0xdc07fffffe000000

def z1251 : W := mkw 0x06ab200005050000 0x00d5640000a0a000 0x973f38000f878005 0x72e7e70001f0f000

def z1252 : W := mkw 0x00111031ac441c42 0x0002220635888388 0xe833fa73fc663e67 0xdd067f4e7f8cc7cc

def z1253 : W := mkw 0x2100177b20807503 0x042002ef64100ea0 0x480007f380007f82 0x090000fe70000ff0

def z1254 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0xe7fffffff0780783 0xfcfffffffe0f00f0

def z1255 : W := mkw 0x07aa176b20000000 0x00f542ed64000000 0xe7fffffff0000003 0xfcfffffffe000000

def z1256 : W := mkw 0x26eeb1ef60000000 0x04ddd63dec000000 0x40f3f9f3f0000000 0x881e7f3e7e000000

def z1257 : W := mkw 0x04a0116120000000 0x0094022c24000000 0xe0f3fbf3f0000003 0xdc1e7f7e7e000000

def z1258 : W := mkw 0x01114e0a8ce66850 0x802229c1519ccd0a 0xa833fe0f8c66787f 0xd5067fc1f18ccf0f

def z1259 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x873ff8000fe78005 0xd0e7ff0001fcf000

def z1260 : W := mkw 0x26eeb1ef60000000 0x04ddd63dec000000 0x203ff87ff0000001 0x0407ff0ffe000000

def z1261 : W := mkw 0x081148109c661e62 0x21022902138cc3cc 0xc80000000c663e66 0x99000000018cc7cc

def z1262 : W := mkw 0x06ffa0000f550000 0x00dff40001eaa000 0x97fff8000fff8005 0xf2ffff0001fff000

def z1263 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0x2f0f060f8f87f87b 0x45e1e0c1f1f0ff0f

def z1264 : W := mkw 0x0944d7f5f0aaffeb 0x61289afebe155ffd 0xf8ccc7fff07fffff 0xbf1998fffe0fffff

def z1265 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x17f3f8000fff8004 0xc2fe7f0001fff000

def z1266 : W := mkw 0x024eb02120000000 0x0049d60424000000 0xe03ffa73f0000003 0xdc07ff4e7e000000

def z1267 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0x6833fa73fc063e63 0x4d067f4e7f80c7cc

def z1268 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0xe7fffffff007807b 0xfcfffffffe00f00f

def z1269 : W := mkw 0x034e96af60000000 0x0069d2d5ec000000 0xe7fffffff0000003 0xfcfffffffe000000

def z1270 : W := mkw 0x16bb28000f550004 0x02d7650001eaa000 0x073f38000f878001 0x40e7e70001f0f000

def z1271 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0xdffff8000fff8607 0xfbffff0001fff0c0

def z1272 : W := mkw 0x16ffa8000f5d8004 0x02dff50001ebb000 0x97ff38000f9f8005 0x72ffe70001f3f000

def z1273 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0xf833fa73fc7e7fe7 0xdf067f4e7f8fcffc

def z1274 : W := mkw 0x16efe800073f8004 0x02ddfd0000e7f000 0x97cff80003ff8005 0xb2f9ff00007ff000

def z1275 : W := mkw 0x2100176ba0806850 0x842002ed74100d0a 0x2800067f8000787a 0x050000cff0000f0f

def z1276 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x173ff8000fff8005 0x42e7ff0001fff000

def z1277 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0x973ff8000f878005 0x72e7ff0001f0f000

def z1278 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0xe73ffa7ff0000003 0xdce7ff4ffe000000

def z1279 : W := mkw 0x0000102120000000 0x0000020424000000 0xf8f3fff3f0784787 0xff1e7ffe7e0f08f0

def z1280 : W := mkw 0x1effe8108f7f9c46 0x23dffd0211eff388 0x97fff8000fffb805 0xf2ffff0001fff700

def z1281 : W := mkw 0x16bb29500f551507 0x02d7652a01eaa2a0 0x47f339f00ff80780 0xc8fe673e01ff00f0

def z1282 : W := mkw 0x0000102120000000 0x0000020424000000 0xe833fa73f0060067 0xdd067f4e7e00c00c

def z1283 : W := mkw 0x125fe8000d6f8004 0x024bfd0001adf000 0x973ff8000fe78005 0xf2e7ff0001fcf000

def z1284 : W := mkw 0x16fee8000b7b8004 0x02dfdd00016f7000 0x97fcf8000ff98004 0xf2ff9f0001ff3000

def z1285 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0xe033fa73fc603e03 0xdc067f4e7f8c07c0

def z1286 : W := mkw 0x16bb280a8f550854 0x82d7650151eaa10a 0x273f380f8f878079 0x44e7e701f1f0f00f

def z1287 : W := mkw 0x020b000a85856850 0x8041600150b0ad0a 0xbf0f000f8f87f87d 0x77e1e001f1f0ff0f

def z1288 : W := mkw 0x16fee8000b7b8004 0x02dfdd00016f7000 0x97fcf80003ff8005 0xb2ff9f00007ff000

def z1289 : W := mkw 0x220a302b20000000 0x0441460564000000 0xe033fa73f0000003 0xdc067f4e7e000000

def z1290 : W := mkw 0x24f4f1f57a7a97ab 0x449e9e3eaf4f52f5 0x40f0f9f070780780 0x881e1f3e0e0f00f0

def z1291 : W := mkw 0x16bb28008f550844 0x02d7650011eaa108 0xaf333a038f863867 0x55e6674071f0c70c

def z1292 : W := mkw 0x16fee8845b7b82ac 0x42dfdd108b6f7055 0x57fcfd8c73f9c798 0xaaff9fb18e7f38f3

def z1293 : W := mkw 0x0100162b20000000 0x002002c564000000 0xe033fe7ff0000003 0xdc067fcffe000000

def z1294 : W := mkw 0x16ffe8000f7f8004 0x02dffd0001eff000 0xb7fffa038fff8007 0xf6ffff4071fff000

def z1295 : W := mkw 0x27eeb7ef60000000 0x04fdd6fdec000000 0xf7ffffffff800007 0xfefffffffff00000

def z1296 : W := mkw 0x004490a560000000 0x00089214ac000000 0xe03ffa7ff0000003 0xdc07ff4ffe000000

def z1297 : W := mkw 0x14f4e8845a7a82ac 0x429e9d108b4f5055 0xfffcfd8c7fffc7ff 0xffff9fb18ffff8ff

def z1298 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0xf8fffffffc7fffff 0xff1fffffff8fffff

def z1299 : W := mkw 0x06ba20000a500000 0x00d74400014a0000 0x97f338000ff80004 0xf2fe670001ff0000

def z1300 : W := mkw 0x27bb377bafd57d53 0x84f766ef75faafaa 0x07333a738f803800 0x40e6674e71f00700

def z1301 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0xe8f3fff3fc663e67 0xfd1e7ffe7f8cc7cc

def z1302 : W := mkw 0x134fee0a85afe854 0x8269fdc150b5fd0a 0x280ffe0f8007f87b 0x0501ffc1f000ff0f

def z1303 : W := mkw 0x030b060a85856850 0x806160c150b0ad0a 0xa70f060f8f87b87b 0x74e1e0c1f1f0f70f

def z1304 : W := mkw 0x081148109ce67e62 0x21022902139ccfcc 0x180000000fe67e64 0x0300000001fccfcc

def z1305 : W := mkw 0x27eeb7ef62906101 0x04fdd6fdec520c20 0xfffffffff3f84787 0xfffffffffe7f08f0

def z1306 : W := mkw 0x08115831bc661e62 0x21022b06378cc3cc 0xa833fa73fc063867 0x55067f4e7f80c70c

def z1307 : W := mkw 0x290017fff0807f63 0x252002fffe100fec 0x680007fff0007fe2 0x0d0000fffe000ffc

def z1308 : W := mkw 0x05b0075a0ad07513 0x80b600eb415a0ea2 0xdff007fc0ff87f9e 0xfbfe00ff81ff0ff3

def z1309 : W := mkw 0x081148109c661e62 0x21022902138cc3cc 0xa80000000c663e67 0x15000000018cc7cc

def z1310 : W := mkw 0x27eeb7ef62906101 0x04fdd6fdec520c20 0xffffffffff987987 0xfffffffffff30f30

def z1311 : W := mkw 0x16ffe8845f7f82ac 0x42dffd108beff055 0xf7fffd8c7fff807f 0xfeffffb18ffff00f

def z1312 : W := mkw 0x0044902120000000 0x0008920424000000 0xe0fffa73f0000003 0xfc1fff4e7e000000

def z1313 : W := mkw 0x25e4b7e560000000 0x04bc96fcac000000 0xe7f3fff3f0000003 0xfcfe7ffe7e000000

def z1314 : W := mkw 0x210016afe0806850 0x842002d5fc100d0a 0x2800060ff000787a 0x050000c1fe000f0f

def z1315 : W := mkw 0x16ffe8001f7f82ac 0x42dffd0003eff055 0xfffff8007fffc7ff 0xffffff000ffff8ff

def z1316 : W := mkw 0x08115831bc661eea 0x61022b06378cc3dd 0xe833fa73fc667fff 0xdd067f4e7f8ccfff

def z1317 : W := mkw 0x16bb68000f7f8004 0x02d76d0001eff000 0x073338000f878000 0x40e6670001f0f000

def z1318 : W := mkw 0x16ffe9500f7f9507 0x02dffd2a01eff2a0 0xdffffbf00fffbf87 0xfbffff7e01fff7f0

def z1319 : W := mkw 0x0a0b1031b5051e62 0x2141620636a0a3cc 0xff0f0273ff87be67 0x7fe1e04e7ff0f7cc

def z1320 : W := mkw 0x124fe884552f82ac 0x4249fd108aa5f055 0xffcffd8c7fffc7ff 0xfff9ffb18ffff8ff

def z1321 : W := mkw 0x06efe084552f82a8 0x40ddfc108aa5f055 0xfffffd8c7fffc7ff 0xffffffb18ffff8ff

def z1322 : W := mkw 0x16bb28000f550004 0x02d7650001eaa000 0x173f38000f818000 0x62e7e70001f03000

def z1323 : W := mkw 0x27eeb7ef60806000 0x04fdd6fdec100c00 0xfffffffffff87f87 0xffffffffffff0ff0

def z1324 : W := mkw 0x16ffa8844f550004 0x02dff51089eaa000 0xe7fffd8c7f800003 0xfcffffb18ff00000

def z1325 : W := mkw 0x181148109fffff67 0x2302290213ffffec 0x180000000fffffe4 0x0300000001fffffc

def z1326 : W := mkw 0x16ffe9d45f7f97af 0x42dffd3a8beff2f5 0xd7fff9f07fff8785 0xfaffff3e0ffff0f0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z7,z3,z4,z8,z6]),(0,[z9,z1,z2,z3,z10,z4,z5])],[(0,[z11,z1,z2,z3,z4,z5,z6]),(0,[z1,z12,z2,z3,z4,z5,z6]),(0,[z13,z1,z2,z3,z4,z5,z6]),(0,[z1,z14,z2,z15,z4,z5,z6]),(0,[z1,z14,z2,z3,z16,z4,z6]),(1,[z1,z2,z3,z4,z17,z6]),(0,[z18,z1,z2,z3,z10,z4,z5])],[(0,[z1,z2,z3,z4,z19,z20,z6]),(0,[z1,z2,z3,z4,z21,z5,z6]),(0,[z1,z22,z2,z3,z4,z5,z6])],[(0,[z23,z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z24,z4,z20,z6]),(0,[z1,z25,z2,z3,z4,z26,z6])],[(0,[z1,z27,z2,z3,z4,z20,z6]),(0,[z28,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z29,z5,z6])],[(1,[z1,z2,z3,z4,z30,z6]),(0,[z1,z31,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z32,z5,z6]),(0,[z33,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z34,z4,z5,z6]),(0,[z35,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z36,z3,z4,z5,z6]),(0,[z1,z14,z2,z3,z4,z26,z6]),(0,[z1,z2,z3,z4,z5,z6,z37]),(0,[z38,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z39,z4,z5,z6]),(0,[z1,z2,z3,z4,z40,z5,z6]),(0,[z1,z2,z3,z4,z8,z41,z6]),(0,[z1,z2,z3,z4,z8,z42,z6]),(0,[z1,z2,z3,z4,z43,z5,z6]),(0,[z1,z2,z3,z24,z4,z5,z44])],[(0,[z45,z1,z2,z3,z4,z5,z6]),(0,[z46,z1,z2,z3,z10,z4,z5]),(0,[z47,z1,z2,z3,z4,z20,z6]),(0,[z1,z48,z3,z49,z4,z5,z6]),(0,[z1,z25,z2,z3,z4,z5,z6]),(0,[z1,z2,z50,z3,z4,z5,z6]),(1,[z23,z1,z2,z19,z5,z6]),(0,[z1,z2,z51,z3,z4,z5,z6])]],
   [[(0,[z52,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z53,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z54,z6]),(0,[z1,z2,z3,z4,z5,z55,z56])],[(0,[z57,z1,z2,z3,z4,z20,z6]),(0,[z58,z1,z2,z3,z4,z5,z6]),(0,[z59,z1,z2,z3,z4,z5,z6]),(0,[z1,z60,z2,z3,z4,z5,z61]),(0,[z1,z14,z2,z3,z4,z5,z6]),(0,[z62,z1,z2,z3,z4,z5,z6]),(0,[z63,z64,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z65,z4,z5,z6])],[(0,[z1,z2,z3,z4,z66,z5,z6]),(0,[z67,z1,z2,z15,z3,z4,z6])],[(0,[z1,z2,z3,z68,z4,z8,z6]),(0,[z1,z69,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z70,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z41,z6]),(0,[z1,z2,z3,z4,z71,z5,z6]),(0,[z1,z2,z3,z71,z5,z42,z6]),(0,[z1,z2,z3,z4,z5,z42,z6]),(0,[z64,z1,z2,z72,z3,z4,z5]),(0,[z1,z2,z3,z10,z4,z5,z73]),(0,[z1,z2,z3,z4,z5,z6,z74])],[(0,[z1,z2,z3,z4,z5,z75,z6]),(1,[z1,z2,z3,z76,z4,z6])],[(0,[z77,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z78,z4,z5,z6]),(0,[z1,z2,z79,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z5,z54,z6]),(0,[z1,z80,z2,z3,z10,z4,z5]),(0,[z1,z2,z3,z81,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z82]),(0,[z64,z1,z2,z15,z3,z4,z5])],[(1,[z52,z2,z83,z4,z5,z6]),(0,[z1,z2,z3,z84,z4,z5,z6]),(0,[z85,z1,z2,z3,z4,z5,z86]),(1,[z85,z1,z2,z4,z5,z55]),(0,[z67,z1,z2,z3,z5,z42,z6])],[(0,[z1,z2,z3,z4,z5,z87,z6]),(1,[z1,z2,z15,z4,z41,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z88,z6]),(0,[z1,z2,z3,z10,z4,z19,z5]),(0,[z1,z2,z3,z4,z5,z89,z6]),(0,[z1,z2,z3,z4,z5,z90,z6])],[(0,[z1,z2,z3,z4,z91,z5,z6]),(0,[z92,z1,z2,z3,z4,z5,z6]),(0,[z1,z93,z2,z3,z4,z5,z6]),(0,[z64,z1,z60,z2,z3,z5,z6])],[(0,[z1,z2,z3,z94,z4,z20,z6]),(0,[z1,z2,z3,z95,z4,z5,z6]),(1,[z1,z2,z3,z4,z96,z6]),(1,[z1,z97,z3,z4,z98,z6]),(0,[z1,z2,z3,z4,z71,z5,z99])],[(1,[z46,z2,z100,z4,z5,z6]),(0,[z47,z1,z2,z3,z101,z5,z6]),(0,[z1,z2,z3,z4,z5,z102,z6]),(0,[z103,z1,z2,z3,z4,z5,z6]),(0,[z104,z1,z2,z3,z4,z5,z105]),(0,[z23,z1,z2,z4,z19,z5,z6]),(0,[z1,z2,z15,z4,z5,z41,z6])],[(0,[z1,z2,z100,z3,z10,z4,z5]),(0,[z1,z2,z3,z4,z106,z5,z6]),(0,[z1,z2,z3,z49,z4,z20,z6]),(0,[z1,z107,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z108,z4,z8,z6]),(0,[z64,z1,z2,z3,z4,z5,z86])],[(0,[z57,z1,z2,z3,z4,z5,z75]),(0,[z46,z1,z2,z3,z4,z5,z6]),(0,[z52,z1,z109,z3,z4,z5,z6]),(0,[z110,z1,z2,z3,z4,z5,z6]),(0,[z111,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z112,z4,z5,z6]),(0,[z113,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z114,z4,z5,z6]),(0,[z115,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z116,z3,z4,z5,z6]),(0,[z64,z1,z2,z3,z4,z4,z5])],[(0,[z1,z2,z3,z4,z5,z117,z6]),(0,[z1,z2,z4,z26,z5,z41,z6])]],
   [[(0,[z1,z2,z118,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z119,z5,z6]),(1,[z1,z2,z3,z4,z91,z6]),(0,[z2,z100,z3,z83,z4,z5,z6]),(0,[z120,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z121,z5,z6])],[(0,[z1,z122,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z10,z4,z5,z56]),(0,[z1,z2,z3,z4,z5,z123,z6]),(1,[z64,z1,z60,z2,z3,z5]),(0,[z1,z2,z124,z3,z4,z5,z86]),(0,[z1,z2,z3,z10,z4,z5,z55])],[(0,[z1,z125,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z126,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z127])],[(0,[z128,z1,z2,z3,z4,z8,z6]),(0,[z1,z60,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z5,z129,z6]),(0,[z1,z2,z3,z16,z10,z4,z5]),(0,[z1,z2,z3,z24,z4,z5,z130])],[(0,[z131,z1,z2,z3,z4,z5,z6]),(0,[z1,z132,z2,z3,z10,z4,z5]),(0,[z133,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z134,z5,z6]),(0,[z135,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z136,z6]),(1,[z1,z2,z3,z137,z4,z6]),(0,[z1,z2,z3,z138,z4,z5,z42]),(0,[z64,z1,z2,z3,z4,z5,z139]),(0,[z1,z2,z3,z24,z4,z140,z6])],[(0,[z141,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z142,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z143]),(1,[z58,z2,z3,z4,z8,z6]),(0,[z144,z1,z2,z3,z4,z5,z6]),(0,[z1,z145,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z146,z5,z6]),(0,[z147,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z148]),(0,[z1,z2,z3,z4,z5,z149,z6])],[(0,[z1,z150,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z151,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z152,z6]),(0,[z64,z1,z2,z3,z4,z140,z5])]],
   [[(0,[z1,z2,z3,z4,z153,z5,z6]),(0,[z1,z2,z3,z4,z8,z6,z154]),(0,[z1,z2,z3,z4,z155,z5,z6]),(0,[z1,z2,z3,z10,z4,z156,z5]),(0,[z1,z157,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z158,z4,z5,z6]),(0,[z1,z2,z3,z4,z159,z5,z6]),(0,[z1,z2,z3,z4,z5,z160,z6]),(0,[z1,z161,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z26,z42,z6]),(0,[z1,z2,z124,z3,z10,z4,z5])],[(0,[z162,z1,z2,z3,z4,z163,z6]),(0,[z1,z2,z100,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z164,z5,z6]),(0,[z1,z2,z3,z4,z5,z165,z6])],[(0,[z1,z2,z3,z4,z5,z6,z166]),(0,[z1,z2,z3,z4,z5,z6,z167]),(0,[z1,z2,z3,z4,z5,z168,z6]),(0,[z169,z1,z2,z3,z4,z5,z6])],[(0,[z170,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z171,z4,z5,z6]),(0,[z1,z2,z3,z4,z172,z5,z6]),(0,[z1,z2,z3,z173,z4,z5,z6]),(0,[z1,z2,z3,z174,z4,z5,z6]),(0,[z1,z2,z68,z4,z19,z5,z6]),(0,[z85,z1,z2,z3,z4,z5,z6]),(0,[z175,z1,z2,z3,z10,z4,z5]),(0,[z1,z2,z3,z176,z140,z5,z6])],[(0,[z1,z2,z3,z4,z5,z177,z6]),(0,[z1,z2,z3,z4,z178,z5,z6]),(0,[z1,z2,z179,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z154]),(1,[z64,z1,z2,z50,z3,z5]),(0,[z1,z2,z3,z180,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z181]),(0,[z1,z2,z3,z10,z4,z182,z6]),(1,[z1,z2,z3,z10,z5,z73])],[(0,[z64,z1,z2,z48,z3,z4,z5]),(0,[z1,z183,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z184,z4,z5,z6]),(1,[z1,z2,z3,z185,z5,z6]),(0,[z1,z2,z186,z3,z4,z5,z6]),(0,[z187,z1,z2,z3,z4,z101,z5]),(1,[z1,z2,z3,z4,z5,z188]),(1,[z64,z1,z2,z3,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z5,z189,z6]),(1,[z1,z2,z3,z4,z190,z6])],[(0,[z1,z2,z3,z4,z191,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z192]),(0,[z1,z2,z15,z3,z4,z193,z6]),(0,[z1,z2,z3,z16,z4,z5,z6])],[(0,[z1,z132,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z83,z10,z4,z5]),(0,[z1,z2,z3,z4,z20,z6,z56]),(0,[z1,z2,z3,z4,z8,z71,z6]),(0,[z1,z194,z2,z3,z4,z5,z6]),(0,[z64,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z195,z6])],[(0,[z1,z2,z3,z4,z19,z8,z6]),(0,[z1,z2,z3,z4,z5,z196,z6])],[(0,[z197,z1,z2,z3,z4,z5,z6]),(0,[z23,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z24,z4,z8,z6]),(0,[z1,z198,z2,z3,z4,z5,z6])],[(0,[z57,z1,z2,z199,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z200]),(0,[z1,z2,z201,z3,z4,z5,z6]),(0,[z1,z27,z2,z3,z4,z8,z6]),(0,[z1,z202,z2,z3,z4,z5,z6])],[(0,[z162,z1,z2,z3,z4,z5,z6]),(0,[z52,z1,z2,z3,z4,z91,z6]),(0,[z203,z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z5,z6,z204]),(0,[z1,z2,z3,z4,z5,z6,z205]),(0,[z1,z2,z3,z4,z206,z5,z6])],[(0,[z207,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z208,z5,z6]),(0,[z64,z1,z2,z3,z4,z8,z5]),(0,[z1,z2,z124,z3,z4,z5,z6]),(0,[z1,z2,z3,z209,z4,z5,z6]),(0,[z1,z2,z3,z210,z4,z5,z6])]],
   [[(0,[z57,z1,z2,z3,z211,z5,z6]),(0,[z212,z1,z2,z3,z4,z5,z6]),(0,[z47,z1,z2,z3,z4,z5,z213]),(0,[z47,z1,z2,z3,z4,z8,z6]),(0,[z214,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z215,z6]),(0,[z1,z2,z3,z4,z5,z216,z6]),(0,[z217,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z218,z6])],[(0,[z57,z1,z2,z3,z4,z8,z6]),(0,[z175,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z219]),(0,[z1,z220,z2,z3,z4,z5,z6]),(1,[z1,z14,z2,z4,z26,z6]),(0,[z1,z2,z3,z4,z5,z6,z221])],[(0,[z46,z2,z100,z3,z4,z5,z6]),(0,[z1,z3,z222,z4,z223,z5,z6])],[(0,[z1,z2,z3,z224,z4,z101,z5]),(0,[z1,z2,z225,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z226,z5,z6])],[(0,[z1,z2,z3,z4,z227,z5,z6]),(0,[z1,z2,z3,z4,z5,z215,z6]),(0,[z1,z2,z3,z4,z193,z5,z6]),(0,[z1,z228,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z229])],[(0,[z64,z1,z2,z3,z4,z5,z54]),(0,[z1,z97,z2,z3,z4,z193,z6]),(0,[z1,z14,z2,z4,z26,z5,z6])]],
   [[(0,[z1,z2,z3,z83,z4,z5,z6]),(0,[z212,z2,z3,z4,z101,z5,z6]),(0,[z230,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z231,z5,z6]),(0,[z1,z232,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z233,z4,z5,z6]),(0,[z1,z2,z3,z4,z234,z5,z6]),(1,[z1,z2,z3,z5,z235,z6])],[(0,[z1,z2,z3,z101,z19,z5,z6]),(0,[z1,z2,z236,z3,z4,z5,z6]),(0,[z9,z1,z2,z3,z222,z5,z6]),(0,[z104,z1,z27,z3,z4,z5,z6]),(1,[z1,z27,z3,z4,z5,z237]),(1,[z104,z1,z3,z4,z5,z105]),(0,[z1,z2,z3,z4,z5,z238,z6]),(0,[z1,z2,z3,z4,z5,z239,z6])],[(0,[z1,z240,z241,z3,z4,z5,z6]),(0,[z1,z2,z241,z3,z10,z4,z5]),(0,[z242,z1,z2,z3,z4,z5,z6])],[(0,[z57,z162,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z243,z5,z6]),(0,[z244,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z10,z4,z5,z245])],[(0,[z57,z1,z2,z246,z4,z5,z6]),(0,[z1,z2,z48,z3,z4,z5,z6]),(0,[z1,z2,z50,z3,z5,z73,z6]),(0,[z1,z2,z3,z4,z247,z5,z6]),(0,[z1,z248,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z249,z5,z6])],[(0,[z52,z1,z2,z3,z185,z5,z6]),(0,[z52,z64,z1,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z250,z6]),(0,[z1,z2,z3,z49,z4,z8,z6]),(0,[z1,z2,z3,z4,z5,z251,z6]),(0,[z1,z252,z2,z3,z4,z5,z6]),(0,[z1,z2,z253,z3,z4,z5,z6])],[(0,[z1,z2,z3,z254,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z255,z6]),(0,[z1,z2,z3,z4,z5,z256,z6]),(0,[z1,z2,z257,z3,z4,z5,z6])],[(0,[z258,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z10,z4,z182])]],
   [[(0,[z64,z1,z2,z3,z4,z101,z5]),(1,[z1,z2,z3,z4,z5,z259]),(0,[z64,z1,z2,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z260,z5,z6]),(1,[z1,z60,z3,z222,z5,z6]),(0,[z64,z1,z60,z2,z3,z4,z5]),(0,[z261,z1,z2,z3,z4,z5,z6])],[(0,[z64,z1,z2,z3,z222,z4,z5]),(0,[z1,z2,z3,z4,z71,z5,z181])],[(0,[z262,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z237,z86]),(0,[z1,z2,z3,z4,z5,z263,z6]),(0,[z1,z2,z50,z3,z68,z5,z6]),(0,[z1,z2,z3,z4,z5,z264,z6])],[(0,[z1,z2,z3,z265,z4,z5,z6]),(0,[z266,z1,z2,z3,z4,z5,z6]),(0,[z1,z267,z2,z3,z4,z5,z6]),(0,[z1,z268,z2,z3,z10,z4,z5]),(0,[z269,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z270]),(0,[z1,z271,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z8,z5,z20,z6]),(0,[z272,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z50,z68,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z273,z6])],[(0,[z274,z1,z2,z3,z4,z5,z6]),(0,[z275,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z15,z3,z4,z44,z6]),(0,[z1,z2,z3,z4,z26,z71,z6]),(0,[z1,z2,z3,z276,z10,z4,z5])],[(0,[z1,z132,z3,z49,z4,z5,z6]),(0,[z67,z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z5,z277,z6]),(0,[z278,z1,z2,z3,z10,z4,z5])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z279,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z280,z6]),(0,[z1,z281,z2,z3,z4,z5,z6]),(0,[z282,z1,z2,z3,z4,z5,z6]),(0,[z64,z47,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z20,z20,z6]),(0,[z274,z1,z2,z3,z4,z283,z6])]],
   [[(0,[z1,z2,z241,z3,z4,z5,z6]),(0,[z52,z1,z2,z3,z4,z5,z284]),(0,[z64,z1,z240,z2,z3,z4,z5]),(0,[z1,z285,z2,z3,z4,z5,z6])],[(0,[z64,z1,z132,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z105,z56]),(0,[z1,z2,z3,z4,z223,z5,z6]),(0,[z64,z1,z2,z124,z3,z4,z5])],[(0,[z1,z286,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z287,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z288]),(0,[z289,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z290,z6]),(0,[z1,z2,z3,z222,z291,z5,z6]),(0,[z1,z2,z3,z292,z4,z5,z6]),(0,[z64,z1,z2,z3,z4,z223,z5]),(0,[z1,z2,z3,z4,z293,z5,z6]),(0,[z294,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z295,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z296,z6])],[(0,[z1,z2,z297,z3,z4,z5,z6]),(0,[z1,z240,z2,z3,z10,z4,z5]),(0,[z1,z97,z2,z3,z4,z41,z6]),(0,[z1,z27,z2,z3,z4,z5,z105]),(0,[z1,z2,z298,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z182,z5,z6])],[(0,[z299,z1,z2,z3,z4,z5,z6]),(1,[z64,z1,z2,z3,z4,z8])],[(1,[z1,z2,z3,z4,z263,z6]),(0,[z300,z64,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z301])],[(0,[z1,z2,z3,z4,z101,z5,z6]),(0,[z1,z2,z3,z4,z8,z6,z130]),(0,[z1,z2,z3,z4,z5,z6,z302]),(0,[z1,z2,z3,z4,z5,z6,z303]),(0,[z1,z14,z2,z3,z4,z98,z6]),(0,[z1,z2,z3,z5,z136,z6,z237]),(0,[z1,z2,z3,z4,z17,z6,z86])]],
   [[(0,[z304,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z305,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z44,z6]),(0,[z1,z2,z3,z4,z5,z306,z6]),(0,[z1,z2,z3,z4,z140,z5,z6])],[(0,[z64,z162,z1,z2,z3,z4,z5]),(0,[z307,z1,z2,z3,z4,z5,z6]),(1,[z64,z1,z2,z3,z101,z5]),(1,[z1,z2,z3,z10,z4,z8]),(0,[z1,z2,z3,z4,z5,z6,z308]),(0,[z9,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z71,z98,z6]),(0,[z64,z1,z2,z3,z68,z4,z5]),(0,[z1,z2,z3,z4,z309,z5,z6]),(0,[z1,z2,z3,z310,z4,z5,z6]),(0,[z1,z2,z3,z24,z4,z42,z6]),(0,[z1,z268,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z291,z10,z4,z5]),(0,[z1,z31,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z8,z55,z6]),(0,[z274,z1,z2,z3,z4,z5,z54]),(1,[z311,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z312,z6]),(0,[z1,z2,z15,z3,z10,z4,z5]),(0,[z1,z2,z3,z10,z4,z5,z86]),(0,[z18,z1,z2,z3,z4,z5,z6]),(0,[z300,z1,z2,z3,z10,z4,z5])],[(0,[z1,z2,z313,z3,z4,z5,z6]),(0,[z1,z2,z3,z314,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z61]),(0,[z1,z2,z3,z276,z4,z5,z6]),(0,[z1,z2,z3,z315,z4,z5,z6]),(0,[z316,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z55,z6,z86]),(0,[z64,z1,z2,z3,z5,z6,z317]),(0,[z1,z2,z3,z5,z73,z6,z317])],[(1,[z1,z2,z3,z39,z5,z6]),(0,[z1,z2,z50,z3,z4,z20,z6]),(0,[z1,z25,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z5,z318,z6]),(0,[z1,z2,z3,z319,z4,z5,z6]),(0,[z320,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z10,z4,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z130])],[(0,[z23,z1,z2,z50,z4,z5,z6]),(1,[z147,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z44,z6]),(0,[z1,z2,z3,z4,z5,z6,z321])],[(1,[z1,z2,z3,z4,z322,z6]),(0,[z1,z2,z3,z4,z30,z5,z6]),(0,[z1,z2,z3,z4,z20,z323,z6]),(0,[z58,z1,z2,z3,z4,z20,z6]),(0,[z1,z14,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z324,z8,z6]),(0,[z1,z2,z3,z325,z4,z5,z6]),(0,[z128,z1,z2,z3,z4,z5,z56]),(0,[z64,z1,z2,z3,z4,z5,z98]),(1,[z1,z2,z50,z68,z5,z6]),(0,[z326,z1,z2,z3,z4,z5,z6])],[(0,[z203,z1,z2,z3,z4,z8,z6]),(0,[z203,z2,z3,z4,z5,z20,z6]),(0,[z1,z25,z97,z3,z4,z5,z6]),(0,[z1,z2,z327,z3,z4,z5,z6]),(0,[z1,z2,z3,z328,z4,z5,z6]),(0,[z1,z329,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z55,z6]),(0,[z64,z1,z2,z3,z330,z4,z5])]],
   [[(0,[z1,z331,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z52,z1,z2,z100,z4,z5,z6]),(0,[z1,z2,z3,z4,z71,z20,z6]),(0,[z1,z2,z15,z3,z16,z4,z6]),(0,[z1,z2,z15,z3,z24,z4,z6]),(0,[z85,z1,z2,z124,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z332,z6]),(0,[z333,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z55,z237]),(0,[z1,z2,z3,z4,z334,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z335])],[(0,[z1,z240,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z336,z6]),(0,[z64,z1,z2,z3,z4,z5,z317]),(0,[z1,z2,z3,z10,z10,z4,z5])],[(0,[z274,z2,z3,z4,z5,z6,z56]),(0,[z1,z2,z3,z4,z337,z5,z6]),(0,[z64,z9,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z338,z6]),(0,[z1,z2,z3,z5,z42,z73,z6])],[(0,[z1,z2,z48,z3,z4,z339,z6]),(0,[z1,z2,z3,z340,z4,z5,z6]),(0,[z1,z2,z15,z3,z4,z26,z6]),(0,[z1,z2,z3,z76,z4,z6,z86]),(0,[z1,z2,z3,z341,z4,z5,z6])],[(0,[z1,z2,z3,z4,z8,z6,z317]),(0,[z1,z2,z3,z4,z5,z342,z6]),(0,[z1,z2,z3,z343,z4,z5,z6]),(0,[z1,z2,z3,z10,z4,z140,z5])],[(0,[z57,z1,z132,z3,z4,z5,z6]),(0,[z63,z1,z2,z3,z4,z5,z6]),(0,[z1,z80,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z16,z5,z73,z6])],[(0,[z1,z2,z3,z68,z291,z5,z6]),(0,[z1,z2,z3,z4,z5,z344,z6]),(1,[z1,z2,z3,z5,z136,z6]),(0,[z1,z2,z3,z4,z345,z5,z6])]],
   [[(1,[z57,z241,z3,z4,z5,z6]),(0,[z1,z2,z3,z291,z4,z5,z6]),(0,[z1,z2,z3,z4,z20,z6,z346]),(0,[z1,z93,z2,z3,z4,z223,z6]),(0,[z1,z97,z2,z3,z10,z4,z5]),(0,[z1,z2,z15,z3,z4,z5,z6]),(0,[z64,z1,z2,z3,z4,z5,z42])],[(0,[z52,z1,z2,z3,z4,z290,z6]),(1,[z1,z2,z3,z265,z5,z6]),(0,[z9,z1,z2,z3,z223,z5,z6]),(0,[z347,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z284]),(0,[z46,z1,z2,z3,z4,z20,z6]),(0,[z64,z1,z27,z2,z3,z4,z5]),(0,[z23,z1,z2,z3,z4,z190,z6]),(1,[z1,z2,z3,z4,z5,z196]),(0,[z1,z2,z3,z4,z348,z5,z6]),(0,[z1,z2,z3,z330,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z317]),(0,[z1,z2,z3,z4,z5,z6,z349])],[(0,[z1,z2,z3,z4,z350,z5,z6]),(0,[z351,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z352,z3,z4,z5,z6]),(1,[z203,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z20,z6,z86]),(0,[z1,z2,z3,z4,z353,z5,z6])],[(0,[z64,z1,z2,z3,z83,z4,z5]),(0,[z1,z2,z3,z354,z10,z4,z5])],[(0,[z1,z2,z3,z4,z20,z105,z6]),(0,[z274,z1,z2,z3,z4,z355,z6]),(0,[z1,z2,z3,z4,z356,z5,z6]),(0,[z357,z64,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z24,z10,z4,z5])],[(0,[z212,z1,z2,z3,z4,z358,z6]),(0,[z1,z97,z2,z3,z16,z4,z6]),(0,[z1,z97,z2,z3,z24,z4,z6]),(0,[z1,z27,z2,z3,z10,z4,z5]),(0,[z1,z2,z3,z4,z5,z359,z6]),(1,[z1,z2,z3,z5,z168,z6])],[(0,[z57,z64,z1,z2,z3,z4,z5]),(0,[z360,z1,z2,z3,z4,z5,z6]),(0,[z361,z1,z2,z3,z4,z5,z6]),(0,[z1,z362,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z5,z6,z363]),(0,[z1,z2,z3,z364,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z218,z42]),(0,[z365,z1,z2,z3,z10,z4,z5])]],
   [[(0,[z1,z240,z2,z3,z4,z366,z6]),(0,[z367,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z368,z6]),(1,[z1,z25,z3,z4,z193,z6]),(0,[z1,z2,z3,z10,z4,z5,z6])],[(1,[z1,z2,z3,z4,z369,z6]),(0,[z1,z2,z3,z4,z8,z73,z6]),(0,[z1,z285,z2,z3,z4,z223,z5]),(0,[z1,z2,z3,z4,z5,z6,z370])],[(0,[z1,z2,z3,z4,z211,z5,z6]),(0,[z371,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z372,z5,z6]),(0,[z1,z2,z373,z3,z4,z5,z6]),(0,[z1,z2,z3,z10,z4,z5,z237])],[(0,[z1,z2,z3,z4,z8,z5,z6]),(0,[z128,z2,z3,z4,z5,z54,z6]),(0,[z1,z240,z2,z48,z4,z5,z6]),(0,[z104,z1,z3,z4,z5,z105,z6]),(0,[z374,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z375,z6]),(1,[z64,z1,z2,z3,z5,z317])],[(1,[z1,z2,z3,z224,z4,z5]),(0,[z64,z203,z1,z2,z3,z4,z5]),(0,[z376,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z377,z6])],[(0,[z1,z2,z3,z10,z4,z8,z5]),(0,[z1,z2,z124,z4,z5,z6,z86]),(0,[z378,z64,z1,z2,z3,z4,z5])],[(0,[z379,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z137,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z380]),(1,[z1,z2,z3,z10,z4,z5]),(0,[z1,z2,z3,z4,z5,z73,z6]),(0,[z64,z1,z2,z3,z24,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z381])],[(0,[z1,z2,z100,z3,z4,z20,z6]),(0,[z67,z1,z2,z3,z4,z8,z6]),(0,[z1,z80,z2,z48,z4,z5,z6]),(0,[z64,z9,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z382,z5,z6]),(0,[z1,z2,z3,z4,z383,z5,z6])]],
   [[(0,[z162,z1,z2,z3,z4,z384,z6]),(0,[z1,z385,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z259]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z104,z1,z2,z3,z10,z4,z5]),(0,[z1,z2,z3,z4,z5,z386,z6]),(0,[z1,z2,z3,z4,z387,z5,z6])],[(0,[z1,z2,z3,z4,z388,z5,z6]),(0,[z85,z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z389,z4,z5,z6]),(0,[z1,z2,z3,z4,z390,z5,z6]),(1,[z1,z240,z48,z4,z5,z6]),(0,[z1,z2,z3,z4,z391,z5,z6]),(1,[z1,z2,z3,z328,z4,z5]),(0,[z64,z1,z2,z50,z3,z4,z5]),(1,[z64,z1,z2,z3,z5,z42])],[(0,[z52,z1,z2,z83,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z392,z6]),(0,[z1,z2,z3,z354,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z283,z6]),(0,[z9,z1,z2,z3,z4,z393,z6]),(0,[z1,z2,z3,z394,z4,z5,z6]),(0,[z1,z395,z2,z3,z4,z5,z6])],[(0,[z128,z274,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z222,z10,z4,z5]),(0,[z396,z64,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z156,z5,z6])],[(0,[z397,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z398,z6])],[(0,[z1,z2,z399,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z400,z6]),(0,[z23,z1,z2,z3,z19,z5,z6]),(0,[z1,z2,z3,z4,z42,z44,z6]),(0,[z1,z2,z3,z24,z4,z71,z6]),(1,[z1,z2,z3,z4,z140,z44])],[(0,[z1,z2,z3,z16,z4,z20,z6]),(0,[z1,z27,z2,z3,z4,z5,z237]),(0,[z1,z2,z298,z3,z4,z5,z6]),(0,[z1,z401,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z402,z5,z6]),(0,[z1,z132,z2,z3,z4,z20,z6]),(0,[z64,z1,z2,z3,z4,z20,z6]),(0,[z1,z403,z2,z3,z4,z5,z6]),(0,[z404,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z274,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z5,z405,z6]),(0,[z406,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z407,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z408,z6]),(0,[z64,z1,z2,z3,z4,z71,z5]),(0,[z64,z1,z2,z3,z4,z409,z5]),(0,[z1,z2,z3,z4,z140,z44,z6])],[(0,[z1,z2,z3,z4,z410,z5,z6]),(0,[z1,z2,z3,z4,z5,z411,z6]),(0,[z311,z1,z2,z3,z5,z6,z237])],[(1,[z64,z1,z2,z3,z291,z5]),(1,[z1,z2,z3,z412,z5,z6]),(1,[z1,z80,z49,z4,z5,z6]),(0,[z1,z80,z3,z49,z4,z5,z6]),(0,[z1,z2,z413,z3,z4,z5,z6]),(0,[z64,z1,z2,z3,z4,z5,z44])],[(0,[z1,z2,z3,z4,z5,z414,z6]),(0,[z162,z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z5,z415,z6]),(0,[z1,z2,z3,z4,z20,z6,z237]),(0,[z1,z416,z2,z3,z4,z5,z6]),(0,[z1,z60,z3,z222,z4,z5,z6]),(0,[z1,z417,z2,z3,z4,z5,z6]),(0,[z418,z64,z1,z2,z3,z4,z5])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z419,z5,z6]),(0,[z1,z2,z3,z4,z208,z20,z6]),(0,[z1,z2,z124,z3,z4,z20,z6]),(0,[z420,z1,z2,z3,z4,z5,z6]),(0,[z421,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z182,z6])],[(0,[z212,z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z50,z3,z4,z8,z6]),(0,[z1,z25,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z422,z5,z6]),(0,[z1,z2,z3,z4,z423,z5,z6])],[(0,[z424,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z10,z4,z101,z5]),(0,[z1,z2,z425,z3,z4,z5,z6]),(0,[z47,z1,z2,z3,z4,z5,z259]),(0,[z1,z426,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z10,z4,z5,z20]),(0,[z1,z2,z3,z4,z5,z366,z6]),(0,[z104,z1,z2,z3,z4,z5,z6]),(0,[z311,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z427,z6]),(0,[z58,z1,z2,z3,z4,z8,z6]),(0,[z1,z14,z2,z3,z4,z8,z6]),(0,[z1,z428,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z429])]],
   [[(0,[z1,z2,z3,z430,z4,z5,z6]),(0,[z431,z1,z2,z3,z4,z5,z6]),(0,[z104,z1,z2,z3,z4,z5,z237]),(0,[z1,z2,z3,z10,z4,z245,z6])],[(0,[z1,z432,z2,z3,z4,z5,z6]),(1,[z128,z2,z3,z4,z5,z54]),(0,[z1,z2,z3,z4,z433,z5,z6]),(0,[z434,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z222,z4,z5,z6])],[(0,[z1,z2,z3,z435,z4,z5,z6]),(0,[z1,z2,z436,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z227,z20,z6]),(0,[z1,z2,z3,z4,z193,z20,z6]),(0,[z64,z1,z2,z3,z4,z193,z5]),(0,[z1,z2,z3,z4,z5,z105,z86]),(0,[z64,z1,z2,z3,z16,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z437])],[(0,[z52,z2,z3,z83,z4,z5,z6]),(0,[z1,z2,z3,z438,z4,z5,z6]),(0,[z64,z1,z2,z3,z101,z5,z6]),(0,[z1,z2,z3,z4,z20,z98,z6]),(0,[z1,z2,z3,z4,z5,z6,z439]),(0,[z440,z1,z2,z3,z4,z5,z6]),(0,[z1,z441,z2,z3,z4,z5,z6]),(0,[z442,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z443])],[(0,[z57,z1,z2,z3,z4,z5,z270]),(0,[z1,z444,z2,z3,z4,z5,z6]),(0,[z52,z1,z2,z3,z10,z4,z5]),(0,[z47,z1,z2,z3,z291,z5,z6]),(0,[z9,z1,z2,z3,z4,z8,z6]),(0,[z1,z445,z2,z3,z4,z5,z6]),(0,[z1,z2,z446,z3,z4,z5,z6])],[(0,[z1,z447,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z83,z4,z20,z6]),(0,[z1,z2,z3,z4,z369,z5,z6]),(0,[z1,z2,z3,z4,z448,z5,z6]),(0,[z64,z1,z2,z50,z3,z5,z6])],[(0,[z449,z1,z2,z3,z4,z5,z6]),(0,[z9,z1,z2,z3,z5,z73,z6]),(0,[z1,z450,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z451,z5,z6]),(0,[z1,z2,z3,z4,z26,z5,z6])],[(1,[z1,z2,z3,z4,z414,z6]),(0,[z1,z2,z3,z4,z5,z452,z6]),(0,[z64,z128,z1,z2,z3,z4,z5]),(0,[z64,z1,z25,z2,z3,z4,z5]),(0,[z1,z2,z3,z68,z10,z4,z5])]],
   [[(0,[z244,z1,z2,z3,z4,z20,z6]),(0,[z23,z1,z2,z3,z4,z263,z6])],[(0,[z453,z1,z2,z3,z4,z5,z6]),(0,[z212,z1,z2,z3,z101,z5,z6]),(0,[z1,z2,z48,z3,z4,z20,z6]),(0,[z1,z2,z3,z10,z4,z223,z5]),(0,[z1,z2,z3,z4,z454,z5,z6])],[(0,[z1,z2,z7,z3,z4,z5,z6]),(0,[z128,z1,z2,z3,z265,z5,z6]),(1,[z1,z2,z3,z4,z366,z6])],[(0,[z46,z1,z2,z3,z4,z8,z6]),(0,[z1,z455,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z456,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z56,z86]),(0,[z457,z1,z2,z3,z4,z5,z6])],[(0,[z64,z104,z1,z2,z3,z4,z5]),(0,[z64,z1,z14,z2,z3,z4,z5]),(0,[z1,z458,z2,z3,z4,z5,z6]),(0,[z459,z1,z2,z3,z4,z5,z6]),(0,[z1,z460,z2,z3,z4,z5,z6])],[(0,[z1,z60,z2,z3,z222,z5,z6]),(0,[z1,z2,z3,z4,z5,z461,z6]),(0,[z1,z462,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z463,z5,z6])],[(1,[z187,z1,z2,z3,z4,z5]),(0,[z1,z464,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z465,z4,z5,z6]),(0,[z1,z466,z2,z3,z4,z5,z6])],[(0,[z467,z1,z2,z3,z4,z5,z6]),(0,[z64,z1,z2,z3,z4,z19,z5]),(0,[z64,z1,z2,z3,z4,z5,z130])]],
   [[(0,[z1,z25,z2,z3,z4,z98,z6])],[(0,[z1,z2,z100,z49,z4,z5,z6]),(0,[z1,z80,z2,z3,z4,z8,z6]),(0,[z1,z468,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z393,z6]),(0,[z1,z25,z3,z4,z193,z5,z6]),(0,[z1,z469,z2,z3,z4,z5,z6])],[(0,[z52,z1,z2,z3,z4,z5,z6]),(0,[z274,z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z134,z8,z6]),(0,[z470,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z471]),(0,[z64,z1,z2,z472,z3,z4,z5]),(0,[z1,z2,z3,z4,z473,z5,z6])],[(0,[z1,z2,z3,z474,z4,z5,z6]),(1,[z1,z2,z3,z4,z452,z6]),(0,[z1,z2,z3,z4,z8,z105,z6]),(0,[z1,z80,z2,z3,z4,z5,z189]),(0,[z1,z475,z2,z3,z4,z5,z6])],[(0,[z57,z1,z2,z3,z39,z5,z6]),(0,[z1,z2,z3,z4,z5,z213,z6]),(0,[z1,z1,z2,z3,z4,z20,z6]),(0,[z476,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z477,z5,z6]),(0,[z1,z2,z3,z10,z4,z5,z98]),(0,[z67,z1,z2,z3,z16,z5,z6]),(0,[z67,z1,z2,z3,z4,z42,z6])],[(0,[z1,z2,z241,z3,z4,z20,z6]),(0,[z1,z2,z3,z291,z5,z73,z6]),(0,[z1,z2,z3,z4,z20,z41,z6]),(0,[z1,z2,z3,z4,z20,z42,z6]),(0,[z1,z2,z3,z4,z5,z478,z6]),(0,[z1,z2,z3,z4,z5,z479,z6]),(0,[z1,z2,z3,z68,z4,z5,z6]),(0,[z480,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z44,z6,z130])],[(0,[z481,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z223,z20,z6]),(0,[z1,z2,z3,z4,z153,z8,z6]),(0,[z1,z97,z2,z3,z4,z44,z6]),(0,[z1,z2,z3,z4,z5,z99,z6])],[(0,[z482,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z20,z54,z6]),(0,[z128,z1,z2,z3,z10,z4,z5]),(0,[z1,z60,z2,z3,z10,z4,z5]),(0,[z1,z2,z483,z3,z4,z5,z6]),(0,[z278,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z100,z3,z4,z8,z6]),(0,[z64,z1,z2,z100,z3,z4,z5]),(0,[z1,z484,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z105,z6]),(0,[z1,z2,z3,z4,z5,z6,z485]),(0,[z1,z2,z3,z486,z4,z5,z6]),(0,[z1,z2,z3,z140,z5,z235,z6])],[(0,[z1,z2,z3,z4,z5,z487,z6]),(0,[z1,z488,z2,z3,z4,z5,z6]),(0,[z1,z2,z489,z3,z4,z5,z6]),(0,[z64,z1,z2,z3,z49,z4,z5]),(0,[z1,z2,z3,z490,z4,z5,z6]),(0,[z1,z2,z3,z4,z491,z5,z6]),(0,[z492,z1,z2,z3,z4,z5,z6])],[(0,[z85,z1,z2,z3,z4,z8,z6]),(0,[z1,z493,z2,z3,z4,z5,z6]),(0,[z1,z240,z2,z3,z4,z337,z6]),(0,[z494,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z188]),(0,[z1,z2,z3,z24,z4,z6,z130]),(0,[z1,z2,z495,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z8,z6,z56]),(0,[z496,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z497,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z498]),(1,[z1,z2,z3,z176,z5,z6])],[(0,[z57,z1,z241,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z101,z20,z6]),(1,[z1,z2,z3,z4,z355,z6]),(0,[z1,z2,z499,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z140,z20,z6]),(1,[z1,z2,z3,z4,z393,z6]),(0,[z1,z2,z3,z4,z5,z500,z6]),(0,[z1,z2,z3,z10,z5,z73,z6])],[(0,[z1,z501,z2,z3,z4,z5,z6]),(0,[z502,z1,z2,z3,z4,z5,z6]),(0,[z9,z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z108,z4,z5,z6]),(0,[z1,z2,z3,z10,z4,z5,z42])],[(0,[z503,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z16,z4,z8,z6]),(0,[z1,z2,z3,z4,z355,z5,z6]),(0,[z1,z2,z504,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z505,z5,z6])]],
   [[(0,[z1,z132,z2,z3,z4,z8,z6]),(0,[z64,z1,z2,z3,z4,z8,z6]),(0,[z64,z274,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z56]),(0,[z1,z2,z3,z4,z506,z5,z6])],[(0,[z1,z2,z3,z4,z185,z5,z6]),(0,[z1,z2,z3,z4,z507,z5,z6])],[(0,[z508,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z509,z5,z6]),(0,[z1,z2,z3,z510,z4,z5,z6]),(0,[z1,z25,z2,z3,z4,z41,z6]),(0,[z1,z2,z511,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z512,z5,z6])],[(0,[z300,z1,z2,z3,z4,z5,z6]),(0,[z64,z46,z1,z2,z3,z4,z5]),(0,[z58,z203,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z56,z237]),(0,[z128,z1,z2,z3,z412,z5,z6]),(0,[z513,z1,z2,z3,z4,z5,z6])],[(0,[z162,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z514,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z515,z6]),(1,[z1,z2,z3,z4,z121,z6]),(0,[z1,z14,z2,z3,z4,z41,z6]),(0,[z1,z2,z516,z3,z10,z4,z5])],[(0,[z1,z2,z199,z3,z4,z5,z6]),(0,[z517,z1,z2,z3,z4,z5,z6]),(0,[z212,z47,z2,z3,z4,z5,z6]),(0,[z1,z2,z124,z3,z4,z8,z6]),(0,[z128,z1,z2,z3,z4,z5,z6]),(0,[z1,z80,z2,z3,z4,z5,z229]),(0,[z1,z60,z2,z3,z4,z5,z6]),(1,[z1,z2,z407,z3,z4,z5]),(0,[z1,z2,z3,z4,z41,z42,z6])],[(0,[z52,z46,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z358,z6]),(0,[z212,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z518,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z71,z41,z6]),(0,[z64,z1,z2,z3,z4,z5,z41]),(1,[z64,z1,z2,z3,z10,z5])],[(0,[z47,z1,z2,z3,z4,z369,z6]),(0,[z1,z240,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z519,z5,z6]),(0,[z1,z2,z3,z4,z5,z55,z54]),(0,[z1,z2,z520,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z521,z6]),(0,[z64,z1,z522,z2,z3,z4,z5])]],
   [[(0,[z1,z2,z523,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z524,z6]),(0,[z525,z1,z2,z3,z4,z5,z6]),(0,[z23,z1,z2,z3,z10,z4,z5])],[(0,[z1,z2,z3,z526,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z527,z6]),(0,[z1,z2,z3,z4,z5,z528,z6])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z529,z6]),(0,[z530,z1,z2,z3,z4,z5,z6]),(0,[z1,z80,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z193,z8,z6]),(0,[z1,z2,z3,z4,z531,z5,z6])],[(0,[z47,z1,z2,z3,z10,z4,z5]),(0,[z1,z2,z3,z4,z20,z165,z6]),(0,[z1,z2,z3,z4,z532,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z533])],[(0,[z132,z2,z241,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z534,z6]),(0,[z1,z2,z3,z291,z4,z20,z6]),(0,[z1,z2,z15,z3,z4,z20,z6]),(0,[z1,z97,z2,z3,z4,z26,z6]),(0,[z1,z535,z2,z3,z4,z5,z6]),(0,[z1,z2,z72,z3,z4,z5,z6])],[(0,[z57,z1,z2,z3,z10,z4,z5]),(0,[z1,z2,z3,z83,z4,z8,z6]),(0,[z170,z1,z2,z3,z4,z5,z6]),(1,[z64,z1,z2,z3,z4,z20]),(0,[z1,z2,z3,z4,z5,z6,z536]),(0,[z1,z2,z3,z4,z5,z537,z6])],[(0,[z1,z2,z3,z101,z5,z73,z6]),(0,[z1,z2,z48,z3,z4,z532,z6]),(0,[z1,z2,z3,z4,z538,z5,z6])]],
   [[(0,[z1,z539,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z540,z5,z6]),(0,[z541,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z139,z6])],[(0,[z1,z2,z3,z4,z8,z98,z6]),(0,[z1,z97,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z542]),(0,[z1,z2,z3,z4,z5,z543,z6]),(0,[z64,z1,z2,z3,z16,z4,z5])],[(0,[z64,z1,z2,z241,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z384,z6]),(0,[z1,z2,z3,z4,z163,z5,z6]),(1,[z1,z2,z3,z4,z358,z6]),(0,[z1,z2,z48,z3,z4,z8,z6]),(0,[z64,z23,z1,z2,z3,z5,z6]),(0,[z1,z2,z50,z3,z4,z5,z188]),(0,[z1,z2,z3,z4,z5,z544,z6]),(0,[z1,z2,z3,z4,z545,z5,z6]),(1,[z1,z2,z3,z4,z5,z181]),(1,[z1,z2,z3,z10,z4,z245]),(0,[z1,z2,z516,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z235,z6])],[(1,[z1,z2,z3,z4,z163,z6]),(0,[z1,z2,z3,z291,z223,z5,z6]),(0,[z64,z85,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z546,z6])],[(0,[z1,z2,z3,z547,z4,z5,z6]),(0,[z58,z64,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z54,z86]),(0,[z548,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z549,z3,z4,z5,z6]),(0,[z64,z1,z97,z2,z3,z4,z5])],[(0,[z1,z2,z3,z10,z4,z20,z6]),(0,[z1,z2,z3,z550,z4,z5,z6]),(0,[z1,z551,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z19,z5,z6]),(0,[z64,z1,z2,z3,z4,z26,z5])],[(1,[z64,z9,z1,z2,z3,z5]),(0,[z1,z2,z3,z4,z172,z223,z6]),(0,[z1,z2,z3,z4,z552,z5,z6]),(0,[z1,z2,z3,z4,z5,z98,z6]),(0,[z23,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z10,z4,z71,z5]),(0,[z1,z2,z3,z24,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z270]),(0,[z553,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z372,z20,z6]),(0,[z1,z27,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z554,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z555,z4,z5,z6]),(0,[z1,z2,z3,z556,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z20,z6]),(0,[z58,z1,z2,z3,z10,z4,z5]),(0,[z1,z2,z3,z10,z4,z5,z54]),(0,[z1,z2,z557,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z558,z5,z6]),(0,[z67,z1,z2,z3,z4,z71,z6]),(0,[z365,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z10,z4,z5,z44])],[(0,[z1,z2,z559,z3,z4,z5,z6]),(0,[z212,z1,z2,z3,z4,z30,z6]),(0,[z560,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z49,z10,z4,z5])],[(0,[z47,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z561,z3,z4,z5,z6]),(0,[z357,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z562,z3,z4,z5,z6]),(0,[z1,z27,z3,z4,z5,z6,z237])],[(1,[z1,z2,z3,z4,z191,z6]),(0,[z563,z1,z2,z3,z4,z5,z6]),(0,[z1,z564,z2,z3,z4,z5,z6])],[(0,[z57,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z565,z6]),(1,[z1,z2,z3,z4,z337,z6]),(0,[z1,z2,z3,z497,z4,z223,z5]),(0,[z1,z97,z3,z4,z5,z98,z6]),(0,[z1,z25,z2,z3,z24,z4,z6]),(1,[z1,z2,z3,z138,z4,z5])],[(0,[z57,z2,z241,z3,z4,z5,z6]),(0,[z1,z385,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z5,z20,z6]),(0,[z1,z1,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z172,z6]),(0,[z1,z2,z3,z4,z566,z5,z6])],[(0,[z1,z2,z241,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z384,z6]),(0,[z1,z567,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z190,z5,z6]),(0,[z1,z14,z2,z3,z24,z4,z6]),(0,[z147,z1,z2,z3,z5,z6,z86])],[(0,[z1,z2,z48,z100,z4,z5,z6]),(0,[z1,z2,z3,z4,z223,z8,z6]),(0,[z1,z2,z568,z3,z4,z5,z6]),(0,[z64,z1,z2,z3,z4,z5,z105])]],
   [[(0,[z569,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z79,z3,z4,z5,z6]),(0,[z1,z2,z3,z10,z4,z193,z5]),(0,[z1,z2,z3,z4,z5,z6,z570]),(0,[z1,z2,z3,z571,z10,z4,z5])],[(1,[z1,z2,z3,z4,z283,z6]),(0,[z1,z2,z3,z4,z5,z572,z6])],[(0,[z573,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z574,z4,z5,z6]),(0,[z1,z575,z2,z3,z4,z5,z6]),(0,[z378,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z576,z5,z6])],[(0,[z1,z241,z3,z49,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z229]),(0,[z1,z2,z3,z577,z4,z5,z6]),(0,[z578,z1,z2,z3,z4,z5,z6]),(0,[z1,z579,z2,z3,z4,z5,z6])],[(0,[z2,z3,z291,z4,z101,z5,z6]),(0,[z1,z2,z3,z580,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z581]),(0,[z1,z2,z3,z16,z4,z42,z6])],[(0,[z1,z2,z3,z4,z101,z8,z6]),(0,[z1,z582,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z94,z4,z5,z6]),(0,[z1,z2,z3,z4,z20,z583,z6])],[(0,[z1,z2,z3,z4,z410,z20,z6]),(0,[z1,z2,z3,z4,z140,z8,z6]),(1,[z9,z1,z3,z223,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z584]),(0,[z1,z2,z50,z3,z19,z5,z6]),(1,[z1,z2,z3,z4,z5,z99])],[(0,[z57,z1,z2,z3,z4,z414,z6]),(0,[z585,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z405,z6]),(0,[z1,z2,z3,z49,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z586,z6]),(0,[z67,z1,z25,z2,z3,z4,z6]),(0,[z1,z2,z3,z10,z4,z387,z5])]],
   [[(0,[z396,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z587,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z588,z5,z6])],[(1,[z1,z589,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z20,z6]),(0,[z1,z240,z2,z49,z4,z5,z6])],[(0,[z1,z2,z3,z4,z322,z5,z6]),(0,[z1,z2,z3,z176,z4,z5,z6])],[(0,[z162,z1,z241,z3,z4,z5,z6]),(0,[z104,z1,z2,z3,z4,z20,z6]),(1,[z1,z2,z3,z4,z5,z368]),(0,[z1,z2,z3,z4,z5,z245,z6]),(0,[z1,z2,z590,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z323,z6]),(0,[z1,z2,z591,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z54,z237]),(1,[z1,z2,z298,z3,z4,z6]),(0,[z67,z1,z14,z2,z3,z4,z6])],[(0,[z1,z2,z3,z101,z223,z5,z6]),(0,[z1,z80,z2,z49,z4,z5,z6]),(0,[z592,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z168,z6,z86]),(0,[z64,z1,z2,z3,z4,z5,z73]),(0,[z1,z2,z3,z10,z4,z5,z130])],[(0,[z162,z132,z2,z3,z4,z5,z6]),(0,[z187,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z222,z4,z20,z6]),(0,[z1,z432,z2,z3,z4,z20,z6]),(0,[z1,z2,z593,z3,z4,z5,z6]),(0,[z1,z2,z3,z571,z4,z5,z6]),(0,[z1,z594,z2,z3,z4,z5,z6])],[(0,[z1,z2,z83,z49,z4,z5,z6]),(0,[z64,z1,z595,z2,z3,z4,z5])]],
   [[(0,[z162,z1,z132,z3,z4,z5,z6]),(0,[z1,z240,z2,z3,z4,z8,z6]),(0,[z418,z1,z2,z3,z4,z5,z6]),(0,[z1,z25,z2,z3,z4,z193,z6]),(0,[z1,z2,z3,z4,z193,z42,z6])],[(0,[z47,z1,z2,z3,z4,z452,z6]),(0,[z1,z2,z596,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z597,z6]),(0,[z1,z14,z2,z3,z4,z193,z6]),(0,[z1,z2,z3,z4,z5,z598,z6])],[(0,[z47,z2,z3,z291,z4,z5,z6]),(0,[z203,z1,z2,z3,z10,z4,z5]),(0,[z1,z2,z3,z4,z26,z20,z6]),(0,[z1,z599,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z600,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z339,z6]),(1,[z1,z93,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z601,z6,z237]),(0,[z1,z2,z3,z4,z602,z5,z6]),(0,[z85,z1,z2,z3,z10,z4,z5])],[(0,[z1,z2,z3,z4,z5,z6,z603]),(0,[z1,z2,z3,z4,z8,z6,z86]),(0,[z1,z3,z4,z5,z105,z6,z237]),(0,[z1,z2,z3,z4,z604,z5,z6]),(0,[z605,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z606]),(0,[z1,z2,z3,z4,z607,z5,z6])],[(1,[z1,z2,z3,z4,z5,z75]),(0,[z1,z2,z3,z4,z5,z608,z6]),(0,[z1,z2,z3,z609,z4,z5,z6]),(0,[z610,z1,z2,z3,z4,z5,z6]),(0,[z85,z1,z2,z3,z4,z5,z55]),(0,[z64,z64,z1,z2,z3,z4,z5]),(0,[z1,z2,z611,z3,z4,z5,z6])],[(0,[z46,z1,z2,z3,z4,z250,z6]),(0,[z1,z2,z3,z291,z4,z8,z6]),(0,[z1,z2,z3,z4,z5,z6,z346]),(0,[z300,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z15,z3,z4,z8,z6]),(1,[z1,z2,z3,z16,z71,z6])],[(0,[z612,z1,z2,z3,z4,z5,z6]),(0,[z197,z64,z1,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z245,z6])]],
   [[(0,[z1,z2,z3,z246,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z613]),(0,[z1,z2,z3,z456,z4,z20,z6]),(0,[z1,z2,z3,z4,z5,z6,z614]),(0,[z1,z615,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z616,z4,z5,z6]),(0,[z1,z2,z3,z4,z617,z5,z6]),(0,[z1,z2,z3,z10,z4,z576,z5])],[(0,[z1,z2,z48,z83,z4,z5,z6]),(0,[z1,z2,z3,z618,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z601,z6]),(0,[z1,z2,z3,z4,z5,z6,z86]),(0,[z64,z1,z2,z3,z10,z4,z5]),(0,[z619,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z24,z4,z130]),(0,[z620,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z621]),(0,[z1,z2,z3,z4,z5,z622,z6]),(0,[z1,z2,z3,z222,z101,z5,z6]),(0,[z1,z2,z3,z305,z4,z5,z6]),(0,[z1,z60,z2,z3,z5,z73,z6])],[(0,[z1,z2,z3,z623,z4,z5,z6]),(0,[z46,z1,z2,z100,z4,z5,z6]),(0,[z1,z2,z3,z224,z4,z5,z6]),(0,[z64,z1,z2,z3,z4,z5,z56]),(0,[z1,z2,z3,z4,z5,z624,z6]),(1,[z1,z2,z3,z497,z4,z5]),(0,[z64,z1,z2,z3,z4,z5,z55]),(0,[z1,z2,z3,z10,z4,z5,z317])],[(0,[z1,z2,z3,z4,z5,z6,z625]),(0,[z1,z2,z3,z291,z19,z5,z6]),(0,[z1,z2,z3,z4,z626,z5,z6])],[(0,[z162,z1,z2,z3,z10,z4,z5]),(0,[z1,z2,z3,z4,z20,z88,z6]),(0,[z627,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z407,z3,z4,z19,z5]),(1,[z1,z2,z124,z4,z5,z86])],[(1,[z1,z2,z3,z4,z5,z280]),(0,[z1,z2,z3,z4,z20,z6,z130]),(0,[z1,z2,z3,z10,z4,z8,z6])],[(0,[z52,z1,z589,z3,z4,z5,z6]),(0,[z52,z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z628,z4,z5,z6]),(0,[z212,z1,z2,z3,z10,z4,z5]),(0,[z1,z2,z3,z4,z20,z44,z6]),(1,[z1,z2,z3,z4,z339,z6]),(0,[z1,z2,z3,z4,z5,z629,z6])]],
   [[(1,[z162,z132,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z324,z5,z6]),(0,[z64,z212,z1,z2,z3,z4,z5]),(0,[z64,z1,z2,z3,z291,z4,z5]),(0,[z1,z2,z3,z4,z8,z630,z6]),(1,[z1,z2,z3,z4,z5,z61]),(0,[z1,z2,z124,z3,z4,z5,z55]),(0,[z85,z1,z2,z4,z5,z55,z6]),(0,[z64,z67,z1,z2,z3,z4,z5])],[(0,[z631,z1,z2,z3,z4,z5,z6]),(0,[z203,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z632,z5,z6]),(0,[z1,z2,z3,z4,z20,z55,z6]),(0,[z1,z2,z3,z4,z8,z8,z6]),(0,[z633,z1,z2,z3,z4,z5,z6]),(0,[z64,z23,z1,z2,z3,z4,z5]),(1,[z67,z1,z2,z3,z42,z6])],[(0,[z1,z2,z3,z68,z4,z20,z6]),(0,[z1,z2,z3,z4,z5,z6,z634]),(1,[z1,z2,z3,z4,z5,z218]),(0,[z1,z2,z472,z3,z4,z5,z6]),(0,[z1,z2,z3,z635,z4,z5,z6])],[(1,[z212,z2,z3,z101,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z636]),(0,[z1,z539,z2,z3,z4,z8,z6]),(1,[z64,z23,z1,z2,z3,z5]),(0,[z1,z595,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z140,z5,z44])],[(0,[z1,z97,z2,z3,z4,z8,z6]),(0,[z2,z3,z4,z5,z54,z6,z56]),(0,[z1,z637,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z10,z4,z5,z41]),(0,[z1,z638,z2,z3,z4,z5,z6])],[(0,[z639,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z640,z5,z6]),(0,[z1,z2,z3,z4,z5,z630,z6]),(1,[z1,z2,z3,z4,z601,z6]),(0,[z1,z2,z641,z3,z4,z5,z6])],[(0,[z1,z589,z2,z3,z4,z5,z6]),(0,[z642,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z138,z4,z5,z6]),(1,[z64,z1,z2,z3,z16,z5])],[(1,[z1,z2,z3,z114,z5,z6]),(0,[z1,z643,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z644,z5,z6]),(0,[z1,z645,z2,z3,z4,z5,z6]),(0,[z9,z1,z2,z3,z4,z96,z6]),(0,[z1,z2,z3,z4,z5,z646,z6]),(0,[z647,z1,z2,z3,z4,z5,z6]),(0,[z1,z648,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z649,z4,z5,z6]),(0,[z650,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z651,z6]),(0,[z1,z2,z3,z4,z5,z105,z54]),(0,[z1,z2,z3,z652,z4,z5,z6]),(0,[z1,z2,z3,z16,z4,z71,z6])],[(0,[z653,z1,z2,z3,z4,z5,z6]),(0,[z1,z654,z2,z3,z4,z5,z6]),(0,[z1,z2,z15,z3,z4,z98,z6]),(0,[z655,z1,z2,z3,z4,z5,z6]),(0,[z64,z1,z2,z3,z4,z5,z237]),(0,[z656,z1,z2,z3,z10,z4,z5])],[(0,[z58,z2,z3,z4,z8,z5,z6]),(0,[z9,z1,z60,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z657,z6]),(0,[z1,z2,z3,z4,z5,z658,z6]),(0,[z659,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z660,z4,z5,z6])],[(0,[z1,z2,z109,z3,z4,z5,z6]),(0,[z1,z240,z48,z3,z4,z5,z6]),(0,[z1,z2,z48,z3,z10,z4,z5]),(1,[z1,z285,z2,z3,z4,z5]),(0,[z23,z1,z2,z3,z5,z73,z6]),(0,[z67,z1,z2,z3,z10,z4,z5]),(0,[z261,z64,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z661,z10,z4,z5])],[(0,[z1,z662,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z663,z4,z5,z6]),(0,[z1,z2,z3,z4,z20,z6,z317]),(0,[z1,z2,z3,z4,z8,z6,z237]),(0,[z1,z25,z2,z3,z4,z44,z6]),(0,[z1,z2,z3,z4,z5,z55,z105]),(0,[z1,z2,z3,z4,z409,z5,z6])],[(1,[z1,z2,z199,z4,z5,z6]),(1,[z2,z3,z4,z8,z20,z6]),(0,[z1,z2,z3,z4,z402,z8,z6]),(0,[z1,z2,z3,z4,z5,z651,z6]),(0,[z1,z2,z664,z3,z4,z5,z6]),(0,[z1,z665,z2,z3,z4,z5,z6]),(0,[z1,z2,z666,z3,z4,z5,z6]),(0,[z1,z2,z667,z3,z4,z5,z6]),(0,[z1,z2,z50,z3,z4,z5,z196]),(0,[z64,z1,z2,z3,z10,z5,z6]),(0,[z1,z2,z668,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z250,z6]),(0,[z669,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z68,z101,z5,z6]),(0,[z1,z670,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z121,z19,z6]),(0,[z1,z14,z2,z3,z4,z44,z6]),(0,[z64,z459,z1,z2,z3,z4,z5])],[(0,[z671,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z672,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z284]),(0,[z1,z673,z2,z3,z4,z5,z6]),(0,[z46,z1,z2,z3,z4,z322,z6]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z1,z2,z3,z674,z4,z5,z6]),(1,[z1,z2,z3,z4,z532,z6]),(0,[z9,z1,z3,z4,z223,z5,z6]),(0,[z1,z2,z3,z137,z4,z6,z237]),(0,[z675,z1,z2,z3,z4,z5,z6]),(0,[z1,z676,z2,z3,z4,z5,z6])]],
   [[(1,[z1,z2,z3,z211,z5,z6]),(0,[z300,z1,z2,z3,z4,z20,z6]),(0,[z128,z1,z2,z3,z4,z405,z6]),(0,[z677,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z678]),(0,[z1,z2,z3,z4,z71,z44,z6])],[(0,[z679,z1,z2,z3,z4,z5,z6]),(0,[z1,z362,z2,z3,z4,z5,z6]),(0,[z680,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z237]),(0,[z23,z1,z2,z3,z68,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z681])],[(1,[z1,z2,z3,z4,z5,z213]),(1,[z1,z2,z3,z4,z8,z6]),(0,[z128,z1,z2,z3,z4,z20,z6]),(0,[z1,z60,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z682,z4,z5,z6]),(0,[z1,z3,z4,z193,z5,z98,z6]),(0,[z1,z2,z3,z4,z5,z683,z6])],[(0,[z1,z2,z3,z4,z8,z684,z6]),(0,[z64,z1,z80,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z685]),(0,[z1,z2,z3,z10,z4,z26,z5]),(0,[z1,z2,z3,z76,z4,z5,z6])],[(0,[z52,z1,z2,z3,z4,z5,z280]),(0,[z64,z1,z2,z3,z291,z5,z6]),(0,[z104,z1,z2,z3,z4,z8,z6]),(0,[z274,z1,z2,z3,z10,z4,z5]),(0,[z1,z2,z3,z4,z412,z5,z6]),(1,[z1,z2,z3,z4,z5,z189]),(0,[z1,z60,z2,z3,z4,z5,z368]),(0,[z67,z1,z97,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z193,z71,z6]),(0,[z1,z2,z3,z4,z5,z686,z6]),(0,[z1,z2,z3,z4,z5,z687,z6]),(0,[z1,z2,z3,z688,z4,z5,z6])],[(0,[z46,z1,z2,z83,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z689,z6]),(1,[z1,z2,z3,z10,z4,z20]),(0,[z128,z1,z2,z3,z4,z5,z54]),(0,[z1,z2,z3,z4,z96,z5,z6]),(0,[z1,z2,z3,z4,z690,z5,z6]),(0,[z1,z2,z3,z4,z5,z17,z6]),(0,[z289,z64,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z274,z1,z2,z3,z4,z5,z56])],[(0,[z1,z2,z3,z222,z4,z8,z6]),(0,[z656,z1,z2,z3,z4,z5,z6]),(0,[z1,z97,z2,z3,z4,z98,z6]),(0,[z1,z2,z3,z10,z4,z182,z5])]],
   [[(0,[z1,z2,z3,z4,z5,z583,z6]),(0,[z1,z2,z3,z4,z20,z73,z6]),(0,[z1,z2,z691,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z684,z6]),(0,[z1,z60,z2,z3,z223,z5,z6]),(0,[z1,z2,z3,z4,z98,z42,z6]),(0,[z1,z2,z3,z4,z5,z692,z6]),(0,[z1,z2,z3,z4,z140,z5,z130])],[(0,[z1,z2,z3,z4,z597,z5,z6]),(0,[z693,z1,z2,z3,z4,z5,z6]),(0,[z1,z25,z2,z3,z10,z4,z5]),(0,[z1,z2,z50,z3,z10,z4,z5]),(0,[z67,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z661,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z694,z6])],[(0,[z1,z695,z2,z3,z4,z5,z6]),(0,[z212,z1,z2,z3,z291,z5,z6]),(0,[z1,z444,z2,z3,z4,z8,z6]),(0,[z1,z2,z696,z3,z4,z5,z6]),(0,[z1,z2,z3,z697,z4,z5,z6])],[(0,[z57,z1,z2,z3,z4,z191,z6]),(0,[z698,z1,z2,z3,z4,z5,z6]),(1,[z274,z2,z3,z4,z5,z56]),(0,[z128,z1,z2,z3,z4,z597,z6]),(0,[z699,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z15,z3,z4,z41,z6]),(0,[z1,z14,z2,z3,z10,z4,z5]),(0,[z1,z2,z3,z16,z71,z5,z6]),(0,[z1,z2,z3,z700,z4,z5,z6])],[(1,[z1,z2,z246,z4,z5,z6]),(0,[z1,z240,z132,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z290,z6]),(0,[z1,z2,z701,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z26,z8,z6]),(0,[z702,z1,z2,z3,z4,z5,z6]),(0,[z64,z1,z2,z3,z5,z42,z6])],[(0,[z52,z1,z2,z3,z114,z5,z6]),(0,[z1,z2,z3,z4,z703,z5,z6]),(0,[z1,z2,z3,z10,z4,z5,z105])],[(0,[z1,z2,z704,z3,z4,z5,z6]),(1,[z47,z2,z3,z291,z5,z6]),(0,[z1,z97,z2,z3,z4,z20,z6]),(0,[z1,z2,z705,z3,z4,z5,z6]),(0,[z1,z706,z2,z3,z4,z5,z6])],[(1,[z1,z109,z3,z4,z5,z6]),(0,[z1,z80,z240,z3,z4,z5,z6]),(0,[z1,z25,z2,z3,z16,z4,z6]),(0,[z1,z2,z3,z328,z4,z19,z5]),(0,[z1,z522,z2,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z39,z5,z270])],[(0,[z1,z2,z3,z4,z5,z707]),(0,[z147,z1,z2,z3,z17,z6]),(0,[z1,z2,z3,z10,z4,z708]),(0,[z1,z2,z3,z4,z140,z709])],[(0,[z52,z64,z2,z83,z4,z5]),(0,[z1,z582,z3,z222,z5,z6]),(0,[z294,z2,z3,z291,z5,z6])],[(0,[z64,z1,z2,z3,z39,z5])],[(0,[z1,z2,z3,z4,z710,z6]),(0,[z1,z2,z3,z4,z140,z215]),(0,[z1,z2,z3,z4,z711,z6]),(0,[z1,z2,z124,z330,z4,z5])],[(0,[z1,z2,z3,z4,z5,z712]),(0,[z1,z2,z3,z4,z5,z280]),(0,[z713,z2,z3,z4,z5,z6])],[(0,[z1,z2,z199,z10,z4,z5]),(0,[z1,z2,z3,z714,z5,z6]),(0,[z1,z2,z3,z4,z20,z75]),(0,[z1,z2,z715,z4,z5,z6]),(0,[z1,z2,z3,z4,z369,z213]),(0,[z1,z2,z3,z4,z5,z716]),(0,[z1,z60,z285,z2,z3,z5])],[(0,[z1,z2,z3,z224,z5,z73]),(0,[z64,z1,z2,z3,z4,z369]),(0,[z2,z3,z4,z8,z538,z6]),(0,[z1,z2,z3,z4,z5,z61]),(0,[z1,z2,z3,z4,z717,z6])],[(0,[z1,z2,z4,z5,z718,z6]),(0,[z64,z1,z2,z3,z8,z317]),(0,[z64,z1,z2,z3,z5,z614]),(0,[z1,z2,z3,z4,z719,z6]),(0,[z496,z64,z1,z2,z3,z5]),(0,[z1,z2,z720,z4,z5,z6]),(0,[z1,z2,z3,z4,z721,z6])],[(0,[z1,z2,z3,z4,z722,z6]),(0,[z1,z125,z49,z4,z5,z6])],[],[(0,[z1,z2,z3,z5,z723,z6]),(0,[z64,z1,z60,z3,z222,z5]),(0,[z64,z1,z2,z3,z176,z5])],[],[(0,[z1,z2,z3,z4,z5,z724]),(0,[z1,z2,z3,z4,z725,z6]),(0,[z1,z2,z3,z726,z5,z6]),(0,[z2,z3,z10,z4,z8,z20])],[(0,[z1,z2,z3,z4,z727,z6]),(0,[z1,z2,z124,z4,z20,z86]),(0,[z64,z1,z2,z3,z5,z684]),(0,[z1,z728,z2,z3,z4,z6])],[(0,[z1,z589,z3,z4,z5,z280]),(0,[z1,z2,z3,z4,z20,z280]),(0,[z1,z2,z3,z4,z5,z729])]],
   [[(0,[z1,z2,z3,z20,z136,z6]),(0,[z1,z2,z3,z4,z730,z6]),(0,[z1,z2,z3,z731,z4,z6]),(0,[z64,z1,z732,z3,z4,z5])],[(0,[z162,z132,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z369,z259]),(0,[z64,z1,z2,z3,z10,z20]),(0,[z147,z1,z2,z3,z5,z105])],[(0,[z64,z1,z2,z3,z4,z384]),(0,[z64,z1,z2,z3,z4,z452])],[(0,[z1,z2,z3,z211,z191,z6]),(0,[z1,z733,z2,z4,z5,z6]),(0,[z1,z2,z3,z734,z5,z6]),(0,[z1,z2,z3,z4,z735,z6]),(0,[z64,z1,z2,z3,z5,z636]),(0,[z1,z2,z3,z4,z20,z218]),(0,[z1,z2,z3,z5,z736,z6]),(0,[z1,z2,z3,z10,z4,z737])],[(0,[z212,z2,z3,z101,z20,z6]),(0,[z1,z738,z49,z4,z5,z6]),(0,[z1,z2,z739,z3,z4,z5])],[(0,[z1,z2,z3,z4,z740,z6]),(0,[z1,z2,z3,z4,z741,z6]),(0,[z1,z2,z3,z742,z4,z5])],[(0,[z1,z2,z3,z10,z211,z5]),(0,[z1,z2,z3,z4,z743,z6]),(0,[z274,z595,z2,z3,z4,z5]),(0,[z406,z64,z1,z2,z3,z5])],[(0,[z2,z3,z715,z4,z5,z6]),(0,[z1,z2,z3,z20,z168,z6]),(0,[z1,z2,z3,z4,z744,z6])],[(0,[z1,z2,z745,z4,z5,z6]),(0,[z1,z2,z3,z10,z4,z746])],[(0,[z1,z2,z3,z4,z5,z213]),(0,[z1,z2,z3,z4,z747,z6])],[(0,[z46,z2,z715,z4,z5,z6]),(0,[z1,z2,z3,z4,z748,z6]),(0,[z64,z1,z2,z3,z32,z5])],[(0,[z103,z2,z3,z4,z20,z6]),(0,[z2,z3,z4,z5,z749,z6]),(0,[z1,z2,z3,z4,z5,z750])],[(0,[z1,z751,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z752]),(0,[z64,z278,z1,z2,z3,z5])],[(0,[z1,z2,z3,z4,z5,z753]),(0,[z1,z2,z3,z4,z5,z754]),(0,[z104,z1,z3,z4,z5,z105])],[(0,[z128,z2,z3,z4,z8,z54])],[(0,[z1,z2,z3,z4,z5,z755]),(0,[z1,z2,z199,z4,z414,z6]),(0,[z1,z2,z756,z4,z5,z6]),(0,[z1,z2,z3,z8,z757,z6]),(0,[z104,z1,z3,z4,z5,z758])]],
   [[(0,[z64,z1,z2,z3,z4,z163]),(0,[z1,z2,z50,z68,z5,z196]),(0,[z1,z2,z3,z4,z759,z6])],[(0,[z1,z2,z3,z211,z20,z6]),(0,[z1,z2,z3,z4,z760,z6]),(0,[z1,z761,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z762,z6]),(0,[z67,z1,z2,z3,z218,z42]),(0,[z64,z763,z2,z3,z4,z5])],[(0,[z1,z3,z4,z5,z764,z6]),(0,[z274,z2,z3,z4,z5,z56])],[(0,[z1,z589,z3,z4,z8,z6]),(0,[z2,z715,z83,z4,z5,z6]),(0,[z1,z2,z3,z4,z765,z6]),(0,[z1,z2,z3,z10,z4,z597]),(0,[z1,z2,z3,z4,z766,z6]),(0,[z1,z2,z3,z10,z4,z182])],[(0,[z1,z2,z3,z4,z767,z6]),(0,[z1,z2,z3,z768,z5,z6]),(0,[z1,z2,z3,z4,z5,z259]),(0,[z1,z2,z3,z5,z757,z6]),(0,[z1,z2,z3,z10,z4,z769])],[(0,[z1,z2,z3,z4,z20,z189]),(0,[z1,z2,z3,z4,z770,z6]),(0,[z1,z2,z3,z771,z4,z5]),(0,[z1,z2,z50,z772,z3,z5]),(0,[z64,z1,z2,z3,z5,z692])],[(0,[z1,z2,z3,z4,z20,z181]),(0,[z64,z23,z1,z2,z3,z190]),(0,[z23,z1,z2,z773,z5,z6])],[(0,[z1,z2,z3,z4,z774,z6]),(0,[z1,z2,z3,z138,z4,z20]),(0,[z64,z9,z1,z522,z3,z5]),(0,[z1,z3,z4,z5,z105,z758]),(0,[z1,z2,z3,z176,z5,z130])],[(0,[z64,z1,z2,z3,z644,z5]),(0,[z64,z1,z2,z3,z265,z5]),(0,[z1,z444,z3,z4,z651,z6]),(0,[z1,z2,z4,z775,z5,z6]),(0,[z1,z2,z3,z4,z17,z6])],[(0,[z1,z2,z3,z776,z4,z5]),(0,[z1,z2,z3,z4,z777,z6]),(0,[z1,z3,z4,z778,z5,z6])],[(0,[z1,z2,z199,z4,z5,z75]),(0,[z1,z2,z3,z4,z779,z6]),(0,[z311,z1,z2,z3,z5,z56]),(0,[z1,z2,z3,z780,z4,z6]),(0,[z1,z2,z3,z10,z4,z741])],[(0,[z1,z2,z3,z4,z781,z6]),(0,[z376,z2,z3,z4,z20,z6]),(0,[z244,z1,z2,z3,z42,z6]),(0,[z1,z2,z3,z782,z4,z6]),(0,[z1,z2,z3,z10,z4,z783])],[(0,[z46,z2,z100,z10,z4,z5]),(0,[z1,z2,z3,z4,z30,z6]),(0,[z1,z2,z3,z4,z5,z784])],[(0,[z1,z2,z246,z4,z20,z6]),(0,[z1,z2,z3,z114,z5,z280]),(0,[z1,z2,z785,z4,z5,z6]),(0,[z147,z1,z2,z3,z5,z56])],[(0,[z1,z2,z3,z661,z176,z5])],[(0,[z1,z2,z3,z4,z290,z6]),(0,[z1,z2,z3,z786,z4,z5]),(0,[z440,z2,z3,z4,z8,z6]),(0,[z1,z3,z778,z223,z5,z6]),(0,[z1,z2,z3,z24,z4,z439]),(0,[z1,z2,z3,z787,z4,z5])]],
   [[(0,[z1,z2,z3,z788,z42,z6])],[(0,[z1,z2,z789,z4,z5,z6]),(0,[z258,z2,z3,z291,z5,z6]),(0,[z64,z1,z2,z3,z4,z8]),(0,[z560,z1,z2,z3,z10,z5]),(0,[z1,z2,z3,z4,z790,z6])],[(0,[z791,z1,z2,z3,z185,z5]),(0,[z64,z2,z3,z4,z8,z20]),(0,[z1,z2,z3,z4,z5,z792]),(0,[z1,z2,z3,z793,z5,z6])],[(0,[z1,z2,z3,z4,z414,z270]),(1,[z1,z3,z4,z5,z758]),(0,[z311,z1,z27,z3,z5,z237]),(0,[z1,z2,z3,z4,z182,z245])],[(0,[z1,z2,z3,z5,z6,z794])],[(0,[z64,z1,z2,z3,z4,z322]),(0,[z1,z2,z3,z343,z71,z6]),(0,[z795,z2,z3,z4,z5,z6])],[(0,[z1,z796,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z797,z6]),(0,[z1,z676,z3,z4,z193,z6]),(0,[z1,z2,z3,z4,z798,z6])],[(0,[z1,z2,z3,z799,z5,z6]),(0,[z120,z1,z2,z4,z5,z55]),(0,[z1,z2,z15,z10,z4,z41]),(0,[z1,z2,z3,z4,z218,z245])],[(0,[z1,z2,z3,z800,z5,z6]),(0,[z1,z2,z3,z4,z801,z5]),(0,[z23,z1,z2,z19,z20,z6]),(0,[z1,z802,z2,z3,z4,z5]),(0,[z1,z2,z3,z5,z168,z188]),(0,[z1,z2,z3,z42,z537,z6])],[(0,[z1,z2,z3,z4,z96,z6]),(0,[z1,z60,z803,z2,z3,z5]),(0,[z1,z97,z3,z4,z98,z6]),(0,[z64,z680,z1,z2,z3,z5]),(0,[z1,z2,z3,z4,z5,z804])],[(0,[z1,z2,z3,z4,z5,z805]),(0,[z1,z2,z3,z4,z322,z6]),(0,[z2,z3,z4,z531,z8,z6]),(0,[z1,z2,z3,z4,z5,z758]),(0,[z64,z1,z2,z3,z4,z601])],[(0,[z64,z1,z2,z3,z5,z806])],[(0,[z1,z2,z3,z4,z807,z6]),(0,[z535,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z5,z73,z61]),(0,[z67,z1,z2,z3,z10,z42])],[(0,[z1,z2,z3,z4,z5,z808]),(0,[z1,z2,z4,z5,z55,z809])],[(0,[z1,z2,z3,z4,z5,z809])],[(0,[z1,z2,z3,z4,z91,z6]),(0,[z1,z97,z3,z10,z4,z98]),(0,[z378,z1,z2,z330,z4,z5]),(1,[z1,z2,z3,z4,z709])]],
   [[(0,[z64,z1,z2,z3,z393,z6]),(0,[z1,z2,z3,z4,z810,z6])],[(0,[z1,z2,z3,z114,z8,z6]),(0,[z2,z3,z4,z382,z8,z6]),(0,[z1,z2,z3,z10,z4,z121])],[(0,[z1,z2,z3,z4,z811,z6])],[(0,[z1,z2,z3,z39,z414,z6]),(0,[z1,z2,z3,z10,z353,z5])],[(0,[z1,z2,z3,z812,z4,z20]),(0,[z1,z2,z3,z328,z4,z121]),(1,[z1,z2,z3,z788,z6])],[(0,[z1,z2,z199,z211,z5,z6]),(0,[z1,z109,z3,z4,z5,z280]),(0,[z1,z2,z3,z4,z813,z5]),(0,[z1,z2,z3,z16,z5,z99]),(0,[z64,z1,z2,z3,z4,z814])],[(0,[z1,z2,z3,z4,z5,z815]),(0,[z1,z2,z3,z5,z816,z6]),(0,[z1,z2,z3,z497,z4,z20]),(0,[z64,z1,z2,z772,z3,z5]),(0,[z64,z1,z817,z3,z4,z5])],[(0,[z2,z3,z4,z8,z765,z6])],[(0,[z619,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z5,z818,z6]),(0,[z64,z1,z2,z3,z5,z318]),(0,[z23,z1,z2,z407,z19,z5])],[(0,[z1,z589,z3,z4,z91,z6]),(0,[z1,z2,z3,z819,z5,z6]),(0,[z1,z2,z3,z4,z5,z820]),(0,[z1,z2,z3,z4,z821,z6])],[(0,[z1,z2,z3,z4,z5,z822]),(0,[z64,z1,z2,z3,z4,z91]),(0,[z1,z2,z3,z10,z247,z5]),(0,[z64,z823,z2,z3,z4,z5]),(0,[z1,z2,z3,z24,z4,z139])],[(0,[z1,z2,z3,z4,z5,z824]),(0,[z1,z150,z48,z4,z5,z6])],[(0,[z1,z2,z825,z4,z5,z6])],[(0,[z1,z2,z3,z4,z369,z6]),(0,[z64,z1,z2,z3,z42,z44])],[(0,[z64,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z826,z6]),(0,[z289,z64,z1,z2,z3,z42])],[(0,[z57,z241,z3,z4,z5,z270]),(0,[z212,z187,z2,z3,z101,z5]),(0,[z1,z2,z3,z4,z190,z6])]],
   [[(0,[z1,z2,z3,z224,z4,z5]),(0,[z1,z80,z49,z10,z4,z5]),(0,[z1,z2,z3,z4,z827,z6]),(0,[z1,z2,z4,z5,z809,z86])],[(0,[z64,z1,z2,z3,z16,z20]),(0,[z1,z362,z3,z4,z193,z6]),(0,[z828,z1,z2,z3,z4,z6]),(0,[z64,z1,z2,z3,z26,z42]),(0,[z1,z2,z124,z76,z4,z86])],[(0,[z1,z2,z3,z829,z5,z6]),(0,[z1,z2,z3,z4,z5,z830])],[(0,[z831,z1,z2,z3,z4,z5]),(0,[z1,z2,z407,z3,z4,z20])],[(0,[z52,z2,z83,z4,z5,z280]),(0,[z1,z2,z3,z4,z20,z61]),(0,[z1,z2,z3,z354,z265,z5]),(0,[z64,z1,z2,z3,z292,z5]),(0,[z832,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z833,z5,z6])],[(0,[z1,z240,z48,z4,z5,z6]),(0,[z64,z1,z2,z3,z5,z42]),(0,[z1,z2,z3,z10,z4,z834])],[(0,[z1,z2,z3,z835,z5,z6]),(0,[z2,z3,z836,z101,z5,z6]),(0,[z1,z285,z2,z3,z4,z20]),(0,[z64,z1,z2,z3,z4,z96]),(0,[z1,z2,z3,z4,z837,z6]),(0,[z147,z1,z2,z124,z5,z86])],[(0,[z2,z587,z3,z4,z8,z6]),(0,[z64,z23,z1,z2,z3,z263])],[(0,[z1,z2,z838,z4,z5,z6]),(0,[z1,z2,z3,z4,z839,z6]),(0,[z1,z2,z3,z4,z5,z840]),(0,[z47,z2,z3,z291,z8,z6]),(0,[z374,z1,z2,z3,z42,z6]),(0,[z620,z1,z2,z3,z10,z5])],[(0,[z64,z299,z1,z2,z3,z5]),(0,[z1,z109,z3,z4,z8,z6]),(0,[z64,z203,z2,z3,z4,z20]),(0,[z128,z2,z3,z4,z5,z749])],[(0,[z1,z2,z3,z4,z841,z6]),(0,[z1,z842,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z134,z215]),(0,[z1,z2,z3,z773,z5,z6]),(0,[z1,z2,z3,z10,z4,z17])],[(0,[z1,z2,z3,z4,z843,z6]),(0,[z844,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z845,z6])],[(0,[z1,z2,z3,z4,z5,z846]),(0,[z64,z1,z2,z3,z5,z165])],[(0,[z1,z2,z352,z68,z5,z6]),(0,[z847,z2,z3,z4,z5,z6]),(0,[z23,z1,z2,z298,z19,z6])],[(0,[z64,z1,z2,z3,z210,z5])],[(0,[z57,z241,z3,z39,z5,z6]),(0,[z64,z1,z2,z3,z4,z191])]],
   [[(0,[z1,z2,z3,z4,z848,z6]),(0,[z1,z2,z3,z4,z8,z229]),(0,[z1,z2,z3,z4,z5,z849]),(0,[z1,z3,z4,z850,z98,z6]),(0,[z1,z2,z851,z4,z5,z6]),(0,[z1,z27,z3,z4,z5,z237]),(0,[z852,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z182,z6])],[(0,[z64,z1,z2,z3,z632,z5]),(0,[z1,z2,z3,z4,z5,z749]),(0,[z1,z2,z3,z4,z5,z853])],[(0,[z1,z2,z246,z4,z191,z6]),(0,[z1,z2,z3,z854,z4,z5]),(0,[z64,z1,z2,z3,z5,z219])],[(0,[z1,z2,z3,z4,z855,z6]),(0,[z64,z1,z80,z49,z4,z5]),(0,[z1,z240,z48,z4,z366,z6]),(0,[z311,z1,z2,z3,z5,z86]),(0,[z64,z1,z2,z856,z4,z5])],[(0,[z1,z2,z857,z4,z5,z6]),(0,[z64,z1,z271,z2,z3,z5]),(0,[z1,z2,z3,z4,z5,z858]),(0,[z706,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z10,z412,z5]),(0,[z1,z2,z3,z4,z859,z6]),(0,[z1,z2,z3,z10,z4,z172]),(0,[z1,z2,z3,z16,z423,z6])],[(0,[z1,z2,z4,z860,z5,z6]),(0,[z275,z2,z3,z4,z5,z54]),(0,[z1,z2,z856,z4,z5,z6])],[(0,[z1,z2,z3,z4,z20,z213]),(0,[z64,z1,z2,z3,z20,z165]),(0,[z1,z2,z3,z4,z861,z6]),(0,[z64,z1,z2,z3,z477,z5]),(0,[z1,z2,z4,z5,z809,z6])],[(0,[z1,z862,z3,z4,z5,z6]),(0,[z1,z2,z3,z114,z91,z6]),(0,[z1,z2,z863,z3,z4,z5])],[(0,[z1,z2,z3,z4,z864,z6]),(0,[z52,z2,z83,z4,z8,z6]),(0,[z85,z1,z2,z4,z8,z55]),(0,[z1,z2,z4,z26,z775,z6])],[(0,[z1,z2,z3,z865,z4,z5]),(0,[z1,z2,z3,z4,z866,z6])],[(0,[z104,z1,z3,z4,z20,z105]),(0,[z64,z1,z2,z3,z4,z190])],[(0,[z1,z2,z3,z867,z5,z6]),(0,[z868,z2,z3,z4,z5,z6]),(0,[z64,z1,z2,z3,z4,z337]),(0,[z64,z1,z2,z3,z4,z393]),(0,[z64,z1,z2,z3,z29,z5])],[(0,[z1,z2,z3,z697,z71,z6])],[(0,[z869,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z185,z5,z280]),(0,[z1,z2,z3,z870,z4,z5]),(0,[z311,z1,z2,z3,z5,z55]),(0,[z23,z1,z2,z330,z5,z6])],[(0,[z1,z3,z4,z871,z5,z6]),(0,[z1,z2,z3,z4,z872,z188])],[(0,[z1,z2,z3,z10,z114,z5]),(0,[z274,z2,z3,z4,z20,z56]),(0,[z1,z2,z562,z4,z41,z6]),(0,[z1,z2,z3,z5,z6,z873])]],
   [[(0,[z1,z2,z3,z874,z4,z5]),(0,[z1,z2,z3,z4,z875,z6]),(0,[z64,z1,z2,z3,z24,z42])],[(0,[z1,z2,z3,z4,z876,z6]),(0,[z1,z2,z3,z4,z877,z6]),(0,[z1,z2,z3,z4,z20,z259]),(0,[z1,z93,z2,z3,z497,z4]),(0,[z64,z1,z2,z3,z16,z42])],[(0,[z1,z2,z3,z101,z5,z213]),(0,[z187,z1,z2,z3,z4,z5]),(0,[z274,z2,z3,z4,z5,z749]),(0,[z1,z2,z3,z878,z4,z6])],[(0,[z1,z2,z3,z879,z211,z5]),(0,[z2,z3,z81,z4,z20,z6]),(0,[z1,z60,z3,z222,z5,z368])],[(0,[z1,z2,z3,z4,z880,z6])],[(0,[z1,z2,z3,z4,z6,z881])],[(0,[z1,z882,z3,z4,z5,z6]),(0,[z1,z2,z3,z224,z4,z8]),(0,[z326,z2,z3,z4,z20,z6]),(0,[z1,z2,z15,z4,z690,z6]),(0,[z883,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z884,z6])],[(0,[z64,z1,z2,z3,z4,z30]),(0,[z64,z1,z2,z3,z5,z873]),(0,[z1,z2,z3,z176,z140,z44])],[(0,[z57,z241,z3,z10,z4,z5]),(0,[z311,z1,z2,z3,z5,z6]),(0,[z1,z2,z298,z3,z10,z4]),(1,[z64,z1,z2,z3,z245])],[(0,[z1,z2,z3,z4,z885,z6]),(0,[z1,z2,z3,z4,z886,z6]),(0,[z64,z1,z2,z3,z209,z5]),(0,[z64,z1,z2,z3,z245,z6])],[(0,[z1,z2,z3,z4,z887,z6])],[(0,[z1,z2,z3,z888,z39,z5]),(0,[z1,z589,z3,z4,z290,z6]),(0,[z1,z2,z3,z4,z5,z889]),(0,[z1,z2,z3,z4,z5,z890]),(0,[z147,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z806])],[(0,[z64,z467,z1,z2,z3,z5])],[(0,[z9,z1,z3,z10,z223,z5]),(0,[z147,z1,z2,z3,z5,z237])],[(0,[z1,z2,z3,z4,z891,z6]),(0,[z1,z109,z3,z4,z91,z6]),(0,[z1,z2,z3,z10,z8,z73]),(0,[z1,z2,z3,z4,z892,z6])]],
   [[(0,[z1,z2,z3,z4,z893,z6]),(0,[z1,z2,z3,z16,z10,z71]),(0,[z1,z2,z3,z4,z44,z709])],[(0,[z1,z2,z3,z185,z8,z6]),(0,[z1,z2,z3,z4,z8,z188])],[(0,[z64,z1,z594,z2,z3,z5]),(0,[z1,z2,z3,z10,z5,z74])],[(0,[z1,z2,z3,z836,z5,z6])],[(0,[z64,z1,z2,z3,z291,z8]),(0,[z64,z1,z60,z2,z3,z20]),(0,[z1,z3,z4,z894,z8,z6]),(0,[z64,z1,z2,z3,z325,z5]),(0,[z895,z1,z2,z3,z5,z6])],[(0,[z64,z1,z2,z3,z4,z250]),(0,[z1,z2,z3,z4,z896,z6]),(0,[z1,z2,z3,z4,z5,z897]),(0,[z1,z2,z3,z65,z42,z6]),(0,[z1,z2,z3,z10,z4,z898])],[],[(0,[z1,z2,z3,z4,z899,z61]),(0,[z1,z2,z3,z4,z900,z5])],[(0,[z212,z2,z3,z224,z101,z5]),(0,[z1,z2,z3,z5,z901,z6]),(0,[z104,z311,z1,z2,z3,z5]),(0,[z1,z2,z3,z4,z121,z6])],[(0,[z59,z132,z3,z4,z5,z6]),(0,[z459,z2,z3,z291,z5,z6]),(0,[z1,z2,z3,z902,z4,z6]),(0,[z1,z2,z3,z4,z903,z6]),(0,[z1,z268,z3,z276,z4,z5])],[(0,[z1,z2,z199,z4,z8,z6]),(0,[z1,z2,z3,z4,z904,z6]),(0,[z64,z1,z2,z664,z3,z5]),(0,[z64,z1,z2,z3,z661,z5]),(0,[z64,z1,z2,z3,z10,z5])],[(0,[z1,z2,z905,z3,z4,z6])],[(0,[z1,z2,z3,z4,z8,z284]),(0,[z1,z2,z3,z4,z44,z685])],[(0,[z64,z1,z2,z3,z4,z405]),(0,[z64,z1,z93,z2,z3,z4])],[(0,[z52,z2,z83,z4,z91,z6]),(0,[z1,z25,z3,z4,z372,z6]),(0,[z1,z2,z3,z24,z4,z154]),(0,[z1,z2,z3,z24,z4,z181])],[(0,[z1,z2,z3,z140,z235,z44])]],
   [[(0,[z64,z1,z2,z199,z4,z5]),(0,[z64,z1,z2,z50,z3,z20]),(0,[z1,z2,z3,z265,z405,z6])],[(0,[z1,z2,z3,z39,z5,z75]),(0,[z1,z31,z3,z4,z583,z6]),(0,[z1,z93,z285,z2,z3,z4])],[(0,[z57,z241,z3,z4,z414,z6]),(0,[z1,z2,z3,z4,z906,z6]),(0,[z907,z1,z2,z3,z5,z6]),(0,[z64,z1,z2,z3,z5,z317])],[(0,[z64,z1,z14,z2,z4,z26])],[(0,[z1,z2,z3,z4,z908,z6]),(0,[z1,z2,z3,z909,z5,z6])],[(0,[z513,z2,z3,z101,z5,z6])],[(0,[z1,z2,z3,z4,z5,z910]),(0,[z1,z2,z3,z10,z4,z245])],[(0,[z1,z2,z911,z3,z4,z6]),(0,[z67,z1,z2,z3,z552,z6]),(0,[z1,z2,z3,z912,z5,z6])],[(0,[z187,z1,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z913]),(0,[z1,z2,z3,z16,z788,z6])],[(0,[z1,z2,z3,z4,z898,z6])],[(0,[z1,z2,z3,z4,z914,z6]),(0,[z1,z2,z3,z114,z290,z6]),(0,[z1,z2,z3,z10,z4,z283])],[(0,[z1,z915,z3,z4,z5,z6]),(0,[z47,z2,z3,z291,z5,z213]),(0,[z64,z1,z2,z3,z4,z263]),(0,[z1,z2,z3,z4,z5,z709])],[(0,[z1,z2,z3,z211,z5,z270]),(0,[z64,z1,z25,z3,z4,z193])],[(0,[z57,z241,z3,z4,z5,z75]),(0,[z64,z1,z2,z3,z4,z916])],[(0,[z1,z2,z3,z4,z8,z270]),(0,[z64,z1,z2,z352,z3,z5]),(0,[z64,z595,z2,z3,z291,z5]),(0,[z1,z2,z666,z4,z5,z86])],[]],
   [[(0,[z1,z2,z3,z917,z5,z6]),(0,[z1,z2,z3,z4,z918,z6]),(0,[z1,z2,z3,z138,z4,z5]),(0,[z64,z1,z268,z2,z3,z5])],[(0,[z64,z1,z2,z201,z3,z5]),(0,[z64,z1,z2,z3,z291,z5]),(0,[z64,z23,z1,z2,z50,z5]),(0,[z64,z1,z2,z15,z4,z41])],[(0,[z1,z2,z3,z4,z919,z6]),(0,[z1,z2,z3,z4,z920,z6]),(0,[z1,z2,z3,z10,z185,z5]),(0,[z1,z2,z3,z10,z4,z290]),(0,[z1,z2,z3,z4,z290,z284]),(0,[z1,z240,z48,z4,z20,z6]),(0,[z64,z1,z2,z3,z20,z42]),(0,[z64,z1,z2,z298,z3,z4])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z14,z2,z4,z694,z6])],[(0,[z162,z921,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z227,z44]),(0,[z58,z2,z3,z10,z4,z8]),(0,[z1,z2,z3,z4,z922,z6])],[(0,[z1,z2,z3,z456,z4,z130])],[(0,[z47,z2,z3,z291,z5,z259]),(0,[z1,z2,z225,z4,z5,z86]),(0,[z1,z599,z49,z4,z5,z6]),(0,[z64,z67,z1,z2,z3,z42])],[(0,[z1,z2,z3,z185,z91,z6]),(0,[z627,z2,z3,z101,z5,z6]),(0,[z64,z1,z2,z3,z354,z5])],[(0,[z1,z2,z246,z4,z5,z270]),(0,[z923,z1,z2,z3,z39,z5]),(0,[z1,z2,z3,z4,z924,z6]),(0,[z1,z2,z3,z4,z925,z6]),(0,[z128,z2,z3,z4,z5,z54]),(0,[z1,z2,z3,z4,z5,z926]),(0,[z64,z1,z2,z3,z76,z4]),(0,[z357,z1,z472,z3,z4,z5]),(0,[z1,z2,z3,z4,z927,z6])],[(0,[z64,z1,z2,z3,z474,z5]),(0,[z1,z2,z3,z412,z405,z6])],[],[(0,[z1,z761,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z928]),(1,[z1,z3,z4,z850,z6])],[(0,[z1,z3,z4,z20,z764,z6]),(0,[z1,z97,z3,z4,z491,z6])],[(0,[z1,z589,z3,z4,z5,z6]),(0,[z1,z27,z3,z4,z20,z237]),(0,[z169,z2,z3,z4,z20,z6]),(0,[z365,z2,z3,z4,z5,z56]),(0,[z1,z2,z3,z4,z929,z6])],[(0,[z1,z2,z3,z39,z8,z6]),(0,[z103,z241,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z930]),(0,[z103,z2,z83,z4,z5,z6]),(0,[z1,z2,z3,z4,z931,z6]),(0,[z1,z2,z3,z4,z932,z6])],[(0,[z1,z2,z407,z3,z4,z8]),(0,[z1,z25,z3,z4,z309,z6])]],
   [[(0,[z923,z1,z2,z3,z4,z5]),(0,[z46,z2,z100,z4,z8,z6]),(0,[z1,z2,z50,z68,z8,z6]),(0,[z64,z1,z2,z3,z10,z8]),(0,[z1,z2,z3,z4,z933,z6]),(0,[z1,z2,z3,z10,z5,z136]),(0,[z64,z1,z2,z3,z5,z168])],[(0,[z1,z2,z3,z934,z5,z6]),(0,[z1,z2,z3,z4,z366,z6]),(0,[z64,z1,z2,z3,z364,z5]),(0,[z64,z1,z2,z520,z3,z5]),(0,[z935,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z936,z6]),(0,[z1,z109,z3,z4,z290,z6]),(0,[z1,z2,z3,z4,z91,z284]),(0,[z67,z1,z2,z3,z684,z6]),(0,[z64,z1,z97,z3,z4,z98]),(0,[z1,z2,z3,z4,z850,z6]),(0,[z1,z2,z3,z4,z409,z44]),(0,[z64,z1,z2,z3,z5,z437])],[(0,[z64,z1,z2,z3,z5,z443])],[(0,[z64,z1,z2,z3,z142,z5]),(0,[z1,z48,z738,z4,z5,z6]),(0,[z1,z3,z222,z778,z5,z6])],[],[(0,[z162,z132,z3,z10,z4,z5]),(0,[z1,z2,z3,z4,z597,z6]),(0,[z1,z2,z3,z4,z937,z6]),(0,[z938,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z939,z6])],[],[(0,[z1,z2,z246,z39,z5,z6]),(0,[z57,z241,z3,z211,z5,z6]),(0,[z64,z1,z2,z3,z5,z296])],[(0,[z1,z2,z3,z878,z4,z229]),(0,[z1,z2,z3,z940,z5,z6]),(0,[z1,z2,z3,z4,z5,z873])],[(0,[z1,z2,z3,z4,z941,z6])],[(0,[z1,z2,z3,z4,z5,z942]),(0,[z1,z2,z3,z4,z943,z6]),(0,[z1,z2,z3,z944,z4,z5]),(0,[z1,z2,z772,z3,z4,z5]),(0,[z147,z1,z2,z3,z76,z6]),(0,[z67,z1,z2,z3,z138,z42]),(0,[z1,z2,z3,z4,z245,z6])],[(0,[z1,z2,z3,z4,z8,z196])],[(0,[z1,z2,z3,z4,z945,z6]),(0,[z1,z2,z3,z812,z4,z5]),(0,[z203,z2,z3,z4,z765,z6]),(0,[z1,z2,z3,z305,z4,z154]),(0,[z64,z1,z2,z3,z5,z288]),(0,[z23,z1,z2,z19,z263,z6])],[(0,[z1,z2,z3,z4,z5,z946]),(0,[z1,z2,z3,z24,z4,z218])],[(0,[z64,z1,z589,z3,z4,z5]),(0,[z1,z2,z3,z4,z947,z6]),(0,[z1,z2,z3,z497,z4,z5]),(0,[z1,z97,z3,z4,z850,z6]),(0,[z1,z2,z3,z4,z948,z6])]],
   [[(0,[z1,z241,z246,z4,z5,z6]),(0,[z1,z416,z3,z4,z5,z237]),(0,[z64,z1,z2,z3,z5,z256]),(0,[z64,z23,z1,z2,z19,z5])],[(0,[z52,z2,z83,z4,z290,z6]),(0,[z1,z2,z3,z108,z153,z6]),(0,[z1,z2,z3,z949,z5,z6])],[],[(0,[z1,z950,z3,z4,z5,z6]),(0,[z1,z951,z3,z4,z5,z6]),(0,[z1,z2,z4,z775,z41,z6])],[(0,[z1,z2,z3,z4,z414,z75]),(0,[z1,z240,z738,z4,z5,z6]),(0,[z1,z2,z3,z4,z393,z6])],[(0,[z64,z1,z2,z523,z3,z5]),(0,[z132,z921,z3,z4,z5,z6]),(0,[z64,z11,z1,z2,z3,z5]),(0,[z64,z9,z1,z60,z3,z5]),(0,[z1,z2,z3,z4,z952,z6]),(1,[z1,z2,z4,z775,z6]),(0,[z67,z1,z2,z3,z42,z6]),(0,[z1,z953,z3,z4,z5,z6])],[(0,[z311,z1,z2,z3,z20,z6]),(0,[z1,z539,z2,z4,z324,z6]),(0,[z2,z3,z688,z4,z8,z6]),(0,[z1,z2,z3,z138,z4,z8]),(0,[z64,z1,z2,z15,z3,z16]),(0,[z1,z2,z257,z4,z41,z6])],[(0,[z1,z2,z3,z888,z4,z5]),(0,[z1,z2,z3,z4,z954,z6]),(0,[z647,z64,z1,z2,z3,z5]),(0,[z311,z1,z27,z2,z3,z5]),(0,[z1,z2,z773,z19,z5,z6])],[(0,[z1,z2,z3,z4,z5,z955]),(0,[z1,z240,z48,z4,z532,z6]),(0,[z1,z2,z3,z956,z5,z6])],[(0,[z147,z1,z2,z3,z20,z6]),(0,[z311,z1,z2,z3,z5,z54])],[(0,[z1,z2,z3,z10,z4,z366]),(0,[z64,z1,z2,z3,z5,z188])],[(0,[z1,z2,z957,z4,z5,z6]),(0,[z1,z2,z3,z114,z5,z6]),(0,[z351,z1,z2,z19,z5,z6]),(0,[z1,z2,z3,z4,z958,z6]),(0,[z1,z2,z3,z4,z959,z6]),(0,[z1,z60,z3,z222,z5,z61]),(0,[z64,z1,z2,z611,z3,z5]),(0,[z1,z2,z3,z4,z960,z6])],[(0,[z147,z1,z2,z3,z5,z54]),(0,[z1,z2,z407,z3,z4,z5]),(0,[z1,z22,z2,z4,z26,z6])],[(0,[z2,z3,z4,z20,z195,z6]),(0,[z1,z2,z3,z10,z5,z251]),(0,[z64,z1,z2,z3,z4,z961])],[(0,[z962,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z963,z6])],[(0,[z64,z1,z2,z3,z211,z5]),(0,[z47,z2,z3,z291,z369,z6]),(0,[z563,z2,z3,z4,z20,z6]),(0,[z1,z285,z2,z3,z4,z5]),(0,[z64,z1,z401,z2,z3,z5])]],
   [[(0,[z170,z1,z2,z3,z684,z6]),(0,[z1,z3,z738,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z964]),(0,[z2,z3,z4,z8,z20,z6]),(0,[z1,z2,z3,z16,z410,z6]),(0,[z1,z965,z2,z3,z4,z6])],[(0,[z1,z2,z246,z10,z4,z5]),(0,[z1,z2,z3,z966,z5,z6]),(0,[z1,z2,z3,z5,z818,z229]),(0,[z1,z2,z3,z4,z967,z6])],[(0,[z1,z2,z3,z4,z968,z6]),(0,[z404,z2,z3,z4,z8,z6]),(0,[z9,z1,z472,z3,z5,z6]),(0,[z365,z2,z3,z354,z4,z5])],[(0,[z1,z2,z3,z4,z969,z6]),(1,[z2,z715,z4,z5,z6]),(0,[z1,z2,z3,z412,z8,z6]),(0,[z1,z80,z49,z4,z8,z6]),(0,[z1,z2,z3,z108,z71,z6])],[(0,[z1,z2,z3,z4,z970,z6]),(0,[z1,z2,z3,z801,z101,z5]),(0,[z1,z2,z3,z4,z971,z6]),(0,[z64,z1,z2,z3,z5,z608]),(0,[z64,z1,z2,z3,z609,z5]),(0,[z1,z2,z3,z4,z972,z6]),(0,[z9,z1,z3,z778,z5,z6]),(0,[z1,z25,z3,z4,z850,z6])],[(0,[z1,z80,z49,z4,z5,z189]),(0,[z1,z2,z3,z4,z973,z6])],[(0,[z974,z2,z3,z4,z5,z6]),(0,[z64,z1,z975,z3,z4,z5]),(0,[z64,z883,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z976]),(0,[z64,z1,z2,z3,z4,z927])],[(0,[z1,z2,z3,z977,z4,z5]),(0,[z1,z2,z3,z10,z4,z20]),(0,[z2,z3,z4,z978,z5,z6])],[(0,[z1,z2,z3,z185,z290,z6]),(0,[z23,z1,z2,z10,z19,z5])],[(0,[z1,z979,z2,z3,z4,z5])],[(0,[z921,z241,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z980]),(0,[z1,z2,z3,z328,z4,z20]),(0,[z64,z1,z2,z3,z4,z597]),(0,[z85,z1,z2,z4,z5,z809]),(0,[z64,z1,z2,z3,z4,z182])],[(0,[z1,z60,z3,z222,z8,z6]),(0,[z64,z656,z1,z2,z3,z5]),(0,[z1,z2,z3,z4,z5,z981]),(0,[z23,z1,z2,z328,z19,z5])],[(0,[z1,z2,z3,z4,z982,z6]),(0,[z64,z459,z2,z3,z4,z20]),(0,[z431,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z983,z6]),(0,[z1,z2,z3,z486,z71,z6]),(0,[z64,z935,z2,z3,z4,z5])],[(0,[z1,z2,z3,z211,z414,z6]),(0,[z64,z1,z2,z3,z20,z317]),(0,[z1,z2,z3,z4,z984,z6]),(0,[z1,z2,z3,z4,z985,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z986]),(0,[z18,z1,z2,z3,z4,z245])],[(0,[z1,z2,z3,z4,z987,z6])],[(0,[z1,z2,z3,z4,z191,z6]),(0,[z1,z2,z3,z4,z5,z988]),(0,[z791,z1,z2,z3,z4,z5]),(0,[z47,z2,z3,z291,z5,z6]),(0,[z1,z2,z3,z4,z5,z989]),(0,[z1,z2,z3,z4,z990,z6]),(0,[z1,z2,z3,z10,z4,z960])],[(0,[z1,z109,z3,z4,z5,z6]),(0,[z680,z1,z2,z3,z42,z6]),(0,[z1,z2,z991,z3,z4,z5]),(0,[z1,z2,z3,z992,z5,z6])],[(0,[z1,z2,z3,z10,z4,z993]),(0,[z311,z1,z2,z3,z10,z5]),(0,[z1,z975,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z994,z6]),(0,[z1,z2,z3,z4,z5,z995]),(0,[z1,z2,z3,z497,z4,z8]),(0,[z1,z2,z3,z4,z996,z6])],[(0,[z1,z2,z3,z997,z4,z5]),(0,[z13,z2,z3,z4,z5,z56]),(0,[z1,z2,z3,z10,z5,z235])],[(0,[z1,z2,z3,z4,z998,z6]),(0,[z1,z2,z3,z999,z5,z6]),(0,[z1000,z2,z3,z4,z5,z6]),(0,[z147,z1,z2,z3,z10,z5])],[(0,[z1,z2,z3,z4,z1001,z6])],[(0,[z1,z1002,z3,z4,z5,z6]),(0,[z1,z1003,z3,z4,z5,z6])],[(0,[z1,z2,z3,z10,z4,z355]),(0,[z1,z2,z3,z4,z5,z229]),(0,[z1,z2,z3,z5,z136,z61])],[(0,[z1,z2,z246,z4,z414,z6]),(0,[z1,z1004,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1005,z6]),(0,[z1,z2,z3,z1006,z5,z6])],[(0,[z592,z2,z3,z4,z8,z6]),(0,[z1,z1007,z3,z4,z5,z6])],[(0,[z64,z1,z2,z3,z5,z338]),(0,[z278,z147,z1,z2,z3,z5])],[(0,[z869,z1,z2,z3,z211,z5]),(0,[z1,z2,z124,z5,z168,z86]),(0,[z85,z147,z1,z2,z3,z5]),(0,[z289,z1,z2,z3,z4,z139]),(0,[z1,z2,z516,z571,z4,z5]),(0,[z1,z2,z3,z5,z73,z873])],[(0,[z1,z2,z3,z4,z1008,z6]),(0,[z1,z2,z79,z4,z41,z6]),(0,[z64,z1,z2,z3,z4,z532]),(0,[z9,z1,z285,z3,z223,z5])]],
   [[(0,[z1,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z5,z1009]),(0,[z1,z2,z3,z4,z5,z1010]),(0,[z1,z2,z4,z1011,z8,z6]),(0,[z64,z1,z2,z3,z16,z8]),(0,[z1,z2,z3,z76,z4,z6])],[(1,[z2,z3,z4,z765,z6]),(0,[z64,z1,z2,z3,z263,z6]),(0,[z64,z1,z14,z2,z3,z16])],[(0,[z52,z2,z83,z4,z5,z6]),(0,[z64,z1,z445,z2,z3,z5])],[],[(0,[z1,z2,z3,z4,z1012,z6]),(0,[z1,z97,z51,z3,z4,z6])],[(0,[z128,z2,z3,z4,z20,z54]),(0,[z1,z285,z2,z3,z4,z8]),(0,[z1,z2,z3,z176,z8,z6]),(0,[z1,z2,z1013,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1014]),(0,[z1,z1015,z2,z3,z4,z5])],[(0,[z1016,z1,z2,z3,z5,z6]),(0,[z289,z1,z2,z3,z42,z6])],[(0,[z1,z2,z3,z1017,z5,z6]),(0,[z1,z2,z4,z773,z5,z6])],[(0,[z1,z3,z4,z5,z758,z6]),(0,[z1,z2,z3,z4,z1018,z6]),(0,[z1,z2,z50,z773,z5,z6]),(0,[z1,z2,z3,z4,z1019,z6])],[(0,[z1,z2,z3,z4,z5,z1020]),(0,[z1,z589,z3,z4,z20,z6]),(0,[z1,z93,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z1021,z6])],[(0,[z162,z132,z3,z4,z163,z6]),(0,[z64,z1,z2,z568,z3,z5]),(0,[z1,z3,z4,z5,z758,z237]),(0,[z1,z268,z3,z4,z5,z237]),(0,[z1,z2,z3,z24,z4,z471])],[],[(0,[z57,z241,z3,z4,z8,z6]),(0,[z1022,z1,z2,z3,z114,z5]),(0,[z64,z1,z60,z2,z3,z5]),(0,[z1,z2,z3,z4,z6,z1023]),(0,[z64,z1,z2,z1024,z4,z5])],[(0,[z1,z2,z3,z265,z8,z6]),(0,[z128,z2,z3,z4,z597,z54]),(0,[z1,z2,z3,z4,z1025,z6])],[(0,[z64,z569,z1,z2,z3,z5]),(0,[z64,z1,z2,z3,z101,z20]),(0,[z1,z2,z3,z1026,z4,z5]),(0,[z1,z1027,z2,z3,z4,z6]),(0,[z418,z1,z522,z3,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z1028,z6]),(0,[z1,z2,z3,z1029,z5,z6]),(0,[z1,z2,z3,z4,z1030,z6]),(0,[z1,z27,z3,z137,z4,z237]),(0,[z1,z2,z3,z4,z1031,z6])],[(0,[z1,z2,z3,z1032,z5,z6]),(0,[z1,z2,z3,z4,z5,z1033]),(0,[z1,z2,z3,z4,z1034,z6]),(0,[z1,z2,z3,z341,z10,z5])],[(0,[z1,z1035,z3,z4,z5,z6]),(0,[z58,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z5,z1036])],[(0,[z1,z2,z3,z4,z1037,z6]),(0,[z1,z2,z3,z1038,z4,z5]),(0,[z1,z14,z2,z10,z4,z26]),(0,[z1,z2,z3,z17,z168,z6]),(0,[z64,z1,z965,z2,z3,z4])],[(0,[z1,z2,z3,z4,z1039,z6]),(0,[z1,z2,z3,z16,z71,z99]),(0,[z64,z1,z2,z516,z3,z5])],[(0,[z763,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1040,z6]),(0,[z162,z132,z3,z4,z384,z6]),(0,[z1,z1041,z3,z4,z5,z6])],[(0,[z57,z241,z246,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1042]),(0,[z2,z3,z4,z20,z160,z6]),(0,[z1,z2,z3,z4,z1043,z6])],[(0,[z1,z2,z3,z4,z1044,z6]),(0,[z64,z1,z2,z3,z4,z925]),(0,[z1,z2,z3,z4,z182,z130])],[(0,[z1,z2,z3,z4,z1045,z6]),(0,[z1,z2,z3,z5,z1046,z6]),(0,[z64,z1,z2,z50,z3,z5]),(0,[z1,z2,z3,z10,z5,z73]),(0,[z1,z2,z3,z10,z182,z73])],[],[(0,[z1,z2,z3,z185,z5,z6]),(0,[z133,z1,z3,z223,z5,z6]),(0,[z1,z2,z3,z10,z4,z369]),(0,[z1,z2,z3,z4,z814,z6]),(0,[z1,z2,z3,z4,z1047,z6])],[(0,[z1,z2,z3,z4,z1048,z6]),(0,[z459,z2,z3,z4,z20,z6]),(0,[z442,z2,z3,z4,z5,z56]),(0,[z1,z2,z3,z4,z5,z1049]),(0,[z1,z2,z3,z1050,z4,z6])],[(0,[z1,z2,z3,z4,z5,z1051]),(0,[z1,z2,z3,z224,z4,z971]),(0,[z64,z1,z2,z3,z16,z5]),(0,[z64,z1,z2,z3,z486,z5])],[(0,[z1,z2,z3,z4,z1052,z6]),(0,[z1,z3,z4,z894,z5,z6]),(0,[z64,z1,z2,z3,z5,z393]),(0,[z64,z1,z97,z2,z3,z16])],[(0,[z1,z2,z3,z1053,z4,z6]),(0,[z459,z2,z3,z4,z5,z54])]],
   [[(0,[z1,z2,z3,z4,z1054,z6]),(0,[z1,z2,z1024,z4,z5,z6]),(0,[z1,z2,z15,z4,z630,z6]),(0,[z1,z2,z3,z4,z961,z6]),(0,[z64,z147,z1,z2,z3,z5])],[],[(0,[z1,z2,z1055,z4,z5,z6]),(0,[z1,z2,z3,z4,z1056,z6]),(0,[z64,z1,z2,z3,z545,z5]),(0,[z1,z2,z3,z176,z5,z44])],[(0,[z64,z1,z2,z3,z4,z17]),(0,[z64,z1,z2,z3,z16,z409]),(0,[z1,z1057,z2,z3,z4,z6])],[(0,[z1,z2,z199,z4,z5,z6]),(0,[z46,z2,z100,z4,z322,z6]),(0,[z1,z2,z3,z10,z4,z1058])],[(0,[z1,z2,z3,z10,z4,z414]),(0,[z1,z2,z3,z10,z4,z358]),(0,[z1,z2,z3,z4,z709,z130])],[(0,[z1,z2,z3,z10,z4,z384]),(0,[z1,z2,z3,z4,z5,z284]),(0,[z1,z2,z3,z4,z532,z6])],[(0,[z1,z2,z3,z8,z235,z6]),(0,[z9,z1,z3,z172,z223,z6]),(0,[z1,z2,z3,z4,z5,z1059])],[(0,[z1,z589,z3,z114,z5,z6]),(0,[z1,z2,z3,z114,z20,z6]),(0,[z2,z3,z4,z20,z6,z221]),(0,[z1,z2,z3,z4,z5,z1060])],[(0,[z1,z2,z3,z224,z4,z1061]),(0,[z1,z2,z3,z4,z1062,z6])],[(0,[z1,z2,z3,z4,z1063,z6]),(0,[z1,z2,z3,z10,z4,z339]),(0,[z1,z3,z4,z850,z5,z6]),(0,[z1,z2,z3,z4,z6,z709])],[(0,[z64,z1,z2,z3,z94,z20]),(0,[z64,z1,z2,z3,z552,z5]),(0,[z1,z2,z3,z5,z218,z235])],[(1,[z1,z738,z4,z5,z6]),(0,[z1,z2,z3,z1064,z5,z6]),(0,[z1,z2,z3,z607,z42,z6]),(0,[z1,z2,z3,z5,z235,z6])],[(0,[z1,z2,z3,z1065,z4,z5]),(0,[z1,z2,z1066,z4,z5,z6]),(0,[z64,z1,z2,z3,z412,z5]),(0,[z64,z1,z2,z3,z4,z172])],[(0,[z64,z1,z2,z3,z193,z42])],[(0,[z1,z2,z407,z3,z291,z5])]],
   [[(0,[z1,z2,z3,z4,z1067,z6]),(0,[z9,z1,z3,z223,z8,z6]),(0,[z1,z2,z3,z4,z8,z99]),(0,[z1,z2,z3,z1068,z4,z5])],[(0,[z1,z2,z3,z4,z250,z6]),(0,[z1,z2,z3,z4,z1069,z6]),(0,[z64,z9,z1,z2,z3,z20]),(0,[z1,z2,z3,z4,z5,z1070])],[(0,[z1,z285,z2,z3,z291,z5]),(0,[z64,z1,z2,z3,z519,z5]),(0,[z1071,z2,z3,z4,z5,z6]),(0,[z64,z1,z25,z2,z3,z16])],[(0,[z64,z1,z60,z2,z3,z8]),(0,[z1,z2,z738,z4,z5,z6]),(0,[z1,z2,z3,z4,z1072,z6]),(0,[z1,z2,z3,z4,z899,z6]),(0,[z1,z25,z3,z4,z90,z6])],[(0,[z1,z2,z3,z10,z4,z163]),(0,[z64,z162,z132,z3,z4,z5]),(0,[z274,z2,z3,z4,z283,z56]),(0,[z396,z1,z2,z72,z4,z5])],[(0,[z1,z921,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z368])],[(0,[z1,z2,z3,z4,z1073,z6]),(0,[z1,z2,z3,z4,z984,z229]),(0,[z1,z2,z3,z1074,z5,z6])],[(0,[z1,z2,z3,z4,z1075,z6]),(0,[z1,z2,z3,z456,z4,z346]),(0,[z320,z2,z3,z4,z8,z6]),(0,[z2,z3,z4,z5,z54,z749]),(0,[z1076,z1,z80,z2,z3,z5])],[(0,[z1,z2,z3,z4,z5,z270]),(0,[z64,z1,z2,z3,z114,z5]),(0,[z2,z3,z4,z1077,z5,z6]),(0,[z1,z2,z3,z4,z1078,z6])],[(0,[z57,z921,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1079,z6])],[(0,[z1,z2,z3,z1080,z4,z5]),(0,[z1,z817,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z806,z42])],[(0,[z1,z2,z3,z4,z1081,z6]),(0,[z1,z2,z1082,z3,z4,z6]),(0,[z1,z2,z3,z24,z4,z245])],[(0,[z64,z1,z2,z246,z4,z5]),(0,[z175,z2,z3,z4,z387,z5])],[(0,[z1,z2,z3,z211,z5,z75]),(0,[z1,z2,z3,z1083,z4,z5]),(0,[z1,z97,z3,z4,z651,z6]),(0,[z1,z2,z1084,z3,z4,z6])],[(0,[z1,z2,z1085,z4,z5,z6]),(0,[z64,z1,z2,z3,z5,z478]),(0,[z1,z2,z298,z3,z328,z4])],[(0,[z1,z2,z3,z4,z8,z75]),(0,[z1086,z1,z2,z3,z4,z5]),(0,[z47,z2,z3,z291,z20,z6]),(0,[z64,z1,z2,z50,z3,z8]),(0,[z1,z539,z2,z4,z26,z6]),(1,[z2,z3,z4,z5,z749]),(0,[z1076,z1,z2,z3,z4,z5])]],
   [[(0,[z1,z109,z3,z4,z20,z6]),(0,[z1,z2,z4,z5,z1087,z6]),(0,[z1,z2,z3,z4,z452,z213]),(0,[z64,z1,z582,z2,z3,z5])],[(0,[z1088,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z393,z73,z6]),(0,[z1,z2,z3,z4,z263,z6]),(0,[z1,z2,z15,z4,z775,z6])],[(0,[z1,z2,z3,z1089,z5,z6]),(0,[z64,z1,z2,z3,z41,z42]),(0,[z823,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z16,z71,z181])],[(0,[z1,z2,z3,z1090,z5,z6]),(0,[z1,z2,z3,z1091,z5,z6]),(0,[z1,z2,z3,z4,z1092,z6]),(0,[z1,z2,z3,z4,z8,z1093]),(0,[z1,z2,z3,z4,z5,z1094]),(0,[z64,z1,z2,z3,z343,z5]),(0,[z1,z2,z3,z5,z788,z6]),(0,[z1,z2,z3,z4,z1095,z6])],[(0,[z1,z2,z3,z4,z1096,z6]),(0,[z85,z1,z2,z4,z5,z55])],[(0,[z1,z2,z3,z4,z1097,z6]),(0,[z1,z1003,z3,z4,z20,z6]),(0,[z1,z2,z3,z5,z1098,z6]),(0,[z1,z2,z15,z4,z41,z6])],[(0,[z1,z2,z3,z4,z5,z1099]),(0,[z1,z2,z3,z1100,z5,z6]),(0,[z1,z2,z3,z4,z20,z229]),(0,[z1,z2,z124,z4,z8,z86]),(0,[z67,z1,z2,z3,z206,z6])],[(0,[z1,z2,z3,z39,z5,z6]),(0,[z1,z2,z3,z4,z8,z280]),(0,[z1,z2,z3,z4,z1101,z6])],[(0,[z1,z2,z246,z4,z5,z75]),(0,[z599,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z265,z5,z56]),(0,[z1,z1102,z2,z3,z4,z5]),(0,[z1,z732,z3,z4,z5,z6])],[(0,[z162,z132,z3,z4,z8,z6]),(0,[z46,z2,z100,z4,z5,z6]),(0,[z1,z2,z50,z68,z5,z6]),(0,[z1,z2,z3,z4,z775,z6])],[(0,[z1,z2,z3,z1103,z5,z6]),(0,[z1,z2,z3,z1104,z4,z6]),(0,[z1,z2,z3,z4,z452,z259]),(0,[z47,z2,z3,z836,z5,z6]),(0,[z278,z1,z2,z4,z156,z5])],[(0,[z1,z2,z1105,z4,z5,z6]),(0,[z1,z2,z3,z5,z1106,z6]),(0,[z1,z2,z3,z4,z8,z218]),(0,[z1,z2,z483,z4,z26,z6]),(0,[z1,z3,z4,z193,z850,z6]),(0,[z85,z1,z2,z4,z156,z5])],[(0,[z1,z2,z3,z4,z5,z1107]),(0,[z212,z2,z3,z101,z8,z6]),(0,[z1,z2,z3,z1108,z4,z5]),(0,[z64,z1,z2,z3,z4,z121]),(0,[z1,z2,z3,z4,z1109,z6]),(0,[z1,z2,z3,z24,z235,z6])],[(0,[z1,z25,z3,z4,z345,z6]),(0,[z64,z1,z2,z3,z5,z263]),(0,[z1,z2,z3,z5,z218,z73])],[(0,[z52,z589,z83,z4,z5,z6]),(0,[z52,z2,z83,z4,z20,z6]),(0,[z1,z2,z1110,z3,z4,z6]),(0,[z1,z2,z3,z245,z73,z6])]],
   [[(0,[z212,z2,z3,z101,z358,z6]),(0,[z1111,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z1112,z6]),(0,[z1,z2,z3,z1113,z4,z6]),(0,[z9,z1,z3,z223,z96,z6]),(0,[z1,z2,z3,z4,z1114,z6])],[(0,[z1,z1115,z2,z4,z5,z6]),(0,[z1,z1116,z2,z3,z4,z5]),(0,[z64,z1,z2,z3,z108,z5])],[(0,[z1117,z1,z2,z3,z5,z6]),(0,[z244,z1,z2,z3,z165,z6]),(0,[z274,z2,z3,z4,z355,z56]),(0,[z1,z2,z3,z661,z4,z182])],[(0,[z1,z2,z3,z1118,z5,z6]),(0,[z1,z2,z3,z4,z1119,z6]),(0,[z1076,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z1120,z6]),(0,[z1,z2,z3,z4,z1121,z5]),(0,[z1,z2,z3,z137,z4,z6]),(0,[z1,z27,z3,z5,z136,z237]),(0,[z1,z2,z3,z4,z1122,z6]),(0,[z1,z2,z3,z1123,z4,z5]),(0,[z64,z1,z2,z1124,z4,z5]),(1,[z1,z2,z3,z5,z873]),(0,[z1,z2,z3,z235,z44,z6])],[(0,[z1,z2,z3,z4,z1125,z6]),(0,[z1,z2,z3,z4,z5,z1126])],[(0,[z1,z2,z3,z4,z1127,z6]),(0,[z1,z2,z3,z1128,z4,z8])],[(0,[z2,z921,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1129,z6]),(0,[z1,z2,z3,z776,z114,z5]),(0,[z1130,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z196]),(0,[z1,z14,z2,z4,z21,z6]),(0,[z1,z2,z3,z76,z168,z6])],[(0,[z1,z2,z1131,z4,z5,z6]),(0,[z64,z47,z2,z3,z291,z5]),(0,[z203,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z8,z1132]),(0,[z1,z240,z48,z10,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1133]),(0,[z1,z2,z3,z1134,z5,z6])],[(0,[z1,z2,z1135,z3,z4,z6]),(0,[z595,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z708,z6]),(0,[z1,z2,z3,z1136,z4,z6])],[(0,[z1,z2,z3,z211,z8,z6]),(0,[z1,z2,z3,z10,z39,z5])],[(0,[z1,z638,z3,z4,z98,z6])],[(0,[z1,z2,z3,z4,z1137,z6]),(0,[z64,z1,z2,z3,z314,z5]),(0,[z1,z25,z3,z4,z193,z6])],[(0,[z1,z2,z3,z1138,z5,z6]),(0,[z47,z2,z3,z291,z10,z5]),(0,[z1,z2,z3,z4,z1139,z6])],[(0,[z1,z109,z3,z114,z5,z6]),(0,[z1,z2,z3,z1140,z4,z6]),(0,[z64,z23,z1,z2,z3,z20]),(0,[z1,z2,z3,z4,z8,z189]),(0,[z1,z2,z3,z4,z5,z188]),(0,[z64,z1,z2,z3,z5,z238])],[(0,[z1,z31,z3,z4,z98,z6]),(0,[z58,z2,z3,z4,z765,z6]),(0,[z1,z2,z3,z4,z8,z181]),(0,[z1,z2,z3,z4,z1141,z6]),(0,[z64,z1,z654,z2,z3,z5]),(0,[z23,z1,z2,z407,z3,z5]),(0,[z64,z1,z2,z3,z4,z245])]],
   [[(0,[z1,z2,z3,z24,z4,z709])],[(1,[z2,z3,z836,z5,z6]),(0,[z2,z3,z4,z765,z5,z6]),(0,[z1,z60,z3,z5,z6,z301]),(0,[z1,z2,z3,z4,z5,z1142]),(0,[z1,z2,z3,z10,z4,z1139])],[(0,[z1,z2,z3,z10,z4,z5]),(0,[z1,z2,z3,z4,z5,z1143]),(1,[z64,z1,z2,z3,z393])],[(0,[z1,z2,z199,z4,z191,z6]),(0,[z1,z2,z3,z4,z1144,z6]),(0,[z665,z2,z3,z4,z20,z6]),(0,[z58,z64,z2,z3,z4,z8]),(0,[z64,z1,z2,z3,z4,z283])],[(0,[z1,z2,z246,z211,z5,z6]),(0,[z261,z64,z1,z2,z3,z42])],[(0,[z1,z2,z3,z4,z1145,z6])],[(0,[z1,z2,z246,z4,z8,z6]),(0,[z1,z109,z3,z4,z5,z284]),(0,[z1,z2,z3,z10,z20,z73])],[(0,[z1,z2,z3,z10,z4,z748])],[(0,[z1,z589,z3,z185,z5,z6]),(0,[z1,z2,z3,z185,z20,z6]),(0,[z1,z2,z3,z5,z1146,z6])],[(0,[z1,z2,z3,z10,z4,z452]),(0,[z525,z2,z3,z4,z20,z6]),(0,[z1,z2,z1147,z3,z4,z6]),(0,[z1,z14,z2,z4,z26,z6]),(0,[z1,z2,z3,z4,z140,z44])],[(0,[z64,z1,z2,z3,z70,z5])],[(0,[z64,z1,z2,z3,z185,z5]),(0,[z64,z1,z2,z3,z4,z290]),(0,[z64,z1,z2,z3,z101,z8]),(0,[z2,z3,z4,z765,z20,z6]),(0,[z64,z1,z2,z3,z10,z182])],[(0,[z1,z2,z3,z4,z227,z88])],[(0,[z52,z2,z83,z114,z5,z6]),(0,[z64,z133,z1,z2,z3,z5])],[(0,[z1,z2,z3,z4,z5,z1148]),(0,[z1,z2,z3,z412,z5,z6]),(0,[z1,z80,z49,z4,z5,z6]),(0,[z64,z1,z2,z3,z391,z5]),(0,[z64,z1,z2,z3,z5,z205]),(0,[z147,z1,z2,z124,z3,z5]),(0,[z656,z1,z3,z4,z576,z5])],[(0,[z1,z2,z1149,z4,z5,z6]),(0,[z1,z2,z3,z4,z1150,z6]),(0,[z1,z2,z3,z4,z1151,z6]),(0,[z1,z2,z3,z4,z8,z1152])]],
   [[],[(0,[z1,z2,z199,z4,z20,z6]),(0,[z23,z1,z2,z19,z8,z6]),(0,[z1,z417,z3,z4,z5,z237]),(0,[z64,z1,z2,z3,z697,z5]),(0,[z64,z1,z1153,z2,z3,z4])],[(0,[z1,z2,z3,z224,z412,z5]),(0,[z1,z2,z3,z1128,z4,z5]),(0,[z1,z2,z3,z4,z5,z1154]),(0,[z1,z1155,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1156,z4,z5]),(0,[z1,z589,z3,z4,z5,z284]),(0,[z1,z2,z3,z4,z20,z284]),(0,[z1,z2,z3,z4,z6,z1157]),(0,[z64,z1,z2,z50,z68,z5]),(0,[z64,z1,z2,z3,z5,z678]),(0,[z64,z1,z882,z3,z4,z5]),(0,[z1,z2,z3,z10,z4,z1158]),(0,[z1,z2,z3,z10,z4,z952])],[(0,[z1,z2,z3,z4,z1159,z6]),(0,[z9,z1,z285,z2,z3,z5]),(0,[z64,z9,z1,z472,z3,z5]),(0,[z1160,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1161]),(0,[z1,z2,z3,z10,z245,z73])],[],[(0,[z1,z2,z3,z4,z1162,z6])],[(0,[z64,z1,z2,z3,z108,z8]),(0,[z1,z60,z3,z222,z5,z6]),(0,[z1,z14,z2,z4,z231,z6]),(0,[z23,z1,z2,z121,z19,z6]),(0,[z1,z2,z15,z319,z4,z6])],[(0,[z541,z2,z3,z4,z20,z6]),(0,[z64,z9,z1,z3,z223,z5]),(0,[z1,z1163,z2,z3,z4,z5]),(0,[z64,z1,z2,z1164,z3,z4])],[(0,[z64,z1,z2,z3,z5,z136]),(0,[z64,z1,z2,z3,z137,z4])],[(0,[z1,z1165,z3,z4,z5,z6]),(0,[z1,z2,z1066,z4,z20,z6]),(0,[z1,z2,z3,z1166,z4,z6]),(0,[z1,z2,z3,z4,z5,z1167])],[(0,[z1,z2,z3,z4,z1168,z6]),(0,[z64,z397,z1,z2,z3,z5]),(0,[z699,z2,z3,z101,z5,z6])],[],[],[(0,[z1,z2,z3,z4,z5,z1169])],[(0,[z1,z2,z3,z1170,z4,z6]),(0,[z1,z80,z738,z4,z5,z6]),(0,[z1,z2,z3,z10,z4,z337])]],
   [[(0,[z1,z2,z3,z10,z4,z959]),(0,[z1,z2,z3,z4,z5,z1171]),(0,[z64,z1,z2,z3,z16,z139])],[(0,[z1,z2,z3,z1172,z5,z6])],[(0,[z675,z2,z3,z4,z8,z6]),(0,[z64,z1,z2,z3,z554,z5]),(0,[z1,z2,z3,z4,z1173,z5])],[(0,[z1,z2,z3,z4,z1174,z6]),(0,[z203,z2,z3,z10,z4,z20]),(0,[z1,z2,z3,z1175,z5,z6]),(0,[z1,z2,z3,z4,z1176,z6]),(0,[z1,z458,z3,z4,z98,z6]),(0,[z1,z2,z3,z5,z1177,z6]),(0,[z1,z2,z1178,z3,z4,z6])],[(0,[z64,z1,z220,z2,z3,z5]),(0,[z64,z23,z1,z2,z330,z5]),(0,[z64,z1,z462,z2,z3,z5])],[(0,[z1,z2,z3,z4,z20,z270]),(0,[z52,z109,z83,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1179]),(0,[z2,z3,z4,z836,z5,z6]),(0,[z1,z2,z3,z4,z834,z6])],[],[(0,[z1,z2,z3,z4,z452,z6]),(0,[z1,z1180,z2,z3,z4,z6]),(0,[z1,z432,z2,z4,z208,z6]),(0,[z1,z60,z3,z778,z5,z6]),(0,[z1,z2,z50,z5,z6,z381])],[(0,[z64,z1,z2,z3,z101,z5]),(0,[z1,z2,z3,z10,z4,z8]),(0,[z1,z385,z3,z4,z372,z6]),(0,[z64,z1,z2,z3,z5,z37]),(0,[z64,z1,z1181,z3,z4,z5])],[(0,[z311,z1,z2,z3,z137,z6])],[],[(0,[z1,z2,z3,z328,z4,z8]),(0,[z1,z2,z3,z1182,z5,z6]),(0,[z1,z522,z3,z4,z5,z105])],[(0,[z1,z2,z3,z10,z4,z322]),(0,[z1,z2,z3,z4,z993,z6]),(0,[z1,z2,z3,z4,z1183,z6]),(0,[z1,z2,z3,z10,z5,z873])],[(0,[z1,z2,z3,z4,z8,z61]),(0,[z110,z64,z1,z2,z3,z5])],[(0,[z64,z1,z2,z3,z315,z5]),(0,[z64,z1,z2,z3,z387,z5])],[(0,[z1,z2,z3,z4,z1184,z6]),(0,[z1,z2,z3,z4,z5,z1185]),(0,[z1,z2,z3,z4,z1186,z6]),(0,[z1,z2,z3,z176,z5,z6])]],
   [[(0,[z1,z93,z2,z3,z10,z4]),(0,[z1,z97,z3,z660,z4,z6])],[(0,[z1,z2,z3,z4,z5,z1187]),(0,[z1,z2,z3,z114,z5,z284]),(0,[z1,z2,z3,z8,z136,z6]),(0,[z1,z2,z3,z1188,z4,z6]),(0,[z1,z2,z3,z10,z4,z601]),(0,[z1,z2,z1189,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1190]),(0,[z85,z1,z2,z4,z20,z55]),(0,[z1,z2,z15,z700,z4,z6])],[(0,[z1,z2,z3,z4,z1191,z6]),(0,[z64,z1,z2,z3,z5,z61]),(0,[z1,z2,z3,z5,z73,z188]),(0,[z1,z2,z3,z4,z5,z1192])],[(0,[z64,z1,z2,z3,z438,z5]),(0,[z64,z1,z2,z3,z8,z684]),(0,[z1,z2,z3,z4,z1193,z6]),(0,[z67,z1,z2,z3,z788,z6]),(0,[z64,z1160,z2,z3,z4,z5])],[(0,[z1,z2,z3,z1194,z5,z6]),(0,[z1,z2,z3,z39,z20,z6]),(0,[z64,z1,z2,z3,z5,z218])],[(0,[z1,z2,z1195,z4,z5,z6]),(0,[z1,z2,z3,z1196,z4,z6]),(0,[z64,z2,z3,z291,z101,z5]),(0,[z1,z2,z3,z5,z136,z6]),(0,[z1,z1197,z2,z3,z4,z6])],[(0,[z57,z241,z3,z4,z5,z6]),(0,[z46,z2,z100,z4,z20,z6]),(0,[z1,z2,z50,z68,z20,z6])],[(0,[z1,z2,z3,z4,z5,z1198]),(0,[z1,z2,z3,z265,z5,z6]),(0,[z1,z362,z3,z4,z402,z6]),(0,[z1,z2,z3,z8,z168,z6]),(0,[z1,z2,z3,z4,z1199,z6])],[(0,[z1,z733,z2,z4,z8,z6]),(0,[z1,z2,z3,z4,z5,z1200]),(0,[z1,z2,z124,z4,z17,z86])],[(0,[z1,z2,z3,z1201,z5,z6]),(0,[z212,z2,z3,z10,z101,z5]),(0,[z38,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z1202,z6]),(0,[z1076,z1,z2,z3,z5,z229]),(0,[z64,z1,z2,z257,z3,z5])],[],[(0,[z1,z2,z3,z4,z1203,z6])],[(0,[z128,z2,z3,z265,z5,z54]),(0,[z1,z2,z3,z4,z1204,z6]),(0,[z1,z2,z3,z5,z168,z6]),(0,[z1,z2,z72,z4,z5,z55]),(0,[z1,z2,z3,z10,z4,z1145])],[(0,[z1,z109,z3,z185,z5,z6]),(0,[z1,z1205,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1158,z6])],[(0,[z1,z2,z3,z4,z1206,z6]),(0,[z1,z2,z3,z4,z8,z213]),(0,[z1,z2,z7,z4,z630,z6]),(0,[z1,z2,z3,z782,z4,z61])]],
   [[(0,[z12,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z1207,z6]),(0,[z1,z2,z3,z4,z290,z280]),(0,[z1,z2,z3,z10,z4,z91]),(0,[z1,z2,z3,z4,z746,z6]),(0,[z212,z2,z3,z836,z5,z6])],[(0,[z64,z1,z2,z3,z626,z5]),(0,[z1,z2,z3,z137,z136,z6]),(0,[z1,z2,z1164,z3,z4,z6])],[(0,[z212,z2,z3,z101,z30,z6]),(0,[z1,z2,z3,z4,z20,z196]),(0,[z104,z1,z3,z4,z8,z105])],[(0,[z64,z212,z2,z3,z101,z5]),(0,[z64,z1,z2,z3,z94,z5]),(0,[z1,z2,z3,z4,z1208,z6])],[(0,[z1,z240,z48,z4,z337,z6])],[(0,[z57,z64,z241,z3,z4,z5]),(0,[z1,z2,z3,z1209,z5,z6]),(0,[z1,z2,z3,z4,z1210,z6])],[(0,[z1,z2,z3,z4,z163,z6]),(0,[z1,z2,z3,z4,z1211,z6]),(0,[z1,z2,z3,z4,z5,z1212]),(0,[z9,z1,z93,z3,z223,z6]),(0,[z23,z1,z2,z19,z190,z6]),(0,[z1,z2,z68,z773,z5,z6])],[(0,[z1,z1213,z3,z4,z5,z6]),(0,[z2,z3,z4,z20,z544,z6]),(0,[z274,z2,z3,z4,z8,z56]),(0,[z1,z1214,z2,z3,z4,z6]),(0,[z1,z2,z3,z328,z4,z5]),(0,[z64,z1,z267,z2,z3,z5])],[(0,[z1,z2,z3,z4,z1215,z6]),(0,[z1,z2,z3,z1216,z4,z5])],[(0,[z1,z2,z3,z4,z8,z259])],[(0,[z1217,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z20,z188]),(0,[z1,z2,z3,z265,z597,z6]),(0,[z1,z2,z3,z4,z916,z6])],[(0,[z64,z1,z2,z3,z224,z5]),(0,[z2,z3,z291,z836,z5,z6])],[(0,[z52,z2,z83,z185,z5,z6]),(0,[z1,z2,z3,z10,z4,z96]),(0,[z1,z551,z2,z4,z5,z55])],[(0,[z1,z2,z3,z4,z5,z1218])],[(0,[z1,z2,z1219,z4,z5,z6]),(0,[z1,z589,z3,z10,z4,z5]),(0,[z1,z2,z3,z4,z20,z1143]),(0,[z1,z2,z3,z4,z5,z1220]),(0,[z64,z1,z2,z3,z5,z235])]],
   [[(0,[z1,z2,z3,z4,z1221,z6]),(0,[z1,z2,z3,z4,z337,z6]),(0,[z1,z2,z3,z4,z1222,z6])],[(0,[z1,z2,z3,z4,z5,z1223]),(0,[z1,z2,z3,z4,z91,z280]),(0,[z64,z351,z1,z2,z3,z5])],[(0,[z1,z1224,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z1225]),(0,[z1,z2,z3,z5,z1226,z6]),(0,[z1,z2,z3,z4,z1058,z6])],[(0,[z1,z2,z3,z4,z1227,z6]),(0,[z64,z1,z2,z3,z4,z355])],[],[(0,[z1,z2,z3,z4,z283,z6]),(0,[z1,z2,z3,z4,z1228,z6]),(0,[z1,z80,z49,z4,z5,z229]),(0,[z1,z2,z3,z4,z1229,z6]),(0,[z1,z2,z3,z4,z1230,z6])],[(0,[z1,z2,z3,z10,z4,z191]),(0,[z1,z2,z3,z4,z1231,z6]),(0,[z1,z2,z3,z20,z235,z6]),(0,[z128,z2,z3,z412,z5,z54]),(0,[z1,z2,z3,z4,z1232,z6]),(0,[z1,z2,z3,z4,z1233,z6]),(0,[z1,z2,z3,z5,z873,z317])],[(0,[z1,z2,z3,z4,z1234,z6]),(0,[z1,z2,z3,z1235,z4,z5]),(0,[z64,z1,z2,z3,z473,z5])],[(0,[z52,z2,z83,z4,z5,z284]),(0,[z1,z2,z3,z4,z5,z1236])],[(0,[z1,z109,z100,z4,z5,z6]),(0,[z1,z2,z3,z1237,z5,z6]),(0,[z1,z2,z3,z4,z1238,z6]),(0,[z347,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z1239,z6]),(0,[z1,z2,z3,z4,z1240,z6])],[(0,[z1,z2,z3,z4,z191,z270]),(0,[z1,z2,z3,z4,z1241,z6]),(0,[z64,z459,z2,z3,z291,z5]),(0,[z9,z1,z3,z223,z5,z6]),(0,[z1,z2,z3,z4,z1242,z6]),(0,[z1,z2,z3,z4,z5,z99])],[(0,[z1,z2,z3,z4,z1243,z6]),(0,[z1,z488,z49,z4,z5,z6]),(0,[z1,z1244,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1061,z6]),(0,[z1,z2,z3,z4,z1245,z6]),(0,[z1,z2,z3,z412,z20,z6]),(0,[z1,z80,z49,z4,z20,z6]),(0,[z1,z2,z3,z4,z405,z6]),(0,[z1,z161,z3,z4,z193,z6]),(0,[z1,z2,z3,z601,z136,z6]),(0,[z1,z2,z3,z5,z6,z1246])],[(0,[z1,z2,z3,z174,z10,z5])],[(0,[z2,z3,z4,z29,z20,z6]),(0,[z1,z803,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z1247,z6])],[(0,[z1,z2,z3,z4,z414,z6]),(0,[z1,z1248,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z783,z6])],[(0,[z1,z2,z3,z4,z5,z368])]],
   [[(0,[z1,z2,z3,z1249,z4,z5]),(0,[z1,z2,z79,z4,z323,z6]),(0,[z128,z2,z3,z4,z405,z54]),(0,[z1,z2,z298,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z1250]),(0,[z1,z2,z516,z4,z5,z86])],[(0,[z1,z2,z3,z1251,z4,z6]),(0,[z1,z2,z3,z10,z4,z190])],[(0,[z1252,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z10,z4,z393])],[(0,[z1,z2,z3,z4,z1253,z6]),(0,[z1,z2,z3,z4,z44,z127])],[(0,[z1,z2,z3,z4,z5,z1254]),(0,[z64,z1,z2,z3,z801,z5]),(0,[z1,z60,z3,z222,z20,z6]),(0,[z1,z2,z3,z412,z597,z6]),(0,[z1,z2,z3,z1255,z4,z5]),(0,[z1,z2,z3,z4,z218,z44])],[(0,[z1,z2,z3,z4,z5,z1256]),(0,[z1,z2,z3,z94,z410,z6]),(0,[z1,z2,z1257,z3,z4,z5]),(0,[z1,z2,z124,z4,z5,z809])],[(0,[z1,z2,z3,z4,z769,z6]),(0,[z197,z459,z2,z3,z4,z5])],[(0,[z128,z2,z3,z4,z387,z5]),(0,[z64,z1,z2,z3,z430,z5]),(0,[z1,z1258,z2,z3,z4,z6])],[(0,[z52,z2,z715,z4,z5,z6]),(0,[z46,z2,z100,z4,z250,z6]),(0,[z1,z240,z48,z4,z339,z6])],[(0,[z1,z2,z3,z4,z5,z75]),(0,[z1,z2,z3,z76,z10,z4])],[(0,[z1,z2,z3,z39,z191,z6]),(0,[z1,z2,z3,z4,z1259,z6]),(0,[z1,z2,z4,z20,z1087,z6]),(0,[z1,z2,z3,z16,z71,z6])],[(0,[z64,z1,z240,z48,z4,z5]),(0,[z1,z2,z407,z3,z4,z121]),(0,[z64,z1,z2,z3,z206,z5]),(0,[z64,z1,z2,z413,z3,z5])],[],[(0,[z1,z2,z4,z1011,z5,z6]),(0,[z64,z1,z458,z2,z3,z5]),(0,[z1,z2,z3,z24,z4,z130])],[(0,[z1,z2,z3,z4,z5,z1260]),(0,[z1,z2,z3,z1261,z4,z5]),(0,[z1,z2,z3,z1172,z20,z6]),(0,[z1,z2,z3,z4,z5,z1093]),(0,[z1,z2,z3,z4,z44,z181])],[(0,[z1,z2,z3,z10,z4,z30]),(0,[z1,z2,z3,z819,z8,z6]),(1,[z1076,z1,z2,z3,z5]),(0,[z1,z2,z3,z5,z42,z99]),(0,[z1,z2,z3,z4,z737,z6])]],
   [[(0,[z1,z2,z3,z20,z1098,z6]),(0,[z64,z9,z1,z2,z3,z8]),(0,[z1,z2,z3,z16,z454,z6])],[(0,[z1,z2,z3,z185,z5,z284]),(0,[z113,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z1262,z4,z6]),(0,[z1,z2,z124,z4,z5,z86])],[(0,[z1,z1263,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1264,z6])],[(0,[z1,z2,z3,z4,z1265,z6]),(0,[z1,z109,z83,z4,z5,z6]),(0,[z1,z2,z3,z4,z355,z6]),(0,[z1,z2,z3,z4,z339,z6]),(0,[z1,z2,z3,z4,z872,z6])],[(0,[z162,z132,z3,z4,z5,z6]),(0,[z1,z1266,z2,z3,z4,z5])],[(0,[z1,z132,z246,z4,z5,z6]),(0,[z1,z2,z3,z1267,z5,z6]),(0,[z64,z1,z2,z3,z158,z5]),(1,[z64,z1,z2,z3,z263])],[(0,[z1,z2,z3,z4,z5,z1268]),(0,[z57,z241,z3,z4,z191,z6]),(0,[z1,z2,z1269,z3,z4,z5]),(0,[z64,z1,z2,z3,z4,z366]),(0,[z1,z27,z472,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z218])],[(0,[z212,z2,z3,z101,z5,z6]),(0,[z1,z2,z3,z4,z1270,z6]),(0,[z64,z23,z1,z2,z3,z5]),(0,[z64,z1,z2,z1189,z4,z5])],[(0,[z1,z2,z3,z4,z1271,z6]),(0,[z1,z2,z3,z944,z185,z5]),(0,[z1,z466,z3,z4,z5,z105]),(0,[z64,z1,z2,z3,z5,z485])],[(0,[z1,z2,z3,z4,z1272,z6]),(0,[z1,z2,z3,z1273,z5,z6]),(0,[z1,z2,z3,z4,z601,z6]),(0,[z1,z27,z3,z4,z601,z237]),(0,[z1,z2,z3,z137,z10,z4]),(1,[z1,z2,z4,z5,z809]),(0,[z64,z1,z1057,z2,z3,z4])],[(0,[z1,z2,z3,z4,z1274,z6]),(0,[z1,z2,z3,z4,z1275,z6])],[(0,[z1,z2,z3,z4,z1276,z6]),(0,[z1,z240,z48,z4,z8,z6]),(0,[z64,z1,z2,z3,z8,z42]),(0,[z9,z1,z3,z223,z393,z6]),(0,[z64,z1,z2,z3,z65,z5])],[(0,[z1,z2,z3,z4,z1277,z6]),(0,[z1,z2,z3,z4,z5,z1278]),(0,[z1279,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z10,z4,z250]),(0,[z1,z2,z3,z176,z20,z6]),(0,[z2,z3,z4,z5,z749,z56])],[(0,[z1,z2,z3,z4,z1280,z6]),(0,[z1,z2,z3,z4,z1281,z6])],[(0,[z64,z1,z2,z3,z4,z414]),(0,[z64,z1,z2,z3,z4,z358]),(0,[z64,z1,z803,z2,z3,z5]),(0,[z64,z1,z2,z3,z10,z245])],[(0,[z1,z2,z3,z4,z20,z1190]),(0,[z1,z2,z3,z71,z788,z6])]],
   [[(0,[z1282,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z1283,z6]),(0,[z1,z2,z3,z10,z4,z1280])],[(0,[z1,z2,z3,z4,z5,z1132]),(0,[z64,z311,z1,z2,z3,z5]),(0,[z1,z2,z3,z497,z4,z172])],[(0,[z64,z595,z2,z3,z4,z20]),(0,[z1,z60,z3,z222,z10,z5])],[(0,[z1,z2,z3,z4,z1284,z6]),(0,[z64,z1,z2,z3,z4,z339])],[(0,[z1,z2,z3,z211,z5,z6]),(0,[z57,z241,z3,z4,z20,z6]),(0,[z1,z2,z3,z10,z4,z405])],[(0,[z1,z2,z3,z1285,z5,z6]),(0,[z1,z109,z3,z10,z4,z5]),(0,[z64,z1,z2,z3,z4,z20]),(0,[z1,z2,z3,z265,z20,z6]),(0,[z1,z2,z3,z4,z1286,z6]),(0,[z1,z1287,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z1288,z6]),(0,[z1,z2,z3,z4,z5,z1289]),(0,[z1,z27,z3,z4,z8,z237]),(0,[z64,z1,z2,z720,z4,z5])],[(0,[z1,z3,z4,z5,z1290,z6]),(0,[z1,z2,z3,z224,z4,z20]),(0,[z64,z1,z2,z3,z580,z5]),(0,[z1,z14,z2,z4,z208,z6]),(0,[z1,z2,z3,z4,z1291,z6]),(1,[z1,z3,z778,z5,z6]),(0,[z64,z1,z953,z3,z4,z5])],[(0,[z64,z46,z2,z100,z4,z5]),(0,[z1,z2,z3,z4,z1292,z6]),(0,[z2,z3,z4,z43,z8,z6]),(0,[z1,z2,z3,z265,z5,z54]),(0,[z1,z2,z3,z4,z5,z189])],[(0,[z1,z2,z3,z4,z358,z6]),(0,[z1,z2,z3,z4,z5,z181]),(0,[z1,z2,z3,z4,z182,z181]),(0,[z64,z795,z2,z3,z4,z5])],[(0,[z144,z1,z3,z4,z5,z105]),(0,[z1,z1293,z2,z3,z4,z5]),(0,[z261,z1,z2,z3,z4,z409])],[(0,[z1,z2,z3,z4,z1294,z6]),(0,[z64,z1,z2,z3,z4,z1018])],[(0,[z1,z2,z199,z4,z5,z270]),(0,[z1,z2,z3,z4,z5,z1295]),(0,[z64,z1,z2,z3,z5,z370]),(0,[z1,z2,z3,z4,z140,z245])],[(0,[z64,z9,z1,z2,z3,z5]),(0,[z64,z374,z1,z2,z3,z5])],[(0,[z1296,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z1297,z6]),(0,[z1,z2,z3,z778,z5,z6]),(0,[z64,z1,z2,z3,z98,z42])],[(0,[z1,z2,z3,z1298,z5,z6]),(0,[z1,z2,z50,z407,z3,z5])]],
   [[(0,[z1,z2,z246,z4,z5,z6]),(0,[z1022,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z1299,z4,z6]),(0,[z1,z2,z1124,z4,z5,z6])],[(0,[z1,z447,z49,z4,z5,z6]),(0,[z2,z100,z715,z4,z5,z6]),(0,[z64,z1,z2,z3,z78,z5]),(0,[z2,z3,z4,z5,z1300,z6]),(0,[z1,z285,z2,z3,z4,z172]),(0,[z64,z1,z2,z3,z5,z380])],[(0,[z311,z1,z2,z3,z601,z6]),(0,[z1,z2,z3,z10,z4,z263]),(0,[z64,z1,z2,z785,z4,z5]),(0,[z64,z1,z2,z3,z4,z982])],[(0,[z1,z2,z3,z291,z5,z213]),(0,[z1,z2,z3,z10,z4,z1073]),(0,[z64,z1,z575,z2,z3,z5])],[(0,[z1,z240,z672,z4,z5,z6]),(0,[z52,z2,z83,z10,z4,z5]),(0,[z1,z2,z3,z4,z172,z6]),(0,[z64,z1,z2,z3,z574,z5]),(0,[z64,z1,z2,z3,z16,z71])],[(0,[z1,z2,z3,z4,z384,z6]),(0,[z1,z2,z3,z1301,z5,z6]),(0,[z64,z1,z2,z3,z291,z20]),(0,[z64,z9,z1,z2,z3,z96]),(0,[z1,z2,z3,z4,z1302,z6]),(1,[z1,z2,z773,z5,z6]),(0,[z1,z2,z50,z68,z5,z188])],[(0,[z1,z1303,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1304,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1305]),(0,[z1,z25,z3,z10,z4,z193]),(0,[z1,z2,z50,z68,z10,z5])],[(0,[z1,z2,z3,z1306,z5,z6]),(0,[z1,z2,z3,z4,z5,z1152])],[(0,[z1,z2,z3,z176,z10,z5])],[(0,[z9,z1,z3,z497,z223,z5]),(0,[z23,z1,z2,z19,z5,z6]),(0,[z1,z2,z3,z263,z73,z6]),(0,[z217,z64,z1,z2,z3,z5])],[(0,[z1,z2,z199,z39,z5,z6]),(0,[z1,z2,z3,z4,z6,z1307])],[(0,[z64,z23,z1,z2,z3,z8]),(0,[z492,z2,z3,z4,z5,z54]),(0,[z1,z2,z1308,z4,z5,z6])],[(0,[z2,z3,z4,z20,z296,z6]),(0,[z656,z311,z1,z2,z3,z5])],[(0,[z1,z2,z3,z1309,z4,z5]),(0,[z1,z2,z3,z4,z20,z1225]),(0,[z311,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z4,z5,z1310]),(0,[z1,z2,z298,z407,z3,z4])]],
   [[(0,[z1,z1153,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z1311,z6])],[(0,[z1,z2,z3,z879,z4,z5]),(0,[z1312,z1,z2,z3,z4,z5]),(0,[z147,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z4,z5,z1313]),(0,[z1,z2,z3,z4,z1314,z6]),(0,[z63,z595,z2,z3,z4,z5]),(0,[z64,z1,z2,z3,z5,z245])],[(1,[z921,z3,z4,z5,z6]),(0,[z1,z2,z3,z265,z10,z5]),(0,[z1,z2,z3,z10,z4,z532]),(0,[z64,z23,z1,z2,z72,z5]),(0,[z1,z2,z3,z4,z182,z44]),(0,[z1,z2,z3,z4,z1315,z6])],[(0,[z1,z2,z3,z1316,z5,z6]),(0,[z702,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z1136,z4,z188]),(0,[z1,z14,z2,z4,z775,z6]),(0,[z1,z2,z3,z4,z1317,z6])],[(0,[z1,z2,z3,z4,z1318,z6]),(0,[z1,z27,z3,z4,z5,z758]),(0,[z1,z1181,z3,z4,z5,z6])],[(0,[z1,z2,z407,z3,z101,z5]),(0,[z64,z1,z202,z2,z3,z5]),(0,[z1,z2,z3,z4,z1319,z6]),(0,[z1,z2,z3,z10,z4,z1031])],[(0,[z9,z1,z3,z223,z20,z6]),(0,[z1,z2,z3,z4,z20,z99]),(0,[z1,z2,z3,z4,z1320,z6]),(0,[z1,z2,z3,z10,z5,z168])],[(0,[z57,z241,z199,z4,z5,z6]),(0,[z1,z2,z3,z4,z191,z75]),(0,[z104,z1,z3,z4,z576,z5])],[(0,[z64,z1,z109,z3,z4,z5]),(0,[z187,z1,z2,z3,z4,z20]),(0,[z1,z285,z2,z3,z101,z5]),(0,[z47,z2,z3,z291,z452,z6]),(0,[z1,z2,z3,z1321,z4,z6])],[(0,[z64,z9,z1,z2,z3,z393]),(0,[z1,z2,z3,z4,z1322,z6]),(0,[z64,z1,z2,z3,z180,z5])],[(0,[z1,z2,z3,z4,z5,z1323]),(0,[z1,z2,z3,z4,z1324,z6])],[(0,[z1,z2,z3,z4,z20,z368]),(0,[z1,z2,z3,z4,z5,z1325])],[(0,[z1,z2,z3,z4,z1326,z6]),(0,[z1,z2,z3,z4,z788,z6]),(0,[z1,z2,z3,z16,z409,z6])],[],[(0,[z677,z2,z100,z4,z5,z6]),(0,[z64,z1,z2,z3,z4,z1294])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 500) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 500).take 500) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1000).take 404) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1404)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [500, 500, 404] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 155).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 155).take 146).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 301).take 145).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 446).take 66).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [155, 146, 145, 66] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_40431

theorem PEqualNP.Outside.L_meta_40431 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4240501952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4240501952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_40431.solve