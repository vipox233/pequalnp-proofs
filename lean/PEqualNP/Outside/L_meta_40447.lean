import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40447

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
  Nat.testBit (4276809448 * 2 ^ 32 + 4276145344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x1002c8c6e238ecc8#64 ++ 0x21002c8c6e238ecc#64 ++ 0x704fd9cfe279eccf#64 ++ 0xd704fd9cfe279ecc#64 : BitVec 256),
   (0x00960211428a0550#64 ++ 0x400960211428a055#64 ++ 0xd1b62631c38e3fff#64 ++ 0xbd1b62631c38e3ff#64 : BitVec 256),
   (0x0628382a2c0570a2#64 ++ 0x80628382a2c0570a#64 ++ 0xee38383e3c0ff0fb#64 ++ 0x7ee38383e3c0ff0f#64 : BitVec 256),
   (0x0b403d4035503a03#64 ++ 0x00b403d4035503a0#64 ++ 0xbfc03fc03ff03f0e#64 ++ 0xfbfc03fc03ff03f0#64 : BitVec 256),
   (0x2dff40001bef800c#64 ++ 0x02dff40001bef800#64 ++ 0xbfffc0003fffc009#64 ++ 0xfbfffc0003fffc00#64 : BitVec 256),
   (0x4ffdb7bd80000000#64 ++ 0x04ffdb7bd8000000#64 ++ 0x4fffffffc0000007#64 ++ 0xf4fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [6, 9]⟩, ⟨.or, [10, 1]⟩, ⟨.or, [6, 9]⟩, ⟨.and, [8, 4]⟩, ⟨.or, [11, 13]⟩, ⟨.and, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00960211428a0550 0x400960211428a055 0xd1b62631c38e3fff 0xbd1b62631c38e3ff

def z1 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xee38383e3c0ff0fb 0x7ee38383e3c0ff0f

def z2 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0xbfc03fc03ff03f0e 0xfbfc03fc03ff03f0

def z3 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x704fd9cfe279eccf 0xd704fd9cfe279ecc

def z4 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xbfffc0003fffc009 0xfbfffc0003fffc00

def z5 : W := mkw 0x4f69b5ac80000000 0x04f69b5ac8000000 0x4e79f9fe00000003 0x74e79f9fe0000000

def z6 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x4fffffffc0000007 0xf4fffffffc000000

def z7 : W := mkw 0x00960211428a0550 0x400960211428a055 0x40360031c00e00f1 0x040360031c00e00f

def z8 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0x2e4019c03c700000 0x42e4019c03c70000

def z9 : W := mkw 0x0002000042080440 0x0000200004208044 0x50060001c2082ccf 0x950060001c2082cc

def z10 : W := mkw 0x100248426238ecc8 0x2100248426238ecc 0x300000002279ecc8 0x0300000002279ecc

def z11 : W := mkw 0x0428000008050000 0x0042800000805000 0xae3800003c0fc009 0x7ae3800003c0fc00

def z12 : W := mkw 0x2fff782a3feff0ae 0x82fff782a3feff0a 0xfffff83e3ffff0fb 0xffffff83e3ffff0f

def z13 : W := mkw 0x0b40350000000000 0x00b4035000000000 0x0fc03fc000000006 0xf0fc03fc00000000

def z14 : W := mkw 0x4ffdbffdb5503a03 0x04ffdbffdb5503a0 0xfffffffffff03f0f 0xffffffffffff03f0

def z15 : W := mkw 0x0dfd000000000000 0x00dfd00000000000 0x0fffc00000000001 0xf0fffc0000000000

def z16 : W := mkw 0x6ffff7bd9bef800c 0x06ffff7bd9bef800 0xffffffffffffc00f 0xfffffffffffffc00

def z17 : W := mkw 0x2d6940001965800c 0x02d6940001965800 0xbfc9c0003ff1c008 0xfbfc9c0003ff1c00

def z18 : W := mkw 0x1002c0c4c2388c48 0x21002c0c4c2388c4 0x1047c1c1c2700c04 0x81047c1c1c2700c0

def z19 : W := mkw 0x1096cad7e2baedd8 0x61096cad7e2baedd 0xf1ffffffe3ffffff 0xff1ffffffe3fffff

def z20 : W := mkw 0x1096c297c2aac5d8 0x61096c297c2aac5d 0x403fc03fc00fc0f1 0x0403fc03fc00fc0f

def z21 : W := mkw 0x2dff42115bef855c 0x42dff42115bef855 0xffffe631ffffffff 0xfffffe631fffffff

def z22 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xae08180e3c0ff0f8 0x4ae08180e3c0ff0f

def z23 : W := mkw 0x4bd5bfd5b5503a03 0x04bd5bfd5b5503a0 0xbfc7ffc1fff03f0e 0xfbfc7ffc1fff03f0

def z24 : W := mkw 0x06be3a3b6e8f75f2 0xc06be3a3b6e8f75f 0xffbe3e3fff8fffff 0xfffbe3e3fff8ffff

def z25 : W := mkw 0x44bd82bd80000000 0x044bd82bd8000000 0x403fc03fc0000001 0x0403fc03fc000000

def z26 : W := mkw 0x0000021140000550 0x4000002114000055 0x40002631c0003ff6 0x040002631c0003ff

def z27 : W := mkw 0x2d6940001965800c 0x02d6940001965800 0x2e49c0003c71c000 0x42e49c0003c71c00

def z28 : W := mkw 0x0f683d6a3d557aa3 0x80f683d6a3d557aa 0xfff83ffe3fffffff 0xffff83ffe3ffffff

def z29 : W := mkw 0x1b42fdc6f778fecb 0x21b42fdc6f778fec 0xffcfffcffff9ffcf 0xfffcfffcffff9ffc

def z30 : W := mkw 0x0b40350000000000 0x00b4035000000000 0x0f80260000000000 0x20f8026000000000

def z31 : W := mkw 0x0940000011400000 0x0094000001140000 0xbfc000003ff00008 0xfbfc000003ff0000

def z32 : W := mkw 0x24bf40000aaf800c 0x024bf40000aaf800 0x003fc000000fc001 0x0003fc000000fc00

def z33 : W := mkw 0x54bfcaffe238ecc8 0x254bfcaffe238ecc 0x707fd9ffe279eccf 0xd707fd9ffe279ecc

def z34 : W := mkw 0x00960211028a0110 0x400960211028a011 0x91b62630038e1339 0xb91b62630038e133

def z35 : W := mkw 0x0002084062182c40 0x00002084062182c4 0x704619c1e2782ccf 0xd704619c1e2782cc

def z36 : W := mkw 0x0094021100000000 0x0009402110000000 0x01b0263000000000 0x201b026300000000

def z37 : W := mkw 0x0940054011500a01 0x00940054011500a0 0x11c007c003f00f04 0x811c007c003f00f0

def z38 : W := mkw 0x0940054011500a01 0x00940054011500a0 0xbfc007c03ff00f0c 0xfbfc007c03ff00f0

def z39 : W := mkw 0x1b40fdc6b570fa8b 0x21b40fdc6b570fa8 0x2e49d9ce3c71c000 0x42e49d9ce3c71c00

def z40 : W := mkw 0x4ffdb7bd80820110 0x44ffdb7bd8082011 0xcfffffffc1861337 0xfcfffffffc186133

def z41 : W := mkw 0x2dff00001bcf0004 0x02dff00001bcf000 0x9fb600001f8e0009 0xb9fb600001f8e000

def z42 : W := mkw 0x06283a3b6c0575f2 0xc06283a3b6c0575f 0xee383e3ffc0fffff 0x7ee383e3ffc0ffff

def z43 : W := mkw 0x02003d4024103a03 0x002003d4024103a0 0x00003fc000003f06 0x000003fc000003f0

def z44 : W := mkw 0x0428002a080540a0 0x80428002a080540a 0xee38003e3c0fc0f9 0x7ee38003e3c0fc0f

def z45 : W := mkw 0x0094021140820550 0x4009402114082055 0xc1b02631c1863ff6 0x2c1b02631c1863ff

def z46 : W := mkw 0x02003d4024103a03 0x002003d4024103a0 0x30403fc022703f0e 0xd30403fc022703f0

def z47 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x4e7fd9ffc0000001 0x44e7fd9ffc000000

def z48 : W := mkw 0x4ffdbfbda4003002 0x04ffdbfbda400300 0xeffffffffc00300f 0xfeffffffffc00300

def z49 : W := mkw 0x0428002a080540a0 0x80428002a080540a 0x4038003e000fc0f1 0x04038003e000fc0f

def z50 : W := mkw 0x29d7400013ea800c 0x029d7400013ea800 0x11c7c00003f00000 0x811c7c00003f0000

def z51 : W := mkw 0x4ffd3f7935503a03 0x04ffd3f7935503a0 0xbff03ff03ff03f0e 0xfbff03ff03ff03f0

def z52 : W := mkw 0x0200382a2c0570a2 0x80200382a2c0570a 0xe000383e3c0ff0fa 0x0e000383e3c0ff0f

def z53 : W := mkw 0x0000000000000000 0x0000000000000000 0x9180260003803f0e 0xb9180260003803f0

def z54 : W := mkw 0x2dff40005bef844c 0x02dff40005bef844 0xffffc001ffffeccf 0xfffffc001ffffecc

def z55 : W := mkw 0x2d69000019450004 0x02d6900001945000 0x0e0000001c000000 0x00e0000001c00000

def z56 : W := mkw 0x4ffdbfbfac0570a2 0x84ffdbfbfac0570a 0xeffffffffc0ff0ff 0xfeffffffffc0ff0f

def z57 : W := mkw 0x4fffb7bdc28a0550 0x44fffb7bdc28a055 0xdfffffffc38e3fff 0xfdfffffffc38e3ff

def z58 : W := mkw 0x2fff7d6a3ffffaaf 0x82fff7d6a3ffffaa 0xfffffffe3fffffff 0xffffffffe3ffffff

def z59 : W := mkw 0x062830280c051022 0x8062830280c05102 0x8e3020301c061030 0x28e3020301c06103

def z60 : W := mkw 0x0bd63f5177da3f53 0x40bd63f5177da3f5 0xfff63ff1fffe3fff 0xffff63ff1fffe3ff

def z61 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z62 : W := mkw 0x0f683d683d553a23 0x80f683d683d553a2 0xbff03ff03ff63f3e 0xfbff03ff03ff63f3

def z63 : W := mkw 0x1000c8c6a030e888 0x21000c8c6a030e88 0x2049d9ce2071c000 0x42049d9ce2071c00

def z64 : W := mkw 0x0200382a240070a2 0x80200382a240070a 0x4000383e000030f2 0x04000383e000030f

def z65 : W := mkw 0x0428000000000000 0x0042800000000000 0x0e38000000000001 0x70e3800000000000

def z66 : W := mkw 0x46bdb7bd80000000 0x046bdb7bd8000000 0x403fffffc0000007 0x0403fffffc000000

def z67 : W := mkw 0x29d7454013fa8a0d 0x029d7454013fa8a0 0x11c7c7c003f00f04 0x811c7c7c003f00f0

def z68 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0xcfffffffc00e30ff 0xfcfffffffc00e30f

def z69 : W := mkw 0x00960000028a0000 0x000960000028a000 0x1186000003800000 0x8118600000380000

def z70 : W := mkw 0x1000c8c6e030ecc8 0x21000c8c6e030ecc 0x6049d9cfe071ecc6 0x46049d9cfe071ecc

def z71 : W := mkw 0x3dffc8c6fbffeccc 0x23dffc8c6fbffecc 0xffffd9cfffffeccf 0xfffffd9cfffffecc

def z72 : W := mkw 0x0628302800000000 0x0062830280000000 0x4e38383e00000003 0x74e38383e0000000

def z73 : W := mkw 0x0000808480000000 0x0000080848000000 0x404fd9cfc0000007 0xd404fd9cfc000000

def z74 : W := mkw 0x0b40bdc4b5503a03 0x00b40bdc4b5503a0 0xffcfffcffff03f0f 0xfffcfffcffff03f0

def z75 : W := mkw 0x00960211428a0550 0x400960211428a055 0x91b02630038e3ff8 0x291b02630038e3ff

def z76 : W := mkw 0x0000084020102800 0x0000008402010280 0x304019c022702c0e 0xd304019c022702c0

def z77 : W := mkw 0x4f69b5ac80000000 0x04f69b5ac8000000 0x0e49d9ce00000000 0x40e49d9ce0000000

def z78 : W := mkw 0x0f683d6a3d557aa3 0x80f683d6a3d557aa 0xbfc83fce3ff1ff0e 0xfbfc83fce3ff1ff0

def z79 : W := mkw 0x100088c6e0106cc0 0x2100088c6e0106cc 0x400019cfc0002cc6 0x0400019cfc0002cc

def z80 : W := mkw 0x0b40350015401203 0x00b4035001540120 0x8f8026001d801300 0x28f8026001d80130

def z81 : W := mkw 0x0628386a2c1578a2 0x80628386a2c1578a 0xfe7839fe3e7ffcff 0xffe7839fe3e7ffcf

def z82 : W := mkw 0x100240024228c4c8 0x2100240024228c4c 0x000000000009c0c0 0x0000000000009c0c

def z83 : W := mkw 0x4b40bffdb5503a03 0x04b40bffdb5503a0 0xffc03ffffff03f0e 0xfffc03ffffff03f0

def z84 : W := mkw 0x2dff42115bef855c 0x42dff42115bef855 0xbfffc601ffffcf0d 0xfbfffc601ffffcf0

def z85 : W := mkw 0x2fff7f517fffbf5f 0x42fff7f517fffbf5 0xfffffff1ffffffff 0xffffffff1fffffff

def z86 : W := mkw 0x4ffdb7bd95401203 0x04ffdb7bd9540120 0xcfffffffdd801307 0xfcfffffffdd80130

def z87 : W := mkw 0x00020000428a0550 0x400020000428a055 0x90000000038e3ff8 0x090000000038e3ff

def z88 : W := mkw 0x200248403fffba0f 0x0200248403fffba0 0xb00000003fffff08 0x0b00000003fffff0

def z89 : W := mkw 0x2dfd000019c70004 0x02dfd000019c7000 0x8fb000001d860000 0x28fb000001d86000

def z90 : W := mkw 0x0000084020102800 0x0000008402010280 0x3000000022702c08 0x03000000022702c0

def z91 : W := mkw 0x0094021100000000 0x0009402110000000 0x41b62631c0000007 0xb41b62631c000000

def z92 : W := mkw 0x4ffff7bd82288008 0x04ffff7bd8228800 0x7fffffffe279c00f 0xf7fffffffe279c00

def z93 : W := mkw 0x0002400002288008 0x0000240000228800 0x304fc0002279c009 0xd304fc0002279c00

def z94 : W := mkw 0x2dfd400019e7800c 0x02dfd400019e7800 0xaff9c0003df7c000 0x6aff9c0003df7c00

def z95 : W := mkw 0x0200380024003002 0x0020038002400300 0xae0038003c00300a 0x7ae0038003c00300

def z96 : W := mkw 0x0094021100820110 0x4009402110082011 0x81b0263001861330 0x281b026300186133

def z97 : W := mkw 0x1002c086c228c4c8 0x21002c086c228c4c 0x400fc00fc009c0c1 0x0400fc00fc009c0c

def z98 : W := mkw 0x0000080220006080 0x0000008022000608 0x6008180e2009e0cb 0x56008180e2009e0c

def z99 : W := mkw 0x0200382a240070a2 0x80200382a240070a 0xee00383e3c0030fa 0x7ee00383e3c0030f

def z100 : W := mkw 0x0000808480000000 0x0000080848000000 0x400fc00fc0000001 0x0400fc00fc000000

def z101 : W := mkw 0x0628382a20006080 0x00628382a2000608 0x6e38383e2009e0cb 0x76e38383e2009e0c

def z102 : W := mkw 0x00960211428a0550 0x400960211428a055 0x11860601c3800f04 0x811860601c3800f0

def z103 : W := mkw 0x0000021100000000 0x0000002110000000 0x40002631c0000006 0x040002631c000000

def z104 : W := mkw 0x04be02114a8f0550 0x404be02114a8f055 0xffbe2631ff8fffff 0xfffbe2631ff8ffff

def z105 : W := mkw 0x0b40354011500a01 0x00b40354011500a0 0x1fc03fc003f00f06 0xf1fc03fc003f00f0

def z106 : W := mkw 0x0000084035503a03 0x00000084035503a0 0xb00000003ff03f08 0x0b00000003ff03f0

def z107 : W := mkw 0x1000c0c480308808 0x21000c0c48030880 0x0041c1c000700000 0x00041c1c00070000

def z108 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xae38180e3c0fc009 0x7ae38180e3c0fc00

def z109 : W := mkw 0x29d7421153ea855c 0x429d7421153ea855 0xd1f7e631c3fe3fff 0xbd1f7e631c3fe3ff

def z110 : W := mkw 0x00960a51629a2d50 0x400960a51629a2d5 0xf1f63ff1e3fe3fff 0xff1f63ff1e3fe3ff

def z111 : W := mkw 0x162af8eeee3dfcea 0xa162af8eeee3dfce 0xfe7ff9fffe7ffcff 0xffe7ff9fffe7ffcf

def z112 : W := mkw 0x0940000011400000 0x0094000001140000 0x11c0000003f00000 0x811c0000003f0000

def z113 : W := mkw 0x4fffb7bd828a0000 0x04fffb7bd828a000 0xdfffffffc38e000f 0xfdfffffffc38e000

def z114 : W := mkw 0x2fff78003fefb00e 0x02fff78003fefb00 0xbffff8003ffff00b 0xfbffff8003ffff00

def z115 : W := mkw 0x46bdb2bd80000000 0x046bdb2bd8000000 0x4e3ff83fc0000003 0x74e3ff83fc000000

def z116 : W := mkw 0x24bf40000aaf800c 0x024bf40000aaf800 0x307fc000227fc009 0xd307fc000227fc00

def z117 : W := mkw 0x0dfd000011400000 0x00dfd00001140000 0xbfffc0003ff00009 0xfbfffc0003ff0000

def z118 : W := mkw 0x0000000000000000 0x0000000000000000 0x8030203000061030 0x2803020300006103

def z119 : W := mkw 0x4ffdbfbfac0570a2 0x84ffdbfbfac0570a 0x6ffffffffc01c007 0xf6ffffffffc01c00

def z120 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0x3e4019c03e702c0e 0xd3e4019c03e702c0

def z121 : W := mkw 0x242940000825800c 0x0242940000825800 0x0009c0000001c000 0x00009c0000001c00

def z122 : W := mkw 0x000008022c0570a2 0x8000008022c0570a 0xe03020303c0ff0fb 0x3e03020303c0ff0f

def z123 : W := mkw 0x062a782a2e2df0aa 0x8062a782a2e2df0a 0xfe7ff83e3e7ff0fb 0xffe7ff83e3e7ff0f

def z124 : W := mkw 0x4ffd373900000000 0x04ffd37390000000 0x0fb0263000000000 0x20fb026300000000

def z125 : W := mkw 0x0000000000000000 0x0000000000000000 0x80300000000e0009 0x380300000000e000

def z126 : W := mkw 0x00020211428a0550 0x400020211428a055 0xd0002631c38e3ffe 0x0d0002631c38e3ff

def z127 : W := mkw 0x0000021140000550 0x4000002114000055 0x00000601c0000f04 0x000000601c0000f0

def z128 : W := mkw 0x0b403d423d557aa3 0x80b403d423d557aa 0xbfc03fc03ffffffe 0xfbfc03fc03ffffff

def z129 : W := mkw 0x0000808480000000 0x0000080848000000 0x400019cfc0000006 0x0400019cfc000000

def z130 : W := mkw 0x0d68000019450000 0x00d6800001945000 0xbff800003fffc009 0xfbff800003fffc00

def z131 : W := mkw 0x64bfc2bd8aaf800c 0x064bfc2bd8aaf800 0x403fc03fc00fc001 0x0403fc03fc00fc00

def z132 : W := mkw 0x4fffbfbfee8f75f2 0xc4fffbfbfee8f75f 0xffffffffff8fffff 0xfffffffffff8ffff

def z133 : W := mkw 0x06be382a2e8f70a2 0x806be382a2e8f70a 0xffbe383e3f8ff0fb 0xfffbe383e3f8ff0f

def z134 : W := mkw 0x100080c4c0100c40 0x2100080c4c0100c4 0x000001c1c0000c04 0x0000001c1c0000c0

def z135 : W := mkw 0x100088c6a0106880 0x2100088c6a010688 0x000019ce00000000 0x0000019ce0000000

def z136 : W := mkw 0x0bd43f5135503a03 0x00bd43f5135503a0 0xfff63ff1fff03f0f 0xffff63ff1fff03f0

def z137 : W := mkw 0x0000000000000000 0x0000000000000000 0xd1b02630038e3fff 0xbd1b02630038e3ff

def z138 : W := mkw 0x00000002080540a0 0x800000002080540a 0x00000000000fc0f0 0x000000000000fc0f

def z139 : W := mkw 0x0ffd350000000000 0x00ffd35000000000 0x0fffffc000000007 0xf0fffffc00000000

def z140 : W := mkw 0x0000000000000000 0x0000000000000000 0x40300030000e00f1 0x040300030000e00f

def z141 : W := mkw 0x0942400013688008 0x0094240001368800 0xbfcfc0003ff9c009 0xfbfcfc0003ff9c00

def z142 : W := mkw 0x2fff75001fef920f 0x02fff75001fef920 0xbfffe6003fffd309 0xfbfffe6003fffd30

def z143 : W := mkw 0x29d7400013ea800c 0x029d7400013ea800 0x91f7c00003fe0009 0xb91f7c00003fe000

def z144 : W := mkw 0x0000808480000000 0x0000080848000000 0x0049d9ce00000000 0x40049d9ce0000000

def z145 : W := mkw 0x4200bffda4103a03 0x04200bffda4103a0 0x40003fffc0003f06 0x040003fffc0003f0

def z146 : W := mkw 0x0000080220006080 0x0000008022000608 0x200000002009e0c8 0x0200000002009e0c

def z147 : W := mkw 0x0bd63d4037da3a03 0x00bd63d4037da3a0 0xbff63fc03ffe3f0f 0xfbff63fc03ffe3f0

def z148 : W := mkw 0x200240001bef800c 0x0200240001bef800 0xb00000003fffc008 0x0b00000003fffc00

def z149 : W := mkw 0x4200b7bd80000000 0x04200b7bd8000000 0x40003fffc0000006 0x040003fffc000000

def z150 : W := mkw 0x294140001160800c 0x0294140001160800 0x0041c00000700000 0x00041c0000070000

def z151 : W := mkw 0x49d5879580000000 0x049d587958000000 0x01c7c7c1c0000004 0x801c7c7c1c000000

def z152 : W := mkw 0x06bc323900000000 0x006bc32390000000 0x4fbe3e3fc0000007 0xf4fbe3e3fc000000

def z153 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0x2e08180e3c01c000 0x42e08180e3c01c00

def z154 : W := mkw 0x0200384024103802 0x0020038402410380 0xbe4039c03e703c0e 0xfbe4039c03e703c0

def z155 : W := mkw 0x0094021100820110 0x4009402110082011 0xc1b62631c1861337 0xbc1b62631c186133

def z156 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0302030000e30fb 0x3c0302030000e30f

def z157 : W := mkw 0x1b42fdc4f778be4b 0x21b42fdc4f778be4 0xbfc7ffc1fff03f0e 0xfbfc7ffc1fff03f0

def z158 : W := mkw 0x4dfd879580000000 0x04dfd87958000000 0x0fffc7c1c0000005 0xf0fffc7c1c000000

def z159 : W := mkw 0x0628302a0c0550a2 0x80628302a0c0550a 0xce38203e1c0fd0f1 0x2ce38203e1c0fd0f

def z160 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xbfb000003fffc008 0x2bfb000003fffc00

def z161 : W := mkw 0x0096421142aa8558 0x40096421142aa855 0xf1ffe631e3ffffff 0xff1ffe631e3fffff

def z162 : W := mkw 0x0000000000000000 0x0000000000000000 0x4008180e00000003 0x54008180e0000000

def z163 : W := mkw 0x5fffffffe238ecc8 0x25fffffffe238ecc 0x7fffffffe279eccf 0xf7fffffffe279ecc

def z164 : W := mkw 0x1202f8c6e638fcca 0x21202f8c6e638fcc 0xfe4ff9cffe79fccf 0xffe4ff9cffe79fcc

def z165 : W := mkw 0x4f69bdaeac0570a2 0x84f69bdaeac0570a 0x2e49d9ce3c01c000 0x42e49d9ce3c01c00

def z166 : W := mkw 0x1000084260106cc0 0x21000084260106cc 0x0000000000002cc0 0x00000000000002cc

def z167 : W := mkw 0x1096cad7e2baedd8 0x61096cad7e2baedd 0x71cfdfcfe3f9efcf 0xd71cfdfcfe3f9efc

def z168 : W := mkw 0x49d5879580000000 0x049d587958000000 0x41f7e7f1c0000007 0xb41f7e7f1c000000

def z169 : W := mkw 0x02003f5164103f53 0x402003f5164103f5 0x40003ff1c0003ff6 0x040003ff1c0003ff

def z170 : W := mkw 0x0200382a240070a2 0x80200382a240070a 0x0000180e00000000 0x00000180e0000000

def z171 : W := mkw 0x2ffd382a3dc770a6 0x82ffd382a3dc770a 0xefb8383e3d8ff0fb 0x7efb8383e3d8ff0f

def z172 : W := mkw 0x00020802620864c0 0x000020802620864c 0x700e180fe209eccf 0xd700e180fe209ecc

def z173 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0xf1cfffcfe3f9ffcf 0xff1cfffcfe3f9ffc

def z174 : W := mkw 0x0dfd021100000000 0x00dfd02110000000 0x4fffe631c0000007 0xf4fffe631c000000

def z175 : W := mkw 0x6ffff5ac9bef800c 0x06ffff5ac9bef800 0xbfffd9ce3fffc009 0xfbfffd9ce3fffc00

def z176 : W := mkw 0x29d7400013ea800c 0x029d7400013ea800 0xbfc7c0003ff00008 0xfbfc7c0003ff0000

def z177 : W := mkw 0x2dfd021119c70114 0x42dfd021119c7011 0x8fb026301d861330 0x28fb026301d86133

def z178 : W := mkw 0x0b403d6a35507aa3 0x80b403d6a35507aa 0xffc03ffe3ff03ffe 0xfffc03ffe3ff03ff

def z179 : W := mkw 0x06283d6a2c157aa3 0x806283d6a2c157aa 0xee383ffe3c0fffff 0x7ee383ffe3c0ffff

def z180 : W := mkw 0x00960211428a0550 0x400960211428a055 0x41b62631c00e00f7 0xb41b62631c00e00f

def z181 : W := mkw 0x0000808480000000 0x0000080848000000 0x0047c1c1c0000004 0x80047c1c1c000000

def z182 : W := mkw 0x09400d4035503a03 0x009400d4035503a0 0xb1c007c03ff03f0c 0x8b1c007c03ff03f0

def z183 : W := mkw 0x34bfc086caafc4cc 0x234bfc086caafc4c 0x403fc00fc00fc0c1 0x0403fc00fc00fc0c

def z184 : W := mkw 0x0b40350015401203 0x00b4035001540120 0xbfc026003ff01308 0xfbfc026003ff0130

def z185 : W := mkw 0x0096021142080440 0x0009602114208044 0x51b62631c2082ccf 0xb51b62631c2082cc

def z186 : W := mkw 0x5f69fdeea030e888 0x25f69fdeea030e88 0x2e49d9ce2071c000 0x42e49d9ce2071c00

def z187 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000260000003f06 0x00000260000003f0

def z188 : W := mkw 0x0b423d4077583e43 0x00b423d4077583e4 0xffc63fc1fff83fcf 0xfffc63fc1fff83fc

def z189 : W := mkw 0x4ffdb7bd8c051022 0x84ffdb7bd8c05102 0xcfffffffdc061037 0xfcfffffffdc06103

def z190 : W := mkw 0x0b403d4020102800 0x00b403d402010280 0x3fc03fc022702c0e 0xf3fc03fc022702c0

def z191 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0x3fc01fc03ff00f04 0xc3fc01fc03ff00f0

def z192 : W := mkw 0x2000000019c70004 0x02000000019c7000 0x800000001d860000 0x0800000001d86000

def z193 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0x3fcfc0003ff1c000 0xc3fcfc0003ff1c00

def z194 : W := mkw 0x1002c0c4c2388c48 0x21002c0c4c2388c4 0x5047c1c1c2782ccf 0x95047c1c1c2782cc

def z195 : W := mkw 0x0200302804001022 0x8020030280400102 0x0000203000001030 0x0000020300000103

def z196 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0x6e08383e3c01f0f2 0x46e08383e3c01f0f

def z197 : W := mkw 0x3d6bc8c6fb7deccc 0x23d6bc8c6fb7decc 0x7e4fd9cffe79eccf 0xd7e4fd9cffe79ecc

def z198 : W := mkw 0x2fff70281fef902e 0x82fff70281fef902 0xbfffe0303fffd039 0xfbfffe0303fffd03

def z199 : W := mkw 0x4bd5b7bd80000000 0x04bd5b7bd8000000 0x41c7ffffc0000006 0x841c7ffffc000000

def z200 : W := mkw 0x24bf40001bef800c 0x024bf40001bef800 0xb03fc0003fffc009 0x0b03fc0003fffc00

def z201 : W := mkw 0x0094021100820110 0x4009402110082011 0xc1b02630018e33fb 0x3c1b02630018e33f

def z202 : W := mkw 0x44bd82bd80000000 0x044bd82bd8000000 0x407fd9ffc0000007 0xd407fd9ffc000000

def z203 : W := mkw 0x2fff7d403fffba0f 0x02fff7d403fffba0 0xbfffffc03fffff0f 0xfbfffffc03fffff0

def z204 : W := mkw 0x0000000000000000 0x0000000000000000 0x40060001c0000007 0x940060001c000000

def z205 : W := mkw 0x6ffd373919c70004 0x06ffd373919c7000 0x8fb026301d860000 0x28fb026301d86000

def z206 : W := mkw 0x4f69b5ac80000000 0x04f69b5ac8000000 0x4e4fd9cfc0000007 0xd4e4fd9cfc000000

def z207 : W := mkw 0x4200b7bdc0000550 0x44200b7bdc000055 0x40003fffc0003ff6 0x040003fffc0003ff

def z208 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0x11ffc00003ffc001 0x811ffc00003ffc00

def z209 : W := mkw 0x0dff0211428a0550 0x40dff0211428a055 0xdfffe631c38e3fff 0xfdfffe631c38e3ff

def z210 : W := mkw 0x00020000028a0000 0x000020000028a000 0x90000000038e0008 0x090000000038e000

def z211 : W := mkw 0x6dffc2bd9bef800c 0x06dffc2bd9bef800 0xffffc03fffffc009 0xfffffc03fffffc00

def z212 : W := mkw 0x6ffdf7bd9965800c 0x06ffdf7bd9965800 0x6ffffffffc71c007 0xf6ffffffffc71c00

def z213 : W := mkw 0x4000879580000000 0x0400087958000000 0x000007c1c0000004 0x0000007c1c000000

def z214 : W := mkw 0x100248426238ecc8 0x2100248426238ecc 0x7008180e2279eccb 0x57008180e2279ecc

def z215 : W := mkw 0x4fff3739428a0550 0x44fff3739428a055 0xdfb62631c38e3fff 0xbdfb62631c38e3ff

def z216 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x0fcfdfcfc0000004 0xc0fcfdfcfc000000

def z217 : W := mkw 0x00960000028a0000 0x000960000028a000 0x91b60000038e0009 0xb91b60000038e000

def z218 : W := mkw 0x6fff77391bef800c 0x06fff77391bef800 0xbfffe6303fffc009 0xfbfffe6303fffc00

def z219 : W := mkw 0x0000000000000000 0x0000000000000000 0x004fc00000000001 0xd004fc0000000000

def z220 : W := mkw 0x24bf42114aaf855c 0x424bf42114aaf855 0xd1bfe631c38fffff 0xbd1bfe631c38ffff

def z221 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0xfff03ff03ffe3fff 0xffff03ff03ffe3ff

def z222 : W := mkw 0x0000000000000000 0x0000000000000000 0x1180060003800f04 0x81180060003800f0

def z223 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0xae4039c03c70300a 0x7ae4039c03c70300

def z224 : W := mkw 0x100288c6e2186cc0 0x2100288c6e2186cc 0x500619cfc2082ccf 0x9500619cfc2082cc

def z225 : W := mkw 0x0b403d0035403203 0x00b403d003540320 0xaf803e003d80330a 0x7af803e003d80330

def z226 : W := mkw 0x00968295c28a0550 0x400968295c28a055 0xd1ffffffc38e3fff 0xfd1ffffffc38e3ff

def z227 : W := mkw 0x0940084035503a03 0x00940084035503a0 0xbfc000003ff03f08 0xfbfc000003ff03f0

def z228 : W := mkw 0x29d7421153ea855c 0x429d7421153ea855 0x11c7c601c3f00f04 0x811c7c601c3f00f0

def z229 : W := mkw 0x1002c8c6a238e888 0x21002c8c6a238e88 0x304fd9ce2279c009 0xd304fd9ce2279c00

def z230 : W := mkw 0x1f6afdeeff7dfeeb 0xa1f6afdeeff7dfee 0xffffffffffffffff 0xffffffffffffffff

def z231 : W := mkw 0x00960a13628a65d0 0x400960a13628a65d 0xf1be3e3fe38fffff 0xff1be3e3fe38ffff

def z232 : W := mkw 0x6ffdb7bd99c70004 0x06ffdb7bd99c7000 0xcfffffffdd860007 0xfcfffffffdd86000

def z233 : W := mkw 0x2dff42111bef800c 0x02dff42111bef800 0xffffe631ffffc00f 0xfffffe631ffffc00

def z234 : W := mkw 0x0f6835281d451223 0x80f6835281d45122 0x8fb026301d861330 0x28fb026301d86133

def z235 : W := mkw 0x49d5879580000000 0x049d587958000000 0x41cfdfcfc0000007 0xd41cfdfcfc000000

def z236 : W := mkw 0x200040001965800c 0x0200040001965800 0x200000003c71c000 0x0200000003c71c00

def z237 : W := mkw 0x0200350004001203 0x0020035000400120 0x0000260000001300 0x0000026000000130

def z238 : W := mkw 0x0b403d4235507a83 0x00b403d4235507a8 0xffc83fce3ff9ffcf 0xfffc83fce3ff9ffc

def z239 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0x11c03fc003f03f06 0x811c03fc003f03f0

def z240 : W := mkw 0x3002c8c6fbffeccc 0x23002c8c6fbffecc 0xf04fd9cfffffeccf 0xdf04fd9cfffffecc

def z241 : W := mkw 0x1002c086c228c4c8 0x21002c086c228c4c 0x500fc00fc209eccf 0x9500fc00fc209ecc

def z242 : W := mkw 0x02003d4024103a03 0x002003d4024103a0 0x91803fc003803f0e 0xb91803fc003803f0

def z243 : W := mkw 0x39d7c8c6f3faeccc 0x239d7c8c6f3faecc 0x71cfd9cfe3f9eccf 0xd71cfd9cfe3f9ecc

def z244 : W := mkw 0x0b40b58480000000 0x00b40b5848000000 0x4fcfffcfc0000007 0xf4fcfffcfc000000

def z245 : W := mkw 0x1002cad7e238edd8 0x61002cad7e238edd 0x704fffffe279ffff 0xd704fffffe279fff

def z246 : W := mkw 0x2f697d403d75ba0f 0x02f697d403d75ba0 0xbfc9ffc03ff1ff0e 0xfbfc9ffc03ff1ff0

def z247 : W := mkw 0x02003d6a24107aa3 0x802003d6a24107aa 0x40003ffe00003ff6 0x040003ffe00003ff

def z248 : W := mkw 0x0428000008050000 0x0042800000805000 0xee3820303c0ff0fb 0x7ee3820303c0ff0f

def z249 : W := mkw 0x0628302800000000 0x0062830280000000 0xce38383e000e30fb 0x7ce38383e000e30f

def z250 : W := mkw 0x00960211428a0550 0x400960211428a055 0xc1b62631c18e13f1 0x2c1b62631c18e13f

def z251 : W := mkw 0x0000000000000000 0x0000000000000000 0x004019c000000006 0xd004019c00000000

def z252 : W := mkw 0x1096c8c6e2baecc8 0x21096c8c6e2baecc 0xf1ffd9cfe3ffeccf 0xff1ffd9cfe3ffecc

def z253 : W := mkw 0x162af8eee238ecc8 0x2162af8eee238ecc 0x7e7ff9ffe279eccf 0xf7e7ff9ffe279ecc

def z254 : W := mkw 0x4200bfbfa40070a2 0x84200bfbfa40070a 0x40003fffc00030f6 0x040003fffc00030f

def z255 : W := mkw 0x4ffdb7bd91400000 0x04ffdb7bd9140000 0xfffffffffff0000f 0xffffffffffff0000

def z256 : W := mkw 0x0002c08482288008 0x00002c0848228800 0x704fd9cfe279c00f 0xd704fd9cfe279c00

def z257 : W := mkw 0x100248426238ecc8 0x2100248426238ecc 0x304fc0002279ecc9 0xd304fc0002279ecc

def z258 : W := mkw 0x24bf40000aaf800c 0x024bf40000aaf800 0x91bfc000038fc009 0xb91bfc000038fc00

def z259 : W := mkw 0x0002000042080440 0x0000200004208044 0xd0362031c20e3cff 0xbd0362031c20e3cf

def z260 : W := mkw 0x00960211428a0550 0x400960211428a055 0x51b62631c3800f07 0xb51b62631c3800f0

def z261 : W := mkw 0x000008022c0570a2 0x8000008022c0570a 0xa00000003c0ff0f8 0x0a00000003c0ff0f

def z262 : W := mkw 0x1000c8c6a030e888 0x21000c8c6a030e88 0x6049d9ce2079e0cb 0x56049d9ce2079e0c

def z263 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xbfffe6003fffff0f 0xfbfffe6003fffff0

def z264 : W := mkw 0x0b40354015501a03 0x00b40354015501a0 0x9fc027c01ff01f04 0xa9fc027c01ff01f0

def z265 : W := mkw 0x0094021100000000 0x0009402110000000 0xd1b62631c3803f0f 0xbd1b62631c3803f0

def z266 : W := mkw 0x0094021100000000 0x0009402110000000 0x01860601c0000004 0x801860601c000000

def z267 : W := mkw 0x0094021100000000 0x0009402110000000 0x40360031c0000001 0x040360031c000000

def z268 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0x6e38383e3c01c003 0x76e38383e3c01c00

def z269 : W := mkw 0x0002000042080440 0x0000200004208044 0xd1862601c3883fcf 0xbd1862601c3883fc

def z270 : W := mkw 0x0002000042080440 0x0000200004208044 0x40060001c00800c1 0x040060001c00800c

def z271 : W := mkw 0x4f69b5ac80000000 0x04f69b5ac8000000 0x0fc9ffce00000006 0xf0fc9ffce0000000

def z272 : W := mkw 0x0428002808050020 0x8042800280805002 0x0030003000060030 0x0003000300006003

def z273 : W := mkw 0x6ffffffdbfffba0f 0x06ffffffdbfffba0 0xffffffffffffff0f 0xfffffffffffffff0

def z274 : W := mkw 0x0000021100000110 0x4000002110000011 0x0000263000001330 0x0000026300000133

def z275 : W := mkw 0x2dffc0849bef800c 0x02dffc0849bef800 0xffffd9cfffffc00f 0xfffffd9cfffffc00

def z276 : W := mkw 0x2d6940001965800c 0x02d6940001965800 0xae79c0003c7fc009 0x7ae79c0003c7fc00

def z277 : W := mkw 0x2f69782a3d65f0ae 0x82f69782a3d65f0a 0xee79f83e3c7ff0fb 0x7ee79f83e3c7ff0f

def z278 : W := mkw 0x0094021100820110 0x4009402110082011 0x0180060001800300 0x0018006000180030

def z279 : W := mkw 0x00028084c2080440 0x000028084c208044 0x504fd9cfc2082ccf 0xd504fd9cfc2082cc

def z280 : W := mkw 0x1002c8c6e2baedd8 0x61002c8c6e2baedd 0xf04fd9cfe3ffffff 0xdf04fd9cfe3fffff

def z281 : W := mkw 0x1200bdc6e4107ec3 0x21200bdc6e4107ec 0x40003fcfc0003fc6 0x040003fcfc0003fc

def z282 : W := mkw 0x0002400042288448 0x0000240004228844 0x704fc001e279eccf 0xd704fc001e279ecc

def z283 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xce30383e1c0630f2 0x2ce30383e1c0630f

def z284 : W := mkw 0x00960211428a0550 0x400960211428a055 0x91860601c38e3ffc 0x891860601c38e3ff

def z285 : W := mkw 0x00960211428a0550 0x400960211428a055 0xd0360031c38e3ff9 0x0d0360031c38e3ff

def z286 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000000002002c0e 0x91000000002002c0

def z287 : W := mkw 0x1002c0c6c238ccc8 0x21002c0c6c238ccc 0x504fc1cfc279ccc5 0x8504fc1cfc279ccc

def z288 : W := mkw 0x0940050000000000 0x0094005000000000 0x01c007c000000004 0x801c007c00000000

def z289 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xae3020303c0ff0f8 0x2ae3020303c0ff0f

def z290 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xffb83e3e3f8fffff 0xfffb83e3e3f8ffff

def z291 : W := mkw 0x3dffcad7fbffeddc 0x63dffcad7fbffedd 0xffffffffffffffff 0xffffffffffffffff

def z292 : W := mkw 0x04bd000000000000 0x004bd00000000000 0x003fc00000000001 0x0003fc0000000000

def z293 : W := mkw 0x29d7400013ea800c 0x029d7400013ea800 0x31cfc00023f9c009 0xd31cfc00023f9c00

def z294 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x604fd9cfe079c0c1 0x4604fd9cfe079c0c

def z295 : W := mkw 0x062838002c053002 0x0062838002c05300 0xae3838003c0ff00b 0x7ae3838003c0ff00

def z296 : W := mkw 0x000008022c0570a2 0x8000008022c0570a 0xe008180e3c0ff0fb 0x5e008180e3c0ff0f

def z297 : W := mkw 0x020038022c0570a2 0x8020038022c0570a 0xae0038003c0ff0fa 0x7ae0038003c0ff0f

def z298 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0x2fc03fc03c700006 0xf2fc03fc03c70000

def z299 : W := mkw 0x00960211428a0550 0x400960211428a055 0xc0362031c00e30fb 0x3c0362031c00e30f

def z300 : W := mkw 0x10964a5362baedd8 0x610964a5362baedd 0xf1b62631e3ffffff 0xbf1b62631e3fffff

def z301 : W := mkw 0x2dff42115bef855c 0x42dff42115bef855 0xffffc031ffffc0f9 0xfffffc031ffffc0f

def z302 : W := mkw 0x0000000000000000 0x0000000000000000 0xae0000003c000008 0x7ae0000003c00000

def z303 : W := mkw 0x0000084020102800 0x0000008402010280 0x000019c000002c06 0x0000019c000002c0

def z304 : W := mkw 0x0428000008050000 0x0042800000805000 0x2e0800003c01c000 0x42e0800003c01c00

def z305 : W := mkw 0x0628302800000000 0x0062830280000000 0x0e08180e00000000 0x40e08180e0000000

def z306 : W := mkw 0x2fff7a3b7feff5fe 0xc2fff7a3b7feff5f 0xfffffe3fffffffff 0xffffffe3ffffffff

def z307 : W := mkw 0x49d5071100000000 0x049d507110000000 0x0180060000000000 0x0018006000000000

def z308 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0xf07ff9ffe27ffcff 0xff07ff9ffe27ffcf

def z309 : W := mkw 0x0628382824003002 0x0062838282400300 0xee38383e3c00300b 0x7ee38383e3c00300

def z310 : W := mkw 0x4628bfbfac0570a2 0x84628bfbfac0570a 0xee383ffffc0ff0ff 0x7ee383ffffc0ff0f

def z311 : W := mkw 0x44bf82bdc28a0550 0x444bf82bdc28a055 0xd1bfe63fc38e3fff 0xbd1bfe63fc38e3ff

def z312 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x4fb03fffc0000006 0x24fb03fffc000000

def z313 : W := mkw 0x02003d4024103a03 0x002003d4024103a0 0x000019c000000000 0x0000019c00000000

def z314 : W := mkw 0x0094021140000550 0x4009402114000055 0x41b62631c0003ff7 0xb41b62631c0003ff

def z315 : W := mkw 0x0200300004001002 0x0020030000400100 0x8e0020001c001000 0x28e0020001c00100

def z316 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x4fbfe63fc0000001 0x24fbfe63fc000000

def z317 : W := mkw 0x0940000000000000 0x0094000000000000 0x0fc0000000000000 0xf0fc000000000000

def z318 : W := mkw 0x2dff48403fffba0f 0x02dff48403fffba0 0xbfffc0003fffff09 0xfbfffc0003fffff0

def z319 : W := mkw 0x5ffdbfffe0106cc0 0x25ffdbfffe0106cc 0x4fffffffc0002cc7 0xf4fffffffc0002cc

def z320 : W := mkw 0x000008423d557aa3 0x8000008423d557aa 0xb00000003ffffff8 0x0b00000003ffffff

def z321 : W := mkw 0x0200302800000000 0x0020030280000000 0x4000383e00000002 0x04000383e0000000

def z322 : W := mkw 0x100248427778fecb 0x2100248427778fec 0xb00000003ff9ffc8 0x0b00000003ff9ffc

def z323 : W := mkw 0x4200b7bd80000000 0x04200b7bd8000000 0x404fffffc0000007 0xd404fffffc000000

def z324 : W := mkw 0x0bd63f5177da3f53 0x40bd63f5177da3f5 0xbfc63fc1fff03f0e 0xfbfc63fc1fff03f0

def z325 : W := mkw 0x4f69bdecb5503a03 0x04f69bdecb5503a0 0xbfc9ffce3ff03f0e 0xfbfc9ffce3ff03f0

def z326 : W := mkw 0x0dfd000008050000 0x00dfd00000805000 0xafffc0003c0fc009 0xfafffc0003c0fc00

def z327 : W := mkw 0x200240000aaf800c 0x0200240000aaf800 0x00000000000fc000 0x000000000000fc00

def z328 : W := mkw 0x4296b7bdc28a0550 0x44296b7bdc28a055 0xd1b63fffc38e3fff 0xbd1b63fffc38e3ff

def z329 : W := mkw 0x2dff48023befe08c 0x02dff48023befe08 0xffffd80e3fffe0cb 0xfffffd80e3fffe0c

def z330 : W := mkw 0x5200bfffe0106cc0 0x25200bfffe0106cc 0x40003fffc0002cc6 0x040003fffc0002cc

def z331 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x0ff7e7f1c0000004 0xa0ff7e7f1c000000

def z332 : W := mkw 0x1942c5c4d3788e49 0x21942c5c4d3788e4 0x11c7c7c1c3f00f04 0x811c7c7c1c3f00f0

def z333 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xffffe0303ffff0fb 0xfffffe0303ffff0f

def z334 : W := mkw 0x0000000000820110 0x4000000000082011 0x8000000001861330 0x0800000000186133

def z335 : W := mkw 0x2002400013ea800c 0x02002400013ea800 0x1000000003f00000 0x01000000003f0000

def z336 : W := mkw 0x0002400002288008 0x0000240000228800 0x300000002279c008 0x0300000002279c00

def z337 : W := mkw 0x4ffdbffdb5503a03 0x04ffdbffdb5503a0 0x6ffffffffc700007 0xf6ffffffffc70000

def z338 : W := mkw 0x1000c8c6a030e888 0x21000c8c6a030e88 0x604fd9cfe071c007 0xd604fd9cfe071c00

def z339 : W := mkw 0x6ffff7bd8aaf800c 0x06ffff7bd8aaf800 0x4fffffffc00fc007 0xf4fffffffc00fc00

def z340 : W := mkw 0x0094000000820000 0x0009400000082000 0x81b0000001860000 0x281b000000186000

def z341 : W := mkw 0x100248426e3dfcea 0xa100248426e3dfce 0xb00000003e7ffcf8 0x0b00000003e7ffcf

def z342 : W := mkw 0x162af8eeee3dfcea 0xa162af8eeee3dfce 0x7e4fd9cffe79eccf 0xd7e4fd9cffe79ecc

def z343 : W := mkw 0x4fffbffdf7da3f53 0x44fffbffdf7da3f5 0xfffffffffffe3fff 0xffffffffffffe3ff

def z344 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xae38383e3c07d030 0x6ae38383e3c07d03

def z345 : W := mkw 0x0000080220006080 0x0000008022000608 0xe038383e200ff0fb 0x7e038383e200ff0f

def z346 : W := mkw 0x0094829580000000 0x0009482958000000 0x41ffffffc0000007 0xf41ffffffc000000

def z347 : W := mkw 0x2dff40005bef855c 0x42dff40005bef855 0xbfffc0003ffffff9 0xfbfffc0003ffffff

def z348 : W := mkw 0x000088c4a0102800 0x0000088c4a010280 0x704fd9cfe2702c0f 0xd704fd9cfe2702c0

def z349 : W := mkw 0x6dffc7959bef800c 0x06dffc7959bef800 0xbfffc7c1ffffc00d 0xfbfffc7c1ffffc00

def z350 : W := mkw 0x59d7c7d5c2388c48 0x259d7c7d5c2388c4 0x11c7c7c1c2700c04 0x811c7c7c1c2700c0

def z351 : W := mkw 0x0bd43f5135d23b13 0x40bd43f5135d23b1 0xbff03ff03ff63f3e 0xfbff03ff03ff63f3

def z352 : W := mkw 0x4ffdbfbfa40070a2 0x84ffdbfbfa40070a 0x4fffffffc00030f7 0xf4fffffffc00030f

def z353 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x700019cfe279ecce 0x0700019cfe279ecc

def z354 : W := mkw 0x0200380024003002 0x0020038002400300 0xbf803e003f803f0e 0xfbf803e003f803f0

def z355 : W := mkw 0x1002484262baedd8 0x61002484262baedd 0xb000000023fffff8 0x0b000000023fffff

def z356 : W := mkw 0x4f69b7bd80000000 0x04f69b7bd8000000 0x4e49ffffc0000006 0x44e49ffffc000000

def z357 : W := mkw 0x4941858480000000 0x0494185848000000 0x0041c1c000000000 0x00041c1c00000000

def z358 : W := mkw 0x4ffdb7bd88050000 0x04ffdb7bd8805000 0xeffffffffc0fc00f 0xfeffffffffc0fc00

def z359 : W := mkw 0x0628b0ac80000000 0x00628b0ac8000000 0x4e7ff9ffc0000007 0xf4e7ff9ffc000000

def z360 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0x6e38183e3c0fc0f1 0x46e38183e3c0fc0f

def z361 : W := mkw 0x0bd4371100000000 0x00bd437110000000 0x4ff63ff1c0000007 0xf4ff63ff1c000000

def z362 : W := mkw 0x0f683d6835503a03 0x00f683d6835503a0 0xfff83ffe3ff03f0f 0xffff83ffe3ff03f0

def z363 : W := mkw 0x0002021142080550 0x4000202114208055 0x50062631c2083fff 0x950062631c2083ff

def z364 : W := mkw 0x6ffff7bddbef855c 0x46ffff7bddbef855 0xffffffffffffffff 0xffffffffffffffff

def z365 : W := mkw 0x200240005bef855c 0x4200240005bef855 0xb00000003ffffff8 0x0b00000003ffffff

def z366 : W := mkw 0x0940000011400000 0x0094000001140000 0x8f8000001d800000 0x28f8000001d80000

def z367 : W := mkw 0x100088c6e0106cc0 0x2100088c6e0106cc 0x704019cfe2702cce 0xd704019cfe2702cc

def z368 : W := mkw 0x0428000008050000 0x0042800000805000 0x8e3000001c060000 0x28e3000001c06000

def z369 : W := mkw 0x34bfc8c6eabfeccc 0x234bfc8c6eabfecc 0x707fd9cfe27feccf 0xd707fd9cfe27fecc

def z370 : W := mkw 0x1628f8eeac35f8aa 0xa1628f8eeac35f8a 0xee79f9fe3c7ff0fb 0x7ee79f9fe3c7ff0f

def z371 : W := mkw 0x0428082a2c0570a2 0x80428082a2c0570a 0xe038003e3c0ff0f9 0x0e038003e3c0ff0f

def z372 : W := mkw 0x0628302a080540a0 0x80628302a080540a 0x4e38383e000fc0f3 0x74e38383e000fc0f

def z373 : W := mkw 0x2d6b40001b6d800c 0x02d6b40001b6d800 0x3e4fc0003e79c009 0xd3e4fc0003e79c00

def z374 : W := mkw 0x06bc3a3b2c0570a2 0x806bc3a3b2c0570a 0xefbe3e3ffc0ff0ff 0xfefbe3e3ffc0ff0f

def z375 : W := mkw 0x4dfd87bd80000000 0x04dfd87bd8000000 0x41ffc7ffc0000005 0x841ffc7ffc000000

def z376 : W := mkw 0x5ffff7fdc2388c48 0x25ffff7fdc2388c4 0x5fffffffc2700c07 0xf5fffffffc2700c0

def z377 : W := mkw 0x0b427d403778ba0b 0x00b427d403778ba0 0xbfcfffc03ff9ff0f 0xfbfcfffc03ff9ff0

def z378 : W := mkw 0x209642115bef855c 0x4209642115bef855 0xf1b62631ffffffff 0xbf1b62631fffffff

def z379 : W := mkw 0x06be32394e8f1572 0xc06be32394e8f157 0xdfb62631df8e3fff 0xbdfb62631df8e3ff

def z380 : W := mkw 0x0200350000000000 0x0020035000000000 0x00003fc000000006 0x000003fc00000000

def z381 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x5047d9cfc2702cc6 0x85047d9cfc2702cc

def z382 : W := mkw 0x0940054011500a01 0x00940054011500a0 0x91c027c003f03f0e 0xb91c027c003f03f0

def z383 : W := mkw 0x2dff402a1befc0ac 0x82dff402a1befc0a 0xffffc03e3fffc0f9 0xfffffc03e3fffc0f

def z384 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x3047c1c1e279eccc 0x83047c1c1e279ecc

def z385 : W := mkw 0x0bd63711428a0550 0x40bd63711428a055 0xdff63ff1c38e3fff 0xfdff63ff1c38e3ff

def z386 : W := mkw 0x000008022c0570a2 0x8000008022c0570a 0x200000003c01c000 0x0200000003c01c00

def z387 : W := mkw 0x0000004000100800 0x0000000400010080 0x104001c002700c04 0x8104001c002700c0

def z388 : W := mkw 0x0000054000100a01 0x00000054000100a0 0x000007c000000f04 0x0000007c000000f0

def z389 : W := mkw 0x26bf782a2eaff0ae 0x826bf782a2eaff0a 0xee3ff83e3c0ff0fb 0x7ee3ff83e3c0ff0f

def z390 : W := mkw 0x0428082a280560a0 0x80428082a280560a 0x6038183e200fe0fb 0x56038183e200fe0f

def z391 : W := mkw 0x4ffd3f3b2c0570a2 0x84ffd3f3b2c0570a 0xefb83e3e3c0ff0fb 0x7efb83e3e3c0ff0f

def z392 : W := mkw 0x2ffd35001dc71207 0x02ffd35001dc7120 0x8fb026001d861300 0x28fb026001d86130

def z393 : W := mkw 0x0000000008050000 0x0000000000805000 0xa00000003c0fc008 0x0a00000003c0fc00

def z394 : W := mkw 0x0000084035503a03 0x00000084035503a0 0xb04019c03ff03f0e 0xdb04019c03ff03f0

def z395 : W := mkw 0x1002c0c4c2388c48 0x21002c0c4c2388c4 0x504fd9cfc2700c07 0xd504fd9cfc2700c0

def z396 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0xdfffffffc3803f0f 0xfdfffffffc3803f0

def z397 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0xbfc019c03ff00008 0xfbfc019c03ff0000

def z398 : W := mkw 0x0200382a240070a2 0x80200382a240070a 0xc030383e000e30fb 0x3c030383e000e30f

def z399 : W := mkw 0x2d6b40001bef800c 0x02d6b40001bef800 0xbe49c0003fffc008 0x4be49c0003fffc00

def z400 : W := mkw 0x1200b8eee4107ce2 0xa1200b8eee4107ce 0x400039ffc0003cf6 0x0400039ffc0003cf

def z401 : W := mkw 0x1002c0c4c2388c48 0x21002c0c4c2388c4 0x304fc1c1e279cc0d 0xd304fc1c1e279cc0

def z402 : W := mkw 0x06bc3a3b2c8771b2 0xc06bc3a3b2c8771b 0xefb83e3e3d8ff3fb 0x7efb83e3e3d8ff3f

def z403 : W := mkw 0x209640001bef800c 0x0209640001bef800 0xb1b600003fffc009 0xbb1b600003fffc00

def z404 : W := mkw 0x000208026e8f75f2 0xc000208026e8f75f 0xb00000003f8ffff8 0x0b00000003f8ffff

def z405 : W := mkw 0x0b403d4024103a03 0x00b403d4024103a0 0x0fc03fc000003f06 0xf0fc03fc000003f0

def z406 : W := mkw 0x4ffd373900000000 0x04ffd37390000000 0x4fb62631c0000007 0xb4fb62631c000000

def z407 : W := mkw 0x142ac8c6ea3decc8 0x2142ac8c6ea3decc 0xfe7fd9cffe7feccf 0xffe7fd9cffe7fecc

def z408 : W := mkw 0x1202f8eee638fcea 0xa1202f8eee638fce 0x704ff9ffe279fcff 0xd704ff9ffe279fcf

def z409 : W := mkw 0x4fffb7bdc28a0550 0x44fffb7bdc28a055 0x4fffffffc00e00f7 0xf4fffffffc00e00f

def z410 : W := mkw 0x000248402238a808 0x0000248402238a80 0x304fd9c02279ec0f 0xd304fd9c02279ec0

def z411 : W := mkw 0x4dfd82bd80000000 0x04dfd82bd8000000 0x4fffc03fc0000001 0xf4fffc03fc000000

def z412 : W := mkw 0x0dfd808480000000 0x00dfd80848000000 0x4fffd9cfc0000007 0xf4fffd9cfc000000

def z413 : W := mkw 0x04be023b4a8f45f0 0xc04be023b4a8f45f 0x403e003fc00fc0f1 0x0403e003fc00fc0f

def z414 : W := mkw 0x4095829580000000 0x0409582958000000 0x0007c001c0000000 0x00007c001c000000

def z415 : W := mkw 0x4ffd373915401203 0x04ffd37391540120 0x8fb026301d801300 0x28fb026301d80130

def z416 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0xbf8026003ff03f08 0x2bf8026003ff03f0

def z417 : W := mkw 0x0000000000000000 0x0000000000000000 0x4030203000000003 0x3403020300000000

def z418 : W := mkw 0x0000000000000000 0x0000000000000000 0x0180260000000006 0xb018026000000000

def z419 : W := mkw 0x2fff7d403fffba0f 0x02fff7d403fffba0 0xbfffd9c03fffc009 0xfbfffd9c03fffc00

def z420 : W := mkw 0x242a40001bef800c 0x0242a40001bef800 0xbe3800003fffc009 0x7be3800003fffc00

def z421 : W := mkw 0x3dff48427bffeccc 0x23dff48427bffecc 0xbfffc0003fffecc9 0xfbfffc0003fffecc

def z422 : W := mkw 0x49d78795c28a0550 0x449d78795c28a055 0x11c7c7c1c3800f04 0x811c7c7c1c3800f0

def z423 : W := mkw 0x16befaffeebffdfa 0xe16befaffeebffdf 0xffffffffffffffff 0xffffffffffffffff

def z424 : W := mkw 0x44bd023900000000 0x044bd02390000000 0x0030003000000000 0x0003000300000000

def z425 : W := mkw 0x09d6075153da0f51 0x409d6075153da0f5 0x11c607c1c3f00f04 0x811c607c1c3f00f0

def z426 : W := mkw 0x0dff0000028a0000 0x00dff0000028a000 0x9fffc000038e0009 0xf9fffc000038e000

def z427 : W := mkw 0x0002400002288008 0x0000240000228800 0x1047c00002700000 0x81047c0000270000

def z428 : W := mkw 0x2ffd30281dc71026 0x82ffd30281dc7102 0x8fb020301d861030 0x28fb020301d86103

def z429 : W := mkw 0x10008ad7e0106dd0 0x610008ad7e0106dd 0x40003fffc0003ff6 0x040003fffc0003ff

def z430 : W := mkw 0x00960000428a0440 0x000960000428a044 0xd1b60001c38e2ccf 0xbd1b60001c38e2cc

def z431 : W := mkw 0x00000802240070a2 0x800000802240070a 0x00000000000030f0 0x000000000000030f

def z432 : W := mkw 0x0094021100820110 0x4009402110082011 0x91b0263003863f3e 0xb91b0263003863f3

def z433 : W := mkw 0x0094021100820110 0x4009402110082011 0x0030003000060030 0x0003000300006003

def z434 : W := mkw 0x00020000428a0550 0x400020000428a055 0xd0302030038e3ffb 0x3d0302030038e3ff

def z435 : W := mkw 0x00020000428a0550 0x400020000428a055 0x91802600038e3ffe 0xb91802600038e3ff

def z436 : W := mkw 0x00020000428a0550 0x400020000428a055 0x00000000000e00f0 0x000000000000e00f

def z437 : W := mkw 0x0000400000208008 0x0000040000020800 0x2049c0002071c000 0x42049c0002071c00

def z438 : W := mkw 0x0940000011400000 0x0094000001140000 0xbfc026003ff03f0e 0xfbfc026003ff03f0

def z439 : W := mkw 0x06be3239428a0550 0x406be3239428a055 0xdfbe3e3fc38e3fff 0xfdfbe3e3fc38e3ff

def z440 : W := mkw 0x0b40350011400000 0x00b4035001140000 0xbfc03fc03ff0000e 0xfbfc03fc03ff0000

def z441 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000000000e30f8 0x080000000000e30f

def z442 : W := mkw 0x4f69bdaeac0570a2 0x84f69bdaeac0570a 0xee79f9fe3c0ff0fb 0x7ee79f9fe3c0ff0f

def z443 : W := mkw 0x1b427d427778fecb 0x21b427d427778fec 0xbfc03fc03ff9ffce 0xfbfc03fc03ff9ffc

def z444 : W := mkw 0x5ffff7bfc228c4c8 0x25ffff7bfc228c4c 0x4fffffffc009c0c7 0xf4fffffffc009c0c

def z445 : W := mkw 0x400082bd80000000 0x0400082bd8000000 0x4000003fc0000000 0x04000003fc000000

def z446 : W := mkw 0x100088c6e0106cc0 0x2100088c6e0106cc 0x600819cfe009eccf 0x5600819cfe009ecc

def z447 : W := mkw 0x54bfc2bfc228c4c8 0x254bfc2bfc228c4c 0x403fc03fc009c0c1 0x0403fc03fc009c0c

def z448 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xae08380e3c01f00a 0x7ae08380e3c01f00

def z449 : W := mkw 0x1002c084c2288448 0x21002c084c228844 0x0007c001c0000000 0x00007c001c000000

def z450 : W := mkw 0x5fffffffee3dfcea 0xa5fffffffee3dfce 0xfffffffffe7ffcff 0xffffffffffe7ffcf

def z451 : W := mkw 0x0f683d2a2c0570a2 0x80f683d2a2c0570a 0xeff83ffe3c0ff0ff 0xfeff83ffe3c0ff0f

def z452 : W := mkw 0x06bc32390c871132 0xc06bc32390c87113 0x8fb026301d861330 0x28fb026301d86133

def z453 : W := mkw 0x042a40000a2d8008 0x0042a40000a2d800 0xbe7fc0003e7fc009 0xfbe7fc0003e7fc00

def z454 : W := mkw 0x300248427bffeccc 0x2300248427bffecc 0xb00000003fffecc8 0x0b00000003fffecc

def z455 : W := mkw 0x0940054011500a01 0x00940054011500a0 0x004001c000700000 0x0004001c00070000

def z456 : W := mkw 0x0f683d6a3d557aa3 0x80f683d6a3d557aa 0xee7839fe3c7ff0fb 0x7ee7839fe3c7ff0f

def z457 : W := mkw 0x0940050011400201 0x0094005001140020 0x0180060001800300 0x0018006000180030

def z458 : W := mkw 0x1628f8eeac35f8aa 0xa1628f8eeac35f8a 0x2e49d9ce3c71c000 0x42e49d9ce3c71c00

def z459 : W := mkw 0x4ffd37390c051022 0x84ffd37390c05102 0x8fb026301c061030 0x28fb026301c06103

def z460 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0x8f803fc01d803f06 0x28f803fc01d803f0

def z461 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x400fd9cfc009ecc7 0x0400fd9cfc009ecc

def z462 : W := mkw 0x2b427d403fffba0f 0x02b427d403fffba0 0xbfc03fc03fffff0e 0xfbfc03fc03fffff0

def z463 : W := mkw 0x5202ffffe238ecc8 0x25202ffffe238ecc 0x704fffffe279eccf 0xd704fffffe279ecc

def z464 : W := mkw 0x5f6bfdeee238ecc8 0x25f6bfdeee238ecc 0x7e4fd9cfe279eccf 0xd7e4fd9cfe279ecc

def z465 : W := mkw 0x02963a3b668a75f2 0xc02963a3b668a75f 0xd1b63e3fc38e3fff 0xbd1b63e3fc38e3ff

def z466 : W := mkw 0x00960a136e8f75f2 0xc00960a136e8f75f 0xf1b62631ff8fffff 0xbf1b62631ff8ffff

def z467 : W := mkw 0x2dfd000019c70004 0x02dfd000019c7000 0x8fffc0001d860001 0xf8fffc0001d86000

def z468 : W := mkw 0x0bd4371115c21313 0x40bd4371115c2131 0x8fb026301d861330 0x28fb026301d86133

def z469 : W := mkw 0x29d740001bef800c 0x029d740001bef800 0xb1c7c0003fffc008 0x8b1c7c0003fffc00

def z470 : W := mkw 0x24bd000008870004 0x024bd00000887000 0x0030000000060000 0x0003000000006000

def z471 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0x4038383e000ff0f3 0x04038383e000ff0f

def z472 : W := mkw 0x0940084031502800 0x0094008403150280 0xbfc019c03ff02c0e 0xfbfc019c03ff02c0

def z473 : W := mkw 0x44bd82bd80000000 0x044bd82bd8000000 0x41bfe63fc0000007 0xb41bfe63fc000000

def z474 : W := mkw 0x24bf42114aaf855c 0x424bf42114aaf855 0x403fc031c00fc0f1 0x0403fc031c00fc0f

def z475 : W := mkw 0x44bd82bf880540a0 0x844bd82bf880540a 0x403fc03fc00fc0f1 0x0403fc03fc00fc0f

def z476 : W := mkw 0x0628386a3d557aa3 0x80628386a3d557aa 0xfe38383e3ffffffb 0x7fe38383e3ffffff

def z477 : W := mkw 0x2dff42111bef811c 0x42dff42111bef811 0xbfffe6303fffd339 0xfbfffe6303fffd33

def z478 : W := mkw 0x062830280c051022 0x8062830280c05102 0xce3020301c0e30fb 0x3ce3020301c0e30f

def z479 : W := mkw 0x1942cdc6f378eec9 0x21942cdc6f378eec 0x71cfdfcfe3f9efcf 0xd71cfdfcfe3f9efc

def z480 : W := mkw 0x39d7c0c4d3fa8c4c 0x239d7c0c4d3fa8c4 0x11c7c1c1c3f00c04 0x811c7c1c1c3f00c0

def z481 : W := mkw 0x4294b7bd80000000 0x04294b7bd8000000 0x41b63fffc0000007 0xb41b63fffc000000

def z482 : W := mkw 0x0002000042080440 0x0000200004208044 0x10060001c2000c04 0x810060001c2000c0

def z483 : W := mkw 0x2f697d403d75ba0f 0x02f697d403d75ba0 0x2e49d9c03c71c000 0x42e49d9c03c71c00

def z484 : W := mkw 0x10008086c00044c0 0x210008086c00044c 0x4000000fc00000c0 0x04000000fc00000c

def z485 : W := mkw 0x1002c086c228c4c8 0x21002c086c228c4c 0x404fd9cfc009c0c7 0xd404fd9cfc009c0c

def z486 : W := mkw 0x0628302800000000 0x0062830280000000 0x0e30203000000000 0x20e3020300000000

def z487 : W := mkw 0x2dfd40001965800c 0x02dfd40001965800 0x2fffc0003c71c001 0xf2fffc0003c71c00

def z488 : W := mkw 0x1096c297c2aac5d8 0x61096c297c2aac5d 0xd1bfe63fc38fffff 0xbd1bfe63fc38ffff

def z489 : W := mkw 0x00960211428a0550 0x400960211428a055 0xd1b60031c38e00f9 0xbd1b60031c38e00f

def z490 : W := mkw 0x0428080228056080 0x0042808022805608 0xee38180e3c0fe0cb 0x7ee38180e3c0fe0c

def z491 : W := mkw 0x1096cad7e238ecc8 0x21096cad7e238ecc 0x71ffffffe279eccf 0xf71ffffffe279ecc

def z492 : W := mkw 0x1002c8c4e238ac48 0x21002c8c4e238ac4 0x3047d9c1e2702c0e 0xd3047d9c1e2702c0

def z493 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000000003803f08 0x09000000003803f0

def z494 : W := mkw 0x0200300000000000 0x0020030000000000 0x0e00380000000002 0x70e0038000000000

def z495 : W := mkw 0x46bdbabfac0570a2 0x846bdbabfac0570a 0xee3ff83ffc0ff0fb 0x7ee3ff83ffc0ff0f

def z496 : W := mkw 0x0ffd382a2c0570a2 0x80ffd382a2c0570a 0xeffff83e3c0ff0fb 0xfeffff83e3c0ff0f

def z497 : W := mkw 0x0200382a240070a2 0x80200382a240070a 0x6008383e2009f0fb 0x56008383e2009f0f

def z498 : W := mkw 0x162a786a6e3dfcea 0xa162a786a6e3dfce 0xfe38383e3e7ffcfb 0x7fe38383e3e7ffcf

def z499 : W := mkw 0x200248023feff0ae 0x8200248023feff0a 0xb00000003ffff0f8 0x0b00000003ffff0f

def z500 : W := mkw 0x0940000011400000 0x0094000001140000 0x2e4000003c700000 0x42e4000003c70000

def z501 : W := mkw 0x0f683d2a3d4572a3 0x80f683d2a3d4572a 0xefb83e3e3d8ff3fb 0x7efb83e3e3d8ff3f

def z502 : W := mkw 0x0f68382a3d4570a2 0x80f68382a3d4570a 0xfff8383e3ffff0fb 0xffff8383e3ffff0f

def z503 : W := mkw 0x062a382a6e0d74e2 0x8062a382a6e0d74e 0xfe3e383ffe0ffcff 0xffe3e383ffe0ffcf

def z504 : W := mkw 0x100048422030e888 0x2100048422030e88 0x200000002071c000 0x0200000002071c00

def z505 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x700fc00fe279ecc9 0x0700fc00fe279ecc

def z506 : W := mkw 0x00960211428a0550 0x400960211428a055 0x91862601c3803f0e 0xb91862601c3803f0

def z507 : W := mkw 0x00960211428a0550 0x400960211428a055 0x00060001c0000000 0x000060001c000000

def z508 : W := mkw 0x4ffdbfffbd557aa3 0x84ffdbfffbd557aa 0xffffffffffffffff 0xffffffffffffffff

def z509 : W := mkw 0x24bf402a0aafc0ac 0x824bf402a0aafc0a 0x403fc03e000fc0f1 0x0403fc03e000fc0f

def z510 : W := mkw 0x3ffffdc6fffffecf 0x23ffffdc6fffffec 0xffffffcfffffffcf 0xfffffffcfffffffc

def z511 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0x2e7fc0003c7fc001 0x42e7fc0003c7fc00

def z512 : W := mkw 0x0bd6371157ca1753 0x40bd6371157ca175 0xdfb62631df8e3fff 0xbdfb62631df8e3ff

def z513 : W := mkw 0x062830280c051022 0x8062830280c05102 0x0e0000001c000000 0x00e0000001c00000

def z514 : W := mkw 0x3dffc0c4dbff8c4c 0x23dffc0c4dbff8c4 0xbfffc1c1ffffcc0d 0xfbfffc1c1ffffcc0

def z515 : W := mkw 0x00960000028a0000 0x000960000028a000 0xd1b62030038e30fb 0xbd1b62030038e30f

def z516 : W := mkw 0x4ffd373900000000 0x04ffd37390000000 0x0fffe63000000001 0xf0fffe6300000000

def z517 : W := mkw 0x0094000000000000 0x0009400000000000 0x01b6000000000001 0xb01b600000000000

def z518 : W := mkw 0x00960211428a0550 0x400960211428a055 0x51862631c3803ff6 0x851862631c3803ff

def z519 : W := mkw 0x062830280c051022 0x8062830280c05102 0xce38383e1c061033 0x7ce38383e1c06103

def z520 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0xbe4019c03ff03f08 0x4be4019c03ff03f0

def z521 : W := mkw 0x00960211428a0550 0x400960211428a055 0x51860601c3882fcf 0x951860601c3882fc

def z522 : W := mkw 0x1942c8c6f378ecc8 0x21942c8c6f378ecc 0xffcfd9cffff9eccf 0xfffcfd9cffff9ecc

def z523 : W := mkw 0x1002c8c6f778fecb 0x21002c8c6f778fec 0xf04fd9cffff9ffcf 0xdf04fd9cffff9ffc

def z524 : W := mkw 0x0b403f5175503f53 0x40b403f5175503f5 0xffc03ff1fff03ffe 0xfffc03ff1fff03ff

def z525 : W := mkw 0x0000080020002000 0x0000008002000200 0x200018002000200a 0x5200018002000200

def z526 : W := mkw 0x062a382a6e8f75f2 0xc062a382a6e8f75f 0xfe38383e3f8ffffb 0x7fe38383e3f8ffff

def z527 : W := mkw 0x5ffffffff778fecb 0x25ffffffff778fec 0xfffffffffff9ffcf 0xffffffffffff9ffc

def z528 : W := mkw 0x062830280c051022 0x8062830280c05102 0xae3820303c0fd039 0x7ae3820303c0fd03

def z529 : W := mkw 0x0b40350000000000 0x00b4035000000000 0x9fc03fc003803f0e 0xf9fc03fc003803f0

def z530 : W := mkw 0x44bf82bdc28a0550 0x444bf82bdc28a055 0x403fc03fc00e00f1 0x0403fc03fc00e00f

def z531 : W := mkw 0x02003a3b640075f2 0xc02003a3b640075f 0x40003e3fc0003ff6 0x040003e3fc0003ff

def z532 : W := mkw 0x0b423d4077da3f53 0x40b423d4077da3f5 0xbfc03fc03ffe3ffe 0xfbfc03fc03ffe3ff

def z533 : W := mkw 0x0200384035503a03 0x00200384035503a0 0xbe0038003ff03f0a 0x7be0038003ff03f0

def z534 : W := mkw 0x1002c086c228c4c8 0x21002c086c228c4c 0x704fc00fe279c0c9 0xd704fc00fe279c0c

def z535 : W := mkw 0x0000084024103a03 0x00000084024103a0 0x0000000000003f00 0x00000000000003f0

def z536 : W := mkw 0x0628b8aeac0570a2 0x80628b8aeac0570a 0xee7ff9fffc0ff0ff 0xfee7ff9fffc0ff0f

def z537 : W := mkw 0x0f68352800000000 0x00f6835280000000 0x4ff83ffe00000007 0xf4ff83ffe0000000

def z538 : W := mkw 0x00008886a0006080 0x000008886a000608 0x604fd9cfe009e0cf 0xd604fd9cfe009e0c

def z539 : W := mkw 0x0000000015401203 0x0000000001540120 0x800000001d801300 0x0800000001d80130

def z540 : W := mkw 0x10968ad7e29a6dd0 0x610968ad7e29a6dd 0xd1b63fffc38e3fff 0xbd1b63fffc38e3ff

def z541 : W := mkw 0x00960000428a0550 0x400960000428a055 0x91b60000038e3ff9 0xb91b60000038e3ff

def z542 : W := mkw 0x042808022c0570a2 0x8042808022c0570a 0xae3800003c0ff0f9 0x7ae3800003c0ff0f

def z543 : W := mkw 0x5ffdffffa030e888 0x25ffdffffa030e88 0x6fffffffe071c007 0xf6fffffffe071c00

def z544 : W := mkw 0x4f69bdecb5503a03 0x04f69bdecb5503a0 0x2e49d9ce3c700000 0x42e49d9ce3c70000

def z545 : W := mkw 0x04be023b4a8f45f0 0xc04be023b4a8f45f 0xd1be263fc38fffff 0xbd1be263fc38ffff

def z546 : W := mkw 0x09d6075153da0f51 0x409d6075153da0f5 0xd1f627f1c3fe3fff 0xbd1f627f1c3fe3ff

def z547 : W := mkw 0x09400d4031502a01 0x009400d4031502a0 0x31c01fc023f02f0e 0xd31c01fc023f02f0

def z548 : W := mkw 0x1002c8c6ee3dfcea 0xa1002c8c6ee3dfce 0xf04fd9cffe7ffcff 0xdf04fd9cffe7ffcf

def z549 : W := mkw 0x2dff48023feff0ae 0x82dff48023feff0a 0xbfffc0003ffff0f9 0xfbfffc0003ffff0f

def z550 : W := mkw 0x2ffd3d403dd73a07 0x02ffd3d403dd73a0 0xbff03fc03ff63f0e 0xfbff03fc03ff63f0

def z551 : W := mkw 0x0f683d6a3d557aa3 0x80f683d6a3d557aa 0x2e4819ce3c71c000 0x42e4819ce3c71c00

def z552 : W := mkw 0x0428000008050000 0x0042800000805000 0x00380000000fc001 0x000380000000fc00

def z553 : W := mkw 0x2fff75001bef800c 0x02fff75001bef800 0xbfffffc03fffc00f 0xfbfffffc03fffc00

def z554 : W := mkw 0x0000084035503a03 0x00000084035503a0 0xb18026003ff03f0e 0xbb18026003ff03f0

def z555 : W := mkw 0x3ffff8eefffffcee 0xa3ffff8eefffffce 0xfffff9fffffffcff 0xffffff9fffffffcf

def z556 : W := mkw 0x0000084035503a03 0x00000084035503a0 0x200000003c700000 0x0200000003c70000

def z557 : W := mkw 0x5fffffffe2baedd8 0x65fffffffe2baedd 0xffffffffe3ffffff 0xfffffffffe3fffff

def z558 : W := mkw 0x0b40380035403002 0x00b4038003540300 0xbfc038003ff0300a 0xfbfc038003ff0300

def z559 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x304fd9cfe271cc04 0xc304fd9cfe271cc0

def z560 : W := mkw 0x4f69352800000000 0x04f6935280000000 0x0e00000000000000 0x00e0000000000000

def z561 : W := mkw 0x24bf40000aaf800c 0x024bf40000aaf800 0xae3fc0003c0fc009 0x7ae3fc0003c0fc00

def z562 : W := mkw 0x0002400002288008 0x0000240000228800 0x000fc0000009c001 0x0000fc0000009c00

def z563 : W := mkw 0x4200373900000000 0x0420037390000000 0x0000263000000000 0x0000026300000000

def z564 : W := mkw 0x0000080220006080 0x0000008022000608 0x2008180e2001c000 0x42008180e2001c00

def z565 : W := mkw 0x0000084220106880 0x0000008422010688 0x704819ce2279eccf 0xd704819ce2279ecc

def z566 : W := mkw 0x3dffc8c6bbffe88c 0x23dffc8c6bbffe88 0xbfffd9ce3fffc009 0xfbfffd9ce3fffc00

def z567 : W := mkw 0x2dff40000aaf800c 0x02dff40000aaf800 0x0fffc000000fc001 0xf0fffc000000fc00

def z568 : W := mkw 0x0428002800000000 0x0042800280000000 0x4038003e00000001 0x04038003e0000000

def z569 : W := mkw 0x0000004011500a01 0x00000004011500a0 0x1000000003f00f00 0x01000000003f00f0

def z570 : W := mkw 0x0000021140000550 0x4000002114000055 0xc0302631c00e3fff 0x3c0302631c00e3ff

def z571 : W := mkw 0x100248426238ecc8 0x2100248426238ecc 0x70060001e279eccf 0x970060001e279ecc

def z572 : W := mkw 0x000000000c051022 0x8000000000c05102 0x800000001c061030 0x0800000001c06103

def z573 : W := mkw 0x02963f51669a3f53 0x402963f51669a3f5 0xd1b63ff1c38e3fff 0xbd1b63ff1c38e3ff

def z574 : W := mkw 0x0002084077da3f53 0x40002084077da3f5 0xb00000003ffe3ff8 0x0b00000003ffe3ff

def z575 : W := mkw 0x1002404042388c48 0x21002404042388c4 0x1000000002700c00 0x01000000002700c0

def z576 : W := mkw 0x2dff400013ea800c 0x02dff400013ea800 0x1fffc00003f00001 0xf1fffc00003f0000

def z577 : W := mkw 0x0002000002080000 0x0000200000208000 0x1006000002080009 0x9100600000208000

def z578 : W := mkw 0x0d69000000000000 0x00d6900000000000 0x0e49c00000000000 0x40e49c0000000000

def z579 : W := mkw 0x2fff782a3feff0ae 0x82fff782a3feff0a 0xbfffd80e3fffc009 0xfbfffd80e3fffc00

def z580 : W := mkw 0x4ffdb7bf880540a0 0x84ffdb7bf880540a 0x4fffffffc00fc0f7 0xf4fffffffc00fc0f

def z581 : W := mkw 0x162af8aeee2df4ea 0xa162af8aeee2df4e 0xee3ff83ffc0ff0fb 0x7ee3ff83ffc0ff0f

def z582 : W := mkw 0x00020000428a0550 0x400020000428a055 0xd0060001c38e3fff 0x9d0060001c38e3ff

def z583 : W := mkw 0x02003d4035503a03 0x002003d4035503a0 0xb0003fc03ff03f0e 0x0b0003fc03ff03f0

def z584 : W := mkw 0x0000000040000440 0x0000000004000044 0x40000001c0002cc6 0x040000001c0002cc

def z585 : W := mkw 0x0200380024003002 0x0020038002400300 0x0000380000003002 0x0000038000000300

def z586 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0x9ff7c0001ff60000 0xa9ff7c0001ff6000

def z587 : W := mkw 0x0dfd000000000000 0x00dfd00000000000 0x0fb0000000000000 0x20fb000000000000

def z588 : W := mkw 0x0000000000000000 0x0000000000000000 0x200800002009c009 0x5200800002009c00

def z589 : W := mkw 0x1096c2d5c2ba8d58 0x61096c2d5c2ba8d5 0xd1f7e7f1c3fe3fff 0xbd1f7e7f1c3fe3ff

def z590 : W := mkw 0x29d5000011c20004 0x029d5000011c2000 0x0180000001800000 0x0018000000180000

def z591 : W := mkw 0x0ffd302800000000 0x00ffd30280000000 0x4ffff83e00000003 0xf4ffff83e0000000

def z592 : W := mkw 0x4628b7bd80000000 0x04628b7bd8000000 0x4e383fffc0000007 0x74e383fffc000000

def z593 : W := mkw 0x1202fdc6e638fecb 0x21202fdc6e638fec 0x704fffcfe279ffcf 0xd704fffcfe279ffc

def z594 : W := mkw 0x1b42fdc6e238ecc8 0x21b42fdc6e238ecc 0x7fcfffcfe279eccf 0xf7fcfffcfe279ecc

def z595 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x0ff9fffe00000000 0x60ff9fffe0000000

def z596 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0x2e403fc03c703f06 0x42e403fc03c703f0

def z597 : W := mkw 0x0200380224007082 0x0020038022400708 0xee08380e3c09f0cb 0x7ee08380e3c09f0c

def z598 : W := mkw 0x0002000042080440 0x0000200004208044 0x1000000002082cc8 0x01000000002082cc

def z599 : W := mkw 0x4ffdb5ac80000000 0x04ffdb5ac8000000 0x0fffd9ce00000001 0xf0fffd9ce0000000

def z600 : W := mkw 0x000248022228e088 0x0000248022228e08 0x704fd80e2279e0cb 0xd704fd80e2279e0c

def z601 : W := mkw 0x06be3a3b6e8f75f2 0xc06be3a3b6e8f75f 0xee3e383ffc0ff0fb 0x7ee3e383ffc0ff0f

def z602 : W := mkw 0x4200b5ac80000000 0x04200b5ac8000000 0x000019ce00000000 0x0000019ce0000000

def z603 : W := mkw 0x2fff70281bef800c 0x02fff70281bef800 0xfffff83e3fffc00b 0xffffff83e3fffc00

def z604 : W := mkw 0x09d6021153ca0550 0x409d6021153ca055 0xfff62631fffe3fff 0xffff62631fffe3ff

def z605 : W := mkw 0x4ffdb7fd91500a01 0x04ffdb7fd91500a0 0x5fffffffc3f00f07 0xf5fffffffc3f00f0

def z606 : W := mkw 0x2bd77d4037faba0f 0x02bd77d4037faba0 0xbfc7ffc03ff03f0e 0xfbfc7ffc03ff03f0

def z607 : W := mkw 0x00960211028a0000 0x000960211028a000 0xd1b62631c38e000f 0xbd1b62631c38e000

def z608 : W := mkw 0x0b40350000000000 0x00b4035000000000 0x0e4019c000000000 0x40e4019c00000000

def z609 : W := mkw 0x0b40350015401203 0x00b4035001540120 0x9f8026001f803f0e 0xb9f8026001f803f0

def z610 : W := mkw 0x142ac8eeea3dece8 0xa142ac8eeea3dece 0x707fd9ffe27fecff 0xd707fd9ffe27fecf

def z611 : W := mkw 0x0ffd3d4035503a03 0x00ffd3d4035503a0 0xbfffffc03ff03f0f 0xfbfffffc03ff03f0

def z612 : W := mkw 0x0200380024003002 0x0020038002400300 0xee3038303c0e30fb 0x7ee3038303c0e30f

def z613 : W := mkw 0x00960211428a0550 0x400960211428a055 0x40362631c00e3ff7 0x040362631c00e3ff

def z614 : W := mkw 0x1096cad7e2baedd8 0x61096cad7e2baedd 0x707fd9ffe27fecff 0xd707fd9ffe27fecf

def z615 : W := mkw 0x1b42fdc6f778fecb 0x21b42fdc6f778fec 0x7e4fd9cffe79eccf 0xd7e4fd9cffe79ecc

def z616 : W := mkw 0x0000000000000000 0x0000000000000000 0x3040000022700008 0xd304000002270000

def z617 : W := mkw 0x3dffc086dbefc4cc 0x23dffc086dbefc4c 0xffffc00fffffc0c9 0xfffffc00fffffc0c

def z618 : W := mkw 0x69d7c79593ea800c 0x069d7c79593ea800 0x11c7c7c1c3f00004 0x811c7c7c1c3f0000

def z619 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0x8fbfc0001d8fc001 0x28fbfc0001d8fc00

def z620 : W := mkw 0x0f683d403d553a03 0x00f683d403d553a0 0xbff83fc03fffff0f 0xfbff83fc03fffff0

def z621 : W := mkw 0x00960a5177da3f53 0x400960a5177da3f5 0xf1b62631fffe3fff 0xbf1b62631fffe3ff

def z622 : W := mkw 0x1b40bdc6f5507ec3 0x21b40bdc6f5507ec 0xffc03fcffff03fce 0xfffc03fcffff03fc

def z623 : W := mkw 0x442980ac80000000 0x0442980ac8000000 0x0009c00e00000000 0x00009c00e0000000

def z624 : W := mkw 0x062838282c053022 0x8062838282c05302 0xae3038303c06303a 0x7ae3038303c06303

def z625 : W := mkw 0x1dffc8c6e238ecc8 0x21dffc8c6e238ecc 0x7fffd9cfe279eccf 0xf7fffd9cfe279ecc

def z626 : W := mkw 0x0000000000000000 0x0000000000000000 0x8180260001801300 0x2818026000180130

def z627 : W := mkw 0x00960211428a0550 0x400960211428a055 0x91b62631c3861f34 0xa91b62631c3861f3

def z628 : W := mkw 0x00960211428a0550 0x400960211428a055 0x91b60601c38e0f0d 0xb91b60601c38e0f0

def z629 : W := mkw 0x3d69c8c6b975e88c 0x23d69c8c6b975e88 0x2e49d9ce3c71c000 0x42e49d9ce3c71c00

def z630 : W := mkw 0x0b40350015401203 0x00b4035001540120 0x8fc03fc01d801306 0xf8fc03fc01d80130

def z631 : W := mkw 0x1628b8eeec157ce2 0xa1628b8eeec157ce 0xee3839fffc0ffcff 0x7ee3839fffc0ffcf

def z632 : W := mkw 0x0000084020102800 0x0000008402010280 0xb1c03fc023f03f0e 0xfb1c03fc023f03f0

def z633 : W := mkw 0x100088c6e0106cc0 0x2100088c6e0106cc 0x404fd9cfc0002cc7 0xd404fd9cfc0002cc

def z634 : W := mkw 0x0000084020102800 0x0000008402010280 0x204019c020700000 0x4204019c02070000

def z635 : W := mkw 0x2097400002aa800c 0x02097400002aa800 0x0007c00000000000 0x00007c0000000000

def z636 : W := mkw 0x4ffdbffda0102800 0x04ffdbffda010280 0x7fffffffe2702c0f 0xf7fffffffe2702c0

def z637 : W := mkw 0x59d7cfd7e238ecc8 0x259d7cfd7e238ecc 0x71cfdfcfe279eccf 0xd71cfdfcfe279ecc

def z638 : W := mkw 0x00960211428a0550 0x400960211428a055 0x51b60631c38e0ff5 0x851b60631c38e0ff

def z639 : W := mkw 0x0628302808050000 0x0062830280805000 0xee38383e3c0fc00b 0x7ee38383e3c0fc00

def z640 : W := mkw 0x4ffdb7bdc0000550 0x44ffdb7bdc000055 0x4fffffffc0003ff7 0xf4fffffffc0003ff

def z641 : W := mkw 0x6ffff7bd93ea800c 0x06ffff7bd93ea800 0x5fffffffc3f00007 0xf5fffffffc3f0000

def z642 : W := mkw 0x1000c0868020c088 0x21000c0868020c08 0x0009c00e0001c000 0x00009c00e0001c00

def z643 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0x6e08180e3c09e0cb 0x56e08180e3c09e0c

def z644 : W := mkw 0x0000080024003002 0x0000008002400300 0xa00000003c003008 0x0a00000003c00300

def z645 : W := mkw 0x2f69782a3d65f0ae 0x82f69782a3d65f0a 0x2e49d80e3c71c000 0x42e49d80e3c71c00

def z646 : W := mkw 0x0000021140000550 0x4000002114000055 0xd1802631c3803ffe 0xbd1802631c3803ff

def z647 : W := mkw 0x0000021140000550 0x4000002114000055 0x40000031c00000f0 0x040000031c00000f

def z648 : W := mkw 0x2dfd000019c70004 0x02dfd000019c7000 0xbff000003ff60008 0xfbff000003ff6000

def z649 : W := mkw 0x0dff400002288008 0x00dff40000228800 0x3fffc0002279c009 0xf3fffc0002279c00

def z650 : W := mkw 0x00020000428a0550 0x400020000428a055 0x1000000003800f00 0x01000000003800f0

def z651 : W := mkw 0x0428002a080540a0 0x80428002a080540a 0xc038203e000ff0fb 0x3c038203e000ff0f

def z652 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x3049d9ce2279ecc8 0x43049d9ce2279ecc

def z653 : W := mkw 0x1b40fdc6b570fa8b 0x21b40fdc6b570fa8 0xbfc9ffce3ff1ff0e 0xfbfc9ffce3ff1ff0

def z654 : W := mkw 0x0628382a240070a2 0x80628382a240070a 0x4e38383e000030f3 0x74e38383e000030f

def z655 : W := mkw 0x6f69f5ac9965800c 0x06f69f5ac9965800 0x2e49d9ce3c71c000 0x42e49d9ce3c71c00

def z656 : W := mkw 0x4ffd373900820110 0x44ffd37390082011 0x8fb0263001861330 0x28fb026300186133

def z657 : W := mkw 0x49d78795c28a0550 0x449d78795c28a055 0xd1f7e7f1c38e3fff 0xbd1f7e7f1c38e3ff

def z658 : W := mkw 0x0000080220006080 0x0000008022000608 0x4000180e000020c2 0x04000180e000020c

def z659 : W := mkw 0x0094021100000000 0x0009402110000000 0xc1b62631c00e30ff 0xbc1b62631c00e30f

def z660 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0xafc03fc03df01300 0x6afc03fc03df0130

def z661 : W := mkw 0x294240001bef800c 0x0294240001bef800 0xbfc000003fffc008 0xfbfc000003fffc00

def z662 : W := mkw 0x0200380024003002 0x0020038002400300 0x2e0018003c000000 0x42e0018003c00000

def z663 : W := mkw 0x00960000028a0000 0x000960000028a000 0x91b62600038e3f0f 0xb91b62600038e3f0

def z664 : W := mkw 0x00960000028a0000 0x000960000028a000 0x00360000000e0001 0x000360000000e000

def z665 : W := mkw 0x1096c2d5c2ba8d58 0x61096c2d5c2ba8d5 0x11c7c7c1c3f00f04 0x811c7c7c1c3f00f0

def z666 : W := mkw 0x4bd5b79580000000 0x04bd5b7958000000 0x0fc7ffc1c0000006 0xf0fc7ffc1c000000

def z667 : W := mkw 0x4ffd373900000000 0x04ffd37390000000 0x4fb83e3e00000003 0x74fb83e3e0000000

def z668 : W := mkw 0x0000000011400000 0x0000000001140000 0xb00000003ff00008 0x0b00000003ff0000

def z669 : W := mkw 0x0000000000000000 0x0000000000000000 0x800020000000300a 0x3800020000000300

def z670 : W := mkw 0x02963a11668a3552 0x402963a11668a355 0xffb63e31ff8e3fff 0xfffb63e31ff8e3ff

def z671 : W := mkw 0x04be00000a8f0000 0x004be00000a8f000 0xbfbe00003f8fc009 0xfbfbe00003f8fc00

def z672 : W := mkw 0x2dfd000019c70004 0x02dfd000019c7000 0xafb800003d8fc009 0x7afb800003d8fc00

def z673 : W := mkw 0x4ffdbffda4103a03 0x04ffdbffda4103a0 0x4fffffffc0003f07 0xf4fffffffc0003f0

def z674 : W := mkw 0x7ffffffffbffeccc 0x27ffffffffbffecc 0xffffffffffffeccf 0xfffffffffffffecc

def z675 : W := mkw 0x0b40350015401203 0x00b4035001540120 0x0e0000001c000000 0x00e0000001c00000

def z676 : W := mkw 0x4ffd373900000000 0x04ffd37390000000 0x0ff03ff000000006 0xf0ff03ff00000000

def z677 : W := mkw 0x0000000000000000 0x0000000000000000 0x40002030000030f2 0x040002030000030f

def z678 : W := mkw 0x0b403d0024003002 0x00b403d002400300 0xafc03fc03c00300e 0xfafc03fc03c00300

def z679 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000000000820cb 0x140000000000820c

def z680 : W := mkw 0x4fffb7bdc2080440 0x04fffb7bdc208044 0x5fffffffc2082ccf 0xf5fffffffc2082cc

def z681 : W := mkw 0x2dff48403bffa80c 0x02dff48403bffa80 0xbfffd9c03fffec0f 0xfbfffd9c03fffec0

def z682 : W := mkw 0x00960211428a0550 0x400960211428a055 0x50360031c20e2cff 0x950360031c20e2cf

def z683 : W := mkw 0x200240001bef800c 0x0200240001bef800 0xb04fc0003fffc009 0xdb04fc0003fffc00

def z684 : W := mkw 0x1000c8c6a030e888 0x21000c8c6a030e88 0x3049d9ce2271ec0e 0xd3049d9ce2271ec0

def z685 : W := mkw 0x02003d4024103a03 0x002003d4024103a0 0xae003fc03c003f0e 0x7ae003fc03c003f0

def z686 : W := mkw 0x262a782a3feff0ae 0x8262a782a3feff0a 0xfe38383e3ffff0fb 0x7fe38383e3ffff0f

def z687 : W := mkw 0x1bd6ffd7f7faffdb 0x61bd6ffd7f7faffd 0xffffffffffffffff 0xffffffffffffffff

def z688 : W := mkw 0x0000000000000000 0x0000000000000000 0x9180000003800008 0xb918000000380000

def z689 : W := mkw 0x0000002a000040a0 0x80000002a000040a 0x4000003e000000f0 0x04000003e000000f

def z690 : W := mkw 0x4b40b7bd80000000 0x04b40b7bd8000000 0x4fc03fffc0000006 0xf4fc03fffc000000

def z691 : W := mkw 0x49d587d591500a01 0x049d587d591500a0 0x11c7c7c1c3f00f04 0x811c7c7c1c3f00f0

def z692 : W := mkw 0x4ffdbfbfa0006080 0x04ffdbfbfa000608 0x6fffffffe009e0cf 0xf6fffffffe009e0c

def z693 : W := mkw 0x0428002a080540a0 0x80428002a080540a 0x0008000e0001c000 0x00008000e0001c00

def z694 : W := mkw 0x0000000040000550 0x4000000004000055 0x0000000000003ff0 0x00000000000003ff

def z695 : W := mkw 0x2dff45401bff8a0d 0x02dff45401bff8a0 0xbfffc7c03fffcf0d 0xfbfffc7c03fffcf0

def z696 : W := mkw 0x09d5000000000000 0x009d500000000000 0x01c7c00000000000 0x801c7c0000000000

def z697 : W := mkw 0x100248426238ecc8 0x2100248426238ecc 0x304019c02279ecce 0xd304019c02279ecc

def z698 : W := mkw 0x2dff02115bcf0554 0x42dff02115bcf055 0xdfb62631df8e3fff 0xbdfb62631df8e3ff

def z699 : W := mkw 0x0ffe3f7b7fdf7ff3 0xc0ffe3f7b7fdf7ff 0xfffe3fffffffffff 0xffffe3ffffffffff

def z700 : W := mkw 0x09d6000013ca0000 0x009d6000013ca000 0xbff600003ffe0009 0xfbff600003ffe000

def z701 : W := mkw 0x1002c886e228e4c8 0x21002c886e228e4c 0x600fd80fe009e0cb 0x5600fd80fe009e0c

def z702 : W := mkw 0x6fffffbfbfeff0ae 0x86fffffbfbfeff0a 0xfffffffffffff0ff 0xffffffffffffff0f

def z703 : W := mkw 0x0000000200004080 0x0000000020000408 0x4008000e0009c0c1 0x04008000e0009c0c

def z704 : W := mkw 0x4fffb7bdc28a0550 0x44fffb7bdc28a055 0x5fffffffc3800f07 0xf5fffffffc3800f0

def z705 : W := mkw 0x0096400002aa8008 0x00096400002aa800 0xb1ffc00023ffc009 0xfb1ffc00023ffc00

def z706 : W := mkw 0x142ac0aeca2dc4e8 0xa142ac0aeca2dc4e 0x403fc03fc00fc0f1 0x0403fc03fc00fc0f

def z707 : W := mkw 0x442980ac80000000 0x0442980ac8000000 0x404fd9cfc0000007 0xd404fd9cfc000000

def z708 : W := mkw 0x4294b7bd80000000 0x04294b7bd8000000 0x41ffffffc0000007 0xf41ffffffc000000

def z709 : W := mkw 0x0428082a2c0570a2 0x80428082a2c0570a 0xee38003e3c0ff0f9 0x7ee38003e3c0ff0f

def z710 : W := mkw 0x1b42f586d768d6cb 0x21b42f586d768d6c 0xcf8fe60fdd89d3c1 0x2cf8fe60fdd89d3c

def z711 : W := mkw 0x2d6940001965800c 0x02d6940001965800 0xae49c0003c71c008 0x7ae49c0003c71c00

def z712 : W := mkw 0x1202b8eee6187ce2 0xa1202b8eee6187ce 0xd03639ffc20e3cff 0xbd03639ffc20e3cf

def z713 : W := mkw 0x100248426238ecc8 0x2100248426238ecc 0x300000002279ecce 0x9300000002279ecc

def z714 : W := mkw 0x4ffdb7bd95401203 0x04ffdb7bd9540120 0xdfffffffdf803f0f 0xfdfffffffdf803f0

def z715 : W := mkw 0x4ffdb7bd88050000 0x04ffdb7bd8805000 0xeffffffffc0ff0ff 0xfeffffffffc0ff0f

def z716 : W := mkw 0x0002000042080440 0x0000200004208044 0xd1b62631c38e3fff 0xbd1b62631c38e3ff

def z717 : W := mkw 0x3dfd88c6f9d76cc4 0x23dfd88c6f9d76cc 0xcfb019cfdd862cc6 0x2cfb019cfdd862cc

def z718 : W := mkw 0x6ffd373919c70114 0x46ffd373919c7011 0x8fb026301d861330 0x28fb026301d86133

def z719 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0xfe4fd9cffe79eccf 0xffe4fd9cffe79ecc

def z720 : W := mkw 0x0bd63f5177da3f53 0x40bd63f5177da3f5 0x6e7619f1fc7e00f1 0x46e7619f1fc7e00f

def z721 : W := mkw 0x6202f7bd9bef800c 0x06202f7bd9bef800 0xf0003fffffffc00e 0x0f0003fffffffc00

def z722 : W := mkw 0x2d6b40001b6d800c 0x02d6b40001b6d800 0x3e49c0003e79c008 0x43e49c0003e79c00

def z723 : W := mkw 0x2dff40005bef844c 0x02dff40005bef844 0xffffe601ffffffcf 0xfffffe601ffffffc

def z724 : W := mkw 0x00960211428a0550 0x400960211428a055 0xd1b02631c38e3ffe 0x2d1b02631c38e3ff

def z725 : W := mkw 0x2d6942115965855c 0x42d6942115965855 0x6e49e631fc71fff6 0x46e49e631fc71fff

def z726 : W := mkw 0x4ffdb7bd80820110 0x44ffdb7bd8082011 0x4fffffffc0060037 0xf4fffffffc006003

def z727 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xbfffc6003fffcf0d 0xfbfffc6003fffcf0

def z728 : W := mkw 0x0b403d6835503a23 0x80b403d6835503a2 0xbfc03ff03ff03f3e 0xfbfc03ff03ff03f3

def z729 : W := mkw 0x2bd7782a37eaf0ae 0x82bd7782a37eaf0a 0x51c7f83e03f030f2 0x851c7f83e03f030f

def z730 : W := mkw 0x0940808480000000 0x0094080848000000 0x4fcfd9cfc0000007 0xf4fcfd9cfc000000

def z731 : W := mkw 0x0b403d4235507a83 0x00b403d4235507a8 0xfff83ffe3fffffff 0xffff83ffe3ffffff

def z732 : W := mkw 0x300248427b7deccc 0x2300248427b7decc 0x300000003e79ecc8 0x0300000003e79ecc

def z733 : W := mkw 0x69d7c795d3ea855c 0x469d7c795d3ea855 0x11c7c7c1c3f00f04 0x811c7c7c1c3f00f0

def z734 : W := mkw 0x162a786a6e3dfcea 0xa162a786a6e3dfce 0xbe3020303e7ffcf8 0x2be3020303e7ffcf

def z735 : W := mkw 0x4b40b7bd80000000 0x04b40b7bd8000000 0x4fcfffffc0000007 0xf4fcfffffc000000

def z736 : W := mkw 0x5fff7f7b6238ecc8 0x25fff7f7b6238ecc 0x3fb026302279ecc8 0x23fb026302279ecc

def z737 : W := mkw 0x4f6bb5acc28a0550 0x44f6bb5acc28a055 0x9e49d9ce038e3ff8 0x49e49d9ce038e3ff

def z738 : W := mkw 0x100248426638fecb 0x2100248426638fec 0x300000002279ffc8 0x0300000002279ffc

def z739 : W := mkw 0x0d68056a19554aa1 0x80d68056a19554aa 0x51f807fe03ffcff5 0x851f807fe03ffcff

def z740 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xbfffc0003fffff09 0xfbfffc0003fffff0

def z741 : W := mkw 0x0d69808480000000 0x00d6980848000000 0x4e4fd9cfc0000007 0xd4e4fd9cfc000000

def z742 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xffffe6303fffffff 0xfffffe6303ffffff

def z743 : W := mkw 0x0000808480000000 0x0000080848000000 0x404fd9cfc0000001 0x4404fd9cfc000000

def z744 : W := mkw 0x06bcb2bd80000000 0x006bcb2bd8000000 0x4fffffffc0000007 0xf4fffffffc000000

def z745 : W := mkw 0x4bd5b7bd80000000 0x04bd5b7bd8000000 0x01c7dfcfc0000004 0x801c7dfcfc000000

def z746 : W := mkw 0x2d69400019e7800c 0x02d69400019e7800 0xae49c0003df7c000 0x4ae49c0003df7c00

def z747 : W := mkw 0x0940084031502800 0x0094008403150280 0xbfc03fc03ff03f0e 0xfbfc03fc03ff03f0

def z748 : W := mkw 0x0428400008258008 0x0042840000825800 0x2e49c0003c71c000 0x42e49c0003c71c00

def z749 : W := mkw 0x0428002a080540a0 0x80428002a080540a 0x6e38003e3c0fc0f1 0x46e38003e3c0fc0f

def z750 : W := mkw 0x1002c0c6c238ccc8 0x21002c0c6c238ccc 0x504fd9cfc279ccc7 0xd504fd9cfc279ccc

def z751 : W := mkw 0x0428082a280560a0 0x80428082a280560a 0xee38183e3c0fe0fb 0x7ee38183e3c0fe0f

def z752 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xee38183e3c0ff0f9 0x4ee38183e3c0ff0f

def z753 : W := mkw 0x4000879580000000 0x0400087958000000 0x404fdfcfc0000007 0xd404fdfcfc000000

def z754 : W := mkw 0x2dff42115bef855c 0x42dff42115bef855 0xffffc601ffffefcf 0xfffffc601ffffefc

def z755 : W := mkw 0x0000808480000000 0x0000080848000000 0x407ff9ffc0000007 0xf407ff9ffc000000

def z756 : W := mkw 0x0428002a080540a0 0x80428002a080540a 0xee38203e3c0ff0fb 0x7ee38203e3c0ff0f

def z757 : W := mkw 0x100248426238ecc8 0x2100248426238ecc 0xb0000000227ffcf8 0x0b0000000227ffcf

def z758 : W := mkw 0x0628302a0c0550a2 0x80628302a0c0550a 0xce38203e1c0ff0fb 0x3ce38203e1c0ff0f

def z759 : W := mkw 0x2dff40001b6d800c 0x02dff40001b6d800 0x3fffc0003e79c009 0xf3fffc0003e79c00

def z760 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0xbfc83fc03ff9ff0f 0xfbfc83fc03ff9ff0

def z761 : W := mkw 0x2dff42115bef855c 0x42dff42115bef855 0xbfffe6303ffffff9 0xfbfffe6303ffffff

def z762 : W := mkw 0x10964a5362baedd8 0x610964a5362baedd 0xb1b0263023fffff8 0x2b1b0263023fffff

def z763 : W := mkw 0x09d6421153ea8558 0x409d6421153ea855 0xffffe631ffffffff 0xfffffe631fffffff

def z764 : W := mkw 0x1002c8c6e638fcca 0x21002c8c6e638fcc 0xf04fd9cffe79fccf 0xdf04fd9cffe79fcc

def z765 : W := mkw 0x1094cad7a0b2e998 0x61094cad7a0b2e99 0xa1f9fffe21f7d330 0x6a1f9fffe21f7d33

def z766 : W := mkw 0x400082bd80000000 0x0400082bd8000000 0x404fd9ffc0000007 0xd404fd9ffc000000

def z767 : W := mkw 0x0000808480000000 0x0000080848000000 0x004fd9cfc0000004 0xc004fd9cfc000000

def z768 : W := mkw 0x4ffdb7bd80820110 0x44ffdb7bd8082011 0x4fffffffc1800307 0xf4fffffffc180030

def z769 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xee3e383ffc0ff0ff 0xfee3e383ffc0ff0f

def z770 : W := mkw 0x00960211428a0550 0x400960211428a055 0x91b62631c38e3ffc 0xa91b62631c38e3ff

def z771 : W := mkw 0x0002c084c2288448 0x00002c084c228844 0x704fd9cfe279eccf 0xd704fd9cfe279ecc

def z772 : W := mkw 0x0b403d6a35507aa3 0x80b403d6a35507aa 0xfff03ffe3ffe3fff 0xffff03ffe3ffe3ff

def z773 : W := mkw 0x100248426238ecc8 0x2100248426238ecc 0x304000002279ecc8 0xd304000002279ecc

def z774 : W := mkw 0x1200bdeee4107ee3 0xa1200bdeee4107ee 0x40003fffc0003ff6 0x040003fffc0003ff

def z775 : W := mkw 0x4200bfffa4107aa3 0x84200bfffa4107aa 0x40003fffc0003ff6 0x040003fffc0003ff

def z776 : W := mkw 0x4f69b5ac80000000 0x04f69b5ac8000000 0x4fcfffcfc0000007 0xf4fcfffcfc000000

def z777 : W := mkw 0x2dff42115bef855c 0x42dff42115bef855 0xbfffe631ffffdf3d 0xfbfffe631ffffdf3

def z778 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xffb8383e3f8ff0fb 0xfffb8383e3f8ff0f

def z779 : W := mkw 0x06be3a3b6e8f75f2 0xc06be3a3b6e8f75f 0x3f8e1e0fff81cf04 0xc3f8e1e0fff81cf0

def z780 : W := mkw 0x2d6940001965800c 0x02d6940001965800 0xee79e0303c7ff0fb 0x7ee79e0303c7ff0f

def z781 : W := mkw 0x0b40354015501a03 0x00b40354015501a0 0x9fc03fc01ff01f06 0xf9fc03fc01ff01f0

def z782 : W := mkw 0x6dff47111bef800c 0x06dff47111bef800 0xbfffc6003fffc009 0xfbfffc6003fffc00

def z783 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xee38183e3c0fc0f9 0x7ee38183e3c0fc0f

def z784 : W := mkw 0x2dff42111bef800c 0x02dff42111bef800 0xbfffe6303fffc009 0xfbfffe6303fffc00

def z785 : W := mkw 0x46bdb7bd80000000 0x046bdb7bd8000000 0x41bfffffc0000007 0xb41bfffffc000000

def z786 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0xffc63fc1fff03f0f 0xfffc63fc1fff03f0

def z787 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0x3fffc0003fffc001 0xc3fffc0003fffc00

def z788 : W := mkw 0x0b403d4235507aa3 0x80b403d4235507aa 0xbfc03fc03ff03ffe 0xfbfc03fc03ff03ff

def z789 : W := mkw 0x2dff40001bef811c 0x42dff40001bef811 0xbfffc0003fffd339 0xfbfffc0003fffd33

def z790 : W := mkw 0x49d5879580000000 0x049d587958000000 0x01cfdfcfc0000004 0xc01cfdfcfc000000

def z791 : W := mkw 0x162af0ecce3d9c6a 0xa162af0ecce3d9c6 0x9e77e1f1de761c34 0xa9e77e1f1de761c3

def z792 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x4fffffffc00e00f7 0xf4fffffffc00e00f

def z793 : W := mkw 0x6ffd37391dc71026 0x86ffd37391dc7102 0x8fb026301d861030 0x28fb026301d86103

def z794 : W := mkw 0x06283d6a2c157aa3 0x806283d6a2c157aa 0xffb83ffe3f8fffff 0xfffb83ffe3f8ffff

def z795 : W := mkw 0x04be42114aaf8558 0x404be42114aaf855 0xffffe631ffffffff 0xfffffe631fffffff

def z796 : W := mkw 0x0094021140820550 0x4009402114082055 0xd1b02631c3863ffe 0xbd1b02631c3863ff

def z797 : W := mkw 0x100248426238ecc8 0x2100248426238ecc 0x000000000009ecc0 0x0000000000009ecc

def z798 : W := mkw 0x100248426238ecc8 0x2100248426238ecc 0x200000002079c0c0 0x0200000002079c0c

def z799 : W := mkw 0x4200b5ac80000000 0x04200b5ac8000000 0x404fd9cfc0000007 0xd404fd9cfc000000

def z800 : W := mkw 0x2dff42115bef855c 0x42dff42115bef855 0xffffe631ffffd3f9 0xfffffe631ffffd3f

def z801 : W := mkw 0x100248426238ecc8 0x2100248426238ecc 0x700000002279eccb 0x1700000002279ecc

def z802 : W := mkw 0x2d6b40005bef855c 0x42d6b40005bef855 0xbe49c0003ffffff8 0x4be49c0003ffffff

def z803 : W := mkw 0x042a40000a2d8008 0x0042a40000a2d800 0x3e4fc0003e79c009 0xd3e4fc0003e79c00

def z804 : W := mkw 0x0628b0ac80000000 0x00628b0ac8000000 0x4e4fd9cfc0000007 0xd4e4fd9cfc000000

def z805 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0xf04ff9cfe279fccf 0xff04ff9cfe279fcc

def z806 : W := mkw 0x0094021100000000 0x0009402110000000 0xd1b62631c38e3fff 0xbd1b62631c38e3ff

def z807 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0xbff03fc03ffe3f0f 0xfbff03fc03ffe3f0

def z808 : W := mkw 0x100248426638fcca 0x2100248426638fcc 0xb00000003e79fcc8 0x0b00000003e79fcc

def z809 : W := mkw 0x142a48426a3decc8 0x2142a48426a3decc 0xbe3800003e7fecc9 0x7be3800003e7fecc

def z810 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xbff9c0003fffc008 0x6bff9c0003fffc00

def z811 : W := mkw 0x2d6940001965800c 0x02d6940001965800 0x2e4fc0003c71c001 0xd2e4fc0003c71c00

def z812 : W := mkw 0x1200bdc6a4107a83 0x21200bdc6a4107a8 0x000019ce00000000 0x0000019ce0000000

def z813 : W := mkw 0x00960211428a0550 0x400960211428a055 0xd1b62631c38e3ff9 0x2d1b62631c38e3ff

def z814 : W := mkw 0x0628302808050000 0x0062830280805000 0xee38383e3c0ff0fb 0x7ee38383e3c0ff0f

def z815 : W := mkw 0x0200b08480000000 0x00200b0848000000 0x4e4ff9cfc0000007 0xf4e4ff9cfc000000

def z816 : W := mkw 0x0628302a080540a0 0x80628302a080540a 0xee38383e3c0fc0fb 0x7ee38383e3c0fc0f

def z817 : W := mkw 0x06283d2a2c0572a3 0x806283d2a2c0572a 0xee383e3e3c0ff3fb 0x7ee383e3e3c0ff3f

def z818 : W := mkw 0x4ffdb7bd80000110 0x44ffdb7bd8000011 0x4fffffffc0001337 0xf4fffffffc000133

def z819 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xce38383e1c0ff0f3 0x2ce38383e1c0ff0f

def z820 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xae7fc0003c7fc009 0x7ae7fc0003c7fc00

def z821 : W := mkw 0x4295b7bd80000000 0x04295b7bd8000000 0x4007ffffc0000006 0x04007ffffc000000

def z822 : W := mkw 0x49d5879580000000 0x049d587958000000 0x41c7dfcfc0000006 0x841c7dfcfc000000

def z823 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x71cfffcfe279eccf 0xf71cfffcfe279ecc

def z824 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x707fd9ffe27fecff 0xd707fd9ffe27fecf

def z825 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0x3fc01fc03ff02f0e 0xd3fc01fc03ff02f0

def z826 : W := mkw 0x6ffdb7bd99450004 0x06ffdb7bd9945000 0x4fffffffdc000007 0xf4fffffffdc00000

def z827 : W := mkw 0x3002484273faeccc 0x23002484273faecc 0x3000000023f9ecc8 0x03000000023f9ecc

def z828 : W := mkw 0x0628386a2c1578a2 0x80628386a2c1578a 0xee7839fe3c7ff0fb 0x7ee7839fe3c7ff0f

def z829 : W := mkw 0x300248426abfeccc 0x2300248426abfecc 0x30000000227fecc8 0x030000000227fecc

def z830 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xbfffd9c03fffc00f 0xfbfffd9c03fffc00

def z831 : W := mkw 0x4ffdb7bd80820110 0x44ffdb7bd8082011 0xcfffffffc18e33ff 0xfcfffffffc18e33f

def z832 : W := mkw 0x0f68b5ac80000000 0x00f68b5ac8000000 0x4fffffffc0000007 0xf4fffffffc000000

def z833 : W := mkw 0x00960211428a0550 0x400960211428a055 0xd1be3e3fc38e3fff 0xfd1be3e3fc38e3ff

def z834 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0x6e38183e3c0fe0fb 0x56e38183e3c0fe0f

def z835 : W := mkw 0x4ffd37391d451223 0x84ffd37391d45122 0x8fb026301d861330 0x28fb026301d86133

def z836 : W := mkw 0x6ffd37391dc71207 0x06ffd37391dc7120 0x8fb026301d861300 0x28fb026301d86130

def z837 : W := mkw 0x6ffdb7bd99c70114 0x46ffdb7bd99c7011 0xcfffffffdd861337 0xfcfffffffdd86133

def z838 : W := mkw 0x2dfd400019e7800c 0x02dfd400019e7800 0x2fc9c0003df1c000 0x42fc9c0003df1c00

def z839 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0xffc83fce3ff03f0f 0xfffc83fce3ff03f0

def z840 : W := mkw 0x0940400011608008 0x0094040001160800 0xbfc9c0003ff1c008 0xfbfc9c0003ff1c00

def z841 : W := mkw 0x00960211428a0550 0x400960211428a055 0xd1b62631c3863ff6 0xad1b62631c3863ff

def z842 : W := mkw 0x0000808480000000 0x0000080848000000 0x4047d9cfc0000006 0x84047d9cfc000000

def z843 : W := mkw 0x0940054011500a01 0x00940054011500a0 0xbfc027c03ff03f0e 0xfbfc027c03ff03f0

def z844 : W := mkw 0x0002c886a228e088 0x00002c886a228e08 0x704fd9cfe279e0cf 0xd704fd9cfe279e0c

def z845 : W := mkw 0x46bdb7bd80000000 0x046bdb7bd8000000 0x407fffffc0000007 0xd407fffffc000000

def z846 : W := mkw 0x19d6c7d5d3fa8f59 0x619d6c7d5d3fa8f5 0x11c7c7c1c3f00f04 0x811c7c7c1c3f00f0

def z847 : W := mkw 0x2dfd400019e7800c 0x02dfd400019e7800 0xafffc0003df7c001 0xfafffc0003df7c00

def z848 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0xbfcfffc03ff03f0f 0xfbfcfffc03ff03f0

def z849 : W := mkw 0x100248426238ecc8 0x2100248426238ecc 0x300000002271cc00 0x0300000002271cc0

def z850 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x704fffcfe279ffcf 0xd704fffcfe279ffc

def z851 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xbfffc0003fffec0f 0xfbfffc0003fffec0

def z852 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x0fcfffcfc0000006 0xf0fcfffcfc000000

def z853 : W := mkw 0x0200b0ac80000000 0x00200b0ac8000000 0x404ff9ffc0000007 0xd404ff9ffc000000

def z854 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x0fffdfcfc0000005 0xf0fffdfcfc000000

def z855 : W := mkw 0x0000c08480208008 0x00000c0848020800 0x604fd9cfe071c007 0xd604fd9cfe071c00

def z856 : W := mkw 0x4ffdb7bd84001203 0x04ffdb7bd8400120 0x4fffffffc0001307 0xf4fffffffc000130

def z857 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x504fd9cfc279ecc7 0x8504fd9cfc279ecc

def z858 : W := mkw 0x0000808480000000 0x0000080848000000 0x400fd9cfc0000007 0x0400fd9cfc000000

def z859 : W := mkw 0x04bd808480000000 0x004bd80848000000 0x407fd9cfc0000007 0xd407fd9cfc000000

def z860 : W := mkw 0x6ffd373919450004 0x06ffd37391945000 0x0fb026301c000000 0x20fb026301c00000

def z861 : W := mkw 0x0628302a0c0550a2 0x80628302a0c0550a 0xee38203e3c0fd0f9 0x7ee38203e3c0fd0f

def z862 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0xfff03ff03ff03f0f 0xffff03ff03ff03f0

def z863 : W := mkw 0x1000c8c6e030ecc8 0x21000c8c6e030ecc 0x604fd9cfe071ecc7 0xd604fd9cfe071ecc

def z864 : W := mkw 0x0094808480000000 0x0009480848000000 0x41ffd9cfc0000007 0xf41ffd9cfc000000

def z865 : W := mkw 0x2dff42115bef844c 0x02dff42115bef844 0xffffe631ffffeccf 0xfffffe631ffffecc

def z866 : W := mkw 0x2d6940001965800c 0x02d6940001965800 0xbff9c0003fffc009 0xfbff9c0003fffc00

def z867 : W := mkw 0x2d6b40005b6d844c 0x02d6b40005b6d844 0x7e4fc001fe79eccf 0xd7e4fc001fe79ecc

def z868 : W := mkw 0x2dfd40001965800c 0x02dfd40001965800 0x2e7fc0003c71c001 0x42e7fc0003c71c00

def z869 : W := mkw 0x300248427bffeddc 0x6300248427bffedd 0xb00000003ffffff8 0x0b00000003ffffff

def z870 : W := mkw 0x00960211428a0550 0x400960211428a055 0xffb62631ff8e3fff 0xfffb62631ff8e3ff

def z871 : W := mkw 0x49d58f97ac0570a2 0x849d58f97ac0570a 0xa1c7c7c1fc0ff0fc 0x8a1c7c7c1fc0ff0f

def z872 : W := mkw 0x2dff40005bef855c 0x42dff40005bef855 0xffffc001ffffffff 0xfffffc001fffffff

def z873 : W := mkw 0x00960211428a0550 0x400960211428a055 0xd1f63ff1c38e3fff 0xfd1f63ff1c38e3ff

def z874 : W := mkw 0x4ffdb7bd8c871132 0xc4ffdb7bd8c87113 0xcfffffffdd861337 0xfcfffffffdd86133

def z875 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xbfcfc0003ff1c008 0xfbfcfc0003ff1c00

def z876 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xffffc0003fffe0cb 0xfffffc0003fffe0c

def z877 : W := mkw 0x4f69bdeebd557aa3 0x84f69bdeebd557aa 0x2e49d9ce3c71c000 0x42e49d9ce3c71c00

def z878 : W := mkw 0x00960211428a0550 0x400960211428a055 0xc1b62631c18e3ff7 0x2c1b62631c18e3ff

def z879 : W := mkw 0x00960211428a0550 0x400960211428a055 0xd1ffe631c38e3fff 0xfd1ffe631c38e3ff

def z880 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0xf1cfd9cfe3f9eccf 0xff1cfd9cfe3f9ecc

def z881 : W := mkw 0x4ffdb7bd95c21313 0x44ffdb7bd95c2131 0xcfffffffdd861337 0xfcfffffffdd86133

def z882 : W := mkw 0x100248427778fecb 0x2100248427778fec 0x300000003e79ecc8 0x0300000003e79ecc

def z883 : W := mkw 0x24bf40001bef800c 0x024bf40001bef800 0xbe3fc0003fffc009 0x7be3fc0003fffc00

def z884 : W := mkw 0x44bd8afdb5503a03 0x044bd8afdb5503a0 0xf03fc03ffff03f09 0x0f03fc03ffff03f0

def z885 : W := mkw 0x4941858480000000 0x0494185848000000 0x404fd9cfc0000007 0xd404fd9cfc000000

def z886 : W := mkw 0x4ffdb7bd84001022 0x84ffdb7bd8400102 0x4fffffffc0001037 0xf4fffffffc000103

def z887 : W := mkw 0x0000808480000000 0x0000080848000000 0xd1cfffcfc3803f0f 0xfd1cfffcfc3803f0

def z888 : W := mkw 0x0628b0ac8c051022 0x80628b0ac8c05102 0xce7ff9ffdc061037 0xfce7ff9ffdc06103

def z889 : W := mkw 0x0096421142aa8558 0x40096421142aa855 0xd1f7e631c3fe3fff 0xbd1f7e631c3fe3ff

def z890 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x4e7fd9ffc0000007 0xd4e7fd9ffc000000

def z891 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xffffc001ffffc00f 0xfffffc001ffffc00

def z892 : W := mkw 0x4ffdb7bd80820000 0x04ffdb7bd8082000 0xcfffffffc1860007 0xfcfffffffc186000

def z893 : W := mkw 0x1002c0c4c2388c48 0x21002c0c4c2388c4 0x704fd9cfe279cc0f 0xd704fd9cfe279cc0

def z894 : W := mkw 0x1002c8c6e238edd8 0x61002c8c6e238edd 0x704fd9cfe279ffff 0xd704fd9cfe279fff

def z895 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xbfffe0303fffd039 0xfbfffe0303fffd03

def z896 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xfe38383e3e0ffcff 0xffe38383e3e0ffcf

def z897 : W := mkw 0x1200bdc6e4107ec3 0x21200bdc6e4107ec 0x400019cfc0002cc6 0x0400019cfc0002cc

def z898 : W := mkw 0x0628386a2c157aa3 0x80628386a2c157aa 0xee38383e3c0ffffb 0x7ee38383e3c0ffff

def z899 : W := mkw 0x2dfd808499c70004 0x02dfd808499c7000 0xcfffd9cfdd860007 0xfcfffd9cfdd86000

def z900 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xee38203e3c0ff0f9 0x2ee38203e3c0ff0f

def z901 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0xcfffffffc1801307 0xfcfffffffc180130

def z902 : W := mkw 0x44bd82bd80000000 0x044bd82bd8000000 0x41ffffffc0000007 0xf41ffffffc000000

def z903 : W := mkw 0x09400d4031502a01 0x009400d4031502a0 0xbfc01fc03ff02f0e 0xfbfc01fc03ff02f0

def z904 : W := mkw 0x194248427378ecc8 0x2194248427378ecc 0xbfc000003ff9ecc8 0xfbfc000003ff9ecc

def z905 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0xf04fd9cfe3f9ffcf 0xdf04fd9cfe3f9ffc

def z906 : W := mkw 0x2d6940001965800c 0x02d6940001965800 0xafc9c0003df1c000 0x6afc9c0003df1c00

def z907 : W := mkw 0x26bf7d402ebfba0f 0x026bf7d402ebfba0 0x003fffc0000fff07 0x0003fffc0000fff0

def z908 : W := mkw 0x0b40354015501a03 0x00b40354015501a0 0x1fc007c01ff00f04 0x81fc007c01ff00f0

def z909 : W := mkw 0x4ffdb7bd88050000 0x04ffdb7bd8805000 0x6ffffffffc01c007 0xf6ffffffffc01c00

def z910 : W := mkw 0x1002c8c6e638fcea 0xa1002c8c6e638fce 0x704fd9cfe279fcff 0xd704fd9cfe279fcf

def z911 : W := mkw 0x2dff42115bef855c 0x42dff42115bef855 0xbfffc001ffffc009 0xfbfffc001ffffc00

def z912 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x4e7fffffc0000007 0x44e7fffffc000000

def z913 : W := mkw 0x2dff42115bef855c 0x42dff42115bef855 0xffffe631ffffc0ff 0xfffffe631ffffc0f

def z914 : W := mkw 0x4095829580000000 0x0409582958000000 0x404fd9cfc0000007 0xd404fd9cfc000000

def z915 : W := mkw 0x1002c8c6e2baedd8 0x61002c8c6e2baedd 0xf07ff9ffe3ffffff 0xff07ff9ffe3fffff

def z916 : W := mkw 0x2dfd40001965800c 0x02dfd40001965800 0x2fcfc0003c71c000 0xc2fcfc0003c71c00

def z917 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0xbff03ff03ff63f3e 0xfbff03ff03ff63f3

def z918 : W := mkw 0x0094021140820550 0x4009402114082055 0xc1b02631c18e3fff 0x3c1b02631c18e3ff

def z919 : W := mkw 0x2dff42115bef855c 0x42dff42115bef855 0xffffe031fffff0fb 0xfffffe031fffff0f

def z920 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x7fffffffe270000f 0xf7fffffffe270000

def z921 : W := mkw 0x4f69b5ac80000000 0x04f69b5ac8000000 0x4e4fd9cfc0000001 0x44e4fd9cfc000000

def z922 : W := mkw 0x2dff42115bef855c 0x42dff42115bef855 0x6e7fc031fc7fc0f1 0x46e7fc031fc7fc0f

def z923 : W := mkw 0x100248426238ecc8 0x2100248426238ecc 0xb000000023f9ffc8 0x0b000000023f9ffc

def z924 : W := mkw 0x2dff42111bef811c 0x42dff42111bef811 0xbfffc0303fffc039 0xfbfffc0303fffc03

def z925 : W := mkw 0x0b403d4235507a83 0x00b403d4235507a8 0xffc03fce3ff03fce 0xfffc03fce3ff03fc

def z926 : W := mkw 0x09400d4035503a03 0x009400d4035503a0 0xbfc007c03ff03f0c 0xfbfc007c03ff03f0

def z927 : W := mkw 0x64bfc2bdcaaf855c 0x464bfc2bdcaaf855 0x403fc03fc00fc0f1 0x0403fc03fc00fc0f

def z928 : W := mkw 0x4200b7bd80000000 0x04200b7bd8000000 0x400fffffc0000007 0x0400fffffc000000

def z929 : W := mkw 0x2dfd421119e7811c 0x42dfd421119e7811 0xaff9e6303df7d330 0x6aff9e6303df7d33

def z930 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xee38383e3c0fd0f1 0x6ee38383e3c0fd0f

def z931 : W := mkw 0x6ffdb7bd88870004 0x06ffdb7bd8887000 0x4fffffffc0060007 0xf4fffffffc006000

def z932 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x71cfdfcfe3f9efcf 0xd71cfdfcfe3f9efc

def z933 : W := mkw 0x1f68fdeebd75faab 0xa1f68fdeebd75faa 0x2e49d9ce3c71c000 0x42e49d9ce3c71c00

def z934 : W := mkw 0x39d7c2d5d3fa8d5c 0x639d7c2d5d3fa8d5 0x11c7c7c1c3f00f04 0x811c7c7c1c3f00f0

def z935 : W := mkw 0x0428080228056080 0x0042808022805608 0xee38383e3c0ff0fb 0x7ee38383e3c0ff0f

def z936 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xafffc0003dffc001 0x6afffc0003dffc00

def z937 : W := mkw 0x34bfc297caafc5dc 0x634bfc297caafc5d 0x403fc03fc00fc0f1 0x0403fc03fc00fc0f

def z938 : W := mkw 0x0094829580820110 0x4009482958082011 0xc1ffffffc1861337 0xfc1ffffffc186133

def z939 : W := mkw 0x0002400002288008 0x0000240000228800 0xbe4fc0003e79c009 0xfbe4fc0003e79c00

def z940 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xae38383e3c0ff0f8 0x6ae38383e3c0ff0f

def z941 : W := mkw 0x46bdb7bd80000000 0x046bdb7bd8000000 0x4e3fffffc0000007 0x74e3fffffc000000

def z942 : W := mkw 0x0000808480000000 0x0000080848000000 0x404fd9cfc00820cf 0xd404fd9cfc00820c

def z943 : W := mkw 0x09d6400013ea8008 0x009d6400013ea800 0xbfffc0003fffc009 0xfbfffc0003fffc00

def z944 : W := mkw 0x4dfd879580000000 0x04dfd87958000000 0x4fffdfcfc0000007 0xf4fffdfcfc000000

def z945 : W := mkw 0x100248426238edd8 0x6100248426238edd 0x300000002279fff8 0x0300000002279fff

def z946 : W := mkw 0x300248427ffffcee 0xa300248427ffffce 0xb00000003ffffcf8 0x0b00000003ffffcf

def z947 : W := mkw 0x29d740001bef800c 0x029d740001bef800 0xbfc7c0003fffc008 0xfbfc7c0003fffc00

def z948 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xbfbfc0003fffc009 0x2bfbfc0003fffc00

def z949 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x5fffffffc3800f07 0xf5fffffffc3800f0

def z950 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xfe38383e3f8ffffb 0x7fe38383e3f8ffff

def z951 : W := mkw 0x09d5808480000000 0x009d580848000000 0x41cfd9cfc0000007 0xd41cfd9cfc000000

def z952 : W := mkw 0x2d6940001965800c 0x02d6940001965800 0xae79c0003c77c000 0x6ae79c0003c77c00

def z953 : W := mkw 0x0094021140820550 0x4009402114082055 0xc1b62631c1863ff7 0xbc1b62631c1863ff

def z954 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0xcfffffffc0061037 0xfcfffffffc006103

def z955 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xbff7c0003fffc008 0xabff7c0003fffc00

def z956 : W := mkw 0x24bf40000aaf800c 0x024bf40000aaf800 0xbe7fc0003e7fc009 0xfbe7fc0003e7fc00

def z957 : W := mkw 0x100248426638fcea 0xa100248426638fce 0x300000002279fcf8 0x0300000002279fcf

def z958 : W := mkw 0x4dfd82bd80000000 0x04dfd82bd8000000 0x4fffd9ffc0000007 0xf4fffd9ffc000000

def z959 : W := mkw 0x0b403d6835503a03 0x00b403d6835503a0 0xffc03ffe3ff03f0e 0xfffc03ffe3ff03f0

def z960 : W := mkw 0x4ffdb7bd91400000 0x04ffdb7bd9140000 0x6ffffffffc700007 0xf6ffffffffc70000

def z961 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0xcfffffffc00e000f 0xfcfffffffc00e000

def z962 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0xbfc03fc03ff03f08 0x6bfc03fc03ff03f0

def z963 : W := mkw 0x0b40354015501a03 0x00b40354015501a0 0x9fc027c01ff03f0e 0xb9fc027c01ff03f0

def z964 : W := mkw 0x4ffdb7bd91400201 0x04ffdb7bd9140020 0x4fffffffc1800307 0xf4fffffffc180030

def z965 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0xbf803fc03ff03f0e 0x2bf803fc03ff03f0

def z966 : W := mkw 0x4bd5b7bd80000000 0x04bd5b7bd8000000 0x41f7ffffc0000007 0xb41f7ffffc000000

def z967 : W := mkw 0x0002c8c4a238a808 0x00002c8c4a238a80 0x704fd9cfe279ec0f 0xd704fd9cfe279ec0

def z968 : W := mkw 0x0b40350011400000 0x00b4035001140000 0xbfc03fc03ff03f0e 0xfbfc03fc03ff03f0

def z969 : W := mkw 0x1296bfd7e69a7fd3 0x61296bfd7e69a7fd 0xd1b63fffc38e3fff 0xbd1b63fffc38e3ff

def z970 : W := mkw 0x2dfd400019e7800c 0x02dfd400019e7800 0x2e79c0003c77c000 0x42e79c0003c77c00

def z971 : W := mkw 0x1b427d427778fecb 0x21b427d427778fec 0xbf8026003ff9ffc8 0x2bf8026003ff9ffc

def z972 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x4fffffffc00030f7 0xf4fffffffc00030f

def z973 : W := mkw 0x4bd5b79580000000 0x04bd5b7958000000 0x4fcfffcfc0000007 0xf4fcfffcfc000000

def z974 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0xbfc03fc03ff01f04 0xebfc03fc03ff01f0

def z975 : W := mkw 0x4ffdb7bd84001002 0x04ffdb7bd8400100 0xcfffffffdc001007 0xfcfffffffdc00100

def z976 : W := mkw 0x0b403d6a35507aa3 0x80b403d6a35507aa 0xbfc03fce3ff03f0e 0xfbfc03fce3ff03f0

def z977 : W := mkw 0x2dff42115bef855c 0x42dff42115bef855 0xffffc631ffffcffd 0xfffffc631ffffcff

def z978 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0xf04fd9cfe27ffcff 0xdf04fd9cfe27ffcf

def z979 : W := mkw 0x1002c8c6a238e888 0x21002c8c6a238e88 0x704fd9cfe279c00f 0xd704fd9cfe279c00

def z980 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xffffd80e3fffc00b 0xfffffd80e3fffc00

def z981 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x4fffffffc00820cf 0xf4fffffffc00820c

def z982 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x204fd9cfe071c000 0x4204fd9cfe071c00

def z983 : W := mkw 0x00960211428a0550 0x400960211428a055 0xf1be2631e38fffff 0xff1be2631e38ffff

def z984 : W := mkw 0x06283d2a2c0570a2 0x806283d2a2c0570a 0xee383ffe3c0ff0ff 0x7ee383ffe3c0ff0f

def z985 : W := mkw 0x2dff42115bef855c 0x42dff42115bef855 0xffffc031fffffff9 0xfffffc031fffffff

def z986 : W := mkw 0x0000808480000000 0x0000080848000000 0x604fd9cfe009c00f 0xd604fd9cfe009c00

def z987 : W := mkw 0x2d6b40001b6d800c 0x02d6b40001b6d800 0x2e4fc0003c79c001 0x42e4fc0003c79c00

def z988 : W := mkw 0x0940054011500a01 0x00940054011500a0 0x9fc007c01ff00f04 0xa9fc007c01ff00f0

def z989 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x4fcfdfcfc0000007 0xd4fcfdfcfc000000

def z990 : W := mkw 0x1200baffe4107df2 0xe1200baffe4107df 0x40003fffc0003ff6 0x040003fffc0003ff

def z991 : W := mkw 0x2dff45001bef820d 0x02dff45001bef820 0xbfffc6003fffc309 0xfbfffc6003fffc30

def z992 : W := mkw 0x0ffdb0ac80000000 0x00ffdb0ac8000000 0x4ffff9ffc0000007 0xf4ffff9ffc000000

def z993 : W := mkw 0x300248427ffffecf 0x2300248427ffffec 0xb00000003fffffc8 0x0b00000003fffffc

def z994 : W := mkw 0x4ffdb5ac80000000 0x04ffdb5ac8000000 0x4fffd9cfc0000007 0xf4fffd9cfc000000

def z995 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0x6e38383e3c0ff0f3 0x46e38383e3c0ff0f

def z996 : W := mkw 0x2d6940001965800c 0x02d6940001965800 0x2fc9c0003c71c000 0xf2fc9c0003c71c00

def z997 : W := mkw 0x0000829580000000 0x0000082958000000 0x404fffffc0000007 0xd404fffffc000000

def z998 : W := mkw 0x4ffdb7bd91400000 0x04ffdb7bd9140000 0x5fffffffc3f00007 0xf5fffffffc3f0000

def z999 : W := mkw 0x4ffdb7bd88050020 0x84ffdb7bd8805002 0x4fffffffc0060037 0xf4fffffffc006003

def z1000 : W := mkw 0x46bdb7bd80000000 0x046bdb7bd8000000 0x403fd9ffc0000001 0x0403fd9ffc000000

def z1001 : W := mkw 0x2d6b40001bef800c 0x02d6b40001bef800 0x2e49c0003c7fc000 0x42e49c0003c7fc00

def z1002 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0xeffffffffc00000f 0xfeffffffffc00000

def z1003 : W := mkw 0x0940054011500a01 0x00940054011500a0 0x3fc007c03ff00f04 0xc3fc007c03ff00f0

def z1004 : W := mkw 0x0dfd000019450000 0x00dfd00001945000 0xbfffc0003fffc009 0xfbfffc0003fffc00

def z1005 : W := mkw 0x1002c8c6e2baedd8 0x61002c8c6e2baedd 0xf1cfffcfe3ffffff 0xff1cfffcfe3fffff

def z1006 : W := mkw 0x49d5879580000000 0x049d587958000000 0x41ffffffc0000007 0xf41ffffffc000000

def z1007 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x0e4fd9cfc0000000 0x40e4fd9cfc000000

def z1008 : W := mkw 0x2dff42111bef800c 0x02dff42111bef800 0xffffc031ffffc009 0xfffffc031ffffc00

def z1009 : W := mkw 0x2d6940001965800c 0x02d6940001965800 0x2e49c0003c79c009 0x52e49c0003c79c00

def z1010 : W := mkw 0x2d6940001965800c 0x02d6940001965800 0xae49c0003c7fc008 0x4ae49c0003c7fc00

def z1011 : W := mkw 0x0dff40000a2d8008 0x00dff40000a2d800 0xbfffc0003e7fc009 0xfbfffc0003e7fc00

def z1012 : W := mkw 0x6ffdb7bd91c20004 0x06ffdb7bd91c2000 0x4fffffffc1800007 0xf4fffffffc180000

def z1013 : W := mkw 0x2dff42115bef855c 0x42dff42115bef855 0xffffc031ffffecff 0xfffffc031ffffecf

def z1014 : W := mkw 0x2dff40005bef855c 0x42dff40005bef855 0xbfffc0003fffc0f9 0xfbfffc0003fffc0f

def z1015 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x304fd9cfe279cc0d 0xd304fd9cfe279cc0

def z1016 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x4fffd9ffc0000001 0xf4fffd9ffc000000

def z1017 : W := mkw 0x0dfd829580000000 0x00dfd82958000000 0x4fffffffc0000007 0xf4fffffffc000000

def z1018 : W := mkw 0x2dff42115bef855c 0x42dff42115bef855 0xbfffc601fffffffd 0xfbfffc601fffffff

def z1019 : W := mkw 0x4ffdb7bd8c051022 0x84ffdb7bd8c05102 0x4fffffffdc000007 0xf4fffffffdc00000

def z1020 : W := mkw 0x0628386a2c1578a2 0x80628386a2c1578a 0xfff83ffe3fffffff 0xffff83ffe3ffffff

def z1021 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0x2fffc0003c7fc001 0xf2fffc0003c7fc00

def z1022 : W := mkw 0x06283d6a2c157aa3 0x806283d6a2c157aa 0xee3839fe3c0ff0fb 0x7ee3839fe3c0ff0f

def z1023 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x304fd9cfe279eccc 0xc304fd9cfe279ecc

def z1024 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0x6e38383e3c0fc0f3 0x76e38383e3c0fc0f

def z1025 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x4fffffffc0000001 0x64fffffffc000000

def z1026 : W := mkw 0x2dfd40001965800c 0x02dfd40001965800 0xafffc0003c7fc009 0xfafffc0003c7fc00

def z1027 : W := mkw 0x4ffdb7bd95401203 0x04ffdb7bd9540120 0x4fffffffdc000007 0xf4fffffffdc00000

def z1028 : W := mkw 0x2d6940001965800c 0x02d6940001965800 0x2e79c0003c71c001 0x72e79c0003c71c00

def z1029 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0xdfffffffc380000f 0xfdfffffffc380000

def z1030 : W := mkw 0x0428400008258008 0x0042840000825800 0xae79c0003c7fc009 0x7ae79c0003c7fc00

def z1031 : W := mkw 0x2dff40281bef800c 0x02dff40281bef800 0xffffc03e3fffc009 0xfffffc03e3fffc00

def z1032 : W := mkw 0x100248427378eec9 0x2100248427378eec 0x3000000023f9efc8 0x03000000023f9efc

def z1033 : W := mkw 0x100248426238ecc8 0x2100248426238ecc 0x300800002279ecc9 0x5300800002279ecc

def z1034 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xee30383e3c0ff0fa 0x2ee30383e3c0ff0f

def z1035 : W := mkw 0x2dfd400019e7800c 0x02dfd400019e7800 0xaff9c0003dffc009 0x7aff9c0003dffc00

def z1036 : W := mkw 0x2dff42111bef800c 0x02dff42111bef800 0xbfffc601ffffc00d 0xfbfffc601ffffc00

def z1037 : W := mkw 0x2dff42115bef855c 0x42dff42115bef855 0xffffe631ffffcf0f 0xfffffe631ffffcf0

def z1038 : W := mkw 0x100248426a3decc8 0x2100248426a3decc 0xb00000003e7fecc8 0x0b00000003e7fecc

def z1039 : W := mkw 0x4200b7bd80000000 0x04200b7bd8000000 0x4047ffffc0000006 0x84047ffffc000000

def z1040 : W := mkw 0x2dff42111bef800c 0x02dff42111bef800 0xffffe631fffff0ff 0xfffffe631fffff0f

def z1041 : W := mkw 0x2dff40005bef844c 0x02dff40005bef844 0xbfffc0003fffecc9 0xfbfffc0003fffecc

def z1042 : W := mkw 0x100248426238ecc8 0x2100248426238ecc 0x1000000002702cc0 0x01000000002702cc

def z1043 : W := mkw 0x2dfd40001965800c 0x02dfd40001965800 0x2ff9c0003c71c000 0x62ff9c0003c71c00

def z1044 : W := mkw 0x44bd82bd80000000 0x044bd82bd8000000 0x407fd9ffc0000001 0x4407fd9ffc000000

def z1045 : W := mkw 0x2097421142aa855c 0x42097421142aa855 0xd1b7e631c38e3fff 0xbd1b7e631c38e3ff

def z1046 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0xf07fd9cfe27feccf 0xff07fd9cfe27fecc

def z1047 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xee7ff83e3c0ff0fb 0xfee7ff83e3c0ff0f

def z1048 : W := mkw 0x100248426e3dfcea 0xa100248426e3dfce 0x300000003e79ecc8 0x0300000003e79ecc

def z1049 : W := mkw 0x1002484277faffdb 0x61002484277faffd 0xb00000003ffffff8 0x0b00000003ffffff

def z1050 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x304fd9cfe271ec0e 0xd304fd9cfe271ec0

def z1051 : W := mkw 0x0200b58480000000 0x00200b5848000000 0x404fffcfc0000007 0xd404fffcfc000000

def z1052 : W := mkw 0x2dff40005bef844c 0x02dff40005bef844 0xbfffc001ffffcc0d 0xfbfffc001ffffcc0

def z1053 : W := mkw 0x0628386a2c1578a2 0x80628386a2c1578a 0xee3839fe3c0ffcff 0x7ee3839fe3c0ffcf

def z1054 : W := mkw 0x44bd82bd80000000 0x044bd82bd8000000 0x403fd9ffc0000007 0x0403fd9ffc000000

def z1055 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0xffc03fc03ff83fcf 0xfffc03fc03ff83fc

def z1056 : W := mkw 0x0dff400013688008 0x00dff40001368800 0xbfffc0003ff9c009 0xfbfffc0003ff9c00

def z1057 : W := mkw 0x2dff42111bef811c 0x42dff42111bef811 0xffffe631ffffd33f 0xfffffe631ffffd33

def z1058 : W := mkw 0x2d6b40001bef800c 0x02d6b40001bef800 0xbe4fc0003fffc009 0xdbe4fc0003fffc00

def z1059 : W := mkw 0x1200bdc6a4107a83 0x21200bdc6a4107a8 0x00003fce00003f06 0x000003fce00003f0

def z1060 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x6fffffffe009c00f 0xf6fffffffe009c00

def z1061 : W := mkw 0x0ffdb58480000000 0x00ffdb5848000000 0x4fffffcfc0000007 0xf4fffffcfc000000

def z1062 : W := mkw 0x0942400013688008 0x0094240001368800 0x3e4fc0003e79c009 0xd3e4fc0003e79c00

def z1063 : W := mkw 0x2dff40005bef844c 0x02dff40005bef844 0xffffe031fffffcff 0xfffffe031fffffcf

def z1064 : W := mkw 0x2d6940001965800c 0x02d6940001965800 0xbfc9e6003ff1ff0e 0xfbfc9e6003ff1ff0

def z1065 : W := mkw 0x4ffdb7bd95401203 0x04ffdb7bd9540120 0xfffffffffff0130f 0xffffffffffff0130

def z1066 : W := mkw 0x4ffdb7bd91400000 0x04ffdb7bd9140000 0xcfffffffdd800007 0xfcfffffffdd80000

def z1067 : W := mkw 0x4ffdb7bd88050000 0x04ffdb7bd8805000 0xcfffffffdc060007 0xfcfffffffdc06000

def z1068 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0xbfc027c03ff03f0c 0xabfc027c03ff03f0

def z1069 : W := mkw 0x2d6b40001b6d800c 0x02d6b40001b6d800 0x3e4fc0003e71c000 0xc3e4fc0003e71c00

def z1070 : W := mkw 0x5200bfffe4107ce2 0xa5200bfffe4107ce 0x40003fffc0003cf6 0x040003fffc0003cf

def z1071 : W := mkw 0x2dff40281bef802c 0x82dff40281bef802 0xbfffc0303fffc039 0xfbfffc0303fffc03

def z1072 : W := mkw 0x4f69b5ac80000000 0x04f69b5ac8000000 0x0e4fd9cfc0000004 0xc0e4fd9cfc000000

def z1073 : W := mkw 0x0628302a0c0550a2 0x80628302a0c0550a 0xce38383e1c0fd0f3 0x7ce38383e1c0fd0f

def z1074 : W := mkw 0x1000c8c6a030e888 0x21000c8c6a030e88 0x204fd9cfe071c004 0xc204fd9cfe071c00

def z1075 : W := mkw 0x6ffdb7bd9dc71207 0x06ffdb7bd9dc7120 0xcfffffffdd861307 0xfcfffffffdd86130

def z1076 : W := mkw 0x2d6b40001bef800c 0x02d6b40001bef800 0x3e49c0003ff1c000 0x43e49c0003ff1c00

def z1077 : W := mkw 0x0428808488050000 0x0042880848805000 0xee7fd9cffc0fc00f 0xfee7fd9cffc0fc00

def z1078 : W := mkw 0x2dff40005bef844c 0x02dff40005bef844 0xffffc001ffffc0c9 0xfffffc001ffffc0c

def z1079 : W := mkw 0x242a40001bef800c 0x0242a40001bef800 0xbe7fc0003fffc009 0xfbe7fc0003fffc00

def z1080 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xefb83e3e3c0ff0ff 0xfefb83e3e3c0ff0f

def z1081 : W := mkw 0x4dfd87bd80000000 0x04dfd87bd8000000 0x41ffdfffc0000007 0xd41ffdfffc000000

def z1082 : W := mkw 0x0b40b58495401203 0x00b40b5849540120 0xcfcfffcfdd801307 0xfcfcfffcfdd80130

def z1083 : W := mkw 0x2d6940001965800c 0x02d6940001965800 0xbe49c0003ff1c008 0x4be49c0003ff1c00

def z1084 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0xdfffffffc38e3fff 0xfdfffffffc38e3ff

def z1085 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xee7839fe3c0ff0ff 0xfee7839fe3c0ff0f

def z1086 : W := mkw 0x100248427378ecc8 0x2100248427378ecc 0xb00000003ff9ecc8 0x0b00000003ff9ecc

def z1087 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xffffc0303fffc0f9 0xfffffc0303fffc0f

def z1088 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x41ffffffc0000007 0x841ffffffc000000

def z1089 : W := mkw 0x0094829580000000 0x0009482958000000 0x41cfdfcfc0000007 0xd41cfdfcfc000000

def z1090 : W := mkw 0x2dfd42111965800c 0x02dfd42111965800 0x6fffe631fc71c007 0xf6fffe631fc71c00

def z1091 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0x3fffc0003ff1c001 0xf3fffc0003ff1c00

def z1092 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xbfffc0003ff7c000 0xebfffc0003ff7c00

def z1093 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0xbfc03fc03ffe3ffe 0xfbfc03fc03ffe3ff

def z1094 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x704ff9ffe279fcff 0xd704ff9ffe279fcf

def z1095 : W := mkw 0x2dfd40001965800c 0x02dfd40001965800 0xbfffc0003ff1c009 0xfbfffc0003ff1c00

def z1096 : W := mkw 0x6ffdb7bd9dc71026 0x86ffdb7bd9dc7102 0xcfffffffdd861037 0xfcfffffffdd86103

def z1097 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x4fbfffffc0000007 0x24fbfffffc000000

def z1098 : W := mkw 0x4ffdb7bd80820110 0x44ffdb7bd8082011 0xdfffffffc3863f3f 0xfdfffffffc3863f3

def z1099 : W := mkw 0x0000808480000000 0x0000080848000000 0xc07ff9ffc00e30ff 0xfc07ff9ffc00e30f

def z1100 : W := mkw 0x0200384024103802 0x0020038402410380 0xbfc03fc03ff03f0e 0xfbfc03fc03ff03f0

def z1101 : W := mkw 0x4bd5b7bd80000000 0x04bd5b7bd8000000 0x41cfffffc0000007 0xd41cfffffc000000

def z1102 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xbe7fc0003fffc009 0x4be7fc0003fffc00

def z1103 : W := mkw 0x5200bfffe4107ec3 0x25200bfffe4107ec 0x40003fffc0003fc6 0x040003fffc0003fc

def z1104 : W := mkw 0x1002c8c6e2baecc8 0x21002c8c6e2baecc 0xf04fd9cfe3ffeccf 0xdf04fd9cfe3ffecc

def z1105 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x4fffffffc0003f07 0xf4fffffffc0003f0

def z1106 : W := mkw 0x1002c8c6e2baedd8 0x61002c8c6e2baedd 0x704fd9cfe3f9efcf 0xd704fd9cfe3f9efc

def z1107 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0xcfffffffc000300f 0xfcfffffffc000300

def z1108 : W := mkw 0x00960211428a0550 0x400960211428a055 0x51b62631c38e3ff7 0x851b62631c38e3ff

def z1109 : W := mkw 0x4ffdb7bd91400000 0x04ffdb7bd9140000 0xfffffffffff03f0f 0xffffffffffff03f0

def z1110 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xefb83e3e3d8ff3fb 0x7efb83e3e3d8ff3f

def z1111 : W := mkw 0x0940858480000000 0x0094085848000000 0x41cfdfcfc0000007 0xd41cfdfcfc000000

def z1112 : W := mkw 0x6ffdb7bd99c70004 0x06ffdb7bd99c7000 0xfffffffffff6000f 0xffffffffffff6000

def z1113 : W := mkw 0x4ffdb7bd88050000 0x04ffdb7bd8805000 0x4fffffffc00fc007 0xf4fffffffc00fc00

def z1114 : W := mkw 0x0094829580000000 0x0009482958000000 0x407fd9ffc0000007 0xd407fd9ffc000000

def z1115 : W := mkw 0x4ffdb7bd9d451223 0x84ffdb7bd9d45122 0xcfffffffdd861337 0xfcfffffffdd86133

def z1116 : W := mkw 0x0628386a2c1578a2 0x80628386a2c1578a 0xfe38383e3e7ffcfb 0x7fe38383e3e7ffcf

def z1117 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x704fd9cfe279ccc5 0xc704fd9cfe279ccc

def z1118 : W := mkw 0x0d6a40001b6d8008 0x00d6a40001b6d800 0xbfffc0003fffc009 0xfbfffc0003fffc00

def z1119 : W := mkw 0x04be40000aaf8008 0x004be40000aaf800 0xbfffc0003fffc009 0xfbfffc0003fffc00

def z1120 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x604fd9cfe079e0cb 0x5604fd9cfe079e0c

def z1121 : W := mkw 0x4628b7bd80000000 0x04628b7bd8000000 0x4e7fffffc0000007 0xf4e7fffffc000000

def z1122 : W := mkw 0x100248427f7dfeeb 0xa100248427f7dfee 0xb00000003ffffff8 0x0b00000003ffffff

def z1123 : W := mkw 0x2dff42115bef855c 0x42dff42115bef855 0xbfffe601ffffff0f 0xfbfffe601ffffff0

def z1124 : W := mkw 0x0000021140000550 0x4000002114000055 0xd1b02631c38e3fff 0xbd1b02631c38e3ff

def z1125 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0x3fcfc0003ff9c009 0xd3fcfc0003ff9c00

def z1126 : W := mkw 0x0940808491400000 0x0094080849140000 0xffcfd9cffff0000f 0xfffcfd9cffff0000

def z1127 : W := mkw 0x1000c8c6a030e888 0x21000c8c6a030e88 0x604fd9cfe071c001 0x4604fd9cfe071c00

def z1128 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xbfcfc0003fffc008 0xcbfcfc0003fffc00

def z1129 : W := mkw 0x4ffdb7bd8c051022 0x84ffdb7bd8c05102 0xcfffffffdc0e30ff 0xfcfffffffdc0e30f

def z1130 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x604fd9cfe079ecc7 0x4604fd9cfe079ecc

def z1131 : W := mkw 0x0bd4b79580000000 0x00bd4b7958000000 0x4fffffffc0000007 0xf4fffffffc000000

def z1132 : W := mkw 0x3dff48427bffeccc 0x23dff48427bffecc 0xbfb000003fffecc8 0x2bfb000003fffecc

def z1133 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0xffc03ff03ff03ffe 0xfffc03ff03ff03ff

def z1134 : W := mkw 0x1002484262baecc8 0x21002484262baecc 0xb000000023ffecc8 0x0b000000023ffecc

def z1135 : W := mkw 0x1200b8c6e4107cc2 0x21200b8c6e4107cc 0x400039cfc0003cc6 0x0400039cfc0003cc

def z1136 : W := mkw 0x2dff42111bef811c 0x42dff42111bef811 0xbfffe6303fffff3f 0xfbfffe6303fffff3

def z1137 : W := mkw 0x042a40004a2d8448 0x0042a40004a2d844 0xfe7fe031fe7ffcff 0xffe7fe031fe7ffcf

def z1138 : W := mkw 0x1002484262baedd8 0x61002484262baedd 0x3000000023f9efc8 0x03000000023f9efc

def z1139 : W := mkw 0x4ffdb7bd8c051022 0x84ffdb7bd8c05102 0xeffffffffc0fd03f 0xfeffffffffc0fd03

def z1140 : W := mkw 0x2d6940001965800c 0x02d6940001965800 0x3e49c0003e71c008 0xd3e49c0003e71c00

def z1141 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x704fd9cfe279ecc9 0x4704fd9cfe279ecc

def z1142 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0x9fc03fc01ff03f06 0xa9fc03fc01ff03f0

def z1143 : W := mkw 0x1200b8eea41078a2 0xa1200b8eea41078a 0x000019ce00000000 0x0000019ce0000000

def z1144 : W := mkw 0x0428808480000000 0x0042880848000000 0x4e7fd9cfc0000007 0xf4e7fd9cfc000000

def z1145 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x704fd9cfe271cc07 0xd704fd9cfe271cc0

def z1146 : W := mkw 0x0428002a080540a0 0x80428002a080540a 0xce38003e1c0fc0f1 0x2ce38003e1c0fc0f

def z1147 : W := mkw 0x1202bdc6e6187ec3 0x21202bdc6e6187ec 0xd1863fcfc3883fcf 0xbd1863fcfc3883fc

def z1148 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x0fffffffc0000004 0xe0fffffffc000000

def z1149 : W := mkw 0x1200b8eea41078a2 0xa1200b8eea41078a 0x400039fe000030f2 0x0400039fe000030f

def z1150 : W := mkw 0x100248426238ecc8 0x2100248426238ecc 0xf0302030227ffcfb 0x3f0302030227ffcf

def z1151 : W := mkw 0x0942400053688448 0x0094240005368844 0xffcfe601fff9ffcf 0xfffcfe601fff9ffc

def z1152 : W := mkw 0x000088c6a0106880 0x0000088c6a010688 0x704fd9cfe279eccf 0xd704fd9cfe279ecc

def z1153 : W := mkw 0x2dff42111bef811c 0x42dff42111bef811 0xbfffc6003fffc309 0xfbfffc6003fffc30

def z1154 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0xbfc01fc03ff03f0c 0xcbfc01fc03ff03f0

def z1155 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x704fd9cfe271ecc6 0xc704fd9cfe271ecc

def z1156 : W := mkw 0x1002c8c6e2baedd8 0x61002c8c6e2baedd 0x704fd9cfe27fecff 0xd704fd9cfe27fecf

def z1157 : W := mkw 0x29d7400013ea800c 0x029d7400013ea800 0xbfcfc0003ff9c009 0xfbfcfc0003ff9c00

def z1158 : W := mkw 0x0096421142aa8558 0x40096421142aa855 0xf1b62631e3ffffff 0xbf1b62631e3fffff

def z1159 : W := mkw 0x2dff42111bef811c 0x42dff42111bef811 0xffffe6303ffff3fb 0xfffffe6303ffff3f

def z1160 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0x3fc03fc03ff03f06 0xc3fc03fc03ff03f0

def z1161 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x604fd9cfe079c0c7 0xd604fd9cfe079c0c

def z1162 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xfe78383e3e7ff0fb 0xffe78383e3e7ff0f

def z1163 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0x3e7fc0003e7fc009 0xd3e7fc0003e7fc00

def z1164 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0xbfc01fc03ff00f0c 0xfbfc01fc03ff00f0

def z1165 : W := mkw 0x100248426238ecc8 0x2100248426238ecc 0xb180260023f9ffce 0xbb180260023f9ffc

def z1166 : W := mkw 0x2dfd400019e7800c 0x02dfd400019e7800 0xbff9c0003ff7c008 0xfbff9c0003ff7c00

def z1167 : W := mkw 0x294240001bef800c 0x0294240001bef800 0xbfcfc0003fffc009 0xfbfcfc0003fffc00

def z1168 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x704fd9cfe279c0c9 0xd704fd9cfe279c0c

def z1169 : W := mkw 0x2dff42115bef855c 0x42dff42115bef855 0x3fcfc601fff1cf04 0xc3fcfc601fff1cf0

def z1170 : W := mkw 0x0b403d4035503a03 0x00b403d4035503a0 0x3fc03fc03ff00f06 0xf3fc03fc03ff00f0

def z1171 : W := mkw 0x2dff40005bef855c 0x42dff40005bef855 0xbfffc0003fffcf09 0xfbfffc0003fffcf0

def z1172 : W := mkw 0x1200bfd7e4107fd3 0x61200bfd7e4107fd 0x40003fffc0003ff6 0x040003fffc0003ff

def z1173 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xbfffc0003ffff0f9 0xfbfffc0003ffff0f

def z1174 : W := mkw 0x0b403d4235507a83 0x00b403d4235507a8 0xbfc83fce3ff1ff0e 0xfbfc83fce3ff1ff0

def z1175 : W := mkw 0x042880ac80000000 0x0042880ac8000000 0x407fd9ffc0000007 0xd407fd9ffc000000

def z1176 : W := mkw 0x2dff40005bef855c 0x42dff40005bef855 0xffffe0303ffffffb 0xfffffe0303ffffff

def z1177 : W := mkw 0x2d6b40001b6d800c 0x02d6b40001b6d800 0xbfcfc0003ff9c009 0xfbfcfc0003ff9c00

def z1178 : W := mkw 0x0000808480000000 0x0000080848000000 0x704fd9cfe270000f 0xd704fd9cfe270000

def z1179 : W := mkw 0x2d6940001965800c 0x02d6940001965800 0x2e79c0003c7fc001 0x42e79c0003c7fc00

def z1180 : W := mkw 0x0096421142aa8558 0x40096421142aa855 0xd1bfe631c38fffff 0xbd1bfe631c38ffff

def z1181 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x4ff7ffffc0000006 0xa4ff7ffffc000000

def z1182 : W := mkw 0x14bec2bfcaafc5f8 0xe14bec2bfcaafc5f 0x403fc03fc00fc0f1 0x0403fc03fc00fc0f

def z1183 : W := mkw 0x0000808480000000 0x0000080848000000 0x41cfffcfc0000007 0xf41cfffcfc000000

def z1184 : W := mkw 0x1002484262baedd8 0x61002484262baedd 0x30000000227fecf8 0x030000000227fecf

def z1185 : W := mkw 0x2d6b40001bef800c 0x02d6b40001bef800 0xbfc9c0003fffc008 0xfbfc9c0003fffc00

def z1186 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0x2e4fc0003c71c000 0x42e4fc0003c71c00

def z1187 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0xf1ffffffe3ffffff 0xff1ffffffe3fffff

def z1188 : W := mkw 0x1000c8c6a030e888 0x21000c8c6a030e88 0x704fd9cfe271ec0f 0xd704fd9cfe271ec0

def z1189 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xffffe0303fffc00b 0xfffffe0303fffc00

def z1190 : W := mkw 0x4bd5b7bd80000000 0x04bd5b7bd8000000 0x4fc7ffffc0000006 0xf4fc7ffffc000000

def z1191 : W := mkw 0x0b403d6a35507aa3 0x80b403d6a35507aa 0xffc83ffe3ff9ffff 0xfffc83ffe3ff9fff

def z1192 : W := mkw 0x00960211428a0550 0x400960211428a055 0xf1f62631e3fe3fff 0xff1f62631e3fe3ff

def z1193 : W := mkw 0x2dff42111bef800c 0x02dff42111bef800 0xffffe631ffffff0f 0xfffffe631ffffff0

def z1194 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xbfffe6003fffd309 0xfbfffe6003fffd30

def z1195 : W := mkw 0x0b403d4235507a83 0x00b403d4235507a8 0xbfc03fc03ff9ffce 0xfbfc03fc03ff9ffc

def z1196 : W := mkw 0x1296baffe69a7df2 0xe1296baffe69a7df 0xd1b63fffc38e3fff 0xbd1b63fffc38e3ff

def z1197 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x5fffffffc2002c0f 0xf5fffffffc2002c0

def z1198 : W := mkw 0x0b40354011500a01 0x00b40354011500a0 0xbfc03fc03ff00f0e 0xfbfc03fc03ff00f0

def z1199 : W := mkw 0x2dff40005bef855c 0x42dff40005bef855 0xbfffe6003fffffff 0xfbfffe6003ffffff

def z1200 : W := mkw 0x1000c8c6a030e888 0x21000c8c6a030e88 0x604fd9cfe079e0cf 0xd604fd9cfe079e0c

def z1201 : W := mkw 0x0628382a2c0570a2 0x80628382a2c0570a 0xee383e3e3c0fffff 0x7ee383e3e3c0ffff

def z1202 : W := mkw 0x100248426a3dece8 0xa100248426a3dece 0x30000000227fecf8 0x030000000227fecf

def z1203 : W := mkw 0x2d6b40001b6d800c 0x02d6b40001b6d800 0xbe7fc0003e7fc009 0xfbe7fc0003e7fc00

def z1204 : W := mkw 0x1200b8eee4107ce2 0xa1200b8eee4107ce 0x400019cfc0002cc6 0x0400019cfc0002cc

def z1205 : W := mkw 0x1002c8c6e238ecc8 0x21002c8c6e238ecc 0x707ff9ffe279eccf 0xf707ff9ffe279ecc

def z1206 : W := mkw 0x4ffdb7bd99450000 0x04ffdb7bd9945000 0xffffffffffffc00f 0xfffffffffffffc00

def z1207 : W := mkw 0x2d6b40001bef800c 0x02d6b40001bef800 0xbe79c0003fffc009 0x7be79c0003fffc00

def z1208 : W := mkw 0x0b40354015501a03 0x00b40354015501a0 0xbfc027c03ff01f0c 0xfbfc027c03ff01f0

def z1209 : W := mkw 0x0628302a0c0550a2 0x80628302a0c0550a 0x4e38003e1c0fc0f1 0x04e38003e1c0fc0f

def z1210 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xbfffe6003fffc00f 0xfbfffe6003fffc00

def z1211 : W := mkw 0x4f69b7bd80000000 0x04f69b7bd8000000 0x4e4fffffc0000007 0xd4e4fffffc000000

def z1212 : W := mkw 0x2d6940001965800c 0x02d6940001965800 0x3fc9c0003ff1c000 0xc3fc9c0003ff1c00

def z1213 : W := mkw 0x2dff40001bef800c 0x02dff40001bef800 0xbfffe0003ffff00b 0xfbfffe0003ffff00

def z1214 : W := mkw 0x0940400011608008 0x0094040001160800 0x2e49c0003c71c000 0x42e49c0003c71c00

def z1215 : W := mkw 0x6ffdb7bd99c70004 0x06ffdb7bd99c7000 0xeffffffffd8fc00f 0xfeffffffffd8fc00

def z1216 : W := mkw 0x0000808480000000 0x0000080848000000 0x504fd9cfc2002c0f 0xd504fd9cfc2002c0

def z1217 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x4e7ff9ffc0000003 0x74e7ff9ffc000000

def z1218 : W := mkw 0x4f69b5ac80000000 0x04f69b5ac8000000 0x4e7ff9ffc0000007 0xf4e7ff9ffc000000

def z1219 : W := mkw 0x0b40b58480000000 0x00b40b5848000000 0x4e4fd9cfc0000007 0xd4e4fd9cfc000000

def z1220 : W := mkw 0x100248426ebffdfa 0xe100248426ebffdf 0xb00000003ffffff8 0x0b00000003ffffff

def z1221 : W := mkw 0x1002c8c6e638fecb 0x21002c8c6e638fec 0x704fd9cfe279ffcf 0xd704fd9cfe279ffc

def z1222 : W := mkw 0x06283d6a2c157aa3 0x806283d6a2c157aa 0xfe783ffe3e7fffff 0xffe783ffe3e7ffff

def z1223 : W := mkw 0x2dff45001bef800c 0x02dff45001bef800 0xbfffc7c03fffc00d 0xfbfffc7c03fffc00

def z1224 : W := mkw 0x1002c086c228c4c8 0x21002c086c228c4c 0x704fd9cfe279c0cf 0xd704fd9cfe279c0c

def z1225 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x4fcfffffc0000006 0xc4fcfffffc000000

def z1226 : W := mkw 0x4ffdb7bd80000000 0x04ffdb7bd8000000 0x4fffdfffc0000005 0xc4fffdfffc000000

def z1227 : W := mkw 0x46bdb2bd80000000 0x046bdb2bd8000000 0x4e7ff9ffc0000007 0xf4e7ff9ffc000000

def z1228 : W := mkw 0x6dff42391bef800c 0x06dff42391bef800 0xbfffc0303fffc009 0xfbfffc0303fffc00

def z1229 : W := mkw 0x0200380224007082 0x0020038022400708 0xee38383e3c0ff0fb 0x7ee38383e3c0ff0f

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z7,z1,z8,z3,z4,z6]),(0,[z9,z0,z1,z2,z10,z3,z4]),(1,[z0,z11,z2,z3,z12,z6]),(1,[z0,z1,z13,z3,z4,z14]),(1,[z0,z1,z2,z15,z3,z16])],[(0,[z7,z0,z1,z2,z3,z17,z6]),(0,[z0,z1,z2,z18,z19,z4,z6]),(0,[z0,z1,z2,z3,z20,z4,z6]),(1,[z0,z1,z2,z10,z3,z21]),(0,[z0,z22,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z23,z6])],[(0,[z0,z1,z24,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z21,z25,z6]),(0,[z26,z1,z2,z3,z27,z4,z6]),(0,[z0,z1,z28,z3,z29,z4,z6]),(0,[z0,z1,z30,z2,z3,z4,z6]),(0,[z0,z1,z31,z2,z3,z32,z6]),(0,[z0,z1,z2,z3,z4,z6,z33]),(0,[z34,z0,z1,z2,z3,z4,z6])],[(0,[z35,z0,z1,z2,z3,z4,z6]),(0,[z36,z0,z1,z2,z3,z4,z6]),(0,[z0,z37,z2,z28,z3,z4,z6]),(0,[z0,z11,z1,z2,z10,z3,z4]),(0,[z0,z1,z38,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z39,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z40])],[(0,[z0,z1,z2,z3,z41,z4,z6]),(0,[z0,z1,z42,z2,z3,z4,z6]),(0,[z0,z43,z44,z2,z3,z4,z6]),(0,[z45,z0,z1,z2,z3,z4,z6]),(0,[z0,z46,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z4,z47]),(0,[z0,z1,z2,z15,z3,z21,z6]),(0,[z0,z1,z2,z3,z4,z6,z48]),(0,[z0,z49,z2,z3,z50,z4,z6]),(0,[z0,z1,z2,z3,z4,z51,z6]),(0,[z0,z52,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z15,z3,z4,z16])],[(0,[z53,z0,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z4,z54,z6]),(0,[z0,z1,z2,z3,z55,z4,z6]),(0,[z0,z1,z2,z3,z4,z56,z57]),(0,[z0,z1,z2,z3,z4,z58,z6]),(0,[z0,z59,z1,z2,z18,z4,z6])]],
   [[(0,[z7,z0,z1,z60,z3,z4,z6]),(0,[z0,z1,z8,z2,z3,z27,z6]),(0,[z0,z1,z2,z3,z21,z21,z6]),(0,[z61,z0,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z29,z21,z6]),(0,[z0,z1,z2,z62,z3,z4,z6])],[(0,[z9,z0,z1,z2,z63,z4,z6]),(0,[z0,z64,z1,z2,z3,z27,z6]),(0,[z0,z65,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z66,z6]),(0,[z0,z1,z2,z3,z67,z4,z6])],[(1,[z0,z1,z2,z3,z4,z68]),(0,[z69,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z70,z3,z4,z6]),(0,[z0,z1,z2,z3,z27,z71,z6]),(0,[z0,z72,z1,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z74,z3,z4]),(0,[z75,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z3,z4,z6]),(0,[z0,z1,z2,z28,z3,z21,z6]),(0,[z76,z0,z1,z2,z3,z21,z6]),(0,[z0,z1,z13,z2,z3,z27,z6]),(0,[z0,z1,z2,z10,z3,z4,z77])],[(0,[z0,z1,z2,z78,z3,z4,z6]),(1,[z26,z1,z2,z3,z27,z6]),(0,[z0,z1,z2,z79,z3,z27,z6]),(0,[z0,z1,z80,z2,z29,z4,z6])],[(0,[z0,z2,z28,z3,z50,z4,z6]),(0,[z76,z0,z81,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z25,z6]),(0,[z0,z1,z2,z82,z10,z3,z4]),(0,[z0,z1,z2,z3,z4,z83,z6])],[(0,[z0,z1,z2,z3,z4,z84,z6]),(0,[z0,z1,z2,z3,z21,z85,z6]),(1,[z0,z1,z2,z3,z4,z86])],[(0,[z87,z0,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z27,z25,z6]),(0,[z73,z0,z1,z2,z3,z4,z12]),(0,[z0,z1,z2,z3,z88,z4,z6]),(1,[z73,z0,z1,z2,z89,z4]),(0,[z90,z0,z1,z2,z10,z3,z4])]],
   [[(0,[z91,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z92]),(0,[z73,z93,z0,z1,z2,z4,z6])],[(0,[z9,z0,z1,z2,z3,z94,z6]),(0,[z0,z1,z2,z3,z4,z25,z57]),(0,[z73,z87,z0,z1,z2,z3,z4]),(0,[z0,z95,z1,z2,z10,z3,z4]),(0,[z73,z0,z1,z80,z2,z3,z4])],[(0,[z96,z0,z1,z2,z19,z4,z6]),(0,[z0,z1,z2,z97,z3,z27,z6]),(0,[z98,z0,z59,z2,z3,z4,z6]),(0,[z0,z1,z80,z97,z3,z4,z6]),(0,[z0,z99,z1,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z4,z14]),(0,[z100,z73,z0,z1,z2,z3,z4]),(0,[z0,z101,z1,z2,z3,z4,z6])],[(0,[z73,z102,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z21,z6]),(0,[z103,z0,z1,z2,z3,z4,z6]),(0,[z0,z104,z1,z2,z3,z4,z6]),(0,[z0,z1,z105,z2,z3,z4,z6]),(0,[z76,z0,z1,z3,z29,z4,z6]),(0,[z106,z0,z1,z2,z10,z3,z4])],[(0,[z91,z0,z1,z2,z3,z4,z57]),(0,[z0,z64,z2,z3,z50,z4,z6])],[(0,[z0,z1,z2,z107,z3,z4,z6]),(1,[z9,z1,z2,z19,z4,z6]),(0,[z0,z1,z2,z3,z27,z21,z6]),(0,[z0,z108,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z109,z4,z6]),(0,[z0,z110,z1,z2,z3,z4,z6]),(0,[z0,z43,z1,z2,z3,z4,z6]),(0,[z0,z1,z31,z2,z10,z3,z4])],[(0,[z96,z0,z1,z2,z10,z3,z4]),(0,[z0,z49,z2,z3,z111,z4,z6]),(0,[z0,z1,z112,z2,z3,z4,z6])],[(0,[z0,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z40]),(0,[z0,z1,z2,z3,z4,z6,z113]),(0,[z98,z0,z1,z2,z3,z27,z6]),(0,[z0,z1,z2,z3,z4,z114,z6]),(0,[z0,z1,z2,z3,z4,z115,z6])]],
   [[(0,[z7,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z54,z6]),(0,[z0,z1,z2,z3,z116,z4,z6]),(0,[z0,z43,z1,z31,z3,z4,z6]),(0,[z0,z1,z2,z117,z3,z4,z6]),(0,[z93,z0,z1,z2,z79,z4,z6])],[(0,[z118,z0,z1,z2,z3,z4,z6]),(0,[z0,z49,z24,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z119]),(0,[z0,z1,z2,z3,z4,z85,z6]),(0,[z0,z1,z120,z2,z3,z4,z6]),(0,[z0,z1,z2,z63,z10,z3,z4]),(0,[z0,z1,z2,z3,z121,z27,z6]),(0,[z122,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z13,z2,z3,z4,z14]),(0,[z0,z1,z123,z2,z3,z4,z6]),(0,[z0,z1,z2,z10,z4,z124,z6])],[(0,[z125,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z37,z60,z3,z4,z6]),(0,[z87,z1,z2,z3,z4,z77,z6]),(0,[z73,z0,z1,z2,z89,z4,z6]),(0,[z126,z0,z1,z2,z3,z4,z6])],[(0,[z127,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z37,z8,z3,z4,z6]),(0,[z0,z1,z2,z128,z3,z4,z6]),(0,[z129,z73,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z130,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z131])],[(0,[z0,z1,z2,z3,z4,z6,z132]),(0,[z0,z1,z133,z2,z3,z4,z6]),(0,[z0,z2,z28,z3,z111,z4,z6]),(0,[z0,z1,z2,z134,z3,z4,z6]),(0,[z0,z64,z1,z2,z3,z50,z6]),(0,[z93,z0,z43,z1,z2,z3,z6])],[(0,[z0,z1,z2,z135,z3,z4,z6]),(0,[z0,z1,z2,z136,z3,z4,z6]),(0,[z137,z0,z1,z2,z3,z4,z6]),(0,[z138,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z139,z3,z4,z6])],[(0,[z140,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z84,z6]),(0,[z96,z0,z1,z2,z63,z4,z6]),(1,[z0,z1,z141,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z142,z6])]],
   [[(0,[z0,z1,z2,z3,z143,z4,z6]),(0,[z0,z1,z2,z63,z97,z4,z6]),(0,[z144,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z145,z6]),(0,[z146,z0,z1,z2,z10,z3,z4])],[(0,[z53,z73,z0,z1,z2,z3,z4]),(0,[z73,z9,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z147,z3,z4,z6]),(0,[z0,z1,z2,z10,z3,z29,z4]),(0,[z0,z1,z2,z3,z148,z149,z6])],[(0,[z0,z1,z2,z3,z150,z4,z6]),(0,[z73,z0,z1,z2,z3,z4,z151]),(0,[z61,z73,z0,z1,z2,z3,z4])],[(0,[z0,z1,z152,z2,z3,z4,z6]),(0,[z0,z153,z1,z2,z3,z21,z6]),(0,[z73,z0,z49,z1,z2,z3,z4]),(0,[z98,z0,z1,z2,z10,z3,z4]),(0,[z0,z154,z1,z2,z3,z4,z6]),(0,[z155,z0,z1,z2,z10,z3,z4])],[(0,[z156,z0,z153,z2,z3,z4,z6]),(1,[z73,z0,z1,z2,z19,z4]),(1,[z0,z1,z2,z3,z21,z6]),(0,[z0,z49,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z157,z4,z6]),(0,[z0,z1,z2,z3,z4,z158,z6]),(0,[z0,z159,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z74,z3,z4,z6]),(0,[z0,z1,z2,z3,z160,z4,z6])],[(0,[z0,z161,z1,z2,z3,z4,z6]),(0,[z162,z73,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z10,z3,z3,z4])],[(0,[z0,z1,z2,z3,z21,z6,z163]),(0,[z0,z1,z2,z3,z164,z4,z6]),(0,[z0,z1,z2,z3,z4,z165,z6]),(0,[z0,z1,z2,z166,z3,z4,z6])],[(0,[z0,z1,z2,z3,z167,z4,z6]),(0,[z0,z1,z2,z3,z4,z168,z6]),(0,[z0,z169,z1,z2,z3,z4,z6]),(0,[z0,z170,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z4,z171,z6]),(1,[z73,z0,z1,z2,z4,z163])]],
   [[(0,[z172,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z173,z4,z6]),(0,[z0,z1,z2,z174,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z175]),(0,[z0,z1,z2,z3,z176,z4,z6]),(0,[z0,z43,z1,z2,z3,z32,z6]),(0,[z93,z0,z1,z2,z3,z71,z6])],[(0,[z102,z153,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z177,z4,z6]),(0,[z73,z91,z0,z1,z2,z3,z4]),(1,[z0,z1,z178,z3,z4,z6]),(0,[z0,z1,z80,z2,z3,z4,z86]),(0,[z0,z43,z179,z2,z3,z4,z6]),(0,[z180,z0,z1,z2,z3,z4,z6])],[(0,[z91,z0,z1,z2,z3,z27,z6]),(0,[z0,z1,z37,z2,z3,z4,z6]),(0,[z181,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z182,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z66]),(0,[z0,z1,z2,z3,z4,z183,z6]),(0,[z0,z1,z184,z2,z3,z4,z6]),(0,[z185,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z186])],[(0,[z187,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z188,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z189]),(0,[z0,z1,z190,z2,z3,z4,z6])],[(0,[z156,z0,z1,z191,z3,z4,z6]),(0,[z53,z0,z1,z2,z3,z4,z47]),(0,[z87,z0,z1,z2,z3,z4,z77]),(0,[z0,z1,z2,z3,z192,z4,z6])],[(1,[z0,z1,z2,z3,z193,z6]),(0,[z0,z1,z2,z194,z3,z4,z6]),(0,[z0,z195,z1,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z4,z6])],[(0,[z0,z196,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z197,z6]),(0,[z0,z1,z2,z3,z4,z198,z6]),(1,[z0,z1,z2,z3,z4,z199]),(0,[z0,z1,z2,z3,z200,z4,z6])],[(0,[z201,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z202,z6]),(0,[z0,z1,z2,z3,z32,z4,z6]),(0,[z0,z1,z31,z3,z4,z203,z6]),(0,[z204,z73,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z4,z6,z205,z16])]],
   [[(1,[z0,z1,z2,z3,z4,z206]),(0,[z0,z1,z2,z3,z27,z197,z6]),(0,[z0,z1,z2,z3,z4,z207,z6]),(0,[z0,z1,z2,z3,z208,z4,z6]),(0,[z73,z0,z11,z1,z2,z3,z4]),(0,[z0,z72,z1,z2,z10,z3,z4]),(0,[z0,z1,z2,z209,z3,z4,z6])],[(0,[z0,z1,z8,z2,z3,z4,z6]),(0,[z210,z0,z1,z2,z3,z4,z6]),(0,[z0,z0,z1,z2,z3,z27,z6]),(0,[z73,z0,z1,z2,z3,z4,z57]),(0,[z0,z43,z1,z3,z32,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z211]),(0,[z73,z0,z1,z2,z3,z4,z149]),(0,[z0,z1,z2,z3,z4,z6,z163])],[(0,[z7,z1,z8,z2,z3,z4,z6]),(0,[z7,z0,z1,z2,z3,z27,z6]),(0,[z26,z96,z1,z2,z3,z4,z6]),(0,[z0,z11,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z27,z6,z212]),(0,[z0,z64,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z213,z6]),(0,[z0,z1,z2,z214,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z4,z71]),(0,[z0,z1,z2,z3,z4,z6,z215])],[(0,[z0,z1,z2,z3,z4,z216,z6]),(0,[z9,z1,z2,z3,z19,z4,z6]),(0,[z26,z217,z1,z2,z3,z4,z6]),(0,[z93,z0,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z27,z6,z163]),(0,[z0,z1,z2,z3,z4,z6,z218])],[(0,[z0,z1,z2,z18,z3,z21,z6]),(1,[z0,z49,z37,z3,z4,z6]),(0,[z0,z1,z13,z2,z3,z4,z6]),(0,[z219,z0,z1,z2,z3,z4,z6])],[(0,[z53,z7,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z220,z4,z6])],[(1,[z0,z1,z221,z3,z4,z6]),(0,[z222,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z223,z2,z3,z4,z6]),(0,[z0,z1,z2,z224,z3,z4,z6]),(0,[z91,z0,z1,z2,z10,z3,z4]),(0,[z0,z1,z225,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z199,z6]),(0,[z73,z0,z1,z2,z79,z3,z4]),(0,[z73,z0,z226,z1,z2,z3,z4]),(0,[z73,z75,z0,z1,z2,z3,z4]),(0,[z0,z1,z227,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z228,z4,z6]),(0,[z0,z1,z2,z229,z3,z4,z6]),(0,[z0,z1,z2,z3,z230,z4,z6]),(0,[z73,z0,z1,z2,z28,z3,z4]),(0,[z0,z11,z49,z2,z3,z4,z6]),(0,[z0,z231,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z232])]],
   [[(0,[z0,z1,z2,z3,z193,z4,z6]),(1,[z0,z1,z2,z3,z233,z6]),(0,[z0,z1,z2,z234,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z235]),(0,[z0,z1,z2,z10,z3,z4,z12])],[(0,[z0,z1,z2,z3,z236,z4,z6]),(0,[z0,z49,z59,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z111,z4]),(0,[z0,z237,z1,z2,z3,z4,z6]),(0,[z106,z0,z1,z13,z3,z4,z6])],[(1,[z1,z2,z3,z19,z21,z6]),(1,[z0,z1,z238,z3,z4,z6]),(0,[z0,z1,z239,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z240,z6])],[(0,[z0,z1,z2,z241,z3,z4,z6]),(0,[z0,z242,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z243,z6]),(0,[z0,z1,z2,z97,z3,z4,z6]),(0,[z0,z1,z2,z244,z3,z29,z4]),(0,[z0,z43,z1,z2,z10,z3,z4]),(1,[z45,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z245,z4,z6]),(0,[z0,z1,z2,z3,z4,z246,z6]),(0,[z0,z247,z1,z2,z3,z4,z6]),(0,[z0,z11,z1,z2,z3,z4,z199])],[(0,[z0,z248,z1,z2,z3,z4,z6]),(0,[z0,z249,z1,z2,z3,z4,z6]),(0,[z250,z0,z1,z2,z3,z4,z6]),(0,[z251,z0,z1,z2,z3,z4,z6])],[(0,[z102,z0,z153,z2,z3,z4,z6]),(0,[z7,z0,z1,z2,z10,z3,z4]),(0,[z0,z49,z1,z2,z3,z27,z6]),(0,[z0,z1,z2,z3,z27,z246,z6])],[(0,[z1,z2,z63,z3,z19,z4,z6]),(0,[z0,z1,z2,z3,z252,z4,z6]),(0,[z0,z1,z80,z2,z3,z21,z6]),(0,[z0,z64,z1,z2,z3,z12,z6]),(0,[z0,z1,z2,z3,z253,z4,z6]),(0,[z0,z1,z2,z3,z4,z254,z6]),(1,[z0,z1,z2,z3,z4,z255]),(1,[z256,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z257,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z258,z4,z6]),(0,[z0,z95,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z21,z71,z6]),(0,[z259,z0,z1,z2,z3,z4,z6]),(0,[z260,z0,z1,z2,z3,z4,z6]),(0,[z261,z0,z1,z2,z3,z4,z151])],[(0,[z0,z1,z2,z262,z3,z4,z6]),(0,[z53,z0,z1,z2,z3,z263,z6]),(0,[z0,z59,z2,z28,z3,z4,z6]),(0,[z0,z1,z264,z2,z3,z4,z6]),(0,[z265,z0,z1,z2,z3,z4,z6])],[(0,[z266,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z121,z4,z6]),(0,[z267,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z111,z21,z6]),(0,[z106,z0,z1,z2,z3,z21,z6]),(0,[z0,z268,z1,z2,z3,z4,z6]),(0,[z269,z0,z1,z2,z3,z4,z6])],[(0,[z270,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z271,z6]),(0,[z0,z272,z1,z2,z3,z4,z6]),(0,[z0,z59,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z273])],[(0,[z274,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z31,z2,z3,z21,z6]),(0,[z0,z1,z37,z2,z3,z27,z6]),(0,[z0,z64,z1,z38,z3,z4,z6])],[(0,[z96,z0,z1,z2,z3,z21,z6]),(0,[z0,z95,z49,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z149,z25]),(0,[z0,z1,z2,z3,z4,z275,z6])],[(0,[z0,z1,z2,z3,z276,z4,z6]),(0,[z0,z1,z2,z3,z27,z277,z6]),(0,[z0,z1,z2,z3,z27,z149,z6])],[(0,[z278,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z19,z27,z6]),(0,[z73,z0,z1,z2,z3,z27,z6]),(0,[z279,z0,z1,z2,z3,z4,z6]),(0,[z87,z0,z1,z2,z280,z4,z6]),(0,[z0,z1,z2,z3,z281,z4,z6]),(0,[z0,z44,z1,z2,z3,z4,z6])]],
   [[(1,[z0,z1,z2,z3,z276,z6]),(0,[z0,z1,z2,z63,z3,z21,z6]),(0,[z217,z0,z1,z2,z3,z27,z6]),(0,[z282,z0,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z21,z203,z6]),(0,[z0,z283,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z32,z27,z6]),(0,[z284,z0,z1,z2,z3,z4,z6]),(0,[z285,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z79,z3,z89,z6])],[(0,[z286,z0,z1,z2,z3,z4,z6]),(1,[z73,z0,z1,z2,z3,z21]),(0,[z0,z1,z2,z287,z3,z4,z6]),(0,[z0,z1,z80,z28,z3,z4,z6]),(0,[z0,z49,z1,z2,z10,z3,z4]),(0,[z93,z45,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z232])],[(0,[z0,z1,z288,z2,z3,z4,z6]),(0,[z0,z2,z18,z3,z111,z4,z6]),(0,[z261,z0,z1,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z4,z56]),(0,[z0,z1,z2,z10,z3,z4,z151]),(0,[z0,z1,z2,z3,z4,z71,z6]),(0,[z0,z289,z1,z2,z3,z4,z6])],[(0,[z53,z0,z290,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z21,z291,z6]),(0,[z0,z292,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z166,z10,z3,z4])],[(0,[z156,z0,z24,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z263,z6]),(0,[z0,z1,z2,z3,z293,z4,z6])],[(0,[z53,z0,z1,z2,z173,z4,z6]),(0,[z0,z1,z2,z294,z3,z4,z6]),(0,[z0,z1,z2,z10,z3,z19,z4]),(0,[z0,z295,z1,z2,z3,z4,z6]),(0,[z296,z0,z1,z2,z3,z4,z6])],[(0,[z73,z0,z1,z2,z19,z4,z6]),(0,[z0,z297,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z224,z3,z27,z6]),(0,[z0,z1,z298,z2,z3,z4,z6])],[(0,[z96,z0,z1,z2,z3,z4,z206]),(0,[z299,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z10,z3,z4,z163]),(0,[z0,z1,z2,z10,z3,z300,z4])],[(0,[z0,z1,z290,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z301,z6]),(0,[z98,z0,z1,z2,z3,z21,z6]),(0,[z302,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z81,z2,z3,z4,z6]),(0,[z303,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z10,z97,z3,z4]),(0,[z73,z0,z1,z2,z15,z3,z4])],[(0,[z0,z304,z1,z2,z3,z4,z6]),(0,[z0,z305,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z21,z306,z6]),(0,[z0,z1,z2,z3,z21,z6,z14]),(0,[z0,z1,z2,z3,z236,z27,z6]),(0,[z0,z1,z2,z3,z4,z307,z6]),(0,[z0,z1,z2,z3,z4,z203,z6]),(0,[z73,z0,z1,z2,z10,z3,z4]),(0,[z73,z0,z1,z2,z4,z6,z163])],[(0,[z0,z1,z2,z3,z308,z4,z6]),(0,[z0,z309,z1,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z4,z275]),(0,[z0,z1,z2,z3,z4,z310,z6])],[(0,[z0,z242,z1,z2,z3,z27,z6]),(0,[z0,z1,z2,z3,z27,z203,z6]),(1,[z87,z1,z2,z3,z4,z77]),(0,[z93,z0,z11,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z311,z6]),(0,[z0,z1,z2,z3,z4,z312,z6])],[(0,[z0,z313,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z27,z6,z56]),(0,[z0,z64,z11,z2,z3,z4,z6]),(0,[z314,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z8,z2,z10,z3,z4]),(0,[z0,z1,z2,z19,z29,z4,z6]),(0,[z0,z1,z2,z3,z4,z291,z6]),(0,[z0,z315,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z316,z6]),(0,[z0,z1,z317,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z318,z6]),(0,[z0,z1,z2,z10,z3,z4,z25]),(0,[z0,z1,z2,z3,z4,z6,z319])]],
   [[(0,[z156,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z60,z3,z21,z6]),(0,[z0,z1,z2,z63,z29,z4,z6]),(0,[z320,z0,z1,z2,z3,z4,z6]),(0,[z0,z321,z1,z2,z3,z4,z6]),(0,[z0,z64,z1,z2,z10,z3,z4]),(1,[z0,z1,z2,z322,z3,z4]),(0,[z0,z1,z2,z3,z89,z4,z323]),(0,[z0,z1,z2,z3,z148,z4,z6])],[(0,[z0,z1,z2,z324,z3,z4,z6]),(0,[z26,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z325,z6]),(0,[z0,z1,z2,z326,z3,z4,z6]),(0,[z0,z1,z2,z3,z327,z4,z6]),(0,[z0,z1,z2,z3,z4,z328,z6])],[(0,[z0,z1,z37,z80,z3,z4,z6]),(0,[z0,z1,z13,z2,z10,z3,z4])],[(0,[z53,z1,z2,z60,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z329,z6]),(0,[z0,z1,z2,z10,z3,z4,z71]),(0,[z0,z1,z2,z79,z10,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z330])],[(0,[z73,z0,z1,z2,z63,z4,z6]),(1,[z0,z1,z2,z280,z4,z6]),(0,[z0,z1,z2,z3,z4,z331,z6]),(0,[z0,z1,z2,z3,z332,z4,z6]),(0,[z106,z73,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z148,z4,z149])],[(0,[z156,z0,z1,z2,z3,z333,z6]),(0,[z0,z1,z2,z97,z19,z4,z6]),(0,[z334,z0,z1,z2,z3,z4,z6]),(0,[z0,z59,z1,z2,z3,z27,z6]),(0,[z0,z1,z2,z3,z335,z4,z6]),(0,[z336,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z306,z6]),(1,[z0,z1,z2,z3,z263,z6]),(0,[z0,z1,z2,z3,z4,z6,z337]),(0,[z0,z1,z2,z338,z3,z4,z6]),(1,[z0,z64,z2,z3,z50,z6]),(1,[z0,z72,z2,z3,z4,z56]),(0,[z0,z1,z2,z3,z4,z6,z339]),(0,[z0,z1,z2,z3,z4,z6,z14]),(0,[z93,z0,z1,z2,z4,z124,z6])],[(0,[z340,z0,z1,z2,z3,z4,z6]),(0,[z0,z72,z1,z2,z3,z21,z6]),(0,[z0,z1,z31,z2,z3,z4,z255]),(0,[z0,z1,z2,z10,z3,z4,z124])]],
   [[(1,[z0,z1,z191,z3,z4,z6]),(0,[z53,z0,z1,z8,z3,z4,z6]),(0,[z0,z1,z2,z3,z27,z6,z14]),(1,[z0,z1,z2,z341,z3,z4]),(1,[z261,z0,z2,z3,z4,z151]),(1,[z0,z1,z2,z79,z89,z6])],[(0,[z0,z1,z2,z3,z342,z4,z6]),(0,[z73,z0,z1,z2,z3,z50,z4]),(0,[z73,z0,z289,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z6,z343]),(0,[z0,z1,z2,z10,z3,z111,z4]),(0,[z0,z1,z2,z3,z4,z149,z56])],[(0,[z0,z344,z1,z2,z3,z4,z6]),(0,[z345,z0,z1,z2,z3,z4,z6]),(1,[z346,z0,z1,z2,z3,z4]),(0,[z87,z0,z1,z2,z3,z347,z6]),(0,[z0,z2,z3,z4,z151,z6,z56]),(0,[z348,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z349]),(0,[z0,z1,z2,z3,z4,z6,z350])],[(0,[z0,z1,z2,z351,z3,z4,z6]),(0,[z261,z0,z1,z2,z3,z27,z6]),(0,[z0,z1,z2,z3,z4,z6,z352]),(0,[z0,z1,z2,z353,z3,z4,z6])],[(0,[z0,z354,z1,z2,z3,z4,z6]),(0,[z9,z0,z1,z2,z3,z54,z6]),(0,[z0,z1,z2,z355,z3,z19,z4]),(0,[z0,z1,z2,z3,z4,z356,z6]),(0,[z0,z1,z2,z322,z3,z29,z4])],[(0,[z102,z0,z24,z2,z3,z4,z6]),(1,[z0,z1,z31,z3,z203,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z357,z6]),(0,[z0,z1,z2,z3,z4,z206,z6]),(0,[z98,z0,z1,z238,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z358]),(0,[z0,z1,z2,z3,z4,z323,z6])],[(1,[z0,z290,z2,z3,z4,z6]),(0,[z0,z1,z359,z2,z3,z4,z6]),(0,[z0,z59,z1,z2,z10,z3,z4]),(0,[z261,z0,z1,z2,z3,z4,z56]),(1,[z0,z81,z2,z3,z4,z6]),(0,[z0,z1,z2,z89,z4,z124,z6])],[(0,[z53,z0,z360,z2,z3,z4,z6]),(0,[z0,z1,z2,z361,z3,z4,z6]),(0,[z0,z43,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z4,z233,z6]),(0,[z0,z59,z2,z18,z3,z4,z6]),(0,[z73,z0,z1,z31,z2,z3,z4])],[(0,[z0,z1,z2,z362,z3,z4,z6]),(0,[z363,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z21,z6,z364]),(0,[z0,z1,z2,z3,z365,z21,z6]),(0,[z98,z73,z0,z1,z2,z3,z4]),(0,[z0,z1,z366,z2,z3,z4,z6]),(0,[z0,z1,z2,z367,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z149,z14])],[(0,[z53,z0,z1,z2,z294,z4,z6]),(0,[z217,z1,z2,z3,z4,z21,z6]),(0,[z0,z304,z1,z2,z3,z27,z6]),(1,[z0,z1,z359,z2,z3,z4]),(0,[z0,z368,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z369,z6])],[(0,[z156,z102,z1,z2,z3,z4,z6]),(1,[z102,z153,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z370,z4,z6]),(0,[z0,z371,z1,z2,z3,z4,z6]),(0,[z0,z372,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z373,z6]),(1,[z0,z1,z2,z10,z3,z27]),(0,[z0,z1,z374,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z375,z6]),(0,[z0,z1,z2,z3,z4,z6,z376]),(0,[z0,z1,z2,z377,z3,z4,z6]),(0,[z0,z1,z2,z3,z378,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z19,z4,z6]),(0,[z0,z1,z2,z10,z3,z27,z6]),(0,[z0,z1,z379,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z29,z4,z6]),(0,[z0,z1,z2,z244,z3,z4,z6]),(0,[z0,z380,z1,z2,z3,z4,z6]),(0,[z73,z0,z1,z13,z2,z3,z4])],[(0,[z217,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z381,z3,z4,z6]),(0,[z261,z0,z1,z2,z10,z3,z4])],[(0,[z102,z0,z1,z2,z3,z4,z6]),(0,[z156,z0,z1,z2,z3,z27,z6]),(0,[z0,z1,z382,z2,z3,z4,z6]),(0,[z9,z0,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z21,z6,z57]),(0,[z0,z1,z2,z3,z148,z27,z6]),(0,[z0,z1,z2,z3,z4,z383,z6]),(0,[z0,z49,z1,z37,z3,z4,z6]),(0,[z73,z0,z1,z37,z2,z3,z4]),(0,[z0,z1,z2,z384,z3,z4,z6]),(0,[z0,z1,z2,z385,z3,z4,z6]),(1,[z73,z93,z0,z1,z2,z4])],[(0,[z0,z1,z2,z63,z4,z124,z6]),(0,[z0,z1,z2,z135,z3,z21,z6]),(0,[z26,z0,z1,z2,z3,z27,z6]),(0,[z0,z1,z2,z3,z4,z6,z212]),(0,[z162,z0,z1,z2,z3,z4,z6]),(0,[z76,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z141,z2,z3,z4,z6]),(1,[z0,z43,z1,z3,z32,z6])],[(0,[z386,z0,z1,z2,z3,z4,z6]),(0,[z387,z0,z1,z2,z3,z4,z6]),(0,[z388,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z10,z3,z4,z56]),(0,[z261,z0,z2,z3,z4,z151,z6]),(0,[z0,z1,z2,z3,z389,z4,z6])],[(1,[z0,z1,z2,z3,z17,z6]),(0,[z346,z0,z1,z2,z3,z19,z4]),(0,[z0,z1,z359,z2,z3,z111,z4]),(0,[z0,z390,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z391,z6])],[(0,[z91,z1,z2,z3,z4,z6,z57]),(0,[z0,z1,z2,z3,z4,z392,z6])],[(0,[z0,z1,z2,z3,z4,z6,z364]),(0,[z393,z0,z1,z2,z3,z4,z6]),(0,[z394,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z73,z0,z1,z24,z2,z3,z4]),(1,[z0,z1,z2,z3,z347,z6]),(0,[z0,z1,z2,z395,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z396]),(0,[z73,z0,z1,z2,z60,z3,z4]),(0,[z0,z49,z1,z2,z3,z21,z6]),(0,[z0,z1,z397,z2,z3,z4,z6]),(0,[z0,z398,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z399,z6]),(0,[z0,z1,z2,z3,z4,z6,z6]),(0,[z0,z1,z2,z3,z400,z111,z6]),(0,[z0,z1,z2,z401,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z151,z16])],[(0,[z0,z1,z2,z221,z3,z4,z6]),(0,[z0,z1,z402,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z403,z4,z6]),(0,[z73,z0,z95,z1,z2,z3,z4])],[(0,[z404,z0,z1,z2,z3,z4,z6]),(0,[z96,z0,z1,z2,z3,z4,z40]),(0,[z0,z1,z405,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z406,z6]),(0,[z0,z1,z2,z3,z21,z149,z6]),(0,[z0,z1,z2,z3,z407,z4,z6]),(0,[z0,z1,z2,z3,z408,z4,z6]),(0,[z0,z1,z2,z3,z4,z149,z151])],[(0,[z0,z1,z2,z3,z4,z6,z409]),(0,[z346,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z174,z3,z21,z6]),(0,[z0,z1,z2,z3,z4,z6,z57]),(0,[z73,z0,z72,z1,z2,z3,z4]),(0,[z410,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z411,z6]),(0,[z0,z1,z2,z412,z3,z4,z6])],[(0,[z156,z0,z1,z2,z10,z3,z4]),(0,[z0,z1,z2,z3,z177,z21,z6]),(0,[z0,z1,z2,z238,z3,z4,z6]),(0,[z0,z1,z2,z10,z3,z4,z14]),(1,[z0,z1,z2,z4,z6,z205])],[(0,[z0,z413,z1,z2,z3,z4,z6]),(0,[z26,z0,z1,z2,z10,z3,z4]),(0,[z0,z1,z2,z3,z27,z6,z57]),(0,[z0,z1,z2,z3,z4,z414,z6]),(0,[z0,z1,z2,z79,z3,z71,z6])]],
   [[(0,[z73,z7,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z415,z6]),(0,[z73,z0,z1,z416,z2,z3,z4])],[(0,[z417,z0,z1,z2,z3,z4,z6]),(0,[z418,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z419,z6]),(0,[z0,z1,z2,z3,z420,z4,z6]),(0,[z0,z1,z2,z3,z4,z421,z6])],[(1,[z0,z1,z2,z355,z3,z4]),(0,[z73,z0,z1,z2,z3,z4,z21]),(0,[z0,z1,z2,z3,z4,z422,z6]),(0,[z0,z1,z2,z412,z3,z4,z71])],[(0,[z0,z1,z2,z3,z423,z4,z6]),(0,[z336,z0,z1,z2,z10,z3,z4])],[(0,[z0,z1,z24,z2,z3,z27,z6]),(0,[z0,z1,z2,z3,z4,z301,z6]),(0,[z0,z1,z2,z3,z4,z424,z6]),(0,[z0,z1,z31,z2,z3,z203,z6]),(0,[z73,z0,z1,z2,z3,z148,z4])],[(0,[z0,z1,z425,z2,z3,z4,z6]),(0,[z0,z1,z2,z426,z3,z4,z6]),(0,[z427,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z428,z6])],[(0,[z0,z1,z8,z2,z3,z21,z6]),(0,[z0,z1,z2,z429,z3,z4,z6]),(0,[z430,z0,z1,z2,z3,z4,z6])],[(1,[z0,z360,z2,z3,z4,z6]),(0,[z0,z64,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z4,z277,z6]),(0,[z431,z0,z1,z2,z3,z4,z6]),(0,[z432,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z149,z6])]],
   [[(0,[z433,z0,z1,z2,z3,z4,z6]),(0,[z434,z0,z1,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z4,z203]),(0,[z435,z0,z1,z2,z3,z4,z6])],[(0,[z0,z153,z2,z28,z3,z4,z6]),(0,[z53,z0,z1,z2,z3,z27,z6]),(0,[z436,z0,z1,z2,z3,z4,z6]),(0,[z96,z1,z2,z63,z3,z4,z6]),(0,[z437,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z13,z2,z3,z21,z6]),(0,[z0,z1,z438,z2,z3,z4,z6]),(0,[z0,z1,z37,z3,z32,z4,z6]),(0,[z0,z1,z439,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z32,z4]),(0,[z0,z1,z440,z2,z3,z4,z6])],[(0,[z441,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z294,z4,z6]),(0,[z0,z1,z2,z3,z373,z4,z6]),(1,[z1,z2,z3,z27,z21,z6]),(0,[z0,z1,z2,z79,z3,z21,z6]),(0,[z61,z0,z1,z2,z3,z27,z6]),(0,[z0,z1,z2,z3,z29,z27,z6]),(0,[z0,z1,z2,z3,z4,z442,z6]),(0,[z0,z1,z2,z3,z443,z4,z6])],[(0,[z1,z8,z2,z60,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z444]),(0,[z0,z1,z2,z3,z4,z445,z6])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z0,z24,z2,z28,z3,z4,z6]),(0,[z102,z0,z1,z2,z3,z27,z6]),(0,[z0,z1,z2,z3,z21,z6,z56]),(0,[z0,z1,z2,z446,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z447])],[(0,[z0,z448,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z28,z3,z27,z6]),(0,[z76,z0,z1,z2,z3,z27,z6]),(0,[z0,z1,z2,z449,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z450]),(0,[z0,z1,z31,z2,z3,z4,z66])],[(0,[z0,z95,z1,z28,z3,z4,z6]),(0,[z0,z1,z2,z451,z3,z4,z6])],[(0,[z0,z1,z452,z2,z3,z4,z6]),(0,[z0,z170,z1,z2,z3,z4,z6]),(0,[z0,z453,z1,z2,z3,z111,z6]),(0,[z93,z0,z1,z31,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z454,z6]),(0,[z144,z73,z0,z1,z2,z3,z4])]],
   [[(0,[z0,z1,z455,z2,z3,z4,z6]),(0,[z0,z1,z2,z456,z3,z4,z6]),(0,[z0,z1,z2,z97,z3,z21,z6]),(0,[z0,z1,z2,z3,z89,z21,z6]),(0,[z73,z0,z1,z2,z3,z27,z4]),(0,[z0,z1,z457,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z458,z4,z6]),(0,[z0,z1,z2,z3,z4,z459,z6]),(0,[z0,z1,z460,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z333,z6]),(0,[z0,z1,z2,z19,z111,z4,z6]),(0,[z87,z0,z1,z2,z3,z27,z6]),(0,[z0,z1,z2,z461,z3,z4,z6]),(0,[z0,z1,z2,z3,z462,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z463])],[(0,[z0,z1,z2,z63,z111,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z464]),(0,[z0,z1,z31,z28,z3,z4,z6]),(0,[z0,z465,z1,z2,z3,z4,z6]),(0,[z0,z466,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z467,z4,z6])],[(0,[z0,z398,z1,z2,z3,z27,z6]),(0,[z0,z1,z2,z3,z4,z14,z57]),(0,[z0,z1,z37,z2,z10,z3,z4]),(1,[z73,z0,z1,z2,z10,z4])],[(1,[z96,z1,z2,z63,z4,z6]),(0,[z0,z1,z2,z3,z4,z454,z71])],[(0,[z73,z0,z153,z1,z2,z3,z4]),(0,[z0,z1,z2,z468,z3,z4,z6]),(0,[z0,z1,z2,z3,z469,z4,z6]),(0,[z0,z1,z2,z3,z470,z4,z6]),(0,[z0,z471,z1,z2,z3,z4,z6]),(0,[z0,z1,z472,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z160,z4])],[(0,[z0,z1,z2,z3,z4,z473,z6]),(0,[z0,z1,z2,z3,z4,z151,z77])],[(0,[z217,z0,z1,z2,z10,z3,z4]),(0,[z0,z1,z2,z3,z474,z4,z6]),(0,[z0,z1,z2,z3,z27,z27,z6]),(0,[z0,z1,z2,z3,z4,z6,z56]),(0,[z0,z1,z2,z3,z4,z475,z6]),(0,[z0,z1,z476,z2,z3,z4,z6])]],
   [[(0,[z102,z0,z1,z2,z10,z3,z4]),(1,[z0,z1,z2,z3,z477,z6]),(0,[z0,z478,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z479,z4,z6]),(0,[z0,z1,z2,z10,z3,z443,z4])],[(0,[z76,z0,z1,z2,z10,z3,z4]),(0,[z0,z1,z2,z3,z4,z480,z6]),(0,[z0,z1,z2,z10,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z481,z6]),(0,[z0,z1,z2,z341,z3,z4,z6]),(0,[z0,z1,z2,z3,z50,z4,z6]),(0,[z256,z0,z1,z2,z4,z6,z16])],[(0,[z482,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z56,z16]),(0,[z0,z1,z2,z322,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z483,z6]),(0,[z93,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z27,z481,z6]),(0,[z0,z1,z2,z3,z399,z4,z6]),(0,[z98,z0,z1,z2,z111,z4,z6]),(0,[z0,z1,z2,z484,z3,z4,z6]),(0,[z0,z1,z2,z485,z3,z4,z6]),(0,[z73,z93,z0,z1,z2,z3,z4]),(0,[z73,z73,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z10,z3,z4,z57]),(0,[z0,z486,z1,z2,z3,z4,z6]),(0,[z0,z11,z1,z2,z79,z3,z6]),(0,[z0,z1,z3,z4,z25,z6,z14]),(0,[z0,z1,z2,z10,z3,z4,z149])],[(0,[z0,z1,z416,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z124,z6,z163]),(1,[z0,z1,z2,z3,z148,z149])],[(0,[z0,z1,z2,z3,z487,z4,z6]),(0,[z0,z1,z2,z3,z4,z77,z14]),(0,[z0,z59,z1,z2,z3,z4,z189]),(0,[z0,z1,z2,z3,z488,z4,z6]),(0,[z489,z0,z1,z2,z3,z4,z6]),(0,[z0,z490,z1,z2,z3,z4,z6])]],
   [[(0,[z261,z0,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z491,z4,z6]),(0,[z0,z1,z2,z492,z3,z4,z6]),(0,[z76,z0,z1,z2,z97,z4,z6]),(1,[z0,z1,z2,z3,z4,z202])],[(0,[z156,z0,z1,z2,z308,z4,z6]),(0,[z493,z0,z1,z2,z3,z4,z6]),(0,[z0,z494,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z495,z6]),(0,[z0,z1,z2,z496,z3,z4,z6])],[(0,[z53,z0,z1,z60,z3,z4,z6]),(0,[z0,z497,z1,z2,z3,z4,z6])],[(0,[z156,z0,z1,z2,z3,z4,z216]),(0,[z437,z0,z1,z2,z3,z27,z6]),(0,[z87,z91,z1,z2,z3,z4,z6]),(0,[z76,z0,z1,z80,z3,z4,z6]),(0,[z100,z0,z1,z2,z3,z4,z6]),(0,[z219,z73,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z498,z4,z6])],[(0,[z87,z0,z1,z2,z3,z487,z6])],[(0,[z0,z153,z1,z2,z3,z27,z6]),(0,[z0,z1,z2,z3,z499,z4,z6]),(0,[z0,z1,z2,z3,z4,z25,z16])],[(1,[z73,z0,z1,z2,z63,z4]),(1,[z0,z1,z2,z3,z27,z6]),(0,[z0,z95,z2,z28,z3,z4,z6]),(0,[z0,z1,z2,z341,z3,z111,z4]),(0,[z0,z72,z2,z3,z4,z6,z56])],[(0,[z0,z1,z2,z3,z173,z4,z6]),(0,[z0,z1,z500,z2,z3,z4,z6]),(1,[z0,z453,z1,z2,z3,z6]),(0,[z0,z1,z80,z2,z3,z4,z6]),(0,[z0,z1,z2,z501,z3,z4,z6]),(0,[z0,z1,z2,z502,z3,z4,z6])]],
   [[(0,[z0,z1,z503,z2,z3,z4,z6]),(0,[z91,z0,z1,z2,z3,z21,z6]),(0,[z1,z2,z3,z4,z77,z6,z57]),(1,[z0,z59,z2,z18,z4,z6])],[(0,[z0,z1,z2,z504,z3,z4,z6])],[(0,[z1,z2,z3,z19,z4,z21,z6]),(0,[z0,z1,z2,z3,z4,z347,z6]),(0,[z0,z1,z2,z3,z111,z4,z6]),(0,[z0,z43,z1,z2,z3,z203,z6]),(0,[z0,z1,z2,z505,z3,z4,z6])],[(1,[z156,z24,z2,z3,z4,z6]),(0,[z156,z1,z24,z2,z3,z4,z6]),(0,[z506,z0,z1,z2,z3,z4,z6]),(0,[z106,z0,z1,z2,z3,z4,z25])],[(0,[z507,z0,z1,z2,z3,z4,z6]),(0,[z87,z0,z1,z2,z338,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z508]),(0,[z0,z1,z2,z3,z509,z4,z6]),(0,[z0,z1,z2,z3,z4,z510,z6]),(0,[z129,z0,z1,z2,z3,z4,z6]),(0,[z251,z73,z0,z1,z2,z3,z4])],[(0,[z156,z0,z1,z2,z3,z21,z6]),(0,[z0,z1,z24,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z511,z4,z6]),(0,[z0,z1,z2,z3,z148,z21,z6]),(0,[z0,z1,z2,z512,z3,z4,z6]),(0,[z0,z1,z2,z10,z3,z148,z4])],[(0,[z0,z513,z1,z2,z3,z4,z6]),(0,[z26,z0,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z4,z514,z6])],[(0,[z0,z0,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z21,z77,z6]),(0,[z515,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z31,z2,z79,z3,z6]),(0,[z0,z1,z2,z3,z4,z516,z6])]],
   [[(0,[z7,z0,z1,z2,z3,z21,z6]),(0,[z517,z0,z1,z2,z3,z4,z6]),(0,[z518,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z178,z3,z4,z6]),(0,[z73,z0,z64,z1,z2,z3,z4]),(0,[z0,z519,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z94,z4,z6]),(0,[z0,z1,z2,z355,z3,z4,z6]),(0,[z0,z1,z520,z2,z3,z4,z6]),(0,[z521,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z522,z4,z6]),(0,[z0,z1,z2,z3,z523,z4,z6]),(0,[z0,z1,z2,z15,z3,z4,z6])],[(0,[z53,z0,z1,z2,z3,z4,z6]),(0,[z53,z0,z1,z2,z3,z4,z396]),(0,[z26,z1,z2,z3,z19,z4,z6]),(0,[z0,z1,z2,z524,z3,z4,z6]),(0,[z525,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z10,z3,z4])],[(0,[z61,z0,z1,z2,z3,z4,z6]),(0,[z9,z96,z1,z2,z3,z4,z6]),(0,[z0,z1,z526,z2,z3,z4,z6]),(1,[z0,z1,z2,z244,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z527]),(0,[z0,z528,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z68]),(0,[z0,z11,z1,z2,z3,z27,z6]),(0,[z0,z1,z2,z3,z50,z27,z6]),(0,[z0,z1,z529,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z530,z6])],[(0,[z0,z531,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z19,z4,z124,z6]),(0,[z93,z0,z1,z2,z3,z27,z6]),(0,[z0,z1,z2,z532,z3,z4,z6]),(0,[z0,z533,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z534,z3,z4,z6]),(0,[z535,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z536,z2,z3,z4,z6]),(0,[z0,z1,z2,z15,z3,z4,z149])],[(0,[z156,z0,z1,z2,z3,z193,z6]),(0,[z0,z360,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z18,z3,z27,z6]),(0,[z0,z1,z2,z28,z3,z4,z6]),(0,[z0,z1,z2,z3,z400,z4,z6]),(0,[z0,z1,z2,z3,z89,z4,z232])],[(0,[z0,z1,z2,z63,z18,z4,z6]),(0,[z0,z1,z2,z537,z3,z4,z6]),(0,[z538,z0,z1,z2,z3,z4,z6]),(0,[z539,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z540,z4,z6]),(0,[z541,z0,z1,z2,z3,z4,z6]),(0,[z0,z542,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z543]),(1,[z73,z0,z1,z2,z3,z27]),(0,[z0,z1,z2,z3,z4,z544,z6])],[(0,[z0,z1,z2,z10,z3,z27,z4]),(1,[z0,z1,z2,z3,z487,z6]),(0,[z0,z545,z1,z2,z3,z4,z6]),(0,[z0,z1,z546,z2,z3,z4,z6]),(0,[z0,z1,z547,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z548,z4,z6]),(0,[z0,z1,z2,z3,z4,z549,z6]),(0,[z0,z1,z2,z3,z4,z550,z6]),(0,[z73,z0,z1,z2,z3,z3,z4])],[(0,[z87,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z77,z6]),(0,[z0,z1,z2,z551,z3,z4,z6]),(0,[z0,z552,z1,z2,z3,z4,z6]),(0,[z261,z73,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z553,z6]),(1,[z106,z0,z1,z3,z4,z25])],[(0,[z554,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z555,z6]),(0,[z0,z1,z80,z2,z3,z4,z202])],[(0,[z556,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z557]),(0,[z0,z1,z2,z3,z27,z77,z6]),(0,[z91,z0,z1,z2,z3,z233,z6]),(1,[z91,z1,z2,z3,z4,z57]),(0,[z0,z1,z558,z2,z3,z4,z6]),(0,[z0,z1,z3,z32,z4,z203,z6])],[(0,[z0,z1,z2,z559,z3,z4,z6]),(1,[z0,z1,z2,z3,z511,z6]),(0,[z0,z1,z2,z3,z4,z560,z6]),(0,[z0,z1,z2,z3,z561,z4,z6]),(0,[z562,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z563,z6])],[(0,[z564,z0,z1,z2,z3,z4,z6]),(0,[z0,z313,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z4,z6]),(0,[z87,z0,z1,z2,z3,z4,z57]),(0,[z565,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z358])],[(0,[z156,z0,z1,z221,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z566,z6]),(1,[z0,z44,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z567,z4,z6]),(0,[z0,z1,z2,z10,z10,z3,z4]),(0,[z0,z1,z2,z15,z3,z148,z6])]],
   [[(0,[z0,z1,z2,z60,z3,z4,z6]),(0,[z204,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z27,z4,z6]),(0,[z0,z1,z2,z3,z21,z12,z6]),(0,[z0,z568,z1,z2,z3,z4,z6]),(0,[z569,z0,z1,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z18,z3,z4]),(0,[z570,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z412,z3,z4]),(0,[z0,z1,z2,z10,z3,z4,z421])],[(0,[z0,z1,z80,z2,z3,z27,z6]),(0,[z0,z1,z500,z2,z3,z27,z6]),(1,[z0,z1,z2,z338,z4,z6]),(0,[z0,z1,z2,z571,z3,z4,z6]),(0,[z0,z1,z28,z3,z32,z4,z6]),(0,[z98,z0,z1,z2,z18,z4,z6]),(0,[z572,z0,z1,z2,z3,z4,z6]),(0,[z0,z573,z1,z2,z3,z4,z6]),(0,[z93,z0,z1,z2,z10,z3,z4]),(0,[z0,z1,z2,z15,z3,z6,z16])],[(0,[z102,z0,z1,z2,z3,z84,z6]),(0,[z0,z1,z37,z2,z3,z21,z6]),(0,[z0,z95,z1,z2,z3,z27,z6]),(0,[z0,z1,z2,z3,z4,z25,z77]),(0,[z0,z1,z13,z3,z4,z6,z14])],[(0,[z156,z0,z1,z2,z559,z4,z6]),(0,[z0,z1,z2,z3,z4,z333,z6]),(0,[z574,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z94,z6]),(0,[z0,z1,z2,z3,z21,z124,z6]),(0,[z0,z1,z2,z3,z21,z6,z16]),(0,[z0,z1,z2,z575,z3,z4,z6]),(0,[z0,z1,z2,z3,z576,z4,z6])],[(0,[z0,z1,z2,z3,z111,z27,z6]),(0,[z106,z0,z1,z2,z3,z27,z6])],[(0,[z577,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z19,z21,z6]),(0,[z73,z0,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z578,z3,z27,z6]),(0,[z91,z0,z1,z2,z3,z4,z77]),(0,[z73,z0,z1,z2,z3,z4,z16])],[(0,[z0,z1,z2,z3,z4,z579,z6]),(0,[z7,z0,z1,z8,z3,z4,z6]),(0,[z217,z0,z1,z2,z3,z21,z6]),(0,[z0,z1,z31,z2,z3,z27,z6])],[(0,[z156,z73,z0,z1,z2,z3,z4]),(0,[z102,z0,z1,z2,z3,z21,z6]),(0,[z96,z0,z1,z2,z3,z27,z6]),(0,[z0,z1,z2,z3,z32,z21,z6]),(0,[z0,z49,z1,z28,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z580]),(0,[z0,z1,z2,z3,z581,z4,z6]),(0,[z73,z0,z1,z2,z10,z4,z6]),(0,[z582,z0,z1,z2,z3,z4,z6]),(0,[z0,z583,z1,z2,z3,z4,z6])]],
   [[(0,[z584,z0,z1,z2,z3,z4,z6]),(0,[z26,z73,z0,z1,z2,z3,z4]),(0,[z0,z585,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z586,z4,z6]),(0,[z0,z11,z1,z2,z3,z50,z6]),(0,[z0,z1,z2,z587,z3,z4,z6])],[(0,[z588,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z589,z4,z6]),(0,[z0,z1,z2,z3,z281,z29,z6])],[(0,[z0,z1,z2,z3,z4,z477,z6]),(0,[z0,z1,z2,z63,z3,z27,z6]),(0,[z0,z1,z37,z3,z29,z4,z6]),(0,[z0,z1,z2,z3,z590,z4,z6]),(0,[z0,z1,z2,z591,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z592,z6]),(1,[z0,z1,z2,z3,z281,z6]),(0,[z0,z1,z2,z3,z593,z4,z6]),(0,[z0,z1,z2,z3,z594,z4,z6]),(0,[z0,z1,z2,z3,z149,z6,z16])],[(0,[z0,z1,z191,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z595,z6]),(0,[z0,z1,z596,z2,z3,z4,z6]),(0,[z0,z1,z2,z15,z3,z27,z6]),(1,[z0,z1,z264,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z12,z6])],[(0,[z0,z453,z1,z2,z3,z4,z6]),(0,[z0,z11,z1,z2,z3,z4,z358]),(0,[z0,z597,z1,z2,z3,z4,z6]),(0,[z0,z1,z179,z2,z3,z4,z6])],[(0,[z598,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z599,z6]),(0,[z0,z1,z2,z3,z27,z12,z6]),(0,[z0,z1,z2,z10,z3,z50,z4]),(0,[z0,z1,z80,z2,z10,z3,z4]),(0,[z73,z0,z1,z2,z3,z89,z4]),(0,[z0,z1,z2,z3,z300,z4,z6])],[(0,[z0,z153,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z124,z6]),(0,[z0,z1,z2,z3,z4,z6,z16])],[(1,[z0,z1,z2,z3,z4,z396]),(0,[z0,z1,z2,z3,z228,z21,z6]),(0,[z600,z0,z1,z2,z3,z4,z6]),(0,[z0,z64,z1,z178,z3,z4,z6]),(0,[z0,z1,z2,z504,z10,z3,z4])]],
   [[(0,[z0,z1,z2,z2,z3,z4,z6]),(0,[z0,z1,z601,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z21,z602,z6]),(0,[z0,z1,z2,z3,z27,z124,z6]),(0,[z0,z1,z2,z3,z27,z6,z16]),(0,[z0,z1,z2,z3,z4,z603,z6]),(0,[z0,z1,z604,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z17,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z605]),(1,[z98,z0,z2,z111,z4,z6]),(0,[z0,z1,z2,z3,z606,z4,z6]),(0,[z607,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z608,z2,z3,z4,z6]),(0,[z73,z0,z1,z8,z2,z3,z4]),(0,[z0,z1,z609,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z610,z4,z6]),(0,[z106,z0,z1,z2,z3,z4,z14]),(0,[z0,z1,z2,z611,z3,z4,z6])],[(0,[z0,z1,z24,z2,z10,z3,z4]),(0,[z0,z612,z1,z2,z3,z4,z6]),(0,[z96,z0,z1,z2,z3,z373,z6]),(0,[z613,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z614,z4,z6]),(0,[z0,z1,z8,z28,z3,z4,z6]),(0,[z0,z1,z2,z3,z615,z4,z6]),(0,[z0,z1,z2,z3,z365,z4,z6]),(0,[z0,z1,z2,z3,z27,z89,z6]),(0,[z616,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z80,z2,z97,z4,z6]),(0,[z0,z1,z2,z3,z4,z617,z6]),(0,[z0,z1,z2,z10,z3,z498,z4]),(0,[z0,z1,z2,z3,z4,z6,z618])],[(1,[z0,z1,z2,z308,z4,z6]),(0,[z0,z248,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z4,z6,z189]),(0,[z93,z0,z64,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z619,z4,z6]),(0,[z0,z43,z1,z2,z79,z3,z6])],[(0,[z156,z0,z1,z2,z3,z4,z68]),(0,[z73,z96,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z21,z151,z6]),(0,[z0,z1,z2,z620,z3,z4,z6]),(1,[z76,z0,z1,z29,z4,z6]),(0,[z0,z621,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z622,z4,z6]),(0,[z0,z519,z1,z2,z10,z3,z4])],[(1,[z0,z1,z2,z3,z4,z216]),(0,[z0,z1,z2,z3,z4,z623,z6]),(0,[z73,z217,z0,z1,z2,z3,z4]),(0,[z0,z624,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z10,z3,z467,z4]),(0,[z0,z1,z2,z15,z10,z3,z4]),(0,[z0,z1,z2,z3,z625,z4,z6]),(0,[z256,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z626,z0,z1,z2,z3,z4,z6]),(0,[z53,z0,z1,z2,z10,z3,z4]),(0,[z0,z1,z2,z3,z4,z77,z56]),(0,[z627,z0,z1,z2,z3,z4,z6]),(0,[z76,z0,z1,z2,z29,z4,z6])],[(0,[z0,z49,z37,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z400,z6]),(0,[z628,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z629,z6]),(0,[z61,z0,z1,z2,z10,z3,z4]),(0,[z0,z1,z630,z2,z3,z4,z6])],[(0,[z0,z1,z2,z60,z3,z27,z6]),(0,[z9,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z631,z4,z6])],[(0,[z632,z0,z1,z2,z3,z4,z6]),(0,[z0,z59,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z4,z602,z6]),(0,[z0,z1,z2,z3,z280,z4,z6]),(0,[z0,z11,z2,z28,z3,z4,z6]),(0,[z93,z0,z1,z2,z4,z71,z6]),(0,[z0,z1,z2,z633,z3,z4,z6])],[(0,[z634,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z635,z4,z6]),(0,[z0,z1,z2,z28,z10,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z636]),(0,[z181,z73,z0,z1,z2,z3,z4])],[(0,[z0,z11,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z637]),(1,[z161,z1,z2,z3,z4,z6])],[(0,[z7,z0,z1,z2,z3,z301,z6]),(0,[z0,z1,z438,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z55,z27,z6]),(0,[z638,z0,z1,z2,z3,z4,z6]),(0,[z73,z0,z59,z1,z2,z3,z4]),(0,[z0,z639,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z640]),(0,[z0,z1,z2,z18,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z641]),(0,[z0,z1,z2,z79,z89,z4,z6])]],
   [[(0,[z0,z1,z2,z642,z3,z4,z6]),(0,[z0,z643,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z27,z4,z21,z6]),(0,[z87,z0,z1,z2,z10,z3,z4]),(0,[z644,z0,z1,z2,z3,z4,z6]),(1,[z0,z95,z28,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z645,z6]),(0,[z646,z0,z1,z2,z3,z4,z6])],[(0,[z647,z0,z1,z2,z3,z4,z6]),(0,[z0,z72,z1,z2,z3,z27,z6]),(1,[z0,z1,z38,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z151,z6]),(0,[z0,z1,z2,z3,z648,z4,z6]),(0,[z0,z1,z2,z649,z3,z4,z6])],[(0,[z73,z0,z1,z2,z3,z19,z4]),(0,[z73,z0,z1,z2,z3,z4,z77]),(0,[z0,z59,z1,z2,z111,z4,z6]),(0,[z76,z73,z0,z1,z2,z3,z4])],[(0,[z650,z0,z1,z2,z3,z4,z6]),(0,[z53,z0,z1,z2,z3,z511,z6]),(0,[z0,z651,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z27,z151,z6]),(0,[z0,z1,z2,z652,z3,z4,z6]),(1,[z0,z179,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z653,z4,z6]),(0,[z76,z0,z159,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z14,z16]),(0,[z0,z654,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z151,z57]),(0,[z0,z72,z1,z2,z3,z4,z56]),(0,[z73,z0,z1,z536,z2,z3,z4]),(0,[z73,z0,z1,z2,z3,z4,z163]),(0,[z0,z1,z2,z3,z4,z6,z655])],[(0,[z0,z1,z2,z60,z10,z3,z4]),(0,[z0,z1,z2,z3,z4,z656,z6]),(0,[z0,z1,z2,z3,z4,z657,z6]),(0,[z73,z0,z1,z2,z97,z3,z4]),(0,[z0,z1,z2,z89,z4,z71,z6])],[(0,[z658,z0,z1,z2,z3,z4,z6]),(0,[z659,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z82,z3,z4,z6]),(0,[z106,z0,z1,z3,z4,z25,z6])]],
   [[(0,[z0,z1,z660,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z63,z3,z4]),(0,[z0,z1,z2,z3,z661,z4,z6])],[(0,[z153,z1,z24,z2,z3,z4,z6]),(0,[z0,z662,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z10,z18,z3,z4]),(0,[z90,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z80,z97,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z255]),(0,[z663,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z575,z10,z3,z4])],[(0,[z664,z0,z1,z2,z3,z4,z6]),(0,[z0,z11,z1,z2,z3,z12,z6])],[(0,[z102,z0,z1,z2,z3,z276,z6]),(0,[z0,z1,z2,z3,z665,z4,z6]),(0,[z0,z95,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z666,z6]),(0,[z0,z1,z2,z3,z4,z667,z6]),(0,[z668,z0,z1,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z4,z25])],[(0,[z669,z0,z1,z2,z3,z4,z6]),(0,[z96,z1,z2,z3,z4,z21,z6]),(0,[z0,z1,z2,z3,z474,z21,z6]),(0,[z0,z43,z1,z2,z3,z27,z6]),(0,[z0,z670,z1,z2,z3,z4,z6]),(0,[z93,z161,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z323]),(1,[z0,z1,z2,z10,z4,z124])],[(0,[z0,z671,z1,z2,z3,z4,z6]),(0,[z106,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z10,z3,z21,z6]),(0,[z0,z1,z2,z10,z3,z4,z21]),(0,[z0,z1,z2,z578,z3,z4,z6]),(0,[z0,z1,z2,z3,z672,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z673]),(0,[z0,z1,z2,z10,z3,z4,z16])],[(0,[z0,z1,z2,z3,z50,z21,z6]),(0,[z98,z0,z2,z3,z111,z4,z6]),(0,[z0,z59,z1,z2,z3,z4,z235]),(0,[z0,z1,z31,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z674])]],
   [[(0,[z0,z49,z153,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z47,z6]),(0,[z0,z1,z675,z2,z3,z4,z6]),(0,[z96,z0,z1,z2,z3,z4,z6]),(0,[z0,z11,z2,z3,z4,z12,z6]),(0,[z0,z1,z2,z3,z4,z676,z6]),(0,[z0,z1,z2,z3,z148,z4,z16])],[(0,[z677,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z678,z2,z3,z4,z6])],[(0,[z679,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z680]),(0,[z0,z64,z1,z2,z79,z3,z6]),(0,[z0,z1,z2,z3,z4,z681,z6]),(0,[z0,z1,z97,z3,z29,z4,z6]),(0,[z682,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z13,z2,z3,z4,z25]),(0,[z0,z1,z2,z79,z3,z4,z6]),(0,[z93,z0,z1,z2,z3,z89,z6]),(0,[z0,z226,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z683,z4,z6])],[(0,[z0,z1,z2,z684,z3,z4,z6]),(0,[z0,z1,z2,z63,z3,z4,z6]),(0,[z282,z0,z1,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z4,z124]),(0,[z598,z0,z1,z2,z10,z3,z4])],[(0,[z0,z153,z1,z2,z10,z3,z4]),(0,[z9,z0,z1,z2,z3,z27,z6]),(0,[z0,z1,z2,z10,z3,z4,z203])],[(0,[z0,z685,z1,z2,z3,z4,z6]),(0,[z0,z1,z141,z2,z3,z29,z6]),(0,[z0,z1,z2,z10,z3,z32,z4]),(0,[z0,z1,z2,z3,z686,z4,z6])],[(1,[z53,z1,z60,z3,z4,z6]),(0,[z0,z1,z2,z3,z687,z4,z6]),(0,[z0,z95,z1,z37,z3,z4,z6]),(0,[z0,z1,z2,z10,z3,z89,z4])],[(1,[z0,z1,z2,z559,z4,z6]),(0,[z688,z0,z1,z2,z3,z4,z6]),(0,[z689,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z690,z6]),(0,[z0,z1,z2,z3,z4,z691,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z692]),(0,[z73,z0,z1,z2,z3,z29,z4]),(0,[z73,z0,z43,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z89,z4,z6])],[(0,[z0,z693,z1,z2,z3,z4,z6]),(0,[z694,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z150,z27,z6]),(0,[z98,z0,z1,z264,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z695,z6]),(0,[z0,z1,z31,z37,z3,z4,z6]),(0,[z146,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z696,z2,z3,z4,z6]),(0,[z0,z1,z2,z697,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z454]),(0,[z0,z1,z2,z3,z698,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z86]),(1,[z73,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z699,z3,z4,z6]),(0,[z0,z1,z700,z2,z3,z4,z6]),(0,[z9,z0,z1,z2,z19,z4,z6]),(0,[z96,z0,z1,z2,z3,z477,z6]),(0,[z0,z1,z2,z701,z3,z4,z6]),(1,[z93,z0,z1,z2,z71,z6])],[(0,[z0,z1,z60,z28,z3,z4,z6]),(1,[z96,z1,z2,z3,z21,z6]),(0,[z91,z0,z1,z2,z3,z399,z6]),(0,[z98,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z702]),(1,[z0,z159,z2,z3,z4,z6]),(0,[z155,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z205])],[(1,[z217,z1,z2,z3,z21,z6]),(0,[z703,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z235,z6]),(0,[z0,z2,z3,z50,z4,z12,z6])],[(0,[z0,z1,z2,z3,z4,z6,z704]),(0,[z0,z705,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z706,z4,z6]),(0,[z261,z0,z72,z2,z3,z4,z6]),(0,[z0,z72,z1,z2,z3,z4,z151]),(0,[z0,z1,z630,z2,z10,z3,z4])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z707]),(0,[z0,z1,z2,z3,z27,z708]),(0,[z0,z1,z2,z3,z400,z6]),(0,[z0,z709,z2,z3,z4,z6])],[(0,[z0,z1,z2,z308,z333,z6])],[(0,[z0,z1,z2,z10,z3,z193]),(0,[z73,z75,z1,z2,z3,z21]),(0,[z0,z1,z2,z710,z4,z6])],[(0,[z0,z1,z2,z3,z84,z6]),(0,[z0,z360,z2,z3,z21,z6]),(0,[z73,z0,z1,z2,z3,z17]),(0,[z0,z1,z2,z3,z711,z6])],[(0,[z0,z1,z2,z3,z27,z47]),(0,[z0,z1,z2,z3,z712,z6])],[(0,[z0,z1,z2,z713,z3,z4]),(0,[z73,z0,z1,z2,z384,z4])],[(0,[z0,z1,z2,z294,z21,z6]),(0,[z0,z1,z2,z3,z4,z714]),(0,[z0,z1,z2,z3,z4,z715]),(0,[z716,z1,z2,z3,z4,z6])],[(0,[z0,z360,z2,z173,z4,z6]),(0,[z73,z0,z1,z2,z173,z4]),(0,[z0,z1,z2,z4,z717,z6])],[(0,[z0,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z27,z68]),(0,[z0,z1,z2,z10,z3,z477]),(0,[z0,z1,z2,z4,z6,z718]),(0,[z0,z1,z2,z719,z4,z6]),(0,[z0,z1,z38,z3,z4,z6])],[(0,[z87,z1,z2,z280,z4,z77])],[(0,[z1,z2,z720,z3,z4,z6]),(0,[z7,z1,z8,z10,z3,z4]),(0,[z0,z1,z2,z3,z6,z721])],[],[(0,[z0,z1,z2,z3,z27,z86]),(0,[z0,z44,z2,z10,z3,z4]),(0,[z0,z1,z2,z10,z3,z722])],[(0,[z156,z24,z2,z3,z4,z68]),(0,[z73,z0,z1,z2,z262,z4]),(0,[z607,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z723,z6]),(0,[z0,z179,z31,z3,z4,z6]),(0,[z724,z1,z2,z3,z4,z6])],[(0,[z1,z2,z355,z3,z19,z21]),(0,[z1,z2,z3,z725,z4,z6])],[(0,[z0,z24,z221,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z726])]],
   [[(0,[z261,z0,z2,z3,z498,z4]),(0,[z0,z1,z2,z3,z722,z6])],[(0,[z0,z1,z2,z3,z193,z6]),(0,[z73,z0,z59,z2,z18,z4]),(0,[z0,z1,z2,z10,z395,z4]),(0,[z73,z0,z1,z2,z4,z232])],[(0,[z0,z1,z2,z3,z727,z6]),(0,[z0,z1,z728,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z199]),(0,[z0,z11,z2,z3,z729,z6]),(0,[z0,z1,z730,z2,z3,z4])],[(0,[z0,z1,z731,z3,z4,z6]),(0,[z0,z1,z2,z3,z27,z732]),(0,[z0,z1,z2,z3,z4,z323])],[(0,[z0,z1,z2,z3,z4,z206]),(0,[z0,z2,z3,z4,z6,z733]),(0,[z0,z1,z2,z3,z734,z4]),(0,[z76,z73,z0,z1,z29,z4]),(0,[z0,z1,z2,z3,z4,z735]),(0,[z73,z0,z1,z2,z4,z736])],[(0,[z1,z2,z3,z4,z737,z6]),(0,[z0,z1,z2,z738,z3,z4]),(0,[z73,z0,z43,z1,z3,z32])],[(0,[z659,z1,z2,z3,z4,z57]),(0,[z0,z37,z739,z3,z4,z6]),(0,[z0,z1,z2,z166,z3,z467])],[(0,[z0,z1,z2,z3,z740,z6]),(0,[z0,z1,z2,z741,z3,z27]),(0,[z0,z1,z2,z3,z742,z6])],[(0,[z73,z102,z153,z2,z3,z4]),(0,[z743,z0,z1,z2,z3,z4]),(0,[z161,z1,z2,z3,z89,z6])],[(0,[z1,z2,z3,z4,z737,z57])],[(0,[z0,z1,z744,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z745]),(0,[z0,z1,z2,z10,z3,z400]),(0,[z0,z1,z2,z3,z746,z6])],[(0,[z75,z1,z2,z63,z4,z6]),(0,[z0,z1,z747,z3,z21,z6]),(0,[z0,z748,z1,z2,z3,z6]),(0,[z0,z749,z2,z3,z4,z6]),(0,[z0,z1,z2,z750,z4,z6]),(0,[z0,z685,z28,z3,z4,z6])],[(0,[z0,z1,z2,z3,z21,z202]),(0,[z0,z49,z547,z3,z4,z6]),(0,[z0,z751,z2,z3,z4,z6]),(0,[z181,z0,z289,z2,z3,z4])],[(0,[z0,z752,z2,z3,z4,z6]),(0,[z53,z1,z60,z3,z4,z396])],[(0,[z0,z1,z2,z559,z4,z6]),(0,[z0,z1,z238,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z753]),(0,[z73,z0,z159,z2,z3,z4])],[(0,[z0,z290,z2,z3,z263,z6]),(0,[z0,z1,z2,z3,z754,z6])]],
   [[(0,[z755,z0,z1,z2,z3,z4]),(0,[z0,z756,z2,z3,z4,z6]),(0,[z98,z0,z453,z2,z111,z6])],[(0,[z0,z1,z2,z10,z3,z373]),(0,[z0,z1,z2,z3,z373,z40])],[(0,[z73,z0,z1,z2,z3,z4]),(0,[z0,z64,z178,z3,z50,z6]),(0,[z0,z1,z2,z326,z3,z16]),(0,[z106,z0,z1,z3,z443,z4])],[(0,[z0,z1,z2,z757,z308,z4]),(0,[z0,z1,z2,z559,z333,z6]),(0,[z0,z758,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z759,z6]),(0,[z0,z1,z760,z3,z4,z6]),(1,[z0,z1,z710,z4,z6]),(0,[z256,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z761,z6])],[(0,[z0,z1,z2,z762,z19,z4]),(0,[z0,z59,z2,z18,z21,z6]),(0,[z0,z1,z2,z504,z338,z4]),(0,[z0,z159,z2,z3,z4,z6])],[(0,[z73,z0,z1,z2,z27,z163])],[(0,[z0,z1,z763,z2,z3,z6]),(0,[z0,z179,z3,z32,z4,z6])],[(0,[z0,z1,z2,z764,z4,z6]),(0,[z0,z1,z2,z15,z3,z16])],[(0,[z9,z1,z2,z765,z4,z6]),(0,[z231,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z27,z66]),(0,[z0,z1,z2,z3,z4,z766])],[(0,[z767,z0,z1,z2,z559,z4]),(0,[z0,z1,z2,z3,z27,z189]),(0,[z0,z1,z630,z3,z4,z14]),(0,[z93,z0,z1,z2,z454,z71])],[(0,[z0,z1,z2,z4,z205,z232])],[(0,[z0,z1,z2,z3,z4,z768]),(0,[z0,z769,z2,z3,z4,z6]),(0,[z73,z770,z1,z2,z3,z4]),(0,[z0,z1,z2,z15,z3,z721])],[(0,[z0,z1,z2,z3,z276,z6]),(0,[z1,z2,z3,z21,z483,z6])],[(0,[z771,z0,z1,z2,z21,z6]),(0,[z0,z1,z772,z3,z4,z6]),(0,[z0,z1,z2,z773,z3,z4])],[(0,[z0,z1,z2,z3,z774,z6]),(0,[z0,z1,z2,z3,z775,z6]),(0,[z0,z1,z38,z10,z3,z4])],[(0,[z0,z1,z2,z3,z4,z776]),(0,[z0,z1,z2,z3,z777,z6])]],
   [[(0,[z0,z778,z2,z3,z4,z6]),(0,[z1,z2,z3,z252,z21,z6]),(0,[z565,z0,z2,z111,z4,z6])],[(0,[z0,z779,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z780,z6]),(0,[z73,z0,z179,z2,z3,z4])],[],[(0,[z0,z59,z238,z3,z4,z6]),(0,[z0,z1,z781,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z782]),(0,[z0,z639,z2,z3,z4,z56]),(0,[z76,z0,z1,z141,z29,z6]),(0,[z93,z0,z1,z2,z10,z71]),(0,[z73,z0,z1,z2,z625,z4])],[(0,[z0,z1,z221,z3,z27,z6]),(0,[z73,z0,z1,z2,z10,z27]),(0,[z0,z1,z31,z3,z246,z6]),(0,[z0,z1,z2,z10,z3,z399])],[(0,[z73,z45,z1,z2,z3,z4])],[(0,[z0,z783,z2,z3,z4,z6]),(0,[z0,z1,z2,z19,z4,z206]),(0,[z201,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z27,z235])],[(0,[z0,z1,z2,z308,z4,z68]),(0,[z53,z1,z60,z3,z27,z6]),(0,[z0,z1,z2,z3,z784,z6]),(0,[z0,z1,z2,z3,z27,z785])],[(0,[z0,z1,z786,z3,z4,z6]),(0,[z91,z1,z2,z3,z21,z57])],[(0,[z156,z24,z221,z3,z4,z6])],[(0,[z0,z1,z2,z3,z787,z6]),(0,[z0,z1,z2,z3,z373,z206]),(0,[z73,z0,z1,z2,z280,z4]),(0,[z0,z1,z788,z3,z4,z6])],[(0,[z0,z1,z2,z3,z789,z6]),(0,[z0,z1,z2,z3,z4,z790])],[(1,[z73,z1,z2,z19,z21]),(0,[z0,z1,z2,z322,z3,z27])],[(0,[z0,z1,z2,z338,z21,z6]),(0,[z0,z1,z2,z3,z27,z255]),(0,[z0,z2,z18,z791,z4,z6]),(0,[z73,z93,z0,z1,z2,z160])],[(0,[z0,z1,z2,z3,z4,z40]),(0,[z122,z0,z2,z3,z4,z151])],[(0,[z73,z0,z1,z2,z252,z4]),(0,[z73,z410,z0,z1,z2,z4])]],
   [[],[(0,[z0,z1,z2,z89,z717,z6]),(0,[z73,z0,z1,z2,z353,z4])],[(0,[z0,z1,z2,z3,z4,z792]),(0,[z0,z1,z2,z244,z63,z4]),(0,[z515,z1,z2,z3,z21,z6]),(0,[z73,z0,z1,z2,z89,z21])],[(0,[z0,z1,z2,z63,z4,z206]),(0,[z0,z1,z2,z4,z6,z793]),(0,[z161,z43,z1,z2,z3,z6]),(0,[z73,z0,z1,z2,z79,z89])],[(0,[z0,z49,z382,z3,z4,z6]),(0,[z0,z794,z2,z3,z4,z6]),(0,[z0,z1,z238,z10,z3,z4]),(0,[z0,z795,z1,z2,z3,z6]),(0,[z796,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z797,z3,z4]),(0,[z0,z1,z2,z79,z89,z6])],[(0,[z45,z1,z2,z3,z373,z6]),(0,[z565,z73,z0,z1,z2,z4])],[(0,[z73,z0,z1,z2,z684,z4]),(0,[z0,z1,z141,z2,z3,z6])],[(0,[z102,z779,z2,z3,z4,z6]),(0,[z0,z1,z2,z798,z294,z4]),(0,[z0,z1,z264,z3,z21,z6]),(0,[z0,z1,z2,z3,z4,z799]),(0,[z0,z1,z2,z3,z800,z6])],[(0,[z0,z1,z2,z801,z3,z4]),(0,[z73,z0,z290,z2,z3,z4]),(0,[z0,z1,z2,z3,z27,z232])],[(0,[z0,z1,z2,z3,z802,z6]),(0,[z638,z1,z2,z3,z21,z6])],[(0,[z282,z1,z2,z19,z4,z6]),(0,[z73,z282,z0,z1,z2,z4]),(0,[z0,z1,z529,z3,z4,z14]),(0,[z0,z159,z2,z10,z3,z4])],[(0,[z0,z803,z1,z2,z3,z6]),(0,[z0,z1,z804,z2,z3,z4]),(0,[z0,z1,z440,z3,z4,z14]),(0,[z256,z0,z1,z2,z4,z14])],[(0,[z0,z1,z2,z805,z4,z6]),(1,[z1,z2,z765,z4,z6]),(0,[z91,z1,z2,z3,z233,z57]),(0,[z806,z1,z2,z3,z4,z6]),(0,[z0,z59,z2,z10,z18,z4])],[(0,[z0,z1,z807,z3,z4,z6]),(0,[z137,z24,z2,z3,z4,z6]),(0,[z0,z290,z2,z3,z4,z396]),(0,[z73,z96,z1,z2,z3,z21]),(0,[z98,z0,z2,z111,z21,z6]),(0,[z0,z1,z2,z808,z3,z4]),(0,[z0,z81,z2,z3,z4,z6])],[(0,[z53,z1,z60,z3,z511,z6]),(0,[z0,z1,z2,z3,z809,z4]),(0,[z0,z519,z2,z3,z4,z56]),(0,[z73,z0,z1,z2,z300,z4])],[(0,[z0,z1,z2,z173,z4,z6]),(1,[z0,z2,z791,z4,z6]),(0,[z0,z1,z80,z97,z4,z86])]],
   [[(0,[z0,z1,z2,z341,z3,z21]),(0,[z0,z1,z178,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z810])],[(0,[z0,z1,z720,z3,z4,z6]),(0,[z0,z1,z359,z2,z3,z27])],[],[(0,[z346,z0,z1,z2,z3,z21]),(0,[z87,z1,z2,z3,z27,z77]),(0,[z0,z1,z2,z3,z811,z6])],[(0,[z0,z1,z2,z3,z812,z6]),(0,[z73,z0,z1,z2,z3,z761]),(0,[z73,z813,z1,z2,z3,z4])],[(0,[z156,z73,z24,z2,z3,z4]),(0,[z0,z814,z2,z3,z21,z6]),(0,[z73,z93,z45,z1,z2,z4])],[(0,[z73,z1,z2,z3,z19,z21]),(0,[z0,z815,z1,z2,z3,z4]),(0,[z0,z816,z2,z3,z4,z6])],[(0,[z73,z0,z1,z2,z19,z21]),(0,[z0,z1,z438,z3,z203,z6]),(0,[z155,z1,z2,z3,z4,z57]),(0,[z0,z817,z2,z3,z4,z6])],[(0,[z73,z0,z1,z2,z257,z4])],[(0,[z0,z1,z2,z559,z4,z68]),(0,[z0,z1,z2,z3,z17,z6]),(0,[z161,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z4,z818]),(0,[z0,z2,z3,z729,z12,z6]),(0,[z0,z1,z781,z10,z3,z4])],[(0,[z73,z217,z1,z2,z3,z21]),(0,[z0,z1,z2,z280,z27,z6]),(0,[z0,z1,z2,z741,z3,z4]),(0,[z0,z819,z2,z3,z4,z6])],[(0,[z156,z779,z2,z3,z4,z6]),(0,[z0,z49,z37,z3,z4,z6]),(0,[z98,z73,z0,z2,z111,z4])],[],[(0,[z0,z1,z2,z3,z820,z6])],[(0,[z0,z1,z2,z3,z511,z47]),(0,[z75,z1,z2,z3,z4,z77]),(0,[z0,z1,z2,z3,z4,z821])],[(0,[z0,z179,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z233,z6])]],
   [[(0,[z0,z651,z37,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z822])],[(0,[z0,z1,z2,z823,z4,z6]),(0,[z1,z2,z3,z19,z21,z6]),(0,[z1,z2,z10,z3,z27,z21])],[(0,[z45,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z205])],[(0,[z0,z1,z221,z308,z4,z6]),(0,[z0,z1,z2,z824,z4,z6]),(0,[z0,z1,z825,z3,z4,z6]),(0,[z0,z1,z2,z3,z27,z826]),(0,[z98,z0,z238,z111,z4,z6]),(0,[z0,z1,z2,z3,z4,z827]),(0,[z0,z44,z2,z79,z3,z6]),(0,[z73,z93,z0,z1,z2,z89])],[(0,[z0,z828,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z829]),(0,[z93,z0,z1,z2,z412,z71])],[(0,[z0,z1,z221,z3,z4,z216]),(0,[z0,z1,z2,z3,z830,z6]),(0,[z93,z0,z1,z2,z412,z4])],[(0,[z87,z1,z2,z3,z487,z77]),(0,[z0,z1,z2,z3,z4,z831])],[(0,[z0,z290,z2,z3,z27,z6]),(0,[z0,z1,z2,z578,z3,z212]),(0,[z0,z1,z2,z832,z3,z4]),(0,[z833,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z10,z21,z124])],[(0,[z0,z360,z2,z294,z4,z6]),(0,[z632,z0,z1,z29,z4,z6])],[(0,[z0,z834,z2,z3,z4,z6]),(1,[z1,z2,z3,z725,z6]),(0,[z1,z2,z3,z21,z629,z6]),(0,[z0,z1,z2,z4,z835,z6]),(0,[z0,z1,z2,z4,z6,z836])],[(0,[z0,z360,z2,z3,z4,z6]),(0,[z0,z248,z2,z3,z12,z6])],[(0,[z102,z153,z2,z3,z27,z6]),(0,[z96,z1,z2,z3,z21,z40]),(0,[z0,z1,z2,z3,z21,z837]),(0,[z0,z1,z2,z3,z838,z6]),(0,[z73,z0,z1,z2,z594,z4]),(0,[z73,z0,z1,z839,z3,z4])],[(0,[z0,z1,z840,z2,z3,z6]),(0,[z0,z1,z2,z280,z487,z6]),(0,[z841,z1,z2,z3,z4,z6]),(0,[z73,z161,z1,z2,z4,z6])],[(0,[z0,z1,z2,z294,z4,z6]),(0,[z842,z0,z1,z2,z3,z4]),(0,[z73,z93,z161,z1,z2,z4])],[(0,[z0,z1,z843,z3,z21,z6]),(0,[z844,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z845])]],
   [[(0,[z0,z2,z3,z846,z4,z6]),(0,[z0,z1,z2,z3,z847,z6]),(0,[z0,z28,z3,z164,z4,z6]),(0,[z0,z1,z848,z3,z4,z6])],[(1,[z1,z2,z3,z4,z737]),(0,[z336,z0,z1,z2,z3,z421])],[(0,[z0,z1,z2,z10,z3,z511]),(0,[z53,z1,z60,z3,z21,z6])],[(0,[z0,z1,z2,z849,z559,z4]),(0,[z73,z0,z1,z2,z3,z276]),(0,[z0,z1,z2,z850,z4,z6]),(0,[z73,z0,z11,z2,z3,z12]),(0,[z0,z81,z2,z10,z3,z4])],[(0,[z0,z1,z2,z3,z851,z6]),(0,[z0,z11,z178,z3,z4,z6])],[(0,[z0,z1,z2,z10,z485,z4]),(0,[z0,z1,z2,z412,z89,z4])],[(0,[z0,z1,z2,z3,z4,z852]),(0,[z0,z1,z2,z3,z21,z454]),(0,[z0,z1,z178,z10,z3,z4]),(0,[z0,z853,z1,z2,z3,z4])],[(0,[z98,z0,z359,z2,z111,z4]),(0,[z73,z0,z1,z2,z10,z4])],[(0,[z0,z1,z2,z3,z4,z854]),(0,[z855,z0,z1,z2,z4,z6]),(0,[z76,z0,z1,z244,z29,z4]),(0,[z0,z1,z2,z3,z4,z856])],[],[(0,[z0,z1,z2,z857,z4,z6]),(0,[z858,z0,z1,z2,z3,z4]),(0,[z256,z0,z1,z2,z148,z4])],[],[(0,[z0,z1,z13,z3,z21,z14]),(0,[z0,z859,z1,z2,z3,z4])],[(0,[z250,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z4,z6,z860]),(0,[z0,z861,z2,z3,z4,z6])],[(0,[z73,z0,z1,z2,z3,z333]),(0,[z0,z1,z862,z3,z4,z6]),(0,[z0,z290,z2,z3,z511,z6]),(0,[z0,z1,z2,z863,z4,z6])],[(0,[z73,z0,z1,z2,z4,z428]),(0,[z0,z1,z2,z322,z3,z4])]],
   [[(0,[z864,z0,z1,z2,z3,z4]),(0,[z0,z1,z3,z710,z4,z6]),(0,[z204,z226,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z865,z6])],[(0,[z0,z49,z37,z10,z3,z4])],[(0,[z0,z1,z2,z3,z866,z6]),(0,[z0,z1,z2,z3,z21,z47]),(0,[z1,z2,z3,z867,z21,z6]),(0,[z0,z1,z2,z3,z868,z6])],[(0,[z0,z1,z80,z10,z97,z4]),(0,[z0,z1,z2,z3,z467,z16])],[(0,[z73,z0,z1,z2,z3,z263]),(0,[z0,z1,z2,z3,z4,z869]),(0,[z73,z0,z1,z2,z3,z487]),(0,[z870,z1,z2,z3,z4,z6]),(0,[z98,z0,z2,z400,z111,z6]),(0,[z0,z2,z3,z4,z871,z56]),(0,[z0,z1,z2,z3,z4,z202]),(0,[z0,z1,z2,z3,z872,z6])],[(0,[z0,z1,z221,z559,z4,z6]),(0,[z0,z1,z2,z3,z263,z396]),(0,[z9,z1,z2,z19,z54,z6]),(0,[z96,z1,z2,z3,z21,z206]),(0,[z0,z1,z2,z341,z3,z400]),(0,[z0,z64,z2,z3,z50,z6]),(0,[z0,z1,z38,z79,z3,z6]),(0,[z73,z0,z1,z2,z401,z4]),(0,[z73,z0,z64,z2,z3,z50]),(0,[z0,z72,z2,z3,z4,z56])],[(0,[z0,z1,z2,z3,z21,z68]),(0,[z0,z1,z2,z173,z4,z47]),(0,[z73,z873,z1,z2,z3,z4])],[(0,[z0,z1,z191,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z874]),(0,[z73,z724,z1,z2,z3,z4])],[(0,[z26,z1,z2,z3,z725,z6]),(0,[z1,z2,z3,z109,z27,z6]),(0,[z73,z0,z1,z2,z3,z347]),(0,[z45,z1,z2,z10,z3,z4])],[(0,[z0,z1,z2,z15,z3,z212])],[(0,[z0,z1,z2,z3,z875,z6]),(0,[z73,z0,z1,z2,z63,z27]),(0,[z0,z1,z2,z3,z21,z86])],[(0,[z1,z2,z19,z29,z21,z6]),(0,[z0,z11,z2,z3,z383,z6]),(0,[z73,z0,z1,z31,z3,z203])],[(0,[z0,z1,z191,z3,z333,z6]),(0,[z0,z1,z2,z3,z876,z6]),(0,[z0,z1,z2,z135,z177,z6]),(0,[z0,z59,z2,z18,z4,z6])],[(0,[z91,z1,z2,z3,z399,z57]),(0,[z1,z2,z3,z4,z877,z6])],[(0,[z878,z1,z2,z3,z4,z6]),(0,[z0,z1,z31,z3,z203,z6]),(0,[z73,z879,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z193,z68]),(0,[z0,z1,z2,z880,z4,z6]),(0,[z73,z0,z1,z2,z355,z4]),(0,[z0,z1,z2,z3,z721,z16])]],
   [[(0,[z1,z2,z3,z488,z21,z6])],[(0,[z0,z360,z2,z10,z3,z4]),(0,[z0,z1,z2,z3,z4,z881]),(0,[z0,z1,z2,z882,z3,z4]),(0,[z340,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z338,z347,z6])],[(0,[z96,z1,z2,z63,z27,z6])],[(0,[z73,z0,z1,z2,z55,z27]),(0,[z0,z1,z2,z3,z883,z6]),(0,[z0,z1,z3,z4,z25,z884])],[(0,[z0,z1,z2,z3,z4,z885]),(0,[z0,z1,z359,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z886]),(0,[z73,z0,z1,z2,z214,z4])],[(0,[z887,z0,z1,z2,z3,z4]),(0,[z0,z1,z888,z2,z3,z4])],[(0,[z0,z1,z2,z3,z373,z6]),(0,[z0,z1,z2,z10,z3,z27])],[(0,[z73,z0,z1,z2,z3,z94]),(0,[z0,z1,z2,z3,z236,z481]),(0,[z0,z49,z453,z2,z3,z6]),(0,[z889,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z717,z6])],[(0,[z0,z1,z2,z3,z4,z890]),(0,[z0,z1,z2,z3,z891,z6]),(0,[z1,z2,z765,z19,z4,z6]),(0,[z0,z1,z2,z3,z4,z892]),(0,[z0,z1,z2,z893,z4,z6]),(0,[z0,z43,z1,z10,z3,z32])],[(0,[z0,z1,z2,z894,z4,z6]),(0,[z0,z247,z2,z3,z50,z6])],[(0,[z0,z43,z1,z3,z32,z6])],[(0,[z0,z1,z2,z10,z548,z4])],[(0,[z0,z1,z2,z3,z895,z6]),(0,[z0,z896,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z4,z392])],[(0,[z0,z1,z2,z3,z897,z6]),(0,[z73,z0,z1,z2,z253,z4]),(0,[z0,z898,z2,z3,z4,z6])],[(0,[z0,z1,z2,z10,z4,z656]),(0,[z73,z0,z1,z2,z899,z4]),(0,[z73,z0,z900,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z901]),(0,[z743,z0,z1,z2,z294,z4]),(0,[z0,z1,z2,z3,z4,z902]),(0,[z0,z1,z2,z3,z347,z6]),(0,[z0,z1,z903,z3,z4,z6]),(0,[z0,z1,z2,z3,z904,z4])]],
   [[(0,[z0,z1,z2,z3,z399,z6]),(0,[z0,z1,z37,z141,z3,z6])],[(0,[z0,z354,z28,z3,z4,z6]),(0,[z0,z1,z2,z905,z4,z6]),(0,[z261,z0,z2,z3,z27,z151]),(0,[z0,z1,z2,z3,z906,z6]),(0,[z0,z1,z31,z3,z907,z6])],[(0,[z0,z1,z908,z3,z4,z6]),(0,[z0,z1,z2,z3,z27,z909]),(0,[z0,z1,z2,z910,z4,z6])],[(0,[z0,z1,z2,z244,z3,z21]),(0,[z73,z0,z1,z2,z21,z163])],[(0,[z0,z1,z2,z3,z911,z6]),(0,[z0,z1,z2,z3,z4,z912]),(0,[z0,z178,z3,z50,z4,z6]),(0,[z0,z1,z2,z3,z913,z6])],[(0,[z73,z93,z0,z1,z2,z21]),(0,[z261,z0,z2,z3,z4,z871])],[(0,[z0,z1,z2,z3,z21,z66]),(0,[z0,z1,z2,z3,z4,z914]),(0,[z73,z0,z453,z1,z2,z3]),(0,[z93,z0,z1,z2,z407,z6]),(0,[z0,z1,z2,z915,z4,z6])],[(0,[z0,z1,z2,z3,z21,z189]),(0,[z1,z2,z3,z21,z328,z6]),(0,[z0,z1,z2,z3,z916,z6]),(0,[z0,z1,z2,z15,z205,z16])],[(0,[z0,z1,z917,z3,z4,z6]),(0,[z269,z1,z2,z19,z4,z6]),(0,[z628,z1,z2,z3,z21,z6]),(0,[z1,z2,z3,z220,z27,z6]),(0,[z918,z1,z2,z3,z4,z6])],[(0,[z156,z24,z2,z3,z27,z6]),(0,[z73,z0,z1,z2,z294,z4]),(0,[z0,z1,z2,z3,z919,z6]),(0,[z0,z11,z123,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z920]),(0,[z813,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z921]),(0,[z0,z43,z179,z3,z32,z6]),(0,[z73,z0,z769,z2,z3,z4])],[(0,[z0,z1,z2,z3,z922,z6]),(0,[z7,z1,z8,z3,z301,z6])],[(0,[z1,z2,z551,z3,z21,z6]),(0,[z0,z1,z2,z633,z10,z4])],[(0,[z0,z1,z2,z923,z173,z4])],[(0,[z0,z1,z191,z10,z3,z4]),(0,[z137,z1,z2,z3,z21,z6]),(0,[z0,z249,z2,z3,z4,z56])],[(0,[z0,z1,z2,z3,z924,z6]),(0,[z0,z1,z925,z3,z4,z6]),(0,[z73,z0,z1,z2,z4,z463]),(0,[z155,z1,z2,z504,z3,z4])],[(0,[z432,z1,z2,z3,z21,z6]),(0,[z73,z0,z1,z2,z4,z464]),(0,[z0,z1,z264,z3,z4,z6]),(0,[z348,z0,z1,z2,z10,z4])]],
   [[(0,[z0,z1,z2,z412,z3,z21]),(0,[z0,z304,z2,z3,z277,z6]),(0,[z0,z1,z926,z3,z4,z6])],[(0,[z1,z2,z3,z27,z21,z6]),(0,[z0,z1,z2,z3,z365,z149])],[(0,[z0,z1,z221,z3,z21,z6]),(0,[z573,z1,z2,z3,z21,z6]),(0,[z0,z1,z3,z21,z6,z927]),(0,[z0,z1,z2,z3,z4,z928])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z929,z6]),(0,[z627,z1,z2,z3,z21,z6])],[(0,[z0,z930,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z21,z235]),(0,[z0,z1,z2,z3,z4,z931])],[(0,[z0,z1,z2,z355,z3,z21]),(0,[z98,z0,z2,z111,z4,z6])],[(0,[z0,z1,z2,z932,z4,z6]),(0,[z0,z1,z2,z10,z3,z54]),(0,[z282,z0,z1,z2,z71,z6]),(0,[z1,z2,z3,z933,z4,z6])],[(0,[z0,z2,z3,z4,z934,z6]),(0,[z0,z935,z2,z3,z21,z6])],[(0,[z0,z1,z2,z3,z333,z6]),(0,[z0,z1,z2,z3,z936,z6]),(0,[z106,z0,z1,z3,z27,z25])],[(0,[z53,z1,z60,z173,z4,z6]),(0,[z0,z1,z2,z4,z736,z163])],[(0,[z0,z1,z2,z10,z3,z17]),(0,[z1,z2,z3,z589,z21,z6]),(0,[z0,z1,z3,z21,z937,z6]),(0,[z0,z1,z3,z32,z907,z6])],[(0,[z0,z1,z221,z3,z193,z6]),(0,[z938,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z21,z255]),(0,[z939,z0,z1,z2,z3,z6]),(0,[z0,z1,z3,z907,z4,z6])],[(0,[z0,z940,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z27,z358]),(0,[z0,z1,z2,z3,z4,z941]),(0,[z98,z0,z2,z791,z4,z6]),(0,[z98,z0,z2,z10,z111,z4])],[(0,[z0,z1,z2,z3,z762,z4]),(0,[z0,z814,z2,z3,z4,z6]),(0,[z0,z44,z2,z3,z27,z6]),(0,[z0,z1,z80,z701,z4,z6]),(1,[z0,z1,z2,z4,z736])],[(0,[z942,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z10,z173,z4]),(0,[z0,z1,z943,z2,z3,z6]),(0,[z96,z1,z2,z10,z3,z21]),(0,[z0,z1,z2,z3,z4,z944])],[(0,[z217,z1,z2,z10,z3,z21]),(0,[z0,z1,z2,z945,z3,z4]),(0,[z0,z1,z2,z3,z4,z946])]],
   [[(0,[z0,z1,z2,z244,z19,z4]),(0,[z0,z1,z2,z3,z947,z6])],[(0,[z161,z1,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z948])],[],[],[(0,[z0,z1,z2,z3,z4,z949]),(0,[z0,z950,z2,z3,z4,z6]),(0,[z0,z1,z951,z2,z3,z4])],[(0,[z0,z1,z2,z3,z952,z6]),(0,[z953,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z148,z149])],[(0,[z0,z1,z2,z3,z4,z954]),(0,[z0,z1,z747,z3,z4,z6]),(0,[z0,z1,z2,z3,z21,z232]),(0,[z0,z1,z2,z3,z955,z6]),(0,[z0,z1,z2,z3,z4,z871]),(0,[z162,z0,z536,z2,z3,z4])],[(0,[z0,z1,z2,z923,z3,z4]),(0,[z96,z1,z2,z63,z477,z6]),(0,[z0,z179,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z956,z6])],[(0,[z96,z1,z2,z229,z4,z6]),(0,[z73,z0,z1,z2,z3,z233]),(0,[z0,z1,z2,z957,z3,z4]),(0,[z0,z1,z2,z3,z4,z958])],[(0,[z73,z1,z2,z19,z4,z21]),(0,[z126,z1,z2,z3,z27,z6]),(0,[z0,z1,z959,z3,z4,z6]),(0,[z76,z0,z81,z29,z4,z6]),(0,[z73,z0,z1,z80,z97,z4])],[(0,[z0,z453,z1,z2,z10,z3])],[(0,[z53,z1,z720,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z960]),(0,[z100,z0,z1,z416,z3,z4]),(0,[z0,z1,z2,z10,z4,z736])],[(0,[z73,z0,z1,z2,z3,z301])],[(0,[z0,z1,z2,z3,z4,z961]),(0,[z0,z1,z2,z3,z27,z396]),(0,[z73,z0,z1,z2,z63,z4]),(0,[z0,z1,z962,z3,z4,z6]),(0,[z0,z1,z416,z3,z4,z25])],[(0,[z0,z1,z963,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z964]),(0,[z73,z0,z1,z965,z3,z4])],[(0,[z0,z1,z2,z3,z4,z966]),(0,[z0,z453,z1,z2,z341,z3])]],
   [[(0,[z0,z2,z3,z50,z729,z6]),(0,[z967,z0,z1,z2,z4,z6])],[(0,[z259,z1,z2,z19,z4,z6]),(0,[z87,z1,z2,z3,z21,z77]),(0,[z1,z2,z3,z27,z698,z6]),(0,[z0,z1,z2,z79,z717,z6])],[(0,[z73,z0,z1,z2,z3,z84]),(0,[z0,z1,z968,z3,z21,z6]),(0,[z0,z1,z2,z3,z969,z6])],[(0,[z0,z1,z2,z308,z27,z6]),(0,[z0,z99,z28,z3,z4,z6]),(0,[z0,z1,z2,z3,z970,z6]),(0,[z0,z1,z2,z3,z971,z4])],[(0,[z0,z1,z2,z3,z4,z972]),(0,[z0,z1,z2,z3,z4,z837]),(0,[z76,z0,z1,z29,z27,z6]),(0,[z0,z1,z2,z79,z593,z6]),(0,[z73,z0,z1,z2,z467,z4])],[(0,[z0,z1,z2,z3,z27,z216]),(0,[z73,z0,z1,z2,z4,z543]),(0,[z0,z1,z2,z3,z4,z973]),(0,[z0,z1,z264,z10,z3,z4])],[(0,[z73,z0,z1,z2,z55,z4]),(0,[z73,z833,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z160,z149])],[(0,[z0,z1,z974,z3,z4,z6]),(0,[z279,z0,z1,z2,z10,z4]),(0,[z0,z1,z2,z3,z4,z975])],[(0,[z156,z24,z2,z308,z4,z6]),(0,[z53,z1,z60,z294,z4,z6]),(0,[z0,z1,z2,z280,z21,z6]),(0,[z0,z1,z976,z3,z21,z6]),(0,[z771,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z977,z6])],[(0,[z0,z1,z2,z10,z3,z4]),(0,[z0,z1,z2,z978,z4,z6]),(0,[z73,z0,z1,z2,z4,z557])],[(0,[z156,z24,z2,z3,z4,z216]),(0,[z0,z1,z2,z979,z4,z6]),(0,[z73,z0,z1,z2,z3,z980])],[(0,[z0,z1,z2,z3,z4,z981]),(0,[z0,z1,z2,z982,z4,z6]),(0,[z0,z1,z2,z79,z10,z89])],[(0,[z261,z0,z2,z3,z21,z151]),(0,[z0,z1,z13,z74,z3,z4])],[(0,[z670,z1,z2,z3,z21,z6]),(0,[z541,z1,z2,z3,z21,z6]),(1,[z0,z739,z3,z4,z6]),(0,[z983,z1,z2,z3,z4,z6]),(0,[z0,z984,z2,z3,z4,z6]),(0,[z73,z93,z0,z43,z1,z2]),(0,[z0,z1,z2,z3,z985,z6])],[(0,[z0,z1,z2,z173,z263,z6]),(0,[z0,z95,z28,z3,z27,z6]),(0,[z986,z0,z1,z2,z3,z4]),(0,[z73,z600,z0,z1,z2,z4]),(0,[z0,z1,z2,z3,z987,z6]),(0,[z0,z1,z2,z3,z4,z454]),(0,[z0,z1,z988,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z989]),(0,[z0,z1,z2,z3,z867,z6]),(0,[z0,z1,z38,z3,z27,z6])]],
   [[(0,[z0,z1,z2,z3,z990,z6])],[(0,[z96,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z991,z6])],[(0,[z73,z0,z1,z2,z559,z4]),(0,[z217,z1,z2,z3,z21,z6]),(0,[z73,z0,z1,z2,z192,z4])],[(0,[z91,z1,z2,z3,z4,z57]),(0,[z0,z1,z2,z3,z980,z6]),(0,[z0,z1,z2,z992,z3,z4]),(0,[z0,z1,z2,z79,z408,z6])],[(0,[z0,z1,z2,z3,z511,z396])],[(0,[z102,z153,z2,z3,z84,z6]),(0,[z0,z290,z2,z3,z21,z6]),(0,[z0,z360,z2,z3,z4,z47])],[(0,[z0,z1,z2,z3,z4,z708]),(0,[z0,z1,z2,z3,z4,z993])],[(0,[z0,z1,z2,z3,z4,z994]),(0,[z0,z1,z80,z97,z27,z6]),(0,[z161,z1,z2,z10,z3,z4])],[(0,[z0,z1,z2,z294,z4,z47]),(0,[z0,z995,z2,z3,z4,z6]),(0,[z0,z1,z2,z338,z4,z6]),(0,[z0,z59,z2,z18,z4,z189]),(0,[z0,z1,z2,z3,z996,z6]),(0,[z0,z1,z2,z3,z148,z421])],[(0,[z0,z290,z2,z173,z4,z6]),(0,[z997,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z998])],[(0,[z102,z153,z2,z3,z21,z6]),(0,[z0,z390,z37,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z999]),(0,[z0,z1,z3,z4,z884,z14]),(0,[z953,z1,z2,z10,z3,z4])],[(0,[z0,z1,z2,z3,z21,z1000]),(0,[z0,z1,z2,z338,z4,z57]),(0,[z0,z1,z2,z3,z1001,z6])],[(0,[z0,z1,z2,z3,z4,z1002]),(0,[z0,z64,z2,z10,z3,z50]),(0,[z0,z179,z2,z10,z3,z4]),(0,[z219,z0,z1,z2,z3,z275])],[(0,[z0,z1,z2,z3,z4,z68]),(0,[z0,z398,z2,z3,z150,z6]),(0,[z0,z1,z1003,z3,z4,z6]),(0,[z0,z1,z2,z1004,z3,z6]),(0,[z73,z0,z1,z2,z534,z4]),(0,[z0,z1,z2,z1005,z4,z6])],[(0,[z0,z2,z3,z4,z151,z871])]],
   [[(0,[z0,z1,z2,z3,z4,z1006]),(0,[z26,z1,z2,z3,z27,z6]),(0,[z0,z1,z2,z3,z4,z1007])],[(0,[z0,z1,z2,z3,z1008,z6]),(0,[z0,z1,z2,z10,z280,z4]),(0,[z0,z1,z2,z3,z1009,z6])],[(0,[z779,z24,z2,z3,z4,z6]),(0,[z1,z2,z18,z19,z21,z6]),(0,[z0,z749,z2,z3,z27,z6]),(0,[z0,z1,z31,z3,z695,z6])],[(0,[z0,z1,z2,z3,z333,z68]),(0,[z0,z612,z28,z3,z4,z6]),(0,[z0,z1,z2,z3,z1010,z6]),(0,[z73,z0,z1,z2,z89,z4])],[(0,[z98,z0,z264,z111,z4,z6]),(0,[z0,z1,z2,z1011,z3,z6]),(0,[z129,z0,z1,z2,z3,z160])],[(0,[z0,z1,z2,z559,z27,z6]),(0,[z0,z1,z2,z244,z3,z281])],[(0,[z1,z2,z10,z3,z19,z21]),(0,[z663,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z4,z1012]),(0,[z73,z0,z1,z962,z3,z4])],[(0,[z0,z1,z2,z3,z1013,z6]),(0,[z73,z256,z0,z1,z2,z4])],[(0,[z0,z1,z2,z3,z1014,z6]),(0,[z1,z2,z3,z765,z4,z6])],[(0,[z0,z1,z2,z1015,z4,z6]),(0,[z0,z1,z2,z3,z4,z1016]),(0,[z0,z1,z2,z3,z4,z732])],[(0,[z156,z24,z2,z559,z4,z6]),(0,[z93,z161,z1,z2,z71,z6])],[(0,[z0,z290,z8,z3,z4,z6]),(0,[z0,z1,z2,z1017,z3,z21]),(0,[z0,z159,z2,z3,z27,z6]),(0,[z161,z64,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z1018,z6])],[(0,[z0,z1,z2,z3,z4,z1019]),(0,[z0,z1,z2,z3,z54,z6]),(0,[z73,z0,z1,z786,z3,z4])],[(0,[z0,z1,z2,z21,z6,z718])],[(0,[z0,z1020,z2,z3,z4,z6]),(0,[z0,z1,z31,z3,z203,z255])],[(0,[z0,z1,z2,z757,z3,z4]),(0,[z0,z1,z2,z3,z1021,z6]),(0,[z0,z1022,z2,z3,z21,z6])]],
   [[(0,[z73,z0,z1,z141,z2,z3]),(0,[z73,z0,z1,z2,z505,z4])],[(0,[z0,z1,z2,z1023,z4,z6]),(0,[z0,z1024,z2,z3,z4,z6]),(0,[z1,z2,z19,z177,z21,z6]),(0,[z0,z1,z2,z341,z3,z27]),(0,[z0,z238,z3,z111,z4,z6])],[(0,[z0,z1,z2,z79,z89,z232])],[(0,[z90,z0,z1,z3,z443,z4])],[(0,[z0,z1,z2,z308,z4,z216]),(0,[z1,z720,z60,z3,z4,z6]),(0,[z0,z1,z2,z765,z4,z6]),(0,[z346,z0,z1,z2,z3,z27]),(0,[z0,z1,z772,z3,z27,z6]),(0,[z73,z0,z1,z2,z164,z4]),(0,[z0,z1,z227,z3,z4,z25])],[(0,[z0,z1,z191,z3,z4,z68]),(0,[z0,z1,z2,z3,z4,z1025])],[(0,[z0,z1,z2,z3,z1026,z6]),(0,[z0,z1,z2,z3,z4,z1027]),(0,[z73,z226,z1,z2,z63,z4]),(0,[z0,z49,z239,z3,z4,z6]),(0,[z0,z1,z2,z3,z1028,z6]),(0,[z0,z1,z3,z4,z884,z6])],[],[(0,[z0,z290,z2,z294,z4,z6]),(0,[z73,z0,z1,z2,z19,z27]),(0,[z0,z1,z2,z3,z420,z149])],[(0,[z0,z2,z3,z21,z6,z733])],[],[(0,[z0,z1,z2,z3,z4,z1029]),(0,[z26,z73,z1,z2,z19,z4]),(0,[z0,z1030,z1,z2,z3,z6]),(0,[z73,z0,z1,z2,z177,z21]),(0,[z0,z1,z2,z3,z1031,z6]),(0,[z0,z1,z2,z1032,z3,z4]),(0,[z0,z1,z839,z3,z4,z6])],[(0,[z73,z1,z2,z19,z21,z6])],[(0,[z0,z1,z2,z1033,z3,z4]),(0,[z73,z0,z1034,z2,z3,z4])],[(0,[z0,z1,z2,z3,z1035,z6]),(0,[z102,z153,z2,z3,z276,z6])],[(0,[z0,z1,z2,z3,z1036,z6]),(0,[z0,z1,z2,z3,z4,z189])]],
   [[(0,[z96,z1,z2,z63,z21,z6]),(0,[z201,z1,z2,z63,z4,z6]),(0,[z0,z1,z2,z3,z1037,z6])],[],[(0,[z0,z95,z739,z3,z4,z6]),(0,[z0,z1,z2,z1038,z3,z4])],[(0,[z9,z1,z2,z19,z27,z6]),(0,[z76,z0,z1,z281,z29,z6]),(0,[z0,z1,z2,z10,z4,z124])],[(0,[z0,z1,z2,z3,z4,z1039]),(0,[z0,z1,z2,z3,z1040,z6])],[(0,[z0,z1,z2,z3,z27,z40]),(0,[z0,z1034,z2,z3,z4,z6])],[(0,[z73,z0,z1,z2,z70,z4]),(0,[z0,z1,z141,z28,z3,z6]),(0,[z0,z1,z2,z791,z4,z6]),(0,[z0,z11,z2,z3,z12,z358])],[(0,[z0,z1,z2,z3,z1041,z6]),(0,[z0,z1,z2,z1042,z3,z4]),(0,[z0,z1,z630,z82,z3,z4]),(0,[z0,z1,z2,z3,z1043,z6])],[(0,[z53,z360,z60,z3,z4,z6]),(0,[z256,z0,z1,z2,z4,z151])],[(0,[z0,z1,z2,z3,z4,z1044])],[(0,[z0,z1,z221,z3,z4,z6]),(0,[z0,z1,z843,z3,z4,z6]),(0,[z1,z2,z3,z1045,z4,z6]),(0,[z73,z0,z1,z2,z4,z205]),(0,[z0,z1,z2,z3,z148,z721])],[(0,[z0,z1,z2,z1046,z4,z6])],[(0,[z96,z1,z2,z63,z4,z206]),(0,[z0,z1047,z2,z3,z4,z6])],[(0,[z53,z1,z60,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z785]),(0,[z0,z1,z438,z3,z85,z6]),(0,[z93,z0,z1,z2,z275,z6])],[(0,[z0,z1,z2,z1048,z3,z4]),(0,[z0,z1,z2,z1049,z3,z4]),(0,[z435,z1,z2,z3,z4,z77]),(1,[z0,z1,z2,z3,z721])],[(0,[z0,z1,z221,z3,z333,z6]),(0,[z0,z935,z2,z3,z4,z6]),(0,[z0,z72,z536,z2,z3,z4]),(0,[z73,z0,z1,z2,z4,z33])]],
   [[(0,[z0,z1,z2,z1050,z4,z6]),(0,[z0,z1,z2,z3,z477,z206]),(0,[z0,z597,z28,z3,z4,z6]),(0,[z0,z1051,z1,z2,z3,z4]),(0,[z0,z1,z2,z10,z3,z847])],[],[(0,[z73,z0,z1,z221,z3,z4]),(0,[z0,z1,z2,z3,z725,z6])],[(0,[z0,z1,z2,z3,z1052,z6]),(0,[z73,z0,z1,z2,z614,z4]),(0,[z0,z453,z1,z359,z2,z3]),(0,[z0,z1053,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z255]),(0,[z0,z1,z2,z3,z4,z1054]),(0,[z73,z0,z1,z2,z3,z955])],[(0,[z256,z0,z1,z2,z4,z25])],[(0,[z0,z1,z1055,z3,z4,z6]),(0,[z87,z1,z2,z3,z347,z77]),(0,[z73,z0,z1,z2,z571,z4]),(0,[z0,z1,z2,z1056,z3,z6]),(0,[z0,z1,z2,z10,z3,z1057]),(0,[z336,z256,z0,z1,z2,z4])],[(0,[z0,z1,z2,z559,z4,z216]),(0,[z0,z1,z2,z173,z27,z6]),(0,[z9,z1,z2,z10,z19,z4]),(0,[z0,z1,z2,z3,z1058,z6]),(0,[z0,z1,z2,z3,z1059,z6]),(0,[z0,z1,z2,z117,z3,z16])],[(0,[z156,z24,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z4,z1060]),(0,[z98,z0,z2,z341,z111,z4]),(1,[z0,z2,z3,z729,z6]),(0,[z0,z542,z2,z3,z4,z151]),(0,[z0,z1,z2,z1061,z3,z4]),(0,[z0,z1,z13,z3,z4,z14])],[(0,[z0,z1,z1062,z2,z3,z6]),(0,[z0,z471,z37,z3,z4,z6]),(0,[z0,z1,z2,z3,z1063,z6])],[(0,[z0,z1,z2,z3,z4,z737])],[(0,[z0,z1,z2,z10,z3,z276])],[(0,[z0,z1,z2,z3,z1064,z6]),(0,[z0,z59,z2,z791,z4,z6]),(0,[z0,z1,z2,z3,z4,z1065])],[(0,[z0,z1,z2,z3,z27,z199]),(0,[z0,z1,z2,z280,z347,z6]),(0,[z0,z1,z31,z3,z203,z66]),(0,[z0,z43,z1,z3,z622,z6])],[(0,[z0,z1,z2,z3,z4,z47]),(0,[z0,z1,z2,z3,z27,z323]),(0,[z0,z1,z2,z3,z4,z1066]),(0,[z73,z0,z1,z2,z4,z92])],[(0,[z0,z1,z2,z3,z27,z206]),(0,[z73,z0,z1,z2,z3,z21]),(0,[z73,z0,z1,z2,z245,z4]),(0,[z0,z1,z2,z3,z4,z1067]),(0,[z93,z0,z44,z2,z3,z6])],[(0,[z0,z1,z1068,z3,z4,z6]),(0,[z0,z1,z2,z3,z1069,z6]),(0,[z0,z43,z1,z3,z907,z6])]],
   [[(0,[z156,z24,z2,z3,z193,z6]),(0,[z9,z1,z2,z19,z94,z6])],[(0,[z0,z1,z2,z3,z6,z1070]),(0,[z73,z0,z81,z2,z3,z4]),(0,[z0,z1,z31,z10,z3,z203]),(0,[z0,z1,z2,z3,z4,z736])],[(0,[z34,z1,z2,z3,z21,z6]),(0,[z0,z49,z37,z3,z27,z6]),(0,[z0,z398,z2,z3,z50,z6]),(0,[z73,z0,z1,z264,z3,z4]),(0,[z0,z1,z80,z710,z4,z6])],[(0,[z705,z1,z2,z3,z21,z6]),(0,[z73,z0,z1,z2,z491,z4]),(0,[z0,z1,z2,z3,z1071,z6]),(0,[z0,z1,z2,z3,z4,z1072]),(0,[z0,z1073,z2,z3,z4,z6])],[(0,[z0,z1,z2,z224,z55,z6]),(0,[z0,z1,z2,z717,z71,z6])],[(0,[z0,z1,z2,z10,z3,z333]),(0,[z0,z315,z28,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z86]),(0,[z0,z1,z2,z3,z661,z149])],[(0,[z73,z1,z2,z63,z19,z4]),(0,[z106,z0,z1,z3,z21,z25]),(0,[z0,z1,z2,z1074,z4,z6]),(0,[z0,z1,z2,z3,z4,z1075])],[(0,[z0,z1,z2,z3,z1076,z6]),(0,[z93,z0,z1,z2,z717,z6])],[(0,[z0,z1,z238,z3,z27,z6]),(0,[z0,z59,z2,z18,z4,z235])],[(0,[z45,z1,z2,z3,z27,z6]),(0,[z87,z1,z2,z3,z4,z77])],[(0,[z0,z478,z2,z18,z4,z6]),(0,[z0,z1,z2,z3,z21,z358]),(0,[z0,z1,z968,z3,z4,z6]),(0,[z0,z1077,z1,z2,z3,z4]),(0,[z0,z81,z80,z3,z4,z6])],[(0,[z0,z1,z2,z10,z3,z263]),(0,[z0,z1,z2,z3,z1078,z6]),(0,[z0,z44,z2,z3,z21,z6]),(0,[z0,z1,z2,z10,z3,z487]),(0,[z0,z1,z2,z3,z1079,z6])],[(0,[z0,z1080,z2,z3,z4,z6]),(0,[z73,z161,z1,z2,z3,z4])],[(0,[z0,z290,z60,z3,z4,z6]),(0,[z0,z360,z2,z3,z263,z6]),(0,[z256,z0,z1,z2,z27,z6]),(0,[z87,z1,z2,z3,z4,z737]),(0,[z0,z1,z2,z3,z4,z1081]),(0,[z873,z1,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z281]),(0,[z0,z1,z2,z1082,z3,z4])],[(0,[z0,z1,z2,z3,z1083,z6]),(0,[z73,z0,z940,z2,z3,z4])],[(0,[z0,z1,z359,z2,z63,z4]),(0,[z0,z1,z2,z10,z3,z347]),(0,[z73,z0,z1,z2,z3,z891])]],
   [[(0,[z0,z1,z221,z10,z3,z4]),(0,[z0,z1,z2,z294,z263,z6]),(0,[z0,z289,z2,z3,z4,z151])],[(0,[z75,z1,z2,z3,z21,z6]),(0,[z363,z1,z2,z3,z27,z6]),(0,[z256,z0,z1,z2,z4,z56]),(0,[z0,z1,z31,z377,z3,z6])],[(0,[z0,z1,z2,z3,z263,z6]),(0,[z0,z1,z2,z3,z4,z1084]),(0,[z0,z1,z141,z2,z10,z3]),(0,[z73,z0,z1085,z2,z3,z4])],[(0,[z53,z1,z60,z10,z3,z4]),(0,[z1,z604,z2,z3,z27,z6]),(0,[z518,z1,z2,z3,z27,z6]),(0,[z0,z1,z2,z3,z948,z6]),(0,[z0,z1,z2,z1086,z3,z4])],[(0,[z73,z0,z1,z191,z3,z4]),(0,[z0,z1,z2,z341,z3,z4])],[(0,[z0,z1,z2,z3,z1087,z6])],[(0,[z73,z0,z1,z2,z308,z4]),(0,[z96,z1,z2,z19,z21,z6]),(0,[z1,z2,z19,z21,z124,z6]),(0,[z96,z1,z2,z63,z4,z40])],[(0,[z346,z0,z1,z2,z3,z4]),(0,[z73,z0,z1,z2,z4,z186]),(0,[z256,z0,z1,z2,z10,z4])],[(0,[z137,z1,z60,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1088])],[(0,[z1089,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z826]),(0,[z0,z1,z2,z3,z1090,z6]),(0,[z110,z1,z2,z3,z21,z6])],[(0,[z0,z1,z2,z3,z1091,z6]),(0,[z0,z1,z2,z3,z477,z40])],[(0,[z73,z0,z1,z2,z3,z193]),(0,[z0,z1,z2,z3,z21,z396]),(0,[z73,z0,z1,z2,z19,z4])],[(0,[z0,z1,z2,z3,z1092,z6]),(0,[z0,z2,z3,z729,z4,z6])],[(0,[z0,z290,z2,z3,z4,z6])],[(0,[z0,z1,z2,z10,z3,z94]),(0,[z1,z2,z97,z19,z21,z6]),(0,[z161,z1,z2,z3,z71,z6]),(0,[z73,z0,z1,z2,z4,z163])],[(0,[z0,z1,z1093,z3,z4,z6]),(0,[z0,z1,z2,z173,z4,z396]),(0,[z73,z0,z95,z28,z3,z4]),(0,[z73,z336,z0,z1,z2,z4]),(0,[z0,z1,z2,z3,z4,z721])]],
   [[(0,[z0,z1,z2,z79,z177,z6]),(0,[z0,z1,z3,z907,z203,z6])],[(0,[z0,z1,z2,z308,z21,z6]),(0,[z0,z1,z2,z1094,z4,z6]),(0,[z0,z1,z2,z3,z1095,z6]),(0,[z73,z0,z1,z2,z3,z477]),(0,[z0,z1,z2,z224,z89,z6]),(0,[z0,z1,z2,z3,z4,z66])],[(0,[z102,z153,z2,z3,z4,z6]),(0,[z76,z0,z1,z29,z21,z6]),(0,[z0,z1,z2,z3,z4,z1096]),(0,[z0,z1,z2,z3,z4,z1097]),(0,[z0,z1,z2,z3,z4,z1098])],[(0,[z0,z1,z2,z3,z21,z216]),(0,[z1099,z0,z1,z2,z3,z4])],[(0,[z0,z1100,z1,z3,z4,z6]),(0,[z506,z153,z2,z3,z4,z6]),(0,[z0,z1,z2,z244,z3,z27]),(0,[z0,z1,z2,z3,z4,z1101]),(0,[z73,z0,z1,z2,z698,z4])],[(0,[z0,z1,z2,z3,z1102,z6]),(0,[z1,z2,z3,z19,z54,z6]),(0,[z91,z1,z2,z3,z4,z737]),(0,[z73,z93,z0,z1,z2,z71])],[(0,[z73,z93,z0,z1,z2,z27]),(0,[z0,z1,z2,z3,z4,z884])],[(0,[z0,z1,z2,z21,z6,z205])],[(0,[z73,z93,z0,z11,z1,z2]),(0,[z0,z1,z2,z3,z6,z1103])],[(0,[z646,z1,z2,z3,z27,z6])],[(0,[z0,z1,z2,z308,z193,z6]),(0,[z0,z1,z2,z1104,z4,z6]),(0,[z0,z1,z2,z338,z4,z77]),(0,[z0,z739,z28,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1105]),(0,[z0,z1,z2,z3,z21,z715])],[(0,[z0,z1,z2,z3,z193,z216]),(0,[z0,z95,z28,z3,z21,z6]),(0,[z0,z72,z2,z3,z27,z56]),(0,[z0,z1,z2,z4,z6,z736])],[(0,[z0,z1,z2,z1106,z4,z6]),(0,[z0,z1,z38,z3,z21,z6]),(0,[z0,z1,z2,z174,z3,z16])],[(0,[z73,z75,z1,z2,z63,z4]),(0,[z0,z794,z2,z3,z27,z6])],[(0,[z0,z1,z2,z3,z4,z1107]),(0,[z0,z1,z2,z3,z4,z235]),(0,[z0,z2,z791,z111,z4,z6])]],
   [[(0,[z0,z1,z2,z10,z294,z4]),(0,[z0,z43,z1,z3,z474,z6]),(0,[z76,z0,z1,z322,z29,z4])],[(0,[z0,z1,z2,z412,z3,z27]),(0,[z1108,z1,z2,z3,z4,z6]),(0,[z0,z900,z2,z3,z4,z6])],[],[(0,[z0,z1,z2,z3,z21,z1109]),(0,[z437,z73,z0,z1,z2,z27]),(0,[z73,z0,z1,z2,z3,z400])],[(0,[z0,z1110,z2,z3,z4,z6]),(0,[z613,z1,z2,z3,z27,z6]),(0,[z0,z1,z2,z27,z6,z205])],[(0,[z0,z1,z80,z97,z21,z6]),(0,[z0,z1,z1111,z2,z3,z4])],[(0,[z0,z1,z2,z355,z3,z27]),(0,[z0,z247,z1,z3,z32,z6]),(0,[z0,z2,z3,z4,z871,z6])],[(0,[z73,z226,z1,z2,z3,z21]),(0,[z0,z81,z2,z3,z27,z6]),(0,[z0,z1,z2,z3,z4,z1112])],[(0,[z0,z1,z2,z3,z21,z323]),(0,[z0,z1,z2,z3,z4,z1113]),(0,[z73,z0,z1,z848,z3,z4])],[(0,[z767,z0,z1,z2,z3,z4]),(0,[z0,z2,z3,z791,z4,z6])],[(0,[z73,z0,z1,z2,z3,z373]),(0,[z0,z1,z178,z3,z27,z6]),(0,[z0,z1,z2,z3,z148,z481]),(0,[z146,z0,z2,z3,z498,z4])],[(0,[z1,z8,z720,z3,z4,z6])],[(0,[z1114,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1115]),(0,[z0,z1116,z2,z3,z4,z6]),(0,[z0,z1,z97,z710,z4,z6])],[(0,[z0,z1,z2,z1117,z4,z6]),(0,[z0,z1,z2,z294,z4,z396]),(0,[z87,z1,z2,z338,z4,z77]),(0,[z0,z1,z2,z1118,z3,z6]),(0,[z73,z0,z1,z238,z3,z4])],[(0,[z0,z1,z2,z3,z21,z745]),(0,[z0,z1,z2,z10,z4,z459])]],
   [[(0,[z0,z1119,z1,z2,z3,z6]),(0,[z0,z1,z2,z1120,z4,z6])],[(0,[z1,z2,z3,z21,z645,z6]),(0,[z0,z1,z2,z3,z4,z232])],[(0,[z437,z0,z1,z2,z197,z6]),(0,[z0,z1,z2,z3,z4,z1121])],[(0,[z0,z1,z2,z559,z21,z6]),(0,[z0,z290,z2,z10,z3,z4])],[(0,[z73,z0,z1,z2,z652,z4]),(0,[z93,z0,z1,z2,z522,z6])],[(0,[z0,z756,z2,z3,z21,z6]),(1,[z73,z161,z1,z2,z4])],[(0,[z1,z2,z3,z21,z6,z655]),(0,[z0,z1,z2,z1122,z3,z4]),(0,[z0,z1,z2,z3,z1123,z6]),(0,[z0,z64,z2,z3,z631,z6])],[(0,[z1124,z1,z2,z3,z4,z6]),(0,[z73,z0,z44,z2,z3,z4]),(1,[z0,z1,z3,z4,z884]),(0,[z73,z93,z0,z1,z2,z275])],[(0,[z0,z1,z2,z3,z1125,z6]),(0,[z102,z153,z2,z10,z3,z4])],[(1,[z779,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z301,z6]),(0,[z0,z159,z2,z3,z21,z6]),(0,[z0,z1,z1126,z2,z3,z4]),(0,[z0,z1,z2,z1127,z4,z6])],[(0,[z0,z1,z2,z3,z1128,z6]),(0,[z0,z1,z359,z2,z19,z4]),(0,[z0,z1,z2,z3,z4,z1129]),(0,[z570,z1,z2,z3,z27,z6]),(0,[z0,z28,z3,z208,z4,z6]),(0,[z0,z72,z2,z3,z4,z871])],[(0,[z346,z1,z2,z3,z19,z21]),(0,[z73,z0,z1,z2,z338,z4]),(0,[z265,z1,z2,z3,z4,z57]),(0,[z161,z11,z1,z2,z3,z6])],[(0,[z0,z1,z2,z559,z193,z6]),(0,[z7,z1,z8,z3,z21,z6]),(0,[z0,z59,z2,z492,z4,z6]),(1,[z0,z1,z3,z907,z6])],[(0,[z73,z0,z1,z2,z3,z399])],[(0,[z0,z1,z2,z1130,z4,z6]),(0,[z0,z1,z2,z1131,z3,z4]),(0,[z0,z1,z2,z355,z280,z4]),(0,[z0,z1,z2,z3,z4,z1132])],[(0,[z0,z1,z2,z27,z6,z860]),(0,[z0,z1,z2,z10,z3,z233]),(0,[z87,z1,z2,z3,z300,z4]),(0,[z538,z0,z1,z2,z10,z4])]],
   [[(0,[z0,z1,z1133,z3,z4,z6]),(0,[z0,z1,z2,z173,z511,z6]),(0,[z0,z1,z2,z1134,z3,z4]),(0,[z73,z0,z1,z2,z27,z89]),(0,[z0,z1,z2,z3,z1135,z6]),(0,[z0,z1,z2,z3,z1136,z6])],[],[(0,[z0,z1137,z1,z2,z3,z6])],[(0,[z0,z1,z2,z1138,z3,z4]),(0,[z0,z1,z976,z3,z4,z6]),(0,[z0,z1,z2,z10,z3,z301]),(0,[z0,z1,z2,z280,z4,z6]),(0,[z465,z1,z2,z3,z21,z6]),(0,[z73,z0,z1,z2,z10,z21]),(0,[z554,z0,z1,z3,z4,z25]),(0,[z73,z0,z1,z2,z593,z4]),(0,[z0,z1,z2,z3,z4,z1139])],[(0,[z161,z1,z2,z4,z124,z6])],[(0,[z0,z360,z2,z3,z27,z6]),(0,[z155,z1,z2,z10,z3,z21]),(0,[z0,z1,z2,z3,z1140,z6])],[(0,[z73,z0,z1,z2,z234,z4]),(0,[z0,z11,z2,z3,z12,z199])],[(0,[z755,z0,z1,z2,z308,z4]),(0,[z0,z1,z2,z1141,z4,z6]),(0,[z261,z0,z2,z3,z4,z151]),(0,[z0,z1,z965,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z909]),(0,[z0,z1,z2,z294,z27,z6]),(0,[z1,z2,z3,z27,z725,z6]),(0,[z0,z242,z1,z3,z121,z6])],[(0,[z0,z1,z2,z10,z3,z84]),(0,[z432,z1,z2,z63,z4,z6]),(0,[z0,z1,z1142,z3,z4,z6])],[(0,[z0,z1,z2,z3,z27,z6])],[(0,[z0,z1,z2,z3,z1143,z6]),(0,[z0,z1,z2,z322,z3,z21]),(0,[z0,z1,z2,z10,z523,z4])],[(0,[z0,z1144,z1,z2,z3,z4])],[(0,[z0,z1,z2,z1145,z4,z6]),(0,[z345,z0,z2,z111,z4,z6]),(0,[z0,z1146,z2,z3,z4,z6])],[(0,[z53,z73,z1,z60,z3,z4]),(0,[z0,z1,z2,z3,z1147,z6])],[(0,[z156,z24,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1148])]],
   [[(0,[z0,z1,z2,z3,z1149,z6]),(0,[z73,z0,z161,z1,z2,z4])],[(0,[z0,z1,z2,z1150,z3,z4]),(0,[z9,z1,z2,z19,z21,z6]),(0,[z0,z170,z2,z3,z228,z6]),(0,[z0,z1,z1151,z2,z3,z6])],[(0,[z855,z0,z1,z2,z27,z6]),(0,[z1152,z0,z1,z2,z4,z6]),(0,[z0,z1,z359,z2,z3,z400]),(0,[z73,z0,z1,z2,z408,z4]),(0,[z0,z64,z2,z3,z729,z6])],[(0,[z0,z1,z2,z3,z1153,z6]),(0,[z0,z1,z2,z3,z21,z40]),(0,[z0,z1085,z2,z3,z4,z6]),(0,[z0,z1116,z2,z10,z3,z4])],[(0,[z156,z24,z2,z3,z333,z6]),(0,[z0,z1,z1154,z3,z4,z6])],[(0,[z0,z1,z2,z1155,z4,z6]),(0,[z0,z1,z2,z1156,z4,z6]),(0,[z0,z1,z2,z3,z1157,z6]),(0,[z0,z1,z2,z10,z4,z415]),(0,[z1158,z1,z2,z3,z4,z6])],[(0,[z73,z0,z1,z2,z229,z4]),(0,[z0,z11,z2,z10,z3,z12])],[(0,[z53,z1,z60,z3,z4,z47]),(0,[z0,z1,z2,z3,z4,z1000]),(0,[z0,z64,z38,z3,z50,z6]),(0,[z0,z1,z2,z244,z3,z4]),(0,[z73,z93,z0,z1,z31,z2])],[(0,[z0,z1,z221,z3,z4,z68]),(0,[z0,z1,z2,z3,z1159,z6])],[(0,[z0,z1,z2,z10,z559,z4]),(0,[z0,z1,z1160,z3,z4,z6]),(1,[z1,z720,z3,z4,z6]),(0,[z73,z282,z0,z1,z2,z21]),(0,[z73,z0,z1,z2,z697,z4]),(0,[z73,z93,z0,z1,z2,z4]),(0,[z0,z1,z2,z10,z3,z1041])],[(0,[z0,z1,z2,z1161,z4,z6]),(0,[z0,z1162,z2,z3,z4,z6]),(0,[z0,z1,z2,z322,z3,z281])],[(0,[z565,z0,z1,z29,z4,z6])],[(0,[z0,z360,z2,z3,z511,z6]),(0,[z0,z1,z2,z3,z1163,z6]),(0,[z0,z1073,z2,z10,z3,z4])],[],[(0,[z96,z1,z2,z63,z373,z6]),(0,[z0,z1,z2,z3,z27,z202]),(0,[z0,z1,z2,z3,z907,z6]),(0,[z106,z0,z1,z3,z4,z25])],[(0,[z0,z1,z2,z294,z511,z6]),(0,[z282,z1,z2,z19,z21,z6]),(0,[z73,z0,z1,z178,z3,z4]),(0,[z93,z0,z1,z38,z3,z6])]],
   [[(0,[z73,z0,z1,z2,z762,z4]),(0,[z0,z1,z359,z2,z3,z21]),(0,[z0,z11,z2,z3,z277,z6])],[(0,[z0,z1,z191,z3,z27,z6]),(0,[z0,z1,z1164,z3,z4,z6]),(0,[z0,z1,z2,z1165,z3,z4]),(0,[z0,z154,z28,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1166,z6]),(0,[z73,z7,z1,z8,z3,z4]),(0,[z0,z81,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z4,z358]),(0,[z0,z1,z2,z3,z1167,z6])],[(0,[z0,z1,z2,z1168,z4,z6]),(0,[z9,z346,z1,z2,z19,z4]),(0,[z1,z2,z209,z3,z27,z6]),(0,[z0,z44,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1169,z6]),(0,[z0,z1,z2,z173,z21,z6]),(0,[z0,z1,z739,z3,z4,z6]),(0,[z0,z1,z2,z412,z3,z4]),(0,[z0,z1,z2,z79,z89,z323]),(0,[z0,z1,z2,z3,z1057,z6])],[(0,[z0,z1,z178,z3,z21,z6]),(0,[z91,z226,z1,z2,z3,z4])],[(0,[z156,z24,z191,z3,z4,z6]),(0,[z0,z1,z1170,z3,z4,z6]),(0,[z437,z73,z0,z1,z2,z4]),(0,[z1,z2,z3,z725,z21,z6]),(0,[z0,z59,z2,z18,z27,z6]),(0,[z73,z0,z1,z2,z649,z4])],[(0,[z0,z1,z2,z3,z1171,z6]),(0,[z0,z1,z2,z3,z94,z6])],[(0,[z1,z2,z3,z540,z21,z6]),(0,[z155,z1,z2,z3,z21,z6]),(0,[z73,z0,z49,z37,z3,z4]),(0,[z0,z1,z2,z89,z899,z4])],[(0,[z0,z1,z2,z3,z1172,z6]),(0,[z0,z1,z2,z355,z3,z4])],[(0,[z0,z1022,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z21,z199]),(0,[z302,z0,z28,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1173,z6])],[(0,[z0,z1,z1174,z3,z4,z6]),(0,[z0,z1,z2,z3,z21,z206]),(0,[z0,z2,z3,z21,z934,z6]),(0,[z0,z1175,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z1176,z6]),(0,[z0,z1,z141,z2,z244,z3]),(0,[z0,z43,z44,z3,z32,z6])],[(0,[z0,z1,z2,z3,z1177,z6]),(0,[z1178,z0,z1,z2,z3,z4])],[(0,[z0,z360,z2,z3,z4,z396]),(0,[z0,z1,z2,z3,z281,z6]),(0,[z256,z0,z1,z2,z15,z4])],[]],
   [[(0,[z582,z1,z2,z19,z4,z6]),(0,[z0,z49,z37,z3,z21,z6])],[(0,[z314,z1,z2,z3,z27,z6]),(0,[z73,z0,z1,z2,z3,z811])],[(0,[z0,z1,z2,z10,z4,z240])],[(0,[z0,z1,z2,z849,z3,z4]),(0,[z0,z1,z2,z3,z4,z396]),(0,[z0,z1,z2,z3,z1179,z6]),(0,[z1180,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1181])],[(0,[z156,z24,z2,z10,z3,z4]),(0,[z161,z1,z31,z2,z3,z6])],[(0,[z0,z1,z238,z3,z21,z6]),(0,[z0,z1,z2,z15,z3,z275])],[(0,[z53,z290,z60,z3,z4,z6]),(0,[z45,z1,z2,z3,z21,z6]),(0,[z73,z0,z1,z2,z4,z637])],[(0,[z0,z1,z3,z1182,z4,z6]),(0,[z430,z1,z2,z3,z21,z6])],[],[(0,[z1183,z0,z1,z2,z3,z4]),(0,[z91,z1,z2,z3,z27,z57]),(0,[z76,z0,z1,z29,z4,z6]),(0,[z76,z0,z1,z10,z29,z4])],[(0,[z73,z0,z1,z2,z3,z511]),(0,[z0,z1,z2,z1184,z3,z4]),(0,[z0,z1,z2,z3,z1185,z6]),(0,[z96,z1,z2,z63,z4,z6]),(0,[z0,z248,z2,z3,z306,z6]),(0,[z256,z0,z1,z2,z21,z6]),(0,[z0,z1,z2,z3,z1186,z6]),(0,[z0,z1,z2,z3,z899,z4]),(0,[z1158,z1,z2,z10,z3,z4])],[(0,[z0,z1,z2,z3,z263,z47]),(0,[z0,z2,z739,z3,z4,z6]),(0,[z0,z1,z2,z1187,z4,z6]),(0,[z0,z519,z2,z575,z3,z4])],[(0,[z0,z1,z3,z4,z6,z927])],[(0,[z0,z1,z2,z1188,z4,z6]),(0,[z1,z2,z3,z373,z21,z6]),(0,[z1,z2,z3,z300,z21,z6])],[(0,[z0,z662,z28,z3,z4,z6]),(0,[z0,z1,z2,z3,z477,z6]),(0,[z1,z2,z3,z21,z197,z6]),(0,[z0,z1,z2,z338,z27,z6])]],
   [[(0,[z0,z1,z2,z3,z333,z216]),(0,[z0,z1,z2,z3,z1189,z6]),(0,[z0,z1,z2,z798,z3,z4]),(0,[z73,z9,z1,z2,z19,z4]),(0,[z0,z1,z2,z3,z4,z1190]),(0,[z0,z1,z1191,z3,z4,z6])],[(0,[z73,z1,z2,z3,z27,z21]),(0,[z1192,z1,z2,z3,z4,z6])],[(0,[z282,z0,z1,z2,z291,z6])],[(0,[z0,z1,z2,z174,z3,z364]),(0,[z93,z0,z1,z2,z197,z6]),(0,[z0,z1,z2,z3,z1193,z6])],[(0,[z0,z1,z2,z3,z1194,z6]),(0,[z0,z95,z28,z3,z4,z6])],[(0,[z1,z2,z19,z111,z21,z6]),(0,[z0,z1,z3,z4,z937,z6]),(0,[z0,z1,z1003,z3,z27,z6])],[(0,[z0,z313,z1,z3,z474,z6]),(0,[z0,z1,z1195,z3,z4,z6]),(0,[z0,z1,z2,z3,z1196,z6]),(0,[z106,z0,z1,z3,z4,z884])],[(0,[z0,z290,z2,z3,z4,z47]),(0,[z0,z1,z2,z3,z4,z1197])],[(0,[z0,z1,z2,z3,z365,z602]),(0,[z0,z1,z1198,z3,z4,z6]),(0,[z598,z1,z2,z3,z300,z4])],[(0,[z0,z1,z264,z3,z27,z6]),(0,[z104,z1,z2,z3,z27,z6]),(0,[z0,z1,z2,z338,z10,z4])],[(0,[z0,z1,z2,z3,z1199,z6]),(0,[z73,z0,z1,z1068,z3,z4])],[(0,[z0,z1,z2,z1200,z4,z6]),(0,[z0,z1,z2,z3,z4,z1109])],[(0,[z1,z2,z3,z4,z77,z737])],[(0,[z7,z1,z8,z3,z17,z6]),(0,[z0,z1,z609,z97,z4,z6]),(0,[z0,z1,z80,z97,z4,z6])],[(0,[z0,z453,z1,z2,z3,z6])],[(0,[z98,z0,z2,z111,z27,z6])]],
   [[(0,[z0,z1,z191,z308,z4,z6]),(0,[z0,z1201,z2,z3,z4,z6]),(0,[z73,z0,z1,z2,z504,z4]),(0,[z0,z1,z2,z1202,z3,z4])],[(0,[z0,z1,z2,z3,z1203,z6]),(0,[z0,z1,z2,z10,z4,z205])],[(0,[z0,z1,z191,z3,z4,z216]),(0,[z1,z779,z2,z3,z4,z6]),(0,[z0,z1,z2,z338,z487,z6]),(0,[z0,z1,z2,z89,z6,z218])],[],[(0,[z0,z1,z2,z3,z1204,z6]),(0,[z7,z1,z720,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z830])],[(0,[z96,z1,z2,z3,z54,z6]),(0,[z0,z64,z2,z3,z228,z6]),(0,[z0,z1,z2,z3,z149,z721])],[(0,[z0,z1,z2,z1205,z4,z6])],[],[(0,[z0,z1,z2,z3,z4,z1206])],[(0,[z0,z1,z2,z3,z1207,z6]),(0,[z73,z0,z1,z2,z63,z21]),(0,[z0,z1,z2,z3,z21,z869]),(0,[z0,z1,z1208,z3,z4,z6])],[(0,[z0,z72,z2,z3,z21,z56])],[(0,[z0,z1209,z2,z3,z4,z6]),(0,[z161,z1,z2,z3,z27,z6])],[(0,[z0,z1,z191,z3,z21,z6])],[(0,[z96,z1,z2,z765,z4,z6]),(0,[z0,z1,z710,z29,z4,z6])],[(0,[z0,z1,z2,z3,z1210,z6])],[(0,[z73,z0,z1,z2,z3,z27]),(0,[z0,z1,z2,z3,z21,z799]),(0,[z879,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z1211]),(0,[z1,z2,z63,z765,z4,z6]),(0,[z0,z1,z2,z3,z487,z6]),(0,[z0,z1,z2,z3,z1212,z6]),(0,[z93,z0,z1,z2,z71,z6]),(1,[z0,z1,z2,z717,z6])],[(0,[z0,z179,z2,z3,z27,z6]),(0,[z0,z1,z80,z97,z4,z202])],[(0,[z1183,z0,z1,z2,z173,z4]),(0,[z26,z73,z1,z2,z3,z27]),(0,[z1,z2,z3,z378,z27,z6]),(0,[z0,z242,z1,z3,z32,z6])],[(0,[z0,z1,z2,z3,z1213,z6]),(0,[z0,z1,z2,z355,z4,z124]),(0,[z226,z1,z2,z3,z21,z6])],[(0,[z73,z0,z1,z2,z167,z4]),(0,[z0,z1,z2,z3,z511,z6]),(0,[z7,z1,z8,z3,z4,z6]),(0,[z0,z1,z1214,z2,z3,z6]),(0,[z0,z11,z2,z3,z12,z6])],[(0,[z0,z1,z191,z3,z193,z6]),(0,[z73,z0,z705,z1,z2,z4]),(0,[z0,z1,z2,z10,z3,z21]),(0,[z0,z1,z2,z3,z27,z960]),(0,[z0,z1,z2,z3,z4,z1215]),(0,[z0,z1,z13,z3,z4,z884])],[(0,[z0,z153,z221,z3,z4,z6]),(0,[z1216,z0,z1,z2,z3,z4]),(0,[z299,z1,z8,z3,z4,z6])],[(0,[z76,z0,z1,z710,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1217]),(0,[z0,z1,z2,z3,z4,z1218]),(0,[z153,z779,z2,z3,z4,z6]),(0,[z0,z670,z28,z3,z4,z6]),(0,[z73,z0,z1,z38,z3,z4])],[(0,[z0,z1,z2,z1219,z3,z4]),(0,[z0,z1,z2,z3,z27,z966])],[(0,[z0,z1,z2,z3,z810,z6]),(0,[z0,z1,z2,z10,z27,z124]),(0,[z0,z95,z28,z10,z3,z4])],[(0,[z73,z93,z0,z64,z1,z2])],[(0,[z73,z96,z1,z2,z63,z4]),(0,[z144,z75,z1,z2,z3,z4]),(0,[z0,z1,z1195,z10,z3,z4])],[(0,[z0,z81,z3,z29,z4,z6])],[(0,[z0,z1,z2,z1220,z3,z4]),(0,[z0,z1,z500,z3,z246,z6]),(0,[z0,z1,z2,z3,z729,z6])],[(0,[z53,z1,z60,z3,z263,z6]),(0,[z0,z1,z2,z1017,z3,z4]),(0,[z0,z1,z2,z1221,z4,z6])]],
   [[(0,[z434,z1,z2,z3,z4,z77])],[(0,[z0,z1222,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z124,z232])],[(0,[z0,z1,z191,z559,z4,z6])],[(0,[z93,z45,z1,z2,z71,z6])],[(0,[z489,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z10,z3,z281]),(0,[z0,z1,z141,z2,z322,z3]),(0,[z0,z1,z2,z4,z124,z736])],[(0,[z0,z1,z2,z3,z1223,z6]),(0,[z0,z1,z2,z1224,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1225]),(0,[z73,z0,z360,z2,z3,z4]),(0,[z9,z1,z2,z355,z19,z4]),(0,[z73,z0,z1047,z2,z3,z4])],[],[(0,[z0,z1,z2,z3,z4,z1226]),(0,[z1,z2,z3,z55,z21,z6]),(0,[z0,z1,z2,z3,z27,z454])],[(0,[z9,z1,z2,z19,z4,z6]),(0,[z1,z2,z10,z3,z300,z21]),(0,[z0,z453,z2,z28,z3,z6]),(0,[z76,z0,z159,z29,z4,z6])],[(0,[z73,z0,z1,z2,z287,z4]),(0,[z0,z1,z2,z3,z4,z1227]),(0,[z770,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z1228]),(0,[z251,z0,z1,z74,z3,z4])],[(0,[z96,z1,z2,z3,z867,z6]),(0,[z161,z1,z2,z3,z55,z6])],[(0,[z0,z1,z2,z308,z4,z6]),(0,[z26,z1,z2,z3,z373,z6]),(0,[z217,z1,z2,z3,z725,z6]),(0,[z26,z1,z2,z10,z3,z27])],[(0,[z0,z1,z2,z10,z308,z4]),(0,[z0,z1229,z2,z3,z4,z6]),(0,[z256,z0,z1,z2,z15,z16])],[(0,[z0,z1,z2,z3,z4,z216]),(0,[z0,z1,z13,z3,z27,z14]),(0,[z0,z49,z739,z3,z4,z6])],[(0,[z73,z0,z1,z2,z3,z54]),(0,[z73,z0,z1,z2,z41,z4]),(0,[z73,z0,z1,z2,z177,z4]),(1,[z0,z2,z3,z4,z871])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 509) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 509).take 510) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1019).take 357) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1376)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [509, 510, 357] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 164).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 164).take 153).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 317).take 167).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 484).take 28).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [164, 153, 167, 28] = true :=
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

end PEqualNP.Outside.L_meta_40447

theorem PEqualNP.Outside.L_meta_40447 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4276145344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4276145344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_40447.solve