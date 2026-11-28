import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45632

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
  Nat.testBit (4008241376 * 2 ^ 32 + 4004046848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x81858bc301adc360#64 ++ 0x0c0c2c5e180d6e1b#64 ++ 0xa38f9fc723ffc7f7#64 ++ 0xbd1c7cfe391ffe3f#64 : BitVec 256),
   (0x0c32a5d84c62d8a0#64 ++ 0x8061952ec26316c5#64 ++ 0xdc73e7f8dc63f8fb#64 ++ 0xfee39f3fc6e31fc7#64 : BitVec 256),
   (0x6058506de0746d01#64 ++ 0x1302c2836f03a368#64 ++ 0x607c78ffe07c7f1d#64 ++ 0xdb03e3c7ff03e3f8#64 : BitVec 256),
   (0x76807e00b68036c8#64 ++ 0x23b403f005b401b6#64 ++ 0xff807f00ff807fff#64 ++ 0xeffc03f807fc03ff#64 : BitVec 256),
   (0x7b7f0000fb5b0004#64 ++ 0x43dbf80007dad800#64 ++ 0xffff8000ffff8001#64 ++ 0xf7fffc0007fffc00#64 : BitVec 256),
   (0x7fefffb600000002#64 ++ 0x7bff7ffdb0000000#64 ++ 0x7fffffff00000001#64 ++ 0x7bfffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [3, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [7, 12]⟩, ⟨.or, [11, 13]⟩, ⟨.and, [9, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0c32a5d84c62d8a0 0x8061952ec26316c5 0xdc73e7f8dc63f8fb 0xfee39f3fc6e31fc7

def z1 : W := mkw 0x6058506de0746d01 0x1302c2836f03a368 0x607c78ffe07c7f1d 0xdb03e3c7ff03e3f8

def z2 : W := mkw 0x76807e00b68036c8 0x23b403f005b401b6 0xbf801f003f8007e6 0x25fc00f801fc003f

def z3 : W := mkw 0x76807e00b68036c8 0x23b403f005b401b6 0xff807f00ff807fff 0xeffc03f807fc03ff

def z4 : W := mkw 0x7b7f0000fb5b0004 0x43dbf80007dad800 0xffff8000ffff8001 0xf7fffc0007fffc00

def z5 : W := mkw 0x7fefffb600000002 0x7bff7ffdb0000000 0x7fffffff00000001 0x7bfffffff8000000

def z6 : W := mkw 0x81858bc301adc360 0x0c0c2c5e180d6e1b 0xa38f9fc723ffc7f7 0xbd1c7cfe391ffe3f

def z7 : W := mkw 0x0832000048420000 0x0041900002421000 0xdc738000dc638001 0xf6e39c0006e31c00

def z8 : W := mkw 0x734d0000b3190004 0x439a68000598c800 0x238c0000239c0000 0x011c6000011ce000

def z9 : W := mkw 0x6048502400000000 0x1302428120000000 0x607c78ff00000001 0x5b03e3c7f8000000

def z10 : W := mkw 0x73cd5a2600000002 0x7b9e6ad130000000 0x238c180700000000 0x011c60c038000000

def z11 : W := mkw 0x7f7f7400ff5b348c 0x63fbfba007fad9a4 0xffffe000ffffb809 0xf7ffff0007fffdc0

def z12 : W := mkw 0x001081c84c62d8a0 0x8000840e426316c5 0x800387c0dc63f8fb 0xbc001c3e06e31fc7

def z13 : W := mkw 0x00800a00b68036c8 0x0004005005b401b6 0xa3801f00ff807fff 0xad1c00f807fc03ff

def z14 : W := mkw 0x0000000000000000 0x0000000000000000 0x407060f800000001 0x5a038307c0000000

def z15 : W := mkw 0xf7857e03b78d37c8 0x2fbc2bf01dbc69be 0xff8c7f07ff9c7fff 0xeffc63f83ffce3ff

def z16 : W := mkw 0x7fffffffe0746d03 0x7bffffffff03a368 0x7fffffffe07c7f1d 0xfbffffffff03e3f8

def z17 : W := mkw 0x7fefffb6b68036ca 0x7bff7ffdb5b401b6 0xffffffffff807fff 0xfffffffffffc03ff

def z18 : W := mkw 0x00100008e0502c01 0x0000800047028160 0x00000000c0003808 0x00000000060001c0

def z19 : W := mkw 0x1e22241000000002 0x60f1112080000000 0x1c00000000000000 0x00e0000000000000

def z20 : W := mkw 0x80100049e1fdef61 0x040080024f0fef7b 0x80000000e3fffffe 0x84000000071fffff

def z21 : W := mkw 0x0000000000000000 0x0000000000000000 0xa380000023800001 0xa51c0000011c0000

def z22 : W := mkw 0x615d506de17d6d01 0x130aea836f0beb68 0xe3fff8ffe3ffff1d 0xff1fffc7ff1ffff8

def z23 : W := mkw 0x083281c04862c020 0x0041940e02431601 0xdc7387c0dc63c0f3 0xfee39c3e06e31e07

def z24 : W := mkw 0x8c32a5d94defdbe0 0x8461952eca6f7edf 0xdc73e7f8ffffffff 0xfee39f3fc7ffffff

def z25 : W := mkw 0xe1cddbe7a1bde761 0x1f0e6edf3d0def3b 0xa38f9fc723ffc7f7 0xbd1c7cfe391ffe3f

def z26 : W := mkw 0x76807e00b68036c8 0x23b403f005b401b6 0xdf806700df8038ea 0x66fc033806fc01c7

def z27 : W := mkw 0x72000000b68036c8 0x0390000005b401b6 0xff800000ff807fff 0xe7fc000007fc03ff

def z28 : W := mkw 0x7eb2ffd8fee2fee8 0xa3f597fec7f717f7 0xfff3fff8ffe3ffff 0xffff9fffc7ff1fff

def z29 : W := mkw 0x00100049fb7f6d05 0x000080024fdbfb68 0x80000000ffffff1c 0x8400000007fffff8

def z30 : W := mkw 0x80808b8200808260 0x0c04045c10040413 0x00000700000000e2 0x0000003800000007

def z31 : W := mkw 0x00800a0000800240 0x0004005000040012 0x00001f00000047f6 0x080000f80000023f

def z32 : W := mkw 0x096f81b600000002 0x584b7c0db0000000 0x007f80ff00000000 0x1003fc07f8000000

def z33 : W := mkw 0x72100000fb5b0004 0x0390800007dad800 0xff800000ffff8001 0xe7fc000007fffc00

def z34 : W := mkw 0x0400240004001080 0x0020012000200084 0xdc006700dc0078fb 0xeee0033806e003c7

def z35 : W := mkw 0x00100049e0746d01 0x000080024f03a368 0x00000000e07c7f1c 0x800000000703e3f8

def z36 : W := mkw 0x7b7f5000fb5b2404 0x43dbfa8007dad920 0xfffff800ffffff1d 0xffffffc007fffff8

def z37 : W := mkw 0x0000502c00002c01 0x1000028160000160 0x0000603800003808 0x00000301c00001c0

def z38 : W := mkw 0x16802e00b68036c8 0x20b4017005b401b6 0x9f800700ff807ffe 0xa4fc003807fc03ff

def z39 : W := mkw 0x0822819000000000 0x0041140c80000000 0x007380f800000000 0x10039c07c0000000

def z40 : W := mkw 0x76c87e24b68036c8 0x33b643f125b401b6 0xfffc7fffff807fff 0xffffe3fffffc03ff

def z41 : W := mkw 0x7fffffb6ffdb36ce 0x7bfffffdb7fed9b6 0xffffffffffffffff 0xffffffffffffffff

def z42 : W := mkw 0x00800a0000800240 0x0004005000040012 0xa3801f00238047f7 0xad1c00f8011c023f

def z43 : W := mkw 0x810581c3012dc120 0x0c082c0e18096e09 0x000f80c7007f8000 0x10007c063803fc00

def z44 : W := mkw 0x9ba78b821b8b8264 0x4cdd3c5c10dc5c13 0x9f8387001f8380e2 0x24fc1c3800fc1c07

def z45 : W := mkw 0x0c32a5984c421880 0x8061952cc26210c4 0x5c73e7f8dc003809 0x7ae39f3fc6e001c0

def z46 : W := mkw 0x72000000b2000000 0x0390000005900000 0xff800000ff800001 0xe7fc000007fc0000

def z47 : W := mkw 0x097f0000495b0004 0x404bf800024ad800 0x007f8000007f8000 0x1003fc000003fc00

def z48 : W := mkw 0x76007400b6003488 0x23b003a005b001a4 0x5c006000dc003808 0x42e0030006e001c0

def z49 : W := mkw 0x7f6ff5b600000002 0x7bfb7fadb0000000 0x5c7fe0ff00000000 0x52e3ff07f8000000

def z50 : W := mkw 0x01858b8200000000 0x080c2c5c10000000 0x238f9fc700000001 0x391c7cfe38000000

def z51 : W := mkw 0x8000004101adc360 0x04000002080d6e1b 0x8000000023ffc7f6 0x84000000011ffe3f

def z52 : W := mkw 0x7fff7e00ffdb36cc 0x63fffbf007fed9b6 0xffffff00ffffffff 0xfffffff807ffffff

def z53 : W := mkw 0x81858b8201898260 0x0c0c2c5c100c4c13 0x83838700038380e2 0x241c1c38001c1c07

def z54 : W := mkw 0x0822000008020000 0x0041100000401000 0x9c0380001c038000 0x24e01c0000e01c00

def z55 : W := mkw 0x81858bc301adc360 0x0c0c2c5e180d6e1b 0x838f87c703ff80e2 0x341c7c3e381ffc07

def z56 : W := mkw 0x0c22a5900c0290a0 0x8061152c80601485 0x9c0387001c0380e2 0x24e01c3800e01c07

def z57 : W := mkw 0x8db7afdb4defdbe0 0x8c6dbd7eda6f7edf 0xffffffffffffffff 0xffffffffffffffff

def z58 : W := mkw 0x7ffffffefee2feea 0xfbfffffff7f717f7 0xffffffffffe3ffff 0xffffffffffff1fff

def z59 : W := mkw 0x7f6fa59000000000 0x43fb7d2c80000000 0x7fffe7f800000001 0x7bffff3fc0000000

def z60 : W := mkw 0x000081c00020c020 0x0000040e00010601 0x800387c00063c0f3 0xbc001c3e00031e07

def z61 : W := mkw 0x81850a03018d0340 0x0c0c2850180c681a 0x238c1807239c0704 0x011c60c0391ce038

def z62 : W := mkw 0x7b7f006dfb7f4905 0x53dbf8036fdbfa48 0xffff80ffffff8001 0xf7fffc07fffffc00

def z63 : W := mkw 0x60580000e0500000 0x0302c00007028000 0x607c0000e07c0001 0xd303e0000703e000

def z64 : W := mkw 0x7b7f506dfb7f6d05 0x53dbfa836fdbfb68 0xfffff8ffffffff1d 0xffffffc7fffffff8

def z65 : W := mkw 0x0105000001090000 0x0008280000084800 0x8383800003838000 0x241c1c00001c1c00

def z66 : W := mkw 0x60485024a0002400 0x1302428125000120 0x607c78ffe0007f1d 0xdb03e3c7ff0003f8

def z67 : W := mkw 0x9fa7af9201898262 0x6cfd3d7c900c4c13 0x9f838700038380e2 0x24fc1c38001c1c07

def z68 : W := mkw 0x7b7f000048420000 0x43dbf80002421000 0xffff8000dc638001 0xf7fffc0006e31c00

def z69 : W := mkw 0x7e6a743400000002 0x73f353a1a0000000 0x5c70603800000000 0x42e38301c0000000

def z70 : W := mkw 0x697f506de97f6d05 0x534bfa836f4bfb68 0x607ff8ffe07fff1d 0xdb03ffc7ff03fff8

def z71 : W := mkw 0x810581c301adc360 0x0c082c0e180d6e1b 0x800f80c723ffc7f6 0x94007c06391ffe3f

def z72 : W := mkw 0x7e7a7434fa520006 0x73f3d3a1a7d29000 0x5c706038dc000000 0x42e38301c6e00000

def z73 : W := mkw 0x81858b83018d0340 0x0c0c2c5c180c681a 0x238f9fc7239c0705 0x391c7cfe391ce038

def z74 : W := mkw 0x0c22a5d80c22d8a0 0x8061152ec06116c5 0x9c03e7f81c03f8fa 0x2ce01f3fc0e01fc7

def z75 : W := mkw 0x6000500000000000 0x0300028000000000 0x6000780000000001 0x4b0003c000000000

def z76 : W := mkw 0x7b7f5024fb5b0004 0x53dbfa8127dad800 0xfffff8ffffff8001 0xffffffc7fffffc00

def z77 : W := mkw 0x76807e00048036c8 0x23b403f0002401b6 0x7f807f0000007fff 0x6bfc03f8000003ff

def z78 : W := mkw 0x0010004840604800 0x0000800242030240 0x407060f8c0607819 0xda038307c60303c0

def z79 : W := mkw 0x00100049ec76fda1 0x800080024f63b7ed 0x80000000fc7ffffe 0x8400000007e3ffff

def z80 : W := mkw 0x0c22a59000000000 0x0061152c80000000 0x5c73e7f800000001 0x7ae39f3fc0000000

def z81 : W := mkw 0x001000484c62d8a0 0x80008002426316c5 0x80000000dc63f8fa 0x8400000006e31fc7

def z82 : W := mkw 0x7ffffffe4c62d8a2 0xfbfffffff26316c5 0xffffffffdc63f8fb 0xfffffffffee31fc7

def z83 : W := mkw 0x80000001018d0340 0x04000000080c681a 0x00000000239c0704 0x00000000011ce038

def z84 : W := mkw 0x16802e00168012c8 0x20b4017000b40096 0x9f8007001f8000e2 0x24fc003800fc0007

def z85 : W := mkw 0x76807e00a0002400 0x23b403f005000120 0x7f807f00e0007f1d 0xebfc03f8070003f8

def z86 : W := mkw 0x0480ffb600000002 0x382407fdb0000000 0x00007fff00000000 0x080003fff8000000

def z87 : W := mkw 0x7b6f000000000000 0x43db780000000000 0x7fff800000000001 0x73fffc0000000000

def z88 : W := mkw 0x7fffffb6fb5b0006 0x7bfffffdb7dad800 0xffffffffffff8001 0xfffffffffffffc00

def z89 : W := mkw 0x60580049e0746d01 0x0302c0024f03a368 0x607c0000e07c7f1d 0xd303e0000703e3f8

def z90 : W := mkw 0x0400a590040090a0 0x8020052c80200485 0x00000700000000e2 0x0000003800000007

def z91 : W := mkw 0x60005000a0002400 0x0300028005000120 0x60007800e0007f1d 0xcb0003c0070003f8

def z92 : W := mkw 0x0000000000000000 0x0000000000000000 0x200c18c700000001 0x190060c638000000

def z93 : W := mkw 0x6048502400000000 0x1302428120000000 0x4070603800000000 0x42038301c0000000

def z94 : W := mkw 0x60d85a6de0f46f41 0x1306c2d36f07a37a 0xe3fc7fffe3fc7fff 0xff1fe3ffff1fe3ff

def z95 : W := mkw 0x60580041e0744100 0x0302c0020f03a208 0x607c18c7e07c4715 0xdb03e0c63f03e238

def z96 : W := mkw 0x0000000000000000 0x0000000000000000 0x8003800000638001 0xb4001c0000031c00

def z97 : W := mkw 0x7b7f0048ff7bd8a4 0xc3dbf80247fbdec5 0xffff8000fffff8fb 0xf7fffc0007ffffc7

def z98 : W := mkw 0x76d87e6df6f47fc9 0x33b6c3f36fb7a3fe 0xfffc7ffffffc7fff 0xffffe3ffffffe3ff

def z99 : W := mkw 0x76907e49f6f47fc9 0x23b483f24fb7a3fe 0xff807f00fffc7fff 0xeffc03f807ffe3ff

def z100 : W := mkw 0x89ff8bc349ffc364 0x4c4ffc5e1a4ffe1b 0xa3ff9fc723ffc7f7 0xbd1ffcfe391ffe3f

def z101 : W := mkw 0x7bef8b8200000000 0x4bdf7c5c10000000 0x7fff9fc700000001 0x7bfffcfe38000000

def z102 : W := mkw 0xe0d8dbefe0f4ef61 0x1f06c6df7f07a77b 0x607c7fffe07c7fff 0xdb03e3ffff03e3ff

def z103 : W := mkw 0x735d0000f3590004 0x439ae800079ac800 0x63fc0000e3fc0001 0xd31fe000071fe000

def z104 : W := mkw 0x7fefffb6a0002402 0x7bff7ffdb5000120 0x7fffffffe0007f1d 0xfbffffffff0003f8

def z105 : W := mkw 0x00000000b68036c8 0x0000000005b401b6 0x80000000ff807ffe 0x8400000007fc03ff

def z106 : W := mkw 0x0400740004003488 0x202003a0002001a4 0x0000600000003808 0x00000300000001c0

def z107 : W := mkw 0xf6807e41b7adf7e8 0x27b403f20dbd6fbf 0xff807f00ffffffff 0xeffc03f807ffffff

def z108 : W := mkw 0x7ea2ff9000000000 0x23f517fc80000000 0x7ff3fff800000001 0x7bff9fffc0000000

def z109 : W := mkw 0x81958bc3fbffc364 0x0c0cac5e1fdffe1b 0xa38f9fc7ffffc7f7 0xbd1c7cfe3ffffe3f

def z110 : W := mkw 0x0400743400000002 0x302003a1a0000000 0x0000603800000000 0x00000301c0000000

def z111 : W := mkw 0xfb7f0041fbffc364 0x47dbf8020fdffe1b 0xffff8000ffffc7f7 0xf7fffc0007fffe3f

def z112 : W := mkw 0x60485025a0142501 0x130242812d00a128 0x200c1807201c0704 0x010060c03900e038

def z113 : W := mkw 0x00100048fee2fee8 0x8000800247f717f7 0x80000000ffe3fffe 0x8400000007ff1fff

def z114 : W := mkw 0x77cdffb600000002 0x7bbe6ffdb0000000 0x238c7fff00000000 0x091c63fff8000000

def z115 : W := mkw 0x0105000001090000 0x0008280000084800 0x238c0000239c0000 0x011c6000011ce000

def z116 : W := mkw 0x6058d1ede074ed21 0x1302c68f6f03a769 0xe07fffffe07fffff 0xff03ffffff03ffff

def z117 : W := mkw 0x0c3224184c421880 0x80619120c26210c4 0x5c706038dc003808 0x42e38301c6e001c0

def z118 : W := mkw 0x64d87e6de4f47fc9 0x3326c3f36f27a3fe 0x607c7fffe07c7fff 0xdb03e3ffff03e3ff

def z119 : W := mkw 0x6000506da0246d01 0x130002836d012368 0x600078ffe0007f1d 0xcb0003c7ff0003f8

def z120 : W := mkw 0xfbff8bc3fbffc364 0x4fdffc5e1fdffe1b 0xffff9fc7ffffc7f7 0xfffffcfe3ffffe3f

def z121 : W := mkw 0x0000004100244100 0x0000000208012208 0x200c18c7207c4715 0x990060c63903e238

def z122 : W := mkw 0x0c32a5d94c66d9a0 0x8061952eca6336cd 0xfc7ffffffc7fffff 0xffe3ffffffe3ffff

def z123 : W := mkw 0x0cb2fffe4c62d8a2 0xb86597fff26316c5 0xdc73ffffdc63f8fb 0xfee39ffffee31fc7

def z124 : W := mkw 0x0010004840604800 0x0000800242030240 0x00000000c0607818 0x80000000060303c0

def z125 : W := mkw 0x0000006d00244901 0x1000000368012248 0x000000ff00000000 0x00000007f8000000

def z126 : W := mkw 0x1b2700001b0b0004 0x40d9380000d85800 0xbf8f80003fff8001 0xb5fc7c0001fffc00

def z127 : W := mkw 0x7fefffb6048036ca 0x7bff7ffdb02401b6 0x7fffffff00007fff 0x7bfffffff80003ff

def z128 : W := mkw 0x0058002c40500801 0x1002c00162028040 0x0070003800000000 0x00038001c0000000

def z129 : W := mkw 0xf785ffc301adc360 0x2fbc2ffe180d6e1b 0xff8fffc723ffc7f7 0xfffc7ffe391ffe3f

def z130 : W := mkw 0x0105000001090000 0x0008280000084800 0xa38f800023ff8001 0xb51c7c00011ffc00

def z131 : W := mkw 0x7fefffb601090002 0x7bff7ffdb0084800 0xffffffff23ff8001 0xfffffffff91ffc00

def z132 : W := mkw 0x89b78bdb49efcb60 0x8c4dbc5eda4f7e5b 0xa3ff9fff23ffc7f7 0xbd1ffcfff91ffe3f

def z133 : W := mkw 0x7ffffffff6f47fcb 0x7bffffffffb7a3fe 0xfffffffffffc7fff 0xffffffffffffe3ff

def z134 : W := mkw 0x7fef7e00b68036c8 0x63ff7bf005b401b6 0xffffff00ff807fff 0xfffffff807fc03ff

def z135 : W := mkw 0x76007400b68036c8 0x23b003a005b401b6 0xdc006000ff807ffe 0xc6e0030007fc03ff

def z136 : W := mkw 0x1fa7af9200000002 0x68fd3d7c90000000 0x5ff3e7f800000001 0x7aff9f3fc0000000

def z137 : W := mkw 0x000081c00020c020 0x0000040e00010601 0x000380c000638000 0x10001c0600031c00

def z138 : W := mkw 0x7e32a5d8fe62d8a0 0x83f1952ec7f316c5 0xfff3e7f8ffe3f8fb 0xffff9f3fc7ff1fc7

def z139 : W := mkw 0x0000000100040100 0x0000000008002008 0x200c1807201c0704 0x010060c03900e038

def z140 : W := mkw 0x0000000000000000 0x0000000000000000 0x200c0000207c0001 0x910060000103e000

def z141 : W := mkw 0x0400a5d80420d8a0 0x8020052ec02106c5 0x000067f8000078fa 0x0800033fc00003c7

def z142 : W := mkw 0x7eb27e00fec236c8 0x23f593f007f611b6 0xfff3ff00ffe3ffff 0xffff9ff807ff1fff

def z143 : W := mkw 0x0400a59000000000 0x0020052c80000000 0x000067f800000000 0x0800033fc0000000

def z144 : W := mkw 0xe058506de1fdef61 0x1702c2836f0fef7b 0xe07c78ffe3ffffff 0xdf03e3c7ff1fffff

def z145 : W := mkw 0x76807e00b68036c8 0x23b403f005b401b6 0x23807f0023807ffe 0x091c03f8011c03ff

def z146 : W := mkw 0x7fef7e3600000002 0x7bff7bf1b0000000 0x7ffc783f00000000 0x43ffe3c1f8000000

def z147 : W := mkw 0x7eb27e18fec23ec8 0xa3f593f0c7f611f6 0xfff07f38ff807fff 0xefff83f9c7fc03ff

def z148 : W := mkw 0x6058506dfb7f6d05 0x1302c2836fdbfb68 0xe07c78ffffffff1d 0xdf03e3c7fffffff8

def z149 : W := mkw 0x04807e00048036c8 0x202403f0002401b6 0x00007f0000007ffe 0x080003f8000003ff

def z150 : W := mkw 0x80808bc300a4c360 0x0c04045e1805261b 0x00001fc7000047f6 0x080000fe3800023f

def z151 : W := mkw 0x096f000000000000 0x404b780000000000 0x007f800000000000 0x1003fc0000000000

def z152 : W := mkw 0x0c3224584c62d8a0 0x80619122c26316c5 0xdc706038dc63f8fa 0xc6e38301c6e31fc7

def z153 : W := mkw 0x735d506df37d6d05 0x539aea836f9beb68 0x63fc78ffe3fc7f1d 0xdb1fe3c7ff1fe3f8

def z154 : W := mkw 0x0c32a5984c4298a0 0x8061952cc26214c5 0xdc73e738dc03b8ea 0x66e39f39c6e01dc7

def z155 : W := mkw 0x0058506d40746d01 0x1002c2836a03a368 0x007c78ff007c7f1c 0x1803e3c7f803e3f8

def z156 : W := mkw 0x697fd1ffe0746d03 0x5b4bfe8fff03a368 0x607ff8ffe07c7f1d 0xdb03ffc7ff03e3f8

def z157 : W := mkw 0x087a81fd4876c921 0x9043d40fea43b649 0x007f80ff007f8000 0x1003fc07f803fc00

def z158 : W := mkw 0x7a7a0000fa520004 0x43d3d00007d29000 0xdc738000dc638001 0xf6e39c0006e31c00

def z159 : W := mkw 0x7efafffdfef6ffe9 0xb3f7d7ffeff7b7ff 0xffffffffffffffff 0xffffffffffffffff

def z160 : W := mkw 0x0048002500140101 0x100240012800a008 0x000c0007001c0000 0x000060003800e000

def z161 : W := mkw 0x6058506de0746d01 0x1302c2836f03a368 0x200c1807e07c7f1c 0x810060c03f03e3f8

def z162 : W := mkw 0x72000000b2000000 0x0390000005900000 0x5c000000dc000000 0x42e0000006e00000

def z163 : W := mkw 0x0105000001090000 0x0008280000084800 0x000f8000007f8000 0x10007c000003fc00

def z164 : W := mkw 0x0c22a59004001080 0x0061152c80200084 0xdc73e7f8dc0078fb 0xfee39f3fc6e003c7

def z165 : W := mkw 0x7fefffb6b280264a 0x7bff7ffdb5940132 0x7fffffff23800705 0x7bfffffff91c0038

def z166 : W := mkw 0x000081c00020c020 0x0000040e00010601 0x000007c0000040f2 0x0800003e00000207

def z167 : W := mkw 0x0927819200000002 0x48493c0c90000000 0x0003800000000000 0x00001c0000000000

def z168 : W := mkw 0x0000506d00246d01 0x1000028368012368 0x000078ff00007f1c 0x080003c7f80003f8

def z169 : W := mkw 0x000000000c0290a0 0x8000000000601485 0x800000001c0380e2 0x0400000000e01c07

def z170 : W := mkw 0x0010506d40646d01 0x100082836a032368 0x407078ffc0607f1d 0xda0383c7fe0303f8

def z171 : W := mkw 0x81850a4301adc360 0x0c0c2852180d6e1b 0xa38c180723ffc7f6 0x851c60c0391ffe3f

def z172 : W := mkw 0xe1dddbefe1fdef61 0x1f0eeedf7f0fef7b 0xe3ffffffe3ffffff 0xff1fffffff1fffff

def z173 : W := mkw 0x7fefffb600800242 0x7bff7ffdb0040012 0xffffffff238047f7 0xfffffffff91c023f

def z174 : W := mkw 0xffeffff701adc362 0x7fff7fffb80d6e1b 0xffffffff23ffc7f7 0xfffffffff91ffe3f

def z175 : W := mkw 0x6c7af5fdec76fda1 0x9363d7afef63b7ed 0xfc7ffffffc7fffff 0xffe3ffffffe3ffff

def z176 : W := mkw 0x7f7fa590ff5b90a4 0xc3fbfd2c87fadc85 0xffff8700ffff80e3 0xf7fffc3807fffc07

def z177 : W := mkw 0x8da7af920d8b92e0 0x8c6d3d7c906c5c97 0x9f8387001f8380e2 0x24fc1c3800fc1c07

def z178 : W := mkw 0x76007400b6003488 0x23b003a005b001a4 0xdc006700dc0078fb 0xeee0033806e003c7

def z179 : W := mkw 0x00000001a0142501 0x000000000d00a128 0x00000000201c0704 0x000000000100e038

def z180 : W := mkw 0x0010004940744901 0x000080024a03a248 0x00000000007c0000 0x000000000003e000

def z181 : W := mkw 0x7b7f0048fb7b4804 0x43dbf80247dbda40 0xffffe0f8fffff819 0xffffff07c7ffffc0

def z182 : W := mkw 0x60580048e0704800 0x0302c00247038240 0x607c60f8e07c7819 0xdb03e307c703e3c0

def z183 : W := mkw 0x60485065a0346501 0x130242832d01a328 0x200c18c7207c4715 0x990060c63903e238

def z184 : W := mkw 0x7e6af5b400000002 0x73f357ada0000000 0x5c73e7f800000001 0x7ae39f3fc0000000

def z185 : W := mkw 0x00000000a0002400 0x0000000005000120 0x00000000e0007f1c 0x80000000070003f8

def z186 : W := mkw 0x7a7a0000fa520004 0x43d3d00007d29000 0x5c700000dc000000 0x42e3800006e00000

def z187 : W := mkw 0xe1dd5a6fe1fd6f41 0x1f0eead37f0feb7a 0x63fc78ffe3fc7f1d 0xdb1fe3c7ff1fe3f8

def z188 : W := mkw 0x0c32a5d84c62d8a0 0x8061952ec26316c5 0x9c7387f81c6380e2 0x34e39c3fc0e31c07

def z189 : W := mkw 0x1b7f00005b5b0004 0x40dbf80002dad800 0x9fff80001fff8000 0x34fffc0000fffc00

def z190 : W := mkw 0x6c7af5fc4c62d8a0 0x9363d7afe26316c5 0xfc7fffffdc63f8fb 0xffe3fffffee31fc7

def z191 : W := mkw 0x00808b8200000000 0x0804045c10000000 0x00001fc700000000 0x080000fe38000000

def z192 : W := mkw 0x0400240004001080 0x0020012000200084 0x9c0007001c0000e2 0x24e0003800e00007

def z193 : W := mkw 0x7fefffb6b3190006 0x7bff7ffdb598c800 0x7fffffff239c0001 0x7bfffffff91ce000

def z194 : W := mkw 0x7fefffb600000002 0x7bff7ffdb0000000 0x5ff3e73800000000 0x62ff9f39c0000000

def z195 : W := mkw 0xf785ffc3b7adf7e8 0x2fbc2ffe1dbd6fbf 0xff8fffc7ffffffff 0xfffc7ffe3fffffff

def z196 : W := mkw 0x7fefffb60c0290a2 0xfbff7ffdb0601485 0xffffffff1c0380e3 0x7ffffffff8e01c07

def z197 : W := mkw 0x1b2700001b0b0004 0x40d9380000d85800 0x9f8380001f838000 0x24fc1c0000fc1c00

def z198 : W := mkw 0xf3855a03b38d2748 0x2f9c2ad01d9c693a 0x238c1807239c0704 0x011c60c0391ce038

def z199 : W := mkw 0x8480ffc304a4f7e8 0x2c2407fe182527bf 0x00007fc700007ffe 0x080003fe380003ff

def z200 : W := mkw 0x76807e00b2000000 0x23b403f005900000 0xff807f00ff800001 0xeffc03f807fc0000

def z201 : W := mkw 0x0d7fa5fe4c62d8a2 0xd86bfd2ff26316c5 0xdc7fe7ffdc63f8fb 0xfee3ff3ffee31fc7

def z202 : W := mkw 0x1fa7ffb600000002 0x78fd3ffdb0000000 0x1f83ffff00000000 0x28fc1ffff8000000

def z203 : W := mkw 0x81858bc301adc360 0x0c0c2c5e180d6e1b 0x83839fc70383c7f6 0x2c1c1cfe381c1e3f

def z204 : W := mkw 0x60005000b68036c8 0x0300028005b401b6 0xe0007800ff807fff 0xcf0003c007fc03ff

def z205 : W := mkw 0x6058502ce0502c01 0x1302c28167028160 0x40706038c0003808 0x42038301c60001c0

def z206 : W := mkw 0x0480ffb6048036ca 0x382407fdb02401b6 0x00007fff00007ffe 0x080003fff80003ff

def z207 : W := mkw 0x80000041012dc120 0x0400000208096e09 0x00000000007f8000 0x000000000003fc00

def z208 : W := mkw 0x0db7afda4c62d8a0 0x886dbd7ed26316c5 0xffffffffdc63f8fb 0xfffffffffee31fc7

def z209 : W := mkw 0x12800a0012800248 0x2094005000940012 0x0380000003800000 0x001c0000001c0000

def z210 : W := mkw 0x7e7a743c4c421882 0xf3f3d3a1e26210c4 0x5c706038dc003808 0x42e38301c6e001c0

def z211 : W := mkw 0x083281d84862c820 0x8041940ec2431641 0xdc7380f8dc638001 0xf6e39c07c6e31c00

def z212 : W := mkw 0x0000000000000000 0x0000000000000000 0xdc000000dc000001 0xe6e0000006e00000

def z213 : W := mkw 0xf385dbc3b3ade768 0x2f9c2ede1d9d6f3b 0xa38f9fc723ffc7f7 0xbd1c7cfe391ffe3f

def z214 : W := mkw 0x73050000b3090000 0x0398280005984800 0xff8f8000ffff8001 0xf7fc7c0007fffc00

def z215 : W := mkw 0x7a7a0000fa520004 0x43d3d00007d29000 0xfff00000ff800001 0xe7ff800007fc0000

def z216 : W := mkw 0x7f6f743400000002 0x73fb7ba1a0000000 0x7fffe03800000001 0x73ffff01c0000000

def z217 : W := mkw 0x7248502400000002 0x7392428120000000 0x0000000000000000 0x0000000000000000

def z218 : W := mkw 0x00100049f6f47fc9 0x000080024fb7a3fe 0x80000000fffc7ffe 0x8400000007ffe3ff

def z219 : W := mkw 0x7fffffb6e0500002 0x7bfffffdb7028000 0x7fffffffe07c0001 0xfbffffffff03e000

def z220 : W := mkw 0x72805a00b2802648 0x239402d005940132 0x2380180023800704 0x011c00c0011c0038

def z221 : W := mkw 0x734d000000000000 0x439a680000000000 0x238c000000000000 0x011c600000000000

def z222 : W := mkw 0x00100000fb5b0004 0x0000800007dad800 0x80000000ffff8000 0x8400000007fffc00

def z223 : W := mkw 0x04802e00048012c0 0x0024017000240096 0xff807f00ff807fff 0xeffc03f807fc03ff

def z224 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z225 : W := mkw 0xf3cd0a03b39d0344 0x4f9e68501d9ce81a 0x238c1807239c0704 0x011c60c0391ce038

def z226 : W := mkw 0x0058006d40744901 0x1002c0036a03a248 0x007c00ff007c0000 0x1003e007f803e000

def z227 : W := mkw 0x73cd5a26b280264a 0x7b9e6ad135940132 0x238c180723800704 0x011c60c0391c0038

def z228 : W := mkw 0x0585ffb600000002 0x382c2ffdb0000000 0x238fffff00000001 0x391c7ffff8000000

def z229 : W := mkw 0x81858b8201898260 0x0c0c2c5c100c4c13 0xa38f870023ff80e3 0xb51c7c38011ffc07

def z230 : W := mkw 0x00100000495b0004 0x00008000024ad800 0x00000000007f8000 0x000000000003fc00

def z231 : W := mkw 0x09270000090b0004 0x4049380000485800 0x0003800000038000 0x00001c0000001c00

def z232 : W := mkw 0x0cb2ffd84ce2fee8 0xa06597fec26717f7 0xdc73fff8dc63ffff 0xfee39fffc6e31fff

def z233 : W := mkw 0x0cb2afd84ce2dae0 0x8065957ec26716d7 0xfff3fff8ffe3ffff 0xffff9fffc7ff1fff

def z234 : W := mkw 0x083281d84862c820 0x8041940ec2431641 0x007380f800638000 0x10039c07c0031c00

def z235 : W := mkw 0x7fa77e00bf8b36cc 0x63fd3bf005fc59b6 0xff83ff00ff83ffff 0xeffc1ff807fc1fff

def z236 : W := mkw 0x8da7afd30dafd3e0 0x8c6d3d7e986d7e9f 0xbf8f9fc73fffc7f7 0xbdfc7cfe39fffe3f

def z237 : W := mkw 0x6058506c40604800 0x1302c28362030240 0x607c78ffc0607819 0xdb03e3c7fe0303c0

def z238 : W := mkw 0xfbff0a03fbdf0344 0x4fdff8501fdef81a 0xffff9807ffff8705 0xf7fffcc03ffffc38

def z239 : W := mkw 0x60005000a0002400 0x0300028005000120 0x40006000c0003808 0x42000300060001c0

def z240 : W := mkw 0x6048506500244100 0x1302428328012208 0x607c78ff207c4715 0xdb03e3c7f903e238

def z241 : W := mkw 0x687a0000e8520000 0x0343d00007429000 0xfc7f8000fc7f8001 0xf7e3fc0007e3fc00

def z242 : W := mkw 0x0000500000002400 0x0000028000000120 0x0000780000007f1c 0x080003c0000003f8

def z243 : W := mkw 0x1fa7af9200000002 0x68fd3d7c90000000 0x1f83870000000000 0x20fc1c3800000000

def z244 : W := mkw 0x8585afdb05addbe0 0x8c2c2d7ed82d6edf 0xa38fffff23ffffff 0xbd1c7ffff91fffff

def z245 : W := mkw 0x1fa7af920c0290a2 0xe8fd3d7c90601485 0x9f8387001c0380e2 0x24fc1c3800e01c07

def z246 : W := mkw 0x1600240016001088 0x20b0012000b00084 0x1c0000001c000000 0x00e0000000e00000

def z247 : W := mkw 0x76d87e00f6d036c8 0x23b6c3f007b681b6 0xfffc7f00fffc7fff 0xffffe3f807ffe3ff

def z248 : W := mkw 0x7eea7e3400000002 0x73f753f1a0000000 0x7ff07f3800000001 0x6bff83f9c0000000

def z249 : W := mkw 0x00100048ff7bd8a4 0x8000800247fbdec5 0x80000000fffff8fa 0x8400000007ffffc7

def z250 : W := mkw 0x8480afdb04a4dbe0 0x8c24057ed82526df 0x00007fff00007ffe 0x080003fff80003ff

def z251 : W := mkw 0x7fa7ff9200000002 0x6bfd3ffc90000000 0x7f83ff0000000001 0x6bfc1ff800000000

def z252 : W := mkw 0x7a7a502cfa522c05 0x53d3d28167d29160 0x5c706038dc003808 0x42e38301c6e001c0

def z253 : W := mkw 0x0105818200000000 0x08082c0c10000000 0x000f80c700000000 0x10007c0638000000

def z254 : W := mkw 0x0d37a5d84d6bd8a0 0x8069bd2ec26b5ec5 0xffffe7f8fffff8fb 0xffffff3fc7ffffc7

def z255 : W := mkw 0x6c7a743cec523c81 0x9363d3a1e76291e4 0x5c706038dc003808 0x42e38301c6e001c0

def z256 : W := mkw 0x72805a00b68036c8 0x239402d005b401b6 0xa3801800ff807ffe 0x851c00c007fc03ff

def z257 : W := mkw 0x81dd8bef41fdcb61 0x1c0eec5f7a0fee5b 0xa3ff9fff23ffc7f7 0xbd1ffcfff91ffe3f

def z258 : W := mkw 0x7fefffb6b600348a 0x7bff7ffdb5b001a4 0x7fffffffdc003809 0x7bfffffffee001c0

def z259 : W := mkw 0x7e6a7434b600348a 0x73f353a1a5b001a4 0x5c706038dc003808 0x42e38301c6e001c0

def z260 : W := mkw 0x7fefffb604001082 0x7bff7ffdb0200084 0xffffffffdc0078fb 0xfffffffffee003c7

def z261 : W := mkw 0xf3cddbe701adc362 0x7f9e6edf380d6e1b 0xa38f9fc723ffc7f7 0xbd1c7cfe391ffe3f

def z262 : W := mkw 0x083281d84862c820 0x8041940ec2431641 0x4073e0f8c063f819 0xda039f07c6031fc0

def z263 : W := mkw 0x0000000000000000 0x0000000000000000 0x40006000c0007819 0xca000300060003c0

def z264 : W := mkw 0xe1cd5a27a19d2741 0x1f0e6ad13d0ce93a 0x238c1807239c0704 0x011c60c0391ce038

def z265 : W := mkw 0x6c7af5fcec72fca1 0x9363d7afe76397e5 0xdc73e7f8dc63f8fb 0xfee39f3fc6e31fc7

def z266 : W := mkw 0x7258506df2746d01 0x1392c2836f93a368 0xfffc78fffffc7f1d 0xffffe3c7ffffe3f8

def z267 : W := mkw 0x8cb2afdb4ce6dbe0 0x8c65957eda6736df 0xdc73ffffdc63ffff 0xfee39ffffee31fff

def z268 : W := mkw 0x000081c10024c120 0x0000040e08012609 0xa00f9fc7207fc7f7 0xbd007cfe3903fe3f

def z269 : W := mkw 0x7fffffd8fffbfeec 0xe3fffffec7ffdff7 0xfffffff8ffffffff 0xffffffffc7ffffff

def z270 : W := mkw 0x04002400b68036c8 0x0020012005b401b6 0xdc006700ff807fff 0xeee0033807fc03ff

def z271 : W := mkw 0x09370000494b0000 0x0049b800024a5800 0xffff8000ffff8001 0xf7fffc0007fffc00

def z272 : W := mkw 0x0da7af9200000000 0x086d3d7c90000000 0x7fffffff00000001 0x7bfffffff8000000

def z273 : W := mkw 0x0010506de0746d01 0x100082836f03a368 0x000078ffe07c7f1c 0x880003c7ff03e3f8

def z274 : W := mkw 0x801000494defdbe0 0x840080024a6f7edf 0x80000000fffffffe 0x8400000007ffffff

def z275 : W := mkw 0x7fefffb6168012ca 0x7bff7ffdb0b40096 0xffffffff1f8000e3 0x7ffffffff8fc0007

def z276 : W := mkw 0x1fb7afda4c62d8a2 0xe8fdbd7ed26316c5 0xdff3e7f8dc63f8fb 0xfeff9f3fc6e31fc7

def z277 : W := mkw 0x8585fff701adc362 0x3c2c2fffb80d6e1b 0xa38fffff23ffc7f7 0xbd1c7ffff91ffe3f

def z278 : W := mkw 0x9785afc317add3e8 0x2cbc2d7e18bd6e9f 0xbf8f9fc73fffc7f7 0xbdfc7cfe39fffe3f

def z279 : W := mkw 0x7b6f0000b2000000 0x43db780005900000 0xffff8000ff800001 0xf7fffc0007fc0000

def z280 : W := mkw 0xfb7f81c3fb7fc124 0x4fdbfc0e1fdbfe09 0xffff80c7ffff8001 0xf7fffc063ffffc00

def z281 : W := mkw 0x8480fff700a4c362 0x3c2407ffb805261b 0x00007fff000047f6 0x080003fff800023f

def z282 : W := mkw 0x7fefffb600000002 0x7bff7ffdb0000000 0x3f8f9f0700000000 0x21fc7cf838000000

def z283 : W := mkw 0x6c7af5fde0746d01 0x1363d7afef03a368 0x7c7fffffe07c7f1d 0xfbe3ffffff03e3f8

def z284 : W := mkw 0x7b7f81c0fb7bc024 0x43dbfc0e07dbde01 0xffff87c0ffffc0f3 0xfffffc3e07fffe07

def z285 : W := mkw 0x893781db496fc920 0x8c49bc0eda4b7e49 0x007f80ff007f8000 0x1003fc07f803fc00

def z286 : W := mkw 0xffefffb601898262 0x7fff7ffdb00c4c13 0xffffffff038380e3 0x7ffffffff81c1c07

def z287 : W := mkw 0x6c6af5b400000000 0x136357ada0000000 0x7c7fffff00000001 0x7be3fffff8000000

def z288 : W := mkw 0x76807e0000000000 0x23b403f000000000 0x7f807f0000000001 0x6bfc03f800000000

def z289 : W := mkw 0x00100000e0500000 0x0000800007028000 0x00000000e07c0000 0x800000000703e000

def z290 : W := mkw 0x7f7f2418ff5b1884 0xc3fbf920c7fad8c4 0xffffe038ffffb809 0xf7ffff01c7fffdc0

def z291 : W := mkw 0x7b7f502cfb5b2c05 0x53dbfa8167dad960 0xffffe038ffffb809 0xf7ffff01c7fffdc0

def z292 : W := mkw 0x0000004000204000 0x0000000200010200 0x000000c000604011 0x9800000600030200

def z293 : W := mkw 0x7feffffe0420d8a2 0xfbff7ffff02106c5 0x7fffffff000078fb 0x7bfffffff80003c7

def z294 : W := mkw 0x73dd5a6fe0746d03 0x7b9eead37f03a368 0x63fc78ffe07c7f1d 0xdb1fe3c7ff03e3f8

def z295 : W := mkw 0x81858b8201898260 0x0c0c2c5c100c4c13 0xa38f9fc7038380e3 0x3d1c7cfe381c1c07

def z296 : W := mkw 0x7a6a000000000000 0x43d3500000000000 0x5c70000000000000 0x42e3800000000000

def z297 : W := mkw 0x7200000000000000 0x0390000000000000 0x7f80000000000001 0x63fc000000000000

def z298 : W := mkw 0x72800a00b2800240 0x0394005005940012 0xff801f00ff8047f7 0xeffc00f807fc023f

def z299 : W := mkw 0x696fd1b600000002 0x5b4b7e8db0000000 0x607ff8ff00000001 0x5b03ffc7f8000000

def z300 : W := mkw 0x7fefffb6b2000002 0x7bff7ffdb5900000 0xffffffffff800001 0xfffffffffffc0000

def z301 : W := mkw 0x80808bc300a4c360 0x0c04045e1805261b 0xa3801fc7238047f7 0xad1c00fe391c023f

def z302 : W := mkw 0x735d0000fb5b0004 0x439ae80007dad800 0xa38c0000ffff8000 0x851c600007fffc00

def z303 : W := mkw 0x083200484c62d8a0 0x80419002426316c5 0xdc738000dc63f8fb 0xf6e39c0006e31fc7

def z304 : W := mkw 0x1fefafb600000002 0x78ff7d7db0000000 0x1fff87ff00000000 0x30fffc3ff8000000

def z305 : W := mkw 0x000081d80020c820 0x8000040ec0010641 0x000000f800000000 0x00000007c0000000

def z306 : W := mkw 0x0c3224184c421880 0x80619120c26210c4 0xdc706738dc0078fb 0xeee38339c6e003c7

def z307 : W := mkw 0xffeffff7012dc122 0x7fff7fffb8096e09 0x7fffffff007f8001 0x7bfffffff803fc00

def z308 : W := mkw 0x04807e00048036c8 0x202403f0002401b6 0xa3807f0023807fff 0xad1c03f8011c03ff

def z309 : W := mkw 0x7b7f0000fb5b0004 0x43dbf80007dad800 0x23ff800023ff8000 0x111ffc00011ffc00

def z310 : W := mkw 0x00100000ffdb36cc 0x0000800007fed9b6 0x80000000fffffffe 0x8400000007ffffff

def z311 : W := mkw 0x81858bc300a4c360 0x0c0c2c5e1805261b 0x238f9fc7000047f7 0x391c7cfe3800023f

def z312 : W := mkw 0x6058502ce0502c01 0x1302c28167028160 0x60707838e0007f1d 0xcb0383c1c70003f8

def z313 : W := mkw 0x8000004100a4c360 0x040000020805261b 0x00000000000047f6 0x000000000000023f

def z314 : W := mkw 0x7b7f0000fa520004 0x43dbf80007d29000 0x7fff8000dc000001 0x73fffc0006e00000

def z315 : W := mkw 0x81958bcb4defdbe0 0x8c0cac5e5a6f7edf 0xa38f9fc7ffffffff 0xbd1c7cfe3fffffff

def z316 : W := mkw 0x0c22a5900c0290a0 0x8061152c80601485 0xdc73e7f81c0380e3 0x7ee39f3fc0e01c07

def z317 : W := mkw 0x7b7f0000ffdb36cc 0x43dbf80007fed9b6 0xffff8000ffffffff 0xf7fffc0007ffffff

def z318 : W := mkw 0x7e7aa5d8fe72d8a4 0xc3f3d52ec7f396c5 0xdc73e7f8dc63f8fb 0xfee39f3fc6e31fc7

def z319 : W := mkw 0x6058502ce0502c01 0x1302c28167028160 0x607c6038e07c3809 0xd303e301c703e1c0

def z320 : W := mkw 0x76807e6db6a47fc9 0x33b403f36db523fe 0xff807fffff807fff 0xeffc03fffffc03ff

def z321 : W := mkw 0x60585024e0500000 0x1302c28127028000 0x607c78ffe07c0001 0xdb03e3c7ff03e000

def z322 : W := mkw 0x76002400b6001080 0x03b0012005b00084 0xff806700ff8078fb 0xeffc033807fc03c7

def z323 : W := mkw 0x815d81ef417dc921 0x1c0aec0f7a0bee49 0x007f80ff007f8000 0x1003fc07f803fc00

def z324 : W := mkw 0x7b6f81b600000002 0x5bdb7c0db0000000 0x7fff80ff00000001 0x73fffc07f8000000

def z325 : W := mkw 0x097f0000495b0004 0x404bf800024ad800 0xa3ff800023ff8001 0xb51ffc00011ffc00

def z326 : W := mkw 0x097f81ff40744903 0x584bfc0ffa03a248 0x007f80ff007c0000 0x1003fc07f803e000

def z327 : W := mkw 0x7b7f0000e0500000 0x43dbf80007028000 0x7fff8000e07c0001 0xf3fffc000703e000

def z328 : W := mkw 0x0d6fa5b600000002 0x586b7d2db0000000 0x5c7fe7ff00000001 0x7ae3ff3ff8000000

def z329 : W := mkw 0x00808bc000a0c260 0x0004045e00050613 0xa3839fc023e3c7f7 0xbd1c1cfe011f1e3f

def z330 : W := mkw 0x72d85a6df2f46f49 0x3396c2d36f97a37a 0x63fc78ffe3fc7f1d 0xdb1fe3c7ff1fe3f8

def z331 : W := mkw 0x81858b8201898260 0x0c0c2c5c100c4c13 0xa3839f002383c7f7 0xad1c1cf8011c1e3f

def z332 : W := mkw 0x0000000000800240 0x0000000000040012 0x80000000238047f6 0x84000000011c023f

def z333 : W := mkw 0x0832004848624800 0x0041900242431240 0xdc73e0f8dc63f819 0xfee39f07c6e31fc0

def z334 : W := mkw 0x1b3700005b4b0004 0x40d9b80002da5800 0xdff38000dfe38001 0xf6ff9c0006ff1c00

def z335 : W := mkw 0x81858bc301adc360 0x0c0c2c5e180d6e1b 0x238c1fc7239c47f6 0x091c60fe391ce23f

def z336 : W := mkw 0x7f7fa5d8ff7bd8a4 0xc3fbfd2ec7fbdec5 0xffffe7f8fffff8fb 0xffffff3fc7ffffc7

def z337 : W := mkw 0x77cd7e00b79936cc 0x63be6bf005bcc9b6 0xff8c7f00ff9c7fff 0xeffc63f807fce3ff

def z338 : W := mkw 0x01850a0200000000 0x080c285010000000 0x238c180700000000 0x011c60c038000000

def z339 : W := mkw 0x0000502400000000 0x1000028120000000 0x000078ff00000000 0x080003c7f8000000

def z340 : W := mkw 0x6048000000000000 0x0302400000000000 0x607c000000000001 0x5303e00000000000

def z341 : W := mkw 0x81958bcbe1fdef61 0x0c0cac5e5f0fef7b 0xa38f9fc7e3ffffff 0xbd1c7cfe3f1fffff

def z342 : W := mkw 0x0c3224004c421080 0x0061912002621084 0xdc73e700dc63f8fb 0xfee39f3806e31fc7

def z343 : W := mkw 0x00000000b2802648 0x0000000005940132 0x0000000023800704 0x00000000011c0038

def z344 : W := mkw 0x76807e00b68036c8 0x23b403f005b401b6 0x7f807800ff803f0c 0x43fc03c007fc01f8

def z345 : W := mkw 0xffeffff7b7adf7ea 0x7fff7fffbdbd6fbf 0xffffffffffffffff 0xffffffffffffffff

def z346 : W := mkw 0x60480000a0100000 0x0302400005008000 0x200c0000201c0000 0x010060000100e000

def z347 : W := mkw 0x0048002400000000 0x1002400120000000 0x007c00ff00000000 0x1003e007f8000000

def z348 : W := mkw 0x0410a5d84460d8a0 0x8020852ec22306c5 0x407067f8c06078fb 0xda03833fc60303c7

def z349 : W := mkw 0x7b6f00001b0b0004 0x43db780000d85800 0xffff80001f838001 0x77fffc0000fc1c00

def z350 : W := mkw 0x76d87e6de0746d01 0x33b6c3f36f03a368 0x7ffc7fffe07c7f1d 0xfbffe3ffff03e3f8

def z351 : W := mkw 0x7ea2ff90b68036c8 0x23f517fc85b401b6 0xfff3fff8ff807fff 0xffff9fffc7fc03ff

def z352 : W := mkw 0x01850a0001890240 0x000c2850000c4812 0xa38f9f0023ffc7f7 0xbd1c7cf8011ffe3f

def z353 : W := mkw 0x7680ffb6b68036ca 0x3bb407fdb5b401b6 0xff807fffff807fff 0xeffc03fffffc03ff

def z354 : W := mkw 0x7b6f502400000000 0x53db7a8120000000 0x7ffff8ff00000001 0x7bffffc7f8000000

def z355 : W := mkw 0x60005041a0246500 0x030002820d012328 0x600c78c7e07c7f1d 0xdb0063c63f03e3f8

def z356 : W := mkw 0x7b6f0000bb1b0004 0x43db780005d8d800 0xbf8f80003f9f8000 0x25fc7c0001fcfc00

def z357 : W := mkw 0x000000400020c020 0x0000000200010601 0x800000000063c0f2 0x8400000000031e07

def z358 : W := mkw 0x041024484c62d8a0 0x80208122426316c5 0xdc006700dc63f8fb 0xeee0033806e31fc7

def z359 : W := mkw 0x6058506dec76fda1 0x9302c2836f63b7ed 0xe07c78fffc7fffff 0xdf03e3c7ffe3ffff

def z360 : W := mkw 0x04807e6d04a47fc9 0x302403f3682523fe 0x00007fff00007ffe 0x080003fff80003ff

def z361 : W := mkw 0x0d7fa5d84d7bd8a4 0xc06bfd2ec26bdec5 0xdc7fe7f8dc7ff8fb 0xfee3ff3fc6e3ffc7

def z362 : W := mkw 0x0000000001090000 0x0000000000084800 0x8000000023ff8000 0x84000000011ffc00

def z363 : W := mkw 0x7b6f000001090000 0x43db780000084800 0xffff800023ff8001 0xf7fffc00011ffc00

def z364 : W := mkw 0x7eeaffb600000002 0x7bf757fdb0000000 0x5c707fff00000000 0x4ae383fff8000000

def z365 : W := mkw 0x7a320000fa420000 0x03d1900007d21000 0xfff38000ffe38001 0xf7ff9c0007ff1c00

def z366 : W := mkw 0x60580000fb5b0004 0x0302c00007dad800 0xe07c0000ffff8001 0xd703e00007fffc00

def z367 : W := mkw 0x60105049e0746d01 0x030082824f03a368 0x60007800e07c7f1d 0xcb0003c00703e3f8

def z368 : W := mkw 0x80000041b7adf7e8 0x040000020dbd6fbf 0x80000000fffffffe 0x8400000007ffffff

def z369 : W := mkw 0x0c22241000000000 0x0061112080000000 0x5c70603800000000 0x42e38301c0000000

def z370 : W := mkw 0x1a2200001a020004 0x40d1100000d01000 0x1c0000001c000000 0x00e0000000e00000

def z371 : W := mkw 0x097f006d497f4905 0x504bf8036a4bfa48 0x007f80ff007f8000 0x1003fc07f803fc00

def z372 : W := mkw 0x7e7a7400fe52348c 0x63f3d3a007f291a4 0x5c706000dc003808 0x42e3830006e001c0

def z373 : W := mkw 0x7a7a0000fb5b0004 0x43d3d00007dad800 0xdc700000ffff8000 0xc6e3800007fffc00

def z374 : W := mkw 0x0010004940644900 0x000080024a032248 0x607c78ffe07c7f1d 0xdb03e3c7ff03e3f8

def z375 : W := mkw 0x0defffb600000002 0x786f7ffdb0000000 0x007fffff00000000 0x1803fffff8000000

def z376 : W := mkw 0x0832001848420800 0x80419000c2421040 0x0070003800000000 0x00038001c0000000

def z377 : W := mkw 0x0c7aa5fd4c76d9a1 0x9063d52fea63b6cd 0xdc7fe7ffdc7ff8fb 0xfee3ff3ffee3ffc7

def z378 : W := mkw 0x76807e00b6003488 0x23b403f005b001a4 0x7f807f00dc003809 0x6bfc03f806e001c0

def z379 : W := mkw 0x76807e00168012c8 0x23b403f000b40096 0xff807f001f8000e3 0x6ffc03f800fc0007

def z380 : W := mkw 0x8585ffc305adf7e8 0x2c2c2ffe182d6fbf 0xa38fffc723ffffff 0xbd1c7ffe391fffff

def z381 : W := mkw 0x000000480420d8a0 0x80000002402106c5 0x00000000000078fa 0x00000000000003c7

def z382 : W := mkw 0x7e6a743400000002 0x73f353a1a0000000 0x7c7c78ff00000001 0x5be3e3c7f8000000

def z383 : W := mkw 0x7b7f0000495b0004 0x43dbf800024ad800 0x7fff8000007f8001 0x73fffc000003fc00

def z384 : W := mkw 0x73cd5a2600000002 0x7b9e6ad130000000 0x63fc78ff00000001 0x5b1fe3c7f8000000

def z385 : W := mkw 0x72005000b2002408 0x2390028005900120 0x0000000000000000 0x0000000000000000

def z386 : W := mkw 0x76802e00b68012c8 0x23b4017005b40096 0xff800700ff8000e3 0xe7fc003807fc0007

def z387 : W := mkw 0x81858bc3012dc120 0x0c0c2c5e18096e09 0x238f9fc7007f8001 0x391c7cfe3803fc00

def z388 : W := mkw 0x6048502400000000 0x1302428120000000 0x200c180700000000 0x010060c038000000

def z389 : W := mkw 0xe1cddbe701adc360 0x1f0e6edf380d6e1b 0xe3ffffff23ffc7f7 0xff1ffffff91ffe3f

def z390 : W := mkw 0x7fefffff00246d03 0x7bff7ffff8012368 0x7fffffff00007f1d 0x7bfffffff80003f8

def z391 : W := mkw 0x09ef8bb600000002 0x584f7c5db0000000 0x23ff9fff00000001 0x391ffcfff8000000

def z392 : W := mkw 0x0c2224100c021080 0x8061112080601084 0x1c0000001c000000 0x00e0000000e00000

def z393 : W := mkw 0x0058006d40744901 0x1002c0036a03a248 0x407c60ffc07c7819 0xda03e307fe03e3c0

def z394 : W := mkw 0x810581c3012dc120 0x0c082c0e18096e09 0x200f98c7207fc715 0x99007cc63903fe38

def z395 : W := mkw 0x7b7f5025fb5f2505 0x53dbfa812fdaf928 0xffff9807ffff8705 0xf7fffcc03ffffc38

def z396 : W := mkw 0x61cddba600000000 0x1b0e6edd30000000 0x63ffffff00000001 0x7b1ffffff8000000

def z397 : W := mkw 0x7e32f5d8fe62fca8 0xa3f197aec7f317e5 0xdc73e7f8dc63f8fb 0xfee39f3fc6e31fc7

def z398 : W := mkw 0x001000484c62d8a0 0x80008002426316c5 0xc07060f8dc63f8fb 0xde038307c6e31fc7

def z399 : W := mkw 0x7785ff82b68036c8 0x2bbc2ffc15b401b6 0xff8fffc7ff807fff 0xfffc7ffe3ffc03ff

def z400 : W := mkw 0x76c87e2400000000 0x33b643f120000000 0x7ffc7fff00000001 0x7bffe3fff8000000

def z401 : W := mkw 0x81858bc301adc360 0x0c0c2c5e180d6e1b 0x8383870023ffc7f6 0xa41c1c38011ffe3f

def z402 : W := mkw 0x0832000048420000 0x0041900002421000 0x0073800000638000 0x10039c0000031c00

def z403 : W := mkw 0x7bef5a2600000002 0x7bdf7ad130000000 0x7fff980700000001 0x73fffcc038000000

def z404 : W := mkw 0x0410244844605880 0x00208122422302c4 0xdc7067f8dc6078fb 0xfee3833fc6e303c7

def z405 : W := mkw 0x01858b8200800240 0x080c2c5c10040012 0xa38f9fc7238047f7 0xbd1c7cfe391c023f

def z406 : W := mkw 0x7b7f506de0746d01 0x53dbfa836f03a368 0x7ffff8ffe07c7f1d 0xfbffffc7ff03e3f8

def z407 : W := mkw 0x0000004800204800 0x0000000240010240 0x000060f800007818 0x08000307c00003c0

def z408 : W := mkw 0x1fa7af9200000002 0x68fd3d7c90000000 0x3f8f9fc700000001 0x39fc7cfe38000000

def z409 : W := mkw 0x73cd5a00b399264c 0x639e6ad0059cc932 0x238c1800239c0704 0x011c60c0011ce038

def z410 : W := mkw 0x76907e00ffdb36cc 0x23b483f007fed9b6 0xff807f00ffffffff 0xeffc03f807ffffff

def z411 : W := mkw 0x64007400a4003480 0x032003a0052001a4 0xfc007f00fc007fff 0xefe003f807e003ff

def z412 : W := mkw 0x04807e00048036c8 0x202403f0002401b6 0xdc007f00dc007fff 0xeee003f806e003ff

def z413 : W := mkw 0x60000000a0000000 0x0300000005000000 0x60000000e0000001 0xc300000007000000

def z414 : W := mkw 0x72005000b2002400 0x0390028005900120 0xff807800ff807f1d 0xeffc03c007fc03f8

def z415 : W := mkw 0x0c32a5d84c62d8a0 0x8061952ec26316c5 0x0073e7f80063f8fa 0x18039f3fc0031fc7

def z416 : W := mkw 0x0400240004001080 0x0020012000200084 0x00006700000078fa 0x08000338000003c7

def z417 : W := mkw 0x7fefffb61b0b0006 0x7bff7ffdb0d85800 0xffffffff1f838001 0x7ffffffff8fc1c00

def z418 : W := mkw 0x0000004100244100 0x0000000208012208 0x00000000207c4714 0x800000000103e238

def z419 : W := mkw 0xf3cd5a27018d0342 0x7f9e6ad1380c681a 0x238c1807239c0704 0x011c60c0391ce038

def z420 : W := mkw 0x001000484862c820 0x8000800242431641 0x0000000000638000 0x0000000000031c00

def z421 : W := mkw 0x0105000000000000 0x0008280000000000 0x238f800000000001 0x311c7c0000000000

def z422 : W := mkw 0x6058506de0746d01 0x1302c2836f03a368 0x407078ffc0007f1c 0x4a0383c7fe0003f8

def z423 : W := mkw 0x896f81f7012dc122 0x5c4b7c0fb8096e09 0x007f80ff007f8000 0x1003fc07f803fc00

def z424 : W := mkw 0x010581c00129c020 0x00082c0e00094e01 0xa38f87c023ffc0f3 0xbd1c7c3e011ffe07

def z425 : W := mkw 0x76807e0004001080 0x23b403f000200084 0xff807f00dc0078fb 0xeffc03f806e003c7

def z426 : W := mkw 0x6058506de0746d01 0x1302c2836f03a368 0x407c60ffc07c3808 0x5203e307fe03e1c0

def z427 : W := mkw 0x7f7fa590fb5b0004 0x43fbfd2c87dad800 0xffffe7f8ffff8001 0xffffff3fc7fffc00

def z428 : W := mkw 0x16802e00168012c8 0x20b4017000b40096 0xbf801f003f8047f7 0xadfc00f801fc023f

def z429 : W := mkw 0x097f0000495b0004 0x404bf800024ad800 0xdc7f8000dc7f8001 0xf6e3fc0006e3fc00

def z430 : W := mkw 0x80808bc300a4c360 0x0c04045e1805261b 0x80039fc70063c7f7 0xbc001cfe38031e3f

def z431 : W := mkw 0x76007400b6003488 0x23b003a005b001a4 0x7c007800fc007f1d 0xcbe003c007e003f8

def z432 : W := mkw 0x8105004101adc360 0x04082802080d6e1b 0xa38f800023ffc7f7 0xb51c7c00011ffe3f

def z433 : W := mkw 0x1fa7af921b0b0006 0x68fd3d7c90d85800 0x9f8387001f838000 0x24fc1c3800fc1c00

def z434 : W := mkw 0x01858bc20020c020 0x080c2c5e10010601 0xa38f9fc70063c0f3 0xbd1c7cfe38031e07

def z435 : W := mkw 0x00000000048036c8 0x00000000002401b6 0x0000000000007ffe 0x00000000000003ff

def z436 : W := mkw 0x7fffffb648420002 0x7bfffffdb2421000 0xffffffffdc638001 0xfffffffffee31c00

def z437 : W := mkw 0x01858b8201090000 0x080c2c5c10084800 0xa38f9fc723ff8001 0xbd1c7cfe391ffc00

def z438 : W := mkw 0x8105818201098020 0x0c082c0c10084c01 0x0003800000038000 0x00001c0000001c00

def z439 : W := mkw 0x64c8ffb600000002 0x3b2647fdb0000000 0x607c7fff00000001 0x5b03e3fff8000000

def z440 : W := mkw 0x81958bcb41edcb60 0x0c0cac5e5a0f6e5b 0xe3ffffffe3ffffff 0xff1fffffff1fffff

def z441 : W := mkw 0x7b270000bb0b0004 0x43d9380005d85800 0xff838000ff838001 0xe7fc1c0007fc1c00

def z442 : W := mkw 0x0c32a5d840604800 0x0061952ec2030240 0x5c73e7f8c0607819 0xfae39f3fc60303c0

def z443 : W := mkw 0x7bff8b82fb5b0004 0x4bdffc5c17dad800 0xffff9fc7ffff8001 0xfffffcfe3ffffc00

def z444 : W := mkw 0x7feffff60020c022 0x7bff7fffb0010601 0xffffffff0063c0f3 0xfffffffff8031e07

def z445 : W := mkw 0x1b370000fb5b0004 0x40d9b80007dad800 0x9f838000ffff8000 0xa4fc1c0007fffc00

def z446 : W := mkw 0x13850a0200000002 0x689c285010000000 0x0380000000000000 0x001c000000000000

def z447 : W := mkw 0x0c3224184c421880 0x80619120c26210c4 0xdc73e038dc63b809 0xf6e39f01c6e31dc0

def z448 : W := mkw 0x7eea7e34b68036ca 0x73f753f1a5b401b6 0xfff07f38ff807fff 0xefff83f9c7fc03ff

def z449 : W := mkw 0x687a506de8766d01 0x1343d2836f43b368 0xfc7ff8fffc7fff1d 0xffe3ffc7ffe3fff8

def z450 : W := mkw 0x7fa7ff92b68036ca 0x6bfd3ffc95b401b6 0xff83ff00ff807fff 0xeffc1ff807fc03ff

def z451 : W := mkw 0x7fffffbe4c421882 0xfbfffffdf26210c4 0x7fffffffdc003809 0x7bfffffffee001c0

def z452 : W := mkw 0xfbff8b82fbdb8264 0x4fdffc5c17dedc13 0xffff8700ffff80e3 0xf7fffc3807fffc07

def z453 : W := mkw 0x086a003400000002 0x50435001a0000000 0x0070003800000000 0x00038001c0000000

def z454 : W := mkw 0x7658742cf6503c89 0x33b2c3a167b281e4 0x5c706038dc003808 0x42e38301c6e001c0

def z455 : W := mkw 0x16802e0000000000 0x20b4017000000000 0x1f80070000000000 0x20fc003800000000

def z456 : W := mkw 0x8185dbef01adef61 0x1c0c2edf780d6f7b 0xa38fffff23ffffff 0xbd1c7ffff91fffff

def z457 : W := mkw 0x0058006de0746d01 0x1002c0036f03a368 0x007c00ffe07c7f1c 0x9003e007ff03e3f8

def z458 : W := mkw 0x7680ffb600000002 0x3bb407fdb0000000 0x7f807fff00000001 0x6bfc03fff8000000

def z459 : W := mkw 0x0000004100244100 0x0000000208012208 0x000018c700004714 0x080000c638000238

def z460 : W := mkw 0x7b7f0049fb7f6d05 0x43dbf8024fdbfb68 0xffff8000ffffff1d 0xf7fffc0007fffff8

def z461 : W := mkw 0x0000818000000000 0x0000040c00000000 0x000387c000000001 0x38001c3e00000000

def z462 : W := mkw 0x89ef8bf701adc362 0x5c4f7c5fb80d6e1b 0xa3ff9fff23ffc7f7 0xbd1ffcfff91ffe3f

def z463 : W := mkw 0x01150000fb5b0004 0x0008a80007dad800 0xa38f8000ffff8001 0xb51c7c0007fffc00

def z464 : W := mkw 0xe185dbc3a1ade760 0x0f0c2ede1d0d6f3b 0xe38fffc7e3ffffff 0xff1c7ffe3f1fffff

def z465 : W := mkw 0x72580000f2500000 0x0392c00007928000 0xfffc0000fffc0001 0xf7ffe00007ffe000

def z466 : W := mkw 0x81858bc301adc360 0x0c0c2c5e180d6e1b 0x000f9fc7007fc7f6 0x18007cfe3803fe3f

def z467 : W := mkw 0x0c22a5900c0290a0 0x8061152c80601485 0xdc03e700dc03f8fb 0xeee01f3806e01fc7

def z468 : W := mkw 0x0c32a5d84c62d8a0 0x8061952ec26316c5 0x5c73e0f8dc63b808 0x52e39f07c6e31dc0

def z469 : W := mkw 0x7bff0a00fbdb0244 0x43dff85007ded812 0xffff9f00ffffc7f7 0xfffffcf807fffe3f

def z470 : W := mkw 0x80100041fbffc364 0x040080020fdffe1b 0x80000000ffffc7f6 0x8400000007fffe3f

def z471 : W := mkw 0x0400240004001080 0x0020012000200084 0x5c006000dc003808 0x42e0030006e001c0

def z472 : W := mkw 0x04807e0000000000 0x202403f000000000 0x00007f0000000000 0x080003f800000000

def z473 : W := mkw 0x734d0000b3190004 0x439a68000598c800 0xa38f800023ff8001 0xb51c7c00011ffc00

def z474 : W := mkw 0x8000004101adc360 0x04000002080d6e1b 0xa00c18c723ffc7f7 0x9d0060c6391ffe3f

def z475 : W := mkw 0x6c7a747dec767d81 0x9363d3a3ef63b3ec 0x7c7c78fffc7c7f1d 0xdbe3e3c7ffe3e3f8

def z476 : W := mkw 0x0822000000000000 0x0041100000000000 0x5c73800000000001 0x72e39c0000000000

def z477 : W := mkw 0x0832000048420000 0x0041900002421000 0x5c700000dc000000 0x42e3800006e00000

def z478 : W := mkw 0x1b27000000000000 0x40d9380000000000 0x1f83800000000000 0x20fc1c0000000000

def z479 : W := mkw 0xffffffc3fffff7ec 0x6ffffffe1fffffbf 0xffffffc7ffffffff 0xfffffffe3fffffff

def z480 : W := mkw 0x8d37a5db4d6fd9a0 0x8c69bd2eda6b7ecd 0xdc7fe7ffdc7ff8fb 0xfee3ff3ffee3ffc7

def z481 : W := mkw 0x00805a0000802648 0x200402d000040132 0x0000180000000704 0x000000c000000038

def z482 : W := mkw 0x72480000b2100004 0x4392400005908000 0x0000000000000000 0x0000000000000000

def z483 : W := mkw 0x72805a00b2802648 0x239402d005940132 0xa3801f00238047f7 0xad1c00f8011c023f

def z484 : W := mkw 0x00000000b2000000 0x0000000005900000 0x80000000ff800000 0x8400000007fc0000

def z485 : W := mkw 0x04802e00048012c8 0x2024017000240096 0x00000700000000e2 0x0000003800000007

def z486 : W := mkw 0x0c22a5d80420d8a0 0x8061152ec02106c5 0x5c73e7f8000078fb 0x7ae39f3fc00003c7

def z487 : W := mkw 0x0c32a5d84c62d8a0 0x8061952ec26316c5 0x5c7067f8dc0078fa 0x4ae3833fc6e003c7

def z488 : W := mkw 0x0480ffd804a0fee8 0xa02407fec02507f7 0x00007ff800007ffe 0x080003ffc00003ff

def z489 : W := mkw 0x81850a03018d0340 0x0c0c2850180c681a 0xa38c1f07239c47f7 0xad1c60f8391ce23f

def z490 : W := mkw 0x72000000b2000000 0x0390000005900000 0x2380000023800000 0x011c0000011c0000

def z491 : W := mkw 0x0010000040400000 0x0000800002020000 0x40700000c0600001 0xd203800006030000

def z492 : W := mkw 0x7680ffd8b6a0fee8 0xa3b407fec5b507f7 0xff807ff8ff807fff 0xeffc03ffc7fc03ff

def z493 : W := mkw 0x60585000e0502400 0x0302c28007028120 0x607c7800e07c7f1d 0xdb03e3c00703e3f8

def z494 : W := mkw 0x00100049e0746d01 0x000080024f03a368 0x200c18c7e07c7f1d 0x990060c63f03e3f8

def z495 : W := mkw 0xffb7ffdbffefffe8 0xaffdbffedfff7fff 0xffffffffffffffff 0xffffffffffffffff

def z496 : W := mkw 0x1200000012000000 0x0090000000900000 0x9f8000001f800000 0x24fc000000fc0000

def z497 : W := mkw 0x0000004100244100 0x0000000208012208 0x000c00c7007c0000 0x100060063803e000

def z498 : W := mkw 0x097f81d8497bc824 0xc04bfc0ec24bde41 0x007f80f8007f8000 0x1003fc07c003fc00

def z499 : W := mkw 0x0058000040500000 0x0002c00002028000 0x007c0000007c0000 0x1003e0000003e000

def z500 : W := mkw 0x7785ff8200000000 0x2bbc2ffc10000000 0x7f8fffc700000001 0x7bfc7ffe38000000

def z501 : W := mkw 0x0000506d00246d01 0x1000028368012368 0x200c78ff207c7f1d 0x990063c7f903e3f8

def z502 : W := mkw 0x7befdbb600000002 0x7bdf7eddb0000000 0x23ff98ff00000000 0x111ffcc7f8000000

def z503 : W := mkw 0x014d000001190004 0x400a68000008c800 0x000c0000001c0000 0x000060000000e000

def z504 : W := mkw 0x73cd5a26b3190006 0x7b9e6ad13598c800 0x238c1807239c0000 0x011c60c0391ce000

def z505 : W := mkw 0x81858b83018d8360 0x0c0c2c5c180c6c1b 0xa38f9f07239f87e6 0x251c7cf8391cfc3f

def z506 : W := mkw 0x810581c3012dc120 0x0c082c0e18096e09 0x800f87c7007fc0f3 0xbc007c3e3803fe07

def z507 : W := mkw 0x7600740000000000 0x23b003a000000000 0x5c00600000000000 0x42e0030000000000

def z508 : W := mkw 0x7f7f7434fb5b0006 0x73fbfba1a7dad800 0xffffe038ffff8001 0xf7ffff01c7fffc00

def z509 : W := mkw 0x0000818000008020 0x0000040c00000401 0x80038700000380e2 0x24001c3800001c07

def z510 : W := mkw 0x76d87e2cf6d03ec9 0x33b6c3f167b681f6 0xfff07f38ff807fff 0xefff83f9c7fc03ff

def z511 : W := mkw 0xffffafdbffffdbe4 0xcffffd7edffffedf 0xffffffffffffffff 0xffffffffffffffff

def z512 : W := mkw 0x08320000fb5b0004 0x0041900007dad800 0xdc738000ffff8001 0xf6e39c0007fffc00

def z513 : W := mkw 0x1f37a5d85f6bd8a4 0xc0f9bd2ec2fb5ec5 0xdff3e7f8dfe3f8fb 0xfeff9f3fc6ff1fc7

def z514 : W := mkw 0x0c32a5d9ec76fda1 0x8061952ecf63b7ed 0xdc73e7f8fc7fffff 0xfee39f3fc7e3ffff

def z515 : W := mkw 0x80800a0300840340 0x0c0400501804201a 0x0000180700000704 0x000000c038000038

def z516 : W := mkw 0x000081b600000002 0x1800040db0000000 0x000000ff00000000 0x00000007f8000000

def z517 : W := mkw 0x0400241804001880 0x80200120c02000c4 0x0000603800003808 0x00000301c00001c0

def z518 : W := mkw 0x7b6f0000b3190004 0x43db78000598c800 0x7fff8000239c0001 0x73fffc00011ce000

def z519 : W := mkw 0x0c32a5d84c62d8a0 0x8061952ec26316c5 0x9c038700dc63f8fa 0xa4e01c3806e31fc7

def z520 : W := mkw 0x0480ffff00246d03 0x382407fff8012368 0x00007fff00007f1c 0x080003fff80003f8

def z521 : W := mkw 0xfbef8bc301adc360 0x4fdf7c5e180d6e1b 0xffff9fc723ffc7f7 0xfffffcfe391ffe3f

def z522 : W := mkw 0x0c32a5d8ff7bd8a4 0x8061952ec7fbdec5 0xdc73e7f8fffff8fb 0xfee39f3fc7ffffc7

def z523 : W := mkw 0x0ca2ffb600000002 0x386517fdb0000000 0x5c73ffff00000001 0x7ae39ffff8000000

def z524 : W := mkw 0x7feffff700244102 0x7bff7fffb8012208 0x7fffffff207c4715 0xfbfffffff903e238

def z525 : W := mkw 0xffefffb7018d0342 0x7fff7ffdb80c681a 0x7fffffff239c0705 0x7bfffffff91ce038

def z526 : W := mkw 0xf3858bc3b3adc360 0x0f9c2c5e1d9d6e1b 0xff8f9fc7ffffc7f7 0xfffc7cfe3ffffe3f

def z527 : W := mkw 0x0400240000000000 0x0020012000000000 0x5c00670000000001 0x6ae0033800000000

def z528 : W := mkw 0x6c32f5d8ec62fca0 0x836197aec76317e5 0xfc73fff8fc63ffff 0xffe39fffc7e31fff

def z529 : W := mkw 0x00800a0000000000 0x0004005000000000 0x23801f0000000001 0x291c00f800000000

def z530 : W := mkw 0x8da7afd301adc360 0x0c6d3d7e980d6e1b 0xffffffff23ffc7f7 0xfffffffff91ffe3f

def z531 : W := mkw 0x7e7a2418fe521884 0xc3f3d120c7f290c4 0x5c706038dc003808 0x42e38301c6e001c0

def z532 : W := mkw 0x7fff7e00fb5b0004 0x63fffbf007dad800 0xffffff00ffff8001 0xfffffff807fffc00

def z533 : W := mkw 0x7ffffffffb7f6d07 0x7bffffffffdbfb68 0xffffffffffffff1d 0xfffffffffffffff8

def z534 : W := mkw 0x6048506d00246d01 0x1302428368012368 0x607c78ff00007f1d 0x5b03e3c7f80003f8

def z535 : W := mkw 0x734d0000b3190004 0x439a68000598c800 0xff8c0000ff9c0001 0xe7fc600007fce000

def z536 : W := mkw 0x615d0000e1590000 0x030ae800070ac800 0xe3ff8000e3ff8001 0xf71ffc00071ffc00

def z537 : W := mkw 0x0c32a5d8fee2fee8 0x8061952ec7f717f7 0xdc73e7f8ffe3ffff 0xfee39f3fc7ff1fff

def z538 : W := mkw 0xfffffff7fbffc366 0x7fffffffbfdffe1b 0xffffffffffffc7f7 0xfffffffffffffe3f

def z539 : W := mkw 0x7efa7e00fed236cc 0x63f7d3f007f691b6 0xfff07f00ff807fff 0xefff83f807fc03ff

def z540 : W := mkw 0x7f7fa5d84c62d8a0 0xc3fbfd2ec26316c5 0xffffe7f8dc63f8fb 0xffffff3fc6e31fc7

def z541 : W := mkw 0x7fffaf92fb5b0006 0x6bfffd7c97dad800 0xffff8700ffff8001 0xf7fffc3807fffc00

def z542 : W := mkw 0xedffffffedffffe1 0x9f6fffffff6fffff 0xffffffffffffffff 0xffffffffffffffff

def z543 : W := mkw 0x60105048e0606c00 0x0300828247030360 0x607078f8e0607f1d 0xdb0383c7c70303f8

def z544 : W := mkw 0x1fa7af92168012ca 0x68fd3d7c90b40096 0x9f8387001f8000e2 0x24fc1c3800fc0007

def z545 : W := mkw 0x80800a4101adc360 0x04040052080d6e1b 0xa3801f0023ffc7f7 0xad1c00f8011ffe3f

def z546 : W := mkw 0x897f81c3497fc124 0x4c4bfc0e1a4bfe09 0x007f80c7007f8000 0x1003fc063803fc00

def z547 : W := mkw 0x76c87e25b69437c9 0x33b643f12db4a1be 0xff8c7f07ff9c7fff 0xeffc63f83ffce3ff

def z548 : W := mkw 0x0c32f5fd4c66fda1 0x906197afea6337ed 0xdc73ffffdc63ffff 0xfee39ffffee31fff

def z549 : W := mkw 0x1fa72e001f8b12cc 0x60fd397000fc5896 0x9f8387001f8380e2 0x24fc1c3800fc1c07

def z550 : W := mkw 0x76807e00b2802648 0x23b403f005940132 0x7f807f0023800705 0x6bfc03f8011c0038

def z551 : W := mkw 0x73cddba600000002 0x7b9e6edd30000000 0x238f9fc700000001 0x391c7cfe38000000

def z552 : W := mkw 0x7fefffb7a0142503 0x7bff7ffdbd00a128 0x7fffffff201c0705 0x7bfffffff900e038

def z553 : W := mkw 0xf680ffc3b6a4f7e8 0x2fb407fe1db527bf 0xff807fc7ff807fff 0xeffc03fe3ffc03ff

def z554 : W := mkw 0x697f0000e95b0004 0x434bf800074ad800 0x607f8000e07f8001 0xd303fc000703fc00

def z555 : W := mkw 0x7b7f81d8fb7bc824 0xc3dbfc0ec7dbde41 0xffff80f8ffff8001 0xf7fffc07c7fffc00

def z556 : W := mkw 0x800081c30024c120 0x0c00040e18012609 0x000000c700000000 0x0000000638000000

def z557 : W := mkw 0x083281d84c62d8a0 0x8041940ec26316c5 0x807380f8dc63f8fa 0x94039c07c6e31fc7

def z558 : W := mkw 0x0000000004001080 0x0000000000200084 0x80000000dc0078fa 0x8400000006e003c7

def z559 : W := mkw 0x9ba78bc31bafc364 0x4cdd3c5e18dd7e1b 0xbf8f9fc73fffc7f7 0xbdfc7cfe39fffe3f

def z560 : W := mkw 0x61dddbefe0746d01 0x1b0eeedf7f03a368 0x63ffffffe07c7f1d 0xfb1fffffff03e3f8

def z561 : W := mkw 0x81858bc201a9c260 0x0c0c2c5e100d4e13 0x838387c003e3c0f3 0xbc1c1c3e001f1e07

def z562 : W := mkw 0x7bff5a00fbdb264c 0x63dffad007ded932 0xffff9800ffff8705 0xf7fffcc007fffc38

def z563 : W := mkw 0x097f81fe4862c822 0xd84bfc0ff2431641 0x007f80ff00638000 0x1003fc07f8031c00

def z564 : W := mkw 0x7b7f0000fb5b0004 0x43dbf80007dad800 0xdff38000df838000 0x66ff9c0006fc1c00

def z565 : W := mkw 0x81858bc3b7adf7e8 0x0c0c2c5e1dbd6fbf 0xa38f9fc7ffffffff 0xbd1c7cfe3fffffff

def z566 : W := mkw 0x014d002600000002 0x580a680130000000 0x000c000700000000 0x0000600038000000

def z567 : W := mkw 0x6c7aa5d8ec72d8a0 0x8363d52ec76396c5 0xfc7fe7f8fc7ff8fb 0xffe3ff3fc7e3ffc7

def z568 : W := mkw 0x7fff7e6dffff7fcd 0x73fffbf36ffffbfe 0xffffffffffffffff 0xffffffffffffffff

def z569 : W := mkw 0x9fa7afd301adc362 0x6cfd3d7e980d6e1b 0xbf8f9fc723ffc7f7 0xbdfc7cfe391ffe3f

def z570 : W := mkw 0x6058506de0746d01 0x1302c2836f03a368 0x40706038e07c7f1c 0xc2038301c703e3f8

def z571 : W := mkw 0x00000000168012c8 0x0000000000b40096 0x800000001f8000e2 0x0400000000fc0007

def z572 : W := mkw 0x0000004900246d01 0x0000000248012368 0x0000000000007f1c 0x00000000000003f8

def z573 : W := mkw 0x0c3224584c625880 0x80619122c26312c4 0x5c7060f8dc607819 0xdae38307c6e303c0

def z574 : W := mkw 0x6058006de0744901 0x1302c0036f03a248 0x607c00ffe07c0001 0xd303e007ff03e000

def z575 : W := mkw 0x00000000b6003488 0x0000000005b001a4 0x00000000dc003808 0x0000000006e001c0

def z576 : W := mkw 0x64d8ffffe0746d03 0x3b26c7ffff03a368 0x607c7fffe07c7f1d 0xdb03e3ffff03e3f8

def z577 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000180020004715 0x890000c001000238

def z578 : W := mkw 0xf7ddffeff7fdffe9 0x3fbeefff7fbfefff 0xffffffffffffffff 0xffffffffffffffff

def z579 : W := mkw 0xffeffff700a4c362 0x7fff7fffb805261b 0x7fffffff000047f7 0x7bfffffff800023f

def z580 : W := mkw 0x7fff2e00ffdb12cc 0x63fff97007fed896 0xffff8700ffff80e3 0xf7fffc3807fffc07

def z581 : W := mkw 0x6058506df6f47fc9 0x1302c2836fb7a3fe 0xe07c78fffffc7fff 0xdf03e3c7ffffe3ff

def z582 : W := mkw 0x6058506ce0706c01 0x1302c28367038360 0x407060f8c0607819 0xda038307c60303c0

def z583 : W := mkw 0x89b78bc349efc360 0x0c4dbc5e1a4f7e1b 0xffff9fc7ffffc7f7 0xfffffcfe3ffffe3f

def z584 : W := mkw 0x77cd7e26b68036ca 0x7bbe6bf135b401b6 0xff8c7f07ff807fff 0xeffc63f83ffc03ff

def z585 : W := mkw 0x6058502de0542d01 0x1302c2816f02a168 0x607c783fe01c3f0c 0x4303e3c1ff00e1f8

def z586 : W := mkw 0x72805a0000000000 0x239402d000000000 0x2380180000000000 0x011c00c000000000

def z587 : W := mkw 0x00000000b3190004 0x000000000598c800 0x00000000239c0000 0x00000000011ce000

def z588 : W := mkw 0x16802e00168012c8 0x20b4017000b40096 0xdf806700df8078fb 0xeefc033806fc03c7

def z589 : W := mkw 0x81050003010d0100 0x0c08280018086808 0x000c0007001c0000 0x000060003800e000

def z590 : W := mkw 0x7fef7e0000000000 0x63ff7bf000000000 0x7fffff0000000001 0x7bfffff800000000

def z591 : W := mkw 0x687ad1fde876ed21 0x9343d68fef43b769 0x607ff8ffe07fff1d 0xdb03ffc7ff03fff8

def z592 : W := mkw 0x60485025a0142501 0x130242812d00a128 0x607c78ff201c0705 0x5b03e3c7f900e038

def z593 : W := mkw 0x76807e0000800240 0x23b403f000040012 0xff807f00238047f7 0xeffc03f8011c023f

def z594 : W := mkw 0x6058502ce0502c01 0x1302c28167028160 0x607c78ffc0003809 0x5b03e3c7fe0001c0

def z595 : W := mkw 0x0010000048420000 0x0000800002421000 0x80000000dc638000 0x8400000006e31c00

def z596 : W := mkw 0x7ffffffeff7bd8a6 0xfbfffffff7fbdec5 0xfffffffffffff8fb 0xffffffffffffffc7

def z597 : W := mkw 0x0010000840400800 0x0000800042020040 0x40706038c0003808 0x42038301c60001c0

def z598 : W := mkw 0x73cd5a27a0142503 0x7b9e6ad13d00a128 0x238c1807201c0704 0x011c60c03900e038

def z599 : W := mkw 0x7fffffb6495b0006 0x7bfffffdb24ad800 0x7fffffff007f8001 0x7bfffffff803fc00

def z600 : W := mkw 0x7b7f0000fb5b0004 0x43dbf80007dad800 0x5c7f8000dc7f8000 0x52e3fc0006e3fc00

def z601 : W := mkw 0x80808bc301adc360 0x0c04045e180d6e1b 0x80001fc723ffc7f6 0x8c0000fe391ffe3f

def z602 : W := mkw 0x01858bc300244100 0x080c2c5e18012208 0x238f9fc7207c4715 0xb91c7cfe3903e238

def z603 : W := mkw 0x7e7af5fc4c62d8a2 0xf3f3d7afe26316c5 0xdc73e7f8dc63f8fb 0xfee39f3fc6e31fc7

def z604 : W := mkw 0x0410a5d84c62d8a0 0x8020852ec26316c5 0x800067f8dc63f8fa 0x8c00033fc6e31fc7

def z605 : W := mkw 0x0400a5d80420d8a0 0x8020052ec02106c5 0x8003e7f80063f8fb 0xbc001f3fc0031fc7

def z606 : W := mkw 0x81850a4301ad4340 0x0c0c2852180d6a1a 0x238c18c723fc4715 0x991c60c6391fe238

def z607 : W := mkw 0x7e327418fe423c88 0xa3f193a0c7f211e4 0x5c706038dc003808 0x42e38301c6e001c0

def z608 : W := mkw 0x7ffffffe4862c822 0xfbfffffff2431641 0x7fffffff00638001 0x7bfffffff8031c00

def z609 : W := mkw 0xf785ff82b789b6e8 0x2fbc2ffc15bc4db7 0xff83ff00ff83ffff 0xeffc1ff807fc1fff

def z610 : W := mkw 0x9785af82178992e8 0x2cbc2d7c10bc4c97 0x9f8387001f8380e2 0x24fc1c3800fc1c07

def z611 : W := mkw 0x0c22a5d00020c020 0x0061152e80010601 0xdc73e7f80063c0f3 0xfee39f3fc0031e07

def z612 : W := mkw 0x7ea2ff90be82b6e8 0xa3f517fc85f415b7 0xff83ff00ff83ffff 0xeffc1ff807fc1fff

def z613 : W := mkw 0x7f7f2400ff5b1084 0x43fbf92007fad884 0xffffe700fffff8fb 0xffffff3807ffffc7

def z614 : W := mkw 0x77857e00b78936c8 0x23bc2bf005bc49b6 0xff8fff00ffffffff 0xfffc7ff807ffffff

def z615 : W := mkw 0x76907e48f6e07ec8 0x23b483f247b703f6 0xfff07ff8ffe07fff 0xffff83ffc7ff03ff

def z616 : W := mkw 0x0000502500042501 0x1000028128002128 0x0000180700000704 0x000000c038000038

def z617 : W := mkw 0x083281d84862c820 0x8041940ec2431641 0x807387f80063c0f3 0xbc039c3fc0031e07

def z618 : W := mkw 0x7fffffb6fa520006 0x7bfffffdb7d29000 0x7fffffffdc000001 0x7bfffffffee00000

def z619 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000700000040f3 0xac00003800000207

def z620 : W := mkw 0x0010004840604800 0x0000800242030240 0x007000f800600000 0x10038007c0030000

def z621 : W := mkw 0x81858bc301adc360 0x0c0c2c5e180d6e1b 0x238f98c723ff8704 0x111c7cc6391ffc38

def z622 : W := mkw 0x81850a03018d0340 0x0c0c2850180c681a 0xa38f980723ff8705 0xb51c7cc0391ffc38

def z623 : W := mkw 0x000000001b0b0004 0x0000000000d85800 0x800000001f838000 0x0400000000fc1c00

def z624 : W := mkw 0x0400f5fd0424fda1 0x902007afe82127ed 0x00007fff00007ffe 0x080003fff80003ff

def z625 : W := mkw 0x001000084c421880 0x80008000426210c4 0x00000000dc003808 0x0000000006e001c0

def z626 : W := mkw 0x72805a00b2802648 0x239402d005940132 0xff801800ff800705 0xe7fc00c007fc0038

def z627 : W := mkw 0x7680ffc0b6a0f6e8 0x23b407fe05b507b7 0xff83ffc0ffe3ffff 0xfffc1ffe07ff1fff

def z628 : W := mkw 0x00805a2600000002 0x380402d130000000 0x0000180700000000 0x000000c038000000

def z629 : W := mkw 0x7b7f0000fb5b0004 0x43dbf80007dad800 0x7ffc0000ff9c0000 0x43ffe00007fce000

def z630 : W := mkw 0x72c85a25b2942749 0x339642d12d94a13a 0x238c1807239c0704 0x011c60c0391ce038

def z631 : W := mkw 0x0c22a5d00c22d0a0 0x8061152e80611685 0x9c0387c01c63c0f3 0xbce01c3e00e31e07

def z632 : W := mkw 0x6458746de4747d81 0x1322c3a36f23a3ec 0xfc7c7ffffc7c7fff 0xffe3e3ffffe3e3ff

def z633 : W := mkw 0x6458f5fde474fda1 0x9322c7afef23a7ed 0x607c7fffe07c7fff 0xdb03e3ffff03e3ff

def z634 : W := mkw 0x00800a4100a44340 0x000400520805221a 0xa38c1fc723fc47f7 0xbd1c60fe391fe23f

def z635 : W := mkw 0x1f27a5901f0b90a4 0xc0f93d2c80f85c85 0x9f8387001f8380e2 0x24fc1c3800fc1c07

def z636 : W := mkw 0x0480af9200000002 0x2824057c90000000 0x0000070000000000 0x0000003800000000

def z637 : W := mkw 0x1ea2af901e8292e8 0xa0f5157c80f41497 0x9f8387001f8380e2 0x24fc1c3800fc1c07

def z638 : W := mkw 0x0480fffe0420d8a2 0xb82407fff02106c5 0x00007fff000078fa 0x080003fff80003c7

def z639 : W := mkw 0x7fffffff40744903 0x7bfffffffa03a248 0x7fffffff007c0001 0x7bfffffff803e000

def z640 : W := mkw 0x76907e48fee2fee8 0xa3b483f247f717f7 0xff807f00ffe3ffff 0xeffc03f807ff1fff

def z641 : W := mkw 0x76007400b6003488 0x23b003a005b001a4 0xff806000ff803809 0xe7fc030007fc01c0

def z642 : W := mkw 0x7658746df6747d89 0x33b2c3a36fb3a3ec 0x7c7c78fffc7c7f1d 0xdbe3e3c7ffe3e3f8

def z643 : W := mkw 0xe15dd1efe17ded21 0x1f0aee8f7f0bef69 0x607ff8ffe07fff1d 0xdb03ffc7ff03fff8

def z644 : W := mkw 0x76807e00b68036c8 0x23b403f005b401b6 0x5c007f00dc007ffe 0x4ae003f806e003ff

def z645 : W := mkw 0x81850a0201890240 0x0c0c2850100c4812 0x0380000003800000 0x001c0000001c0000

def z646 : W := mkw 0x734d5025b31d2505 0x539a6a812d98e928 0x238c1807239c0704 0x011c60c0391ce038

def z647 : W := mkw 0x04807e00b68036c8 0x202403f005b401b6 0x80007f00ff807ffe 0x8c0003f807fc03ff

def z648 : W := mkw 0x60580000e0500000 0x0302c00007028000 0x40700000c0000000 0x4203800006000000

def z649 : W := mkw 0x7ffffffe40604802 0x7bfffffff2030240 0x7fffffffc0607819 0xfbfffffffe0303c0

def z650 : W := mkw 0x800081c101adc360 0x0400040e080d6e1b 0x800387c023ffc7f7 0xbc001c3e011ffe3f

def z651 : W := mkw 0x7e7a743ce0502c03 0x73f3d3a1e7028160 0x5c706038c0003808 0x42e38301c60001c0

def z652 : W := mkw 0x76807e41b6a477c8 0x23b403f20db523be 0xff8c7fc7fffc7fff 0xfffc63fe3fffe3ff

def z653 : W := mkw 0x8585afc305add3e0 0x0c2c2d7e182d6e9f 0xff8fffc7ffffffff 0xfffc7ffe3fffffff

def z654 : W := mkw 0x01050041012d4100 0x0008280208096a08 0xa38f98c723ffc715 0xbd1c7cc6391ffe38

def z655 : W := mkw 0x7b7f81b6fb5b0006 0x5bdbfc0db7dad800 0xffff80ffffff8001 0xf7fffc07fffffc00

def z656 : W := mkw 0x1305000013090004 0x4098280000984800 0x0380000003800000 0x001c0000001c0000

def z657 : W := mkw 0x097f0000fb5b0004 0x404bf80007dad800 0x807f8000ffff8000 0x9403fc0007fffc00

def z658 : W := mkw 0x00100049e0746d01 0x000080024f03a368 0x407060f8e07c7f1d 0xda038307c703e3f8

def z659 : W := mkw 0x1eb2afd85ee2dae8 0xa0f5957ec2f716d7 0xdff3e7f8dfe3f8fb 0xfeff9f3fc6ff1fc7

def z660 : W := mkw 0x7fefaf9200000002 0x6bff7d7c90000000 0x7fff870000000001 0x73fffc3800000000

def z661 : W := mkw 0x8000000001898260 0x04000000000c4c13 0x80000000038380e2 0x04000000001c1c07

def z662 : W := mkw 0x00800a0000800240 0x0004005000040012 0x2380180023800704 0x011c00c0011c0038

def z663 : W := mkw 0x810581c3012dc120 0x0c082c0e18096e09 0xa38f80c723ff8001 0xb51c7c06391ffc00

def z664 : W := mkw 0x7f7ff5fdff7ffda5 0xd3fbffafeffbffed 0xffffffffffffffff 0xffffffffffffffff

def z665 : W := mkw 0x60005000a0002400 0x0300028005000120 0x2000180020000704 0x010000c001000038

def z666 : W := mkw 0x7bff5a26fb5b0006 0x7bdffad137dad800 0xffff9807ffff8001 0xf7fffcc03ffffc00

def z667 : W := mkw 0x0c32a5904c4290a0 0x8061952c82621485 0xdc738700dc6380e3 0xf6e39c3806e31c07

def z668 : W := mkw 0x8db7afda4debdae0 0x8c6dbd7ed26f5ed7 0xdff3e7f8dfe3f8fb 0xfeff9f3fc6ff1fc7

def z669 : W := mkw 0x0c32a5d84862c820 0x8061952ec2431641 0x5c73e7f800638001 0x7ae39f3fc0031c00

def z670 : W := mkw 0x0822819008028020 0x8041140c80401401 0x0003800000038000 0x00001c0000001c00

def z671 : W := mkw 0x60805a00a0802640 0x030402d005040132 0xe3807f00e3807fff 0xef1c03f8071c03ff

def z672 : W := mkw 0x00100000fa520004 0x0000800007d29000 0x00000000dc000000 0x0000000006e00000

def z673 : W := mkw 0x0400a5d80420d8a0 0x8020052ec02106c5 0xdc0067f8dc0078fb 0xeee0033fc6e003c7

def z674 : W := mkw 0x7fffffffec76fda3 0xfbffffffff63b7ed 0xfffffffffc7fffff 0xffffffffffe3ffff

def z675 : W := mkw 0x80808bc300a4c360 0x0c04045e1805261b 0x200c1fc7207c47f7 0x990060fe3903e23f

def z676 : W := mkw 0x01858b8200000000 0x080c2c5c10000000 0x0383870000000000 0x201c1c3800000000

def z677 : W := mkw 0x7a7a506dfa766d05 0x53d3d2836fd3b368 0x7c7c78fffc7c7f1d 0xdbe3e3c7ffe3e3f8

def z678 : W := mkw 0x6058506de0746d01 0x1302c2836f03a368 0x207c18ff207c0704 0x1103e0c7f903e038

def z679 : W := mkw 0xffffffff4defdbe2 0xfffffffffa6f7edf 0xffffffffffffffff 0xffffffffffffffff

def z680 : W := mkw 0x0c22a59000000000 0x0061152c80000000 0x1c03870000000000 0x20e01c3800000000

def z681 : W := mkw 0x77cd7e2600000002 0x7bbe6bf130000000 0x7f8c7f0700000001 0x6bfc63f838000000

def z682 : W := mkw 0xf3cd8bc3b3bdc364 0x4f9e6c5e1d9dee1b 0xa38f9fc723ffc7f7 0xbd1c7cfe391ffe3f

def z683 : W := mkw 0x64807e00a48036c8 0x232403f0052401b6 0x60007f00e0007fff 0xcb0003f8070003ff

def z684 : W := mkw 0x72805a00b2802648 0x239402d005940132 0x63807800e3807f1d 0xcb1c03c0071c03f8

def z685 : W := mkw 0x001081c84060c820 0x0000840e42030641 0xc073e7f8c063f8fb 0xfe039f3fc6031fc7

def z686 : W := mkw 0x0058006d40744901 0x1002c0036a03a248 0x207c18ff207c4715 0x9903e0c7f903e238

def z687 : W := mkw 0x6048506da0346d01 0x130242836d01a368 0x200c78ff201c7f1c 0x090063c7f900e3f8

def z688 : W := mkw 0x60585025e0542501 0x1302c2812f02a128 0x607c1807e07c0705 0xd303e0c03f03e038

def z689 : W := mkw 0x7fffffbee0502c03 0x7bfffffdf7028160 0x7fffffffc0003809 0x7bfffffffe0001c0

def z690 : W := mkw 0xfbffdbeffbffef65 0x5fdffedf7fdfff7b 0xffffffffffffffff 0xffffffffffffffff

def z691 : W := mkw 0x7b7f0041fb7f4104 0x43dbf8020fdbfa08 0xffff98c7ffffc715 0xfffffcc63ffffe38

def z692 : W := mkw 0x087a000048520004 0x4043d00002429000 0x0070000000000000 0x0003800000000000

def z693 : W := mkw 0x16807e00168036c8 0x20b403f000b401b6 0x9f807f001f807ffe 0x2cfc03f800fc03ff

def z694 : W := mkw 0x6058506d40744901 0x1302c2836a03a248 0x607c78ff007c0001 0x5b03e3c7f803e000

def z695 : W := mkw 0x0c32a59048420000 0x0061952c82421000 0xdc73e7f8dc638001 0xfee39f3fc6e31c00

def z696 : W := mkw 0x097f81b6495b0006 0x584bfc0db24ad800 0x007f80ff007f8000 0x1003fc07f803fc00

def z697 : W := mkw 0x60485025a0142501 0x130242812d00a128 0x600c7807e01c7f1d 0xcb0063c03f00e3f8

def z698 : W := mkw 0xffffffffe1fdef63 0x7fffffffff0fef7b 0xffffffffe3ffffff 0xffffffffff1fffff

def z699 : W := mkw 0x7a7a0000fa520004 0x43d3d00007d29000 0x7c7c0000fc7c0001 0xd3e3e00007e3e000

def z700 : W := mkw 0x7e7a747de0746d03 0x73f3d3a3ef03a368 0x7c7c78ffe07c7f1d 0xdbe3e3c7ff03e3f8

def z701 : W := mkw 0x0400a5c00420d0a0 0x0020052e00210685 0xdc03e7c0dc63f8fb 0xfee01f3e06e31fc7

def z702 : W := mkw 0x60485024a0102401 0x1302428125008120 0x0000000000000000 0x0000000000000000

def z703 : W := mkw 0xe1dd8bc3e1fdc360 0x0f0eec5e1f0fee1b 0xe3ff9fc7e3ffc7f7 0xff1ffcfe3f1ffe3f

def z704 : W := mkw 0x7eb2ffd84c62d8a0 0xa3f597fec26316c5 0xfff3fff8dc63f8fb 0xffff9fffc6e31fc7

def z705 : W := mkw 0x00800a0000800240 0x0004005000040012 0x83800700038000e2 0x241c0038001c0007

def z706 : W := mkw 0x8080dbef00a4ef61 0x1c0406df7805277b 0x00007fff00007ffe 0x080003fff80003ff

def z707 : W := mkw 0x7258506df2746d09 0x3392c2836f93a368 0x607c78ffe07c7f1d 0xdb03e3c7ff03e3f8

def z708 : W := mkw 0x76c8ffb600000002 0x3bb647fdb0000000 0x7ffc7fff00000001 0x7bffe3fff8000000

def z709 : W := mkw 0x1b27506d1b2f6d05 0x50d93a8368d97b68 0x9f83f8ff1f83ff1c 0x2cfc1fc7f8fc1ff8

def z710 : W := mkw 0x01150049e17d6d01 0x0008a8024f0beb68 0xa38f8000e3ffff1d 0xb51c7c00071ffff8

def z711 : W := mkw 0x7fa7ff92b68036c8 0x2bfd3ffc95b401b6 0xffffffffff807fff 0xfffffffffffc03ff

def z712 : W := mkw 0x73dd5a6e4c62d8a2 0xfb9eead3726316c5 0xa38c1807dc63f8fa 0x851c60c03ee31fc7

def z713 : W := mkw 0x0c32a5984c4298a0 0x8061952cc26214c5 0xdc73e738dc03f8fb 0xeee39f39c6e01fc7

def z714 : W := mkw 0x80100049417dc921 0x040080024a0bee49 0x00000000007f8000 0x000000000003fc00

def z715 : W := mkw 0x096f81b6b68036ca 0x584b7c0db5b401b6 0x807f80ffff807ffe 0x9403fc07fffc03ff

def z716 : W := mkw 0x61cd5a2600000000 0x1b0e6ad130000000 0x63fc78ff00000001 0x5b1fe3c7f8000000

def z717 : W := mkw 0x7fefffb600002402 0x7bff7ffdb0000120 0x7fffffff00007f1d 0x7bfffffff80003f8

def z718 : W := mkw 0x0c22a5900c0290a0 0x8061152c80601485 0xdc73e7f8dc03f8fb 0xfee39f3fc6e01fc7

def z719 : W := mkw 0x60485024a0102401 0x1302428125008120 0x607c78ff00000001 0x5b03e3c7f8000000

def z720 : W := mkw 0x00100049e0f46f41 0x000080024f07a37a 0x80000000e3fc7ffe 0x84000000071fe3ff

def z721 : W := mkw 0x7fefffb61e8292ea 0xfbff7ffdb0f41497 0xffffffff1f8380e3 0x7ffffffff8fc1c07

def z722 : W := mkw 0x76807e00048012c0 0x23b403f000240096 0xff807f00ff807fff 0xeffc03f807fc03ff

def z723 : W := mkw 0x0dff7e004ddb36cc 0x606ffbf0026ed9b6 0x007fff00007ffffe 0x1803fff80003ffff

def z724 : W := mkw 0x1b2700001b0b0004 0x40d9380000d85800 0x9f8f80001fff8000 0x34fc7c0000fffc00

def z725 : W := mkw 0x7b7f0024fb5b0004 0x53dbf80127dad800 0xffff80ffffff8001 0xf7fffc07fffffc00

def z726 : W := mkw 0x7fefffb6b600348a 0x7bff7ffdb5b001a4 0x7ffffffffc007f1d 0xfbffffffffe003f8

def z727 : W := mkw 0x7eeaffb6b68036ca 0x7bf757fdb5b401b6 0xfff07fffff807fff 0xefff83fffffc03ff

def z728 : W := mkw 0x7f6fa5b600000002 0x5bfb7d2db0000000 0x7fffe7ff00000001 0x7bffff3ff8000000

def z729 : W := mkw 0x7fefffb6b200240a 0x7bff7ffdb5900120 0x7fffffff00000001 0x7bfffffff8000000

def z730 : W := mkw 0x84902e494defdbe0 0x842481724a6f7edf 0xff807f00ffffffff 0xeffc03f807ffffff

def z731 : W := mkw 0x1fb7afdbe0746d03 0x68fdbd7edf03a368 0x1f838700e07c7f1c 0xa0fc1c380703e3f8

def z732 : W := mkw 0x0c32a5d84c62d8a0 0x8061952ec26316c5 0xdc73e7f8dc03f8fa 0x6ee39f3fc6e01fc7

def z733 : W := mkw 0xe1dddbaee1d9ae61 0x1f0eeedd770ecd73 0xc3f3e738c383b8ea 0x661f9f39c61c1dc7

def z734 : W := mkw 0x0d6fa5b60c0290a2 0xd86b7d2db0601485 0x9c7f87ff1c0380e2 0x34e3fc3ff8e01c07

def z735 : W := mkw 0x7fefffb601090002 0x7bff7ffdb0084800 0x7fffffff239c0001 0x7bfffffff91ce000

def z736 : W := mkw 0x76c8ffb6b68036ca 0x3bb647fdb5b401b6 0xfffc7fffff807fff 0xffffe3fffffc03ff

def z737 : W := mkw 0x7fefffb600800242 0x7bff7ffdb0040012 0x7fffffff000047f7 0x7bfffffff800023f

def z738 : W := mkw 0x7fefffb6b68036ca 0x7bff7ffdb5b401b6 0x7fffffffdc007fff 0x7bfffffffee003ff

def z739 : W := mkw 0x0c32a5d84c62d8a0 0x8061952ec26316c5 0xfc73fff8fc63ffff 0xffe39fffc7e31fff

def z740 : W := mkw 0x72905a49f2f46f49 0x239482d24f97a37a 0x23801800e3fc7f1c 0x811c00c0071fe3f8

def z741 : W := mkw 0x7ab2dbd8fae2ee68 0xa3d596dec7d71773 0x23f398f823e38704 0x111f9cc7c11f1c38

def z742 : W := mkw 0x00100049e0746d01 0x000080024f03a368 0x607c78ffe07c7f1d 0xdb03e3c7ff03e3f8

def z743 : W := mkw 0xf3cd5a27b38d274a 0x7f9e6ad13d9c693a 0x238c1807239c0704 0x011c60c0391ce038

def z744 : W := mkw 0x81858b83018d8360 0x0c0c2c5c180c6c1b 0xa38f9f0723ff87e7 0xb51c7cf8391ffc3f

def z745 : W := mkw 0x76007400b6003480 0x03b003a005b001a4 0xff807f00ff807fff 0xeffc03f807fc03ff

def z746 : W := mkw 0x76c87e24b69036c9 0x33b643f125b481b6 0xff807f00ff807fff 0xeffc03f807fc03ff

def z747 : W := mkw 0x1bef8bb600000002 0x78df7c5db0000000 0x03ff80ff00000000 0x101ffc07f8000000

def z748 : W := mkw 0x7a320000fb5b0004 0x03d1900007dad800 0xfff38000ffff8001 0xf7ff9c0007fffc00

def z749 : W := mkw 0x7b6f50241b0b0004 0x53db7a8120d85800 0xfffff8ff1f838001 0x7fffffc7f8fc1c00

def z750 : W := mkw 0x7fefffb6b399264e 0x7bff7ffdb59cc932 0x7fffffff239c0705 0x7bfffffff91ce038

def z751 : W := mkw 0x8db72e1b4dcf1bc0 0x8c6db970da6e78de 0x7ffc783fff9c3f0c 0x43ffe3c1fffce1f8

def z752 : W := mkw 0x8480afc304a4d3e8 0x2c24057e1825269f 0x00001fc7000047f6 0x080000fe3800023f

def z753 : W := mkw 0x60485065a0246500 0x130242832d012328 0x607c78ffe07c7f1d 0xdb03e3c7ff03e3f8

def z754 : W := mkw 0x00100049e97f6d05 0x000080024f4bfb68 0x00000000e07fff1c 0x800000000703fff8

def z755 : W := mkw 0x72480000b2000000 0x0392400005900000 0xfffc0000ff800001 0xf7ffe00007fc0000

def z756 : W := mkw 0x8480ffff04a4ffe1 0x9c2407fff82527ff 0x00007fff00007ffe 0x080003fff80003ff

def z757 : W := mkw 0x6058506de0746d01 0x1302c2836f03a368 0x607c78ffe01c7f1c 0x4b03e3c7ff00e3f8

def z758 : W := mkw 0x73150000fb5b0004 0x0398a80007dad800 0xff8f8000ffff8001 0xf7fc7c0007fffc00

def z759 : W := mkw 0x774da5d8b739d8a4 0xc3ba6d2ec5b9cec5 0x238c67f8239c78fa 0x091c633fc11ce3c7

def z760 : W := mkw 0x7b7f0026fb5b0006 0x5bdbf80137dad800 0xffff8007ffff8001 0xf7fffc003ffffc00

def z761 : W := mkw 0x00100049e0746d01 0x000080024f03a368 0x40006000e07c7f1d 0xca0003000703e3f8

def z762 : W := mkw 0x686a502400000000 0x1343528120000000 0x7c7ff8ff00000001 0x7be3ffc7f8000000

def z763 : W := mkw 0x897f81db497fc924 0xcc4bfc0eda4bfe49 0x007f80ff007f8000 0x1003fc07f803fc00

def z764 : W := mkw 0x0c22a59000000000 0x0061152c80000000 0x7c7fffff00000001 0x7be3fffff8000000

def z765 : W := mkw 0x09ef8bb600000002 0x584f7c5db0000000 0x03ff87ff00000000 0x301ffc3ff8000000

def z766 : W := mkw 0x7ea2ffb600000002 0x3bf517fdb0000000 0x7ff3ffff00000001 0x7bff9ffff8000000

def z767 : W := mkw 0x096f81b600000002 0x584b7c0db0000000 0x007f87ff00000001 0x3803fc3ff8000000

def z768 : W := mkw 0x01850a4101ad4340 0x000c2852080d6a1a 0xa38f9fc723ffc7f7 0xbd1c7cfe391ffe3f

def z769 : W := mkw 0x0400240004001080 0x0020012000200084 0xdc7067f8dc0078fb 0xfee3833fc6e003c7

def z770 : W := mkw 0xf7cdffe7b7adf7e8 0x3fbe6fff3dbd6fbf 0xffffffffffffffff 0xffffffffffffffff

def z771 : W := mkw 0x72485024b2000000 0x1392428125900000 0xfffc78ffff800001 0xffffe3c7fffc0000

def z772 : W := mkw 0x7fefffb6168012ca 0x7bff7ffdb0b40096 0xffffffffdf8078fb 0xfffffffffefc03c7

def z773 : W := mkw 0x7fefffb61f0b90a6 0xfbff7ffdb0f85c85 0xffffffff1f8380e3 0x7ffffffff8fc1c07

def z774 : W := mkw 0x76002400b68036c8 0x03b0012005b401b6 0xff806700ff807fff 0xeffc033807fc03ff

def z775 : W := mkw 0x6058506d40644900 0x1302c2836a032248 0x607c78ffe07c7f1d 0xdb03e3c7ff03e3f8

def z776 : W := mkw 0x7b6fd1b600000002 0x7bdb7e8db0000000 0x007f80ff00000000 0x1003fc07f8000000

def z777 : W := mkw 0x81958bcbe1fdef61 0x0c0cac5e5f0fef7b 0x83838700e3fffffe 0xa41c1c38071fffff

def z778 : W := mkw 0x04802e00b68036c8 0x0024017005b401b6 0xff807f00ff807fff 0xeffc03f807fc03ff

def z779 : W := mkw 0x7248502400000002 0x7392428120000000 0x607c78ff00000001 0x5b03e3c7f8000000

def z780 : W := mkw 0xffefffb601898262 0x7fff7ffdb00c4c13 0xffffffff23ff80e3 0xfffffffff91ffc07

def z781 : W := mkw 0x0c32a5d94c76d9a1 0x8061952eca63b6cd 0xdc73e7f8dc7ff8fb 0xfee39f3fc6e3ffc7

def z782 : W := mkw 0x001000494876c921 0x800080024a43b649 0x00000000007f8000 0x000000000003fc00

def z783 : W := mkw 0x7fefffb6b68036ca 0x7bff7ffdb5b401b6 0x7fffffff23807fff 0x7bfffffff91c03ff

def z784 : W := mkw 0x1b7f0000fb5b0004 0x40dbf80007dad800 0x9fff8000ffff8000 0xb4fffc0007fffc00

def z785 : W := mkw 0x7b6f5024b2002400 0x53db7a8125900120 0xfffff8ffff807f1d 0xffffffc7fffc03f8

def z786 : W := mkw 0x082281b600000002 0x1841140db0000000 0x007380ff00000000 0x10039c07f8000000

def z787 : W := mkw 0x76802e00b68036c8 0x23b4017005b401b6 0xff800700ff807fff 0xe7fc003807fc03ff

def z788 : W := mkw 0x614d502401090000 0x130a6a8120084800 0xe3fff8ff23ff8001 0xff1fffc7f91ffc00

def z789 : W := mkw 0x0c32a5d84c62d8a0 0x8061952ec26316c5 0xfc7fffffdc63f8fb 0xffe3fffffee31fc7

def z790 : W := mkw 0x1fa7af921f8b12ce 0x68fd3d7c90fc5896 0x9f8387001f8380e2 0x24fc1c3800fc1c07

def z791 : W := mkw 0x0d6fa5b600000002 0x586b7d2db0000000 0x5c7fe0ff00000000 0x52e3ff07f8000000

def z792 : W := mkw 0x00808bc100a4c360 0x0004045e0805261b 0xa38f9fc723ffc7f7 0xbd1c7cfe391ffe3f

def z793 : W := mkw 0x1b370000fb5b0004 0x40d9b80007dad800 0xdff38000ffff8001 0xf6ff9c0007fffc00

def z794 : W := mkw 0xf705f5c3b72df5a8 0x2fb82fae1db96fad 0x5c0fe0c7dc7fb808 0x52e07f063ee3fdc0

def z795 : W := mkw 0x8da7af920d8b92e0 0x8c6d3d7c906c5c97 0xffffffff1f8380e3 0x7ffffffff8fc1c07

def z796 : W := mkw 0x76c87e24b68036c8 0x33b643f125b401b6 0xff8c7f07ff807fff 0xeffc63f83ffc03ff

def z797 : W := mkw 0x0c32a5d84c62d8a0 0x8061952ec26316c5 0xfff3e7f8ffe3f8fb 0xffff9f3fc7ff1fc7

def z798 : W := mkw 0x7248502400000000 0x1392428120000000 0x7ffc78ff00000001 0x7bffe3c7f8000000

def z799 : W := mkw 0x7b7f0000fb5b0004 0x43dbf80007dad800 0xffff8700ffffc0f3 0xfffffc3807fffe07

def z800 : W := mkw 0x7fefffb60080264a 0x7bff7ffdb0040132 0x7fffffff00000705 0x7bfffffff8000038

def z801 : W := mkw 0x0010004940644900 0x000080024a032248 0x00000000e07c7f1c 0x800000000703e3f8

def z802 : W := mkw 0x0c32a5d84c62d8a0 0x8061952ec26316c5 0x5c73e7f8dc63f8fa 0x5ae39f3fc6e31fc7

def z803 : W := mkw 0x6058506de876ed21 0x9302c2836f43b769 0x607c78ffe07fff1d 0xdb03e3c7ff03fff8

def z804 : W := mkw 0x6defffb600000002 0x7b6f7ffdb0000000 0x607fffff00000001 0x5b03fffff8000000

def z805 : W := mkw 0x0048502400000000 0x1002428120000000 0x007c78ff00000000 0x1803e3c7f8000000

def z806 : W := mkw 0x00100049ffff7fcd 0x000080024ffffbfe 0x80000000fffffffe 0x8400000007ffffff

def z807 : W := mkw 0x7fefffb601090002 0x7bff7ffdb0084800 0xffffffff03838001 0x7ffffffff81c1c00

def z808 : W := mkw 0x097f81fd497fc925 0xd04bfc0fea4bfe49 0x007f80ff007f8000 0x1003fc07f803fc00

def z809 : W := mkw 0x7eeaffb600000002 0x7bf757fdb0000000 0x5c73ffff00000001 0x7ae39ffff8000000

def z810 : W := mkw 0x16d82e6d56f45bc9 0x30b6c1736ab7a2de 0x9ffc07ff1ffc00e2 0x34ffe03ff8ffe007

def z811 : W := mkw 0x7fefffb608020002 0x7bff7ffdb0401000 0xffffffff1c038001 0x7ffffffff8e01c00

def z812 : W := mkw 0x6448742404001080 0x132243a120200084 0xfc7c7fffdc0078fb 0xffe3e3fffee003c7

def z813 : W := mkw 0x80100049496fc920 0x840080024a4b7e49 0x00000000007f8000 0x000000000003fc00

def z814 : W := mkw 0x0ca2af9200000000 0x0865157c90000000 0x5c73ffff00000001 0x7ae39ffff8000000

def z815 : W := mkw 0x696fd1b6a0002402 0x5b4b7e8db5000120 0x607ff8ffe0007f1d 0xdb03ffc7ff0003f8

def z816 : W := mkw 0x73cd5a2600000002 0x7b9e6ad130000000 0x23fc18ff00000000 0x111fe0c7f8000000

def z817 : W := mkw 0x7b270000bb0b0004 0x43d9380005d85800 0xff8f8000ffff8001 0xf7fc7c0007fffc00

def z818 : W := mkw 0x7fefffb601190006 0x7bff7ffdb008c800 0x7fffffff001c0001 0x7bfffffff800e000

def z819 : W := mkw 0x76907e49ffff7fcd 0x23b483f24ffffbfe 0xff807f00ffffffff 0xeffc03f807ffffff

def z820 : W := mkw 0x7fefffb601090002 0x7bff7ffdb0084800 0x7fffffff007f8001 0x7bfffffff803fc00

def z821 : W := mkw 0xf3cd5a27b39d2749 0x3f9e6ad13d9ce93a 0x238c1807239c0704 0x011c60c0391ce038

def z822 : W := mkw 0x09ef8bb600000002 0x584f7c5db0000000 0x007f9fff00000000 0x1803fcfff8000000

def z823 : W := mkw 0x1305000013090000 0x0098280000984800 0xbf8f80003fff8001 0xb5fc7c0001fffc00

def z824 : W := mkw 0x7fefffb6a48036ca 0x7bff7ffdb52401b6 0x7fffffffe0007fff 0xfbffffffff0003ff

def z825 : W := mkw 0x7b7f5024fb5b0004 0x53dbfa8127dad800 0xffffe038ffff8001 0xf7ffff01c7fffc00

def z826 : W := mkw 0x7eeaffb600000002 0x7bf757fdb0000000 0x7c7c7fff00000001 0x5be3e3fff8000000

def z827 : W := mkw 0x76907e49e0746d01 0x23b483f24f03a368 0x7f807f00e07c7f1d 0xebfc03f80703e3f8

def z828 : W := mkw 0x7b6f0000b3090000 0x43db780005984800 0xffff8000ffff8001 0xf7fffc0007fffc00

def z829 : W := mkw 0x7eeaffb4b68036c8 0x33f757fda5b401b6 0xffffffffff807fff 0xfffffffffffc03ff

def z830 : W := mkw 0x00100049e0746d01 0x000080024f03a368 0x00000000207c0704 0x000000000103e038

def z831 : W := mkw 0x00100049f2746d01 0x000080024f93a368 0x80000000fffc7f1c 0x8400000007ffe3f8

def z832 : W := mkw 0x1b3700005b4b0004 0x40d9b80002da5800 0xffff8000ffff8001 0xf7fffc0007fffc00

def z833 : W := mkw 0x09370000fb5b0004 0x0049b80007dad800 0xffff8000ffff8001 0xf7fffc0007fffc00

def z834 : W := mkw 0x16802e00b68036c8 0x20b4017005b401b6 0xdf806700ff807fff 0xeefc033807fc03ff

def z835 : W := mkw 0x8480afd304a4d3e0 0x8c24057e9825269f 0x00001fc7000047f6 0x080000fe3800023f

def z836 : W := mkw 0x7e7a743cfe523c89 0xb3f3d3a1e7f291e4 0x5c706038dc003808 0x42e38301c6e001c0

def z837 : W := mkw 0x7b7f0000fb5b0004 0x43dbf80007dad800 0x7fff8000ffff8000 0x53fffc0007fffc00

def z838 : W := mkw 0x0c32a5d94c66d9a0 0x8061952eca6336cd 0xdc73ffffdc63ffff 0xfee39ffffee31fff

def z839 : W := mkw 0x7fefffb6b2000002 0x7bff7ffdb5900000 0x7fffffffdc000001 0x7bfffffffee00000

def z840 : W := mkw 0x0c22a5b600000002 0x1861152db0000000 0x5c73e7ff00000001 0x7ae39f3ff8000000

def z841 : W := mkw 0x6058506de8766d01 0x1302c2836f43b368 0xe07c78fffc7fff1d 0xdf03e3c7ffe3fff8

def z842 : W := mkw 0x09efdbb600000002 0x784f7eddb0000000 0x007f98ff00000000 0x1003fcc7f8000000

def z843 : W := mkw 0x096f81b601090002 0x584b7c0db0084800 0xa3ff80ff23ff8001 0xb51ffc07f91ffc00

def z844 : W := mkw 0x7fefffb600008022 0x7bff7ffdb0000401 0xffffffff000380e3 0x7ffffffff8001c07

def z845 : W := mkw 0x7e6af5b600000002 0x7bf357adb0000000 0x5c7060ff00000000 0x42e38307f8000000

def z846 : W := mkw 0x7fefffb6a4003482 0x7bff7ffdb52001a4 0xfffffffffc007fff 0xffffffffffe003ff

def z847 : W := mkw 0x1fa7af9200000002 0x68fd3d7c90000000 0x7fffffff00000001 0x7bfffffff8000000

def z848 : W := mkw 0x7eea7e3400000002 0x73f753f1a0000000 0x7ffc7fff00000001 0x7bffe3fff8000000

def z849 : W := mkw 0x64c8ffb600000002 0x3b2647fdb0000000 0x40707fff00000000 0x4a0383fff8000000

def z850 : W := mkw 0x6048502400002400 0x1302428120000120 0x607c78ff00007f1d 0x5b03e3c7f80003f8

def z851 : W := mkw 0x096f81b601090002 0x584b7c0db0084800 0x007f80ff007f8000 0x1003fc07f803fc00

def z852 : W := mkw 0x60485025a0142501 0x130242812d00a128 0x607c78ffe01c7f1d 0xdb03e3c7ff00e3f8

def z853 : W := mkw 0x65cdffb600000002 0x3b2e6ffdb0000000 0x63ffffff00000001 0x7b1ffffff8000000

def z854 : W := mkw 0x0490ffb6fb5b0006 0x382487fdb7dad800 0x80007fffffff8000 0x8c0003fffffffc00

def z855 : W := mkw 0x7fefffb604001082 0x7bff7ffdb0200084 0x7fffffff000078fb 0x7bfffffff80003c7

def z856 : W := mkw 0x8480ffef04a4ffe9 0x3c2407ff782527ff 0x00007fff00007ffe 0x080003fff80003ff

def z857 : W := mkw 0x7e6a7434b600348a 0x73f353a1a5b001a4 0x7c7c78fffc007f1d 0xdbe3e3c7ffe003f8

def z858 : W := mkw 0x1b3700005b5b0004 0x40d9b80002dad800 0x9f8380001fff8000 0x24fc1c0000fffc00

def z859 : W := mkw 0x7fefffb6b3090002 0x7bff7ffdb5984800 0xffffffffffff8001 0xfffffffffffffc00

def z860 : W := mkw 0x7fef7e2400000000 0x73ff7bf120000000 0x7fffffff00000001 0x7bfffffff8000000

def z861 : W := mkw 0x80100049f7fdffe9 0x040080024fbfefff 0x80000000fffffffe 0x8400000007ffffff

def z862 : W := mkw 0x8010004941fdcb61 0x040080024a0fee5b 0x8000000023ffc7f6 0x84000000011ffe3f

def z863 : W := mkw 0x6058506df2746d01 0x1302c2836f93a368 0xe07c78fffffc7f1d 0xdf03e3c7ffffe3f8

def z864 : W := mkw 0x6048d1b600000002 0x1b02468db0000000 0x607c78ff00000001 0x5b03e3c7f8000000

def z865 : W := mkw 0x60485024a0002400 0x1302428125000120 0x607c78ffc0003809 0x5b03e3c7fe0001c0

def z866 : W := mkw 0x7fefffb6a0102403 0x7bff7ffdb5008120 0x7fffffff00000001 0x7bfffffff8000000

def z867 : W := mkw 0x083281d84862c820 0x8041940ec2431641 0x0003800000638000 0x00001c0000031c00

def z868 : W := mkw 0x76107449f6747d89 0x23b083a24fb3a3ec 0x5c006000fc7c7f1c 0xc2e0030007e3e3f8

def z869 : W := mkw 0x6048502400000000 0x1302428120000000 0x607c78ff207c0001 0xdb03e3c7f903e000

def z870 : W := mkw 0x00800a0000800240 0x0004005000040012 0xa38c1fc7238047f7 0xbd1c60fe391c023f

def z871 : W := mkw 0xfafa8bc3faf6c364 0x4fd7d45e1fd7b61b 0x5c701fc7dc0047f6 0x4ae380fe3ee0023f

def z872 : W := mkw 0x7a7a0000fa520000 0x03d3d00007d29000 0xffff8000ffff8001 0xf7fffc0007fffc00

def z873 : W := mkw 0x1b370049fb7f6d05 0x40d9b8024fdbfb68 0x9f838000ffffff1c 0xa4fc1c0007fffff8

def z874 : W := mkw 0x0c32a5904c421080 0x0061952c82621084 0xdc73e7f8dc63f8fb 0xfee39f3fc6e31fc7

def z875 : W := mkw 0x6c6af5b40c0290a0 0x936357ada0601485 0xfc7fffff1c0380e3 0x7fe3fffff8e01c07

def z876 : W := mkw 0x7b6f00001b0b0004 0x43db780000d85800 0xffff80003fff8001 0xf7fffc0001fffc00

def z877 : W := mkw 0xfe6a747501adc362 0x77f353a3a80d6e1b 0xdc70603823ffc7f6 0xc6e38301c11ffe3f

def z878 : W := mkw 0x734d0000b3190004 0x439a68000598c800 0xff8f8000ffff8001 0xf7fc7c0007fffc00

def z879 : W := mkw 0x7fefffb6b280264a 0x7bff7ffdb5940132 0xffffffff238047f7 0xfffffffff91c023f

def z880 : W := mkw 0x7fefafb600000002 0x7bff7d7db0000000 0x7fff87ff00000001 0x73fffc3ff8000000

def z881 : W := mkw 0x7b6fd1b600000002 0x5bdb7e8db0000000 0x7ffff8ff00000001 0x7bffffc7f8000000

def z882 : W := mkw 0x0defffb6048036ca 0x786f7ffdb02401b6 0x007fffff00007ffe 0x1803fffff80003ff

def z883 : W := mkw 0x7e7a7434fe52348e 0x73f3d3a1a7f291a4 0x5c706038dc003808 0x42e38301c6e001c0

def z884 : W := mkw 0x04907e49e4f47fc9 0x202483f24f27a3fe 0x00007f00e07c7ffe 0x880003f80703e3ff

def z885 : W := mkw 0x096f81b600000002 0x584b7c0db0000000 0x23ff80ff00000001 0x311ffc07f8000000

def z886 : W := mkw 0x64107449ec76fda1 0x832083a24f63b7ed 0xfc007f00fc7fffff 0xefe003f807e3ffff

def z887 : W := mkw 0x16802e00168012c8 0x20b4017000b40096 0xff807f00ff807fff 0xeffc03f807fc03ff

def z888 : W := mkw 0x00100049e876ed21 0x800080024f43b769 0x00000000e07fff1c 0x800000000703fff8

def z889 : W := mkw 0x6448743400000002 0x332243a1a0000000 0x607c78ff00000001 0x5b03e3c7f8000000

def z890 : W := mkw 0x7b370000fb5b0004 0x43d9b80007dad800 0xff838000ffff8001 0xe7fc1c0007fffc00

def z891 : W := mkw 0x00100049e17d6d01 0x000080024f0beb68 0x80000000e3ffff1c 0x84000000071ffff8

def z892 : W := mkw 0x7f6f743400000002 0x73fb7ba1a0000000 0x7ffff8ff00000001 0x7bffffc7f8000000

def z893 : W := mkw 0x7fefffb6b2000002 0x7bff7ffdb5900000 0x7fffffff23800001 0x7bfffffff91c0000

def z894 : W := mkw 0x614dd1a600000000 0x1b0a6e8d30000000 0x607ff8ff00000001 0x5b03ffc7f8000000

def z895 : W := mkw 0x7fefffb6b68036ca 0x7bff7ffdb5b401b6 0xffffffff3f8007e7 0x7ffffffff9fc003f

def z896 : W := mkw 0x04807e24048036c8 0x302403f1202401b6 0x00007fff00007ffe 0x080003fff80003ff

def z897 : W := mkw 0x16807e00b68036c8 0x20b403f005b401b6 0x9f807f00ff807ffe 0xacfc03f807fc03ff

def z898 : W := mkw 0x00100049e4f47fc9 0x000080024f27a3fe 0x00000000e07c7ffe 0x800000000703e3ff

def z899 : W := mkw 0x0c32a5d84c62d8a0 0x8061952ec26316c5 0xdc73e738dc63f8fa 0xe6e39f39c6e31fc7

def z900 : W := mkw 0x73cd5a26b399264e 0x7b9e6ad1359cc932 0x238c1807239c0704 0x011c60c0391ce038

def z901 : W := mkw 0x61cddba6a0802640 0x1b0e6edd35040132 0xe3ffffffe3807fff 0xff1fffffff1c03ff

def z902 : W := mkw 0x7fefffb600000002 0x7bff7ffdb0000000 0x7fffffff20004715 0xfbfffffff9000238

def z903 : W := mkw 0x6048506d00246d01 0x1302428368012368 0x607c78ff207c7f1d 0xdb03e3c7f903e3f8

def z904 : W := mkw 0x0c32a5984c4298a0 0x8061952cc26214c5 0xdc73e7f8dc03b8eb 0x7ee39f3fc6e01dc7

def z905 : W := mkw 0x096f81b600000002 0x584b7c0db0000000 0x5c7f80ff00000001 0x72e3fc07f8000000

def z906 : W := mkw 0x69efdbb600000002 0x5b4f7eddb0000000 0x63ffffff00000001 0x7b1ffffff8000000

def z907 : W := mkw 0x76807e00b68036c8 0x23b403f005b401b6 0xff8c7fc7ff807fff 0xfffc63fe3ffc03ff

def z908 : W := mkw 0x7258506de0746d01 0x1392c2836f03a368 0x7ffc78ffe07c7f1d 0xfbffe3c7ff03e3f8

def z909 : W := mkw 0x0058506d40746d01 0x1002c2836a03a368 0x207c78ff207c7f1d 0x9903e3c7f903e3f8

def z910 : W := mkw 0x0c22a5d00420d0a0 0x0061152e80210685 0xdc73e7f8dc63f8fb 0xfee39f3fc6e31fc7

def z911 : W := mkw 0x8010004941edcb60 0x040080024a0f6e5b 0x80000000e3fffffe 0x84000000071fffff

def z912 : W := mkw 0x09270000090b0000 0x0049380000485800 0xbf8f80003fff8001 0xb5fc7c0001fffc00

def z913 : W := mkw 0x76c87e00b68036c8 0x23b643f005b401b6 0xfffc7f00ff807fff 0xffffe3f807fc03ff

def z914 : W := mkw 0x7fefffb6a0002402 0x7bff7ffdb5000120 0x7fffffffc0003809 0x7bfffffffe0001c0

def z915 : W := mkw 0x6058506d40746d01 0x1302c2836a03a368 0x607c78ff007c7f1d 0x5b03e3c7f803e3f8

def z916 : W := mkw 0x7f6ff5b600000002 0x7bfb7fadb0000000 0x7fffe0ff00000001 0x73ffff07f8000000

def z917 : W := mkw 0x76807e00b68036c8 0x23b403f005b401b6 0xfff07ff8ff807fff 0xffff83ffc7fc03ff

def z918 : W := mkw 0x7b7f5000fb5b240c 0x63dbfa8007dad920 0xffff8000ffff8001 0xf7fffc0007fffc00

def z919 : W := mkw 0x6048d1a400000000 0x1302468d20000000 0x607fffff00000001 0x7b03fffff8000000

def z920 : W := mkw 0x00100049e0746d01 0x000080024f03a368 0x00000000c0007f1c 0x00000000060003f8

def z921 : W := mkw 0x01858b8200000000 0x080c2c5c10000000 0x63ffffff00000001 0x7b1ffffff8000000

def z922 : W := mkw 0x09ef8bb600000002 0x584f7c5db0000000 0x23ff98ff00000000 0x111ffcc7f8000000

def z923 : W := mkw 0x7fefffb6a0000002 0x7bff7ffdb5000000 0x7fffffffe0000001 0xfbffffffff000000

def z924 : W := mkw 0x81858bc301adc360 0x0c0c2c5e180d6e1b 0xa38f9fc723ff87e6 0x351c7cfe391ffc3f

def z925 : W := mkw 0x00100049fef6ffe9 0x800080024ff7b7ff 0x80000000fffffffe 0x8400000007ffffff

def z926 : W := mkw 0x7e6af5b400000002 0x73f357ada0000000 0x7c7fffff00000001 0x7be3fffff8000000

def z927 : W := mkw 0x096fd1b600000002 0x584b7e8db0000000 0x007ff8ff00000000 0x1803ffc7f8000000

def z928 : W := mkw 0x096f81b600000002 0x584b7c0db0000000 0x207f98ff00000001 0x1903fcc7f8000000

def z929 : W := mkw 0x0ca2ffb6048036ca 0x386517fdb02401b6 0xdc73ffffdc007fff 0xfee39ffffee003ff

def z930 : W := mkw 0x7b7f5024fb5b0006 0x73dbfa8127dad800 0xffff8000ffff8001 0xf7fffc0007fffc00

def z931 : W := mkw 0x7648742400000000 0x33b243a120000000 0x7c7c78ff00000001 0x5be3e3c7f8000000

def z932 : W := mkw 0x80100049e1fd6f41 0x040080024f0feb7a 0x00000000e3fc7f1c 0x80000000071fe3f8

def z933 : W := mkw 0x76807e24b68036c8 0x33b403f125b401b6 0xff807fffff807fff 0xeffc03fffffc03ff

def z934 : W := mkw 0x0010004940746d01 0x000080024a03a368 0x00000000007c7f1c 0x000000000003e3f8

def z935 : W := mkw 0x81858bdb01adcb60 0x8c0c2c5ed80d6e5b 0xa38f9fff23ffc7f7 0xbd1c7cfff91ffe3f

def z936 : W := mkw 0x7fefffb6048012ca 0x7bff7ffdb0240096 0x7fffffff000000e3 0x7bfffffff8000007

def z937 : W := mkw 0x09370000495b0004 0x4049b800024ad800 0x00038000007f8000 0x00001c000003fc00

def z938 : W := mkw 0x7b7f0000fb5b0004 0x43dbf80007dad800 0xffff98c7ffff8001 0xfffffcc63ffffc00

def z939 : W := mkw 0x7fefffb6b280264a 0x7bff7ffdb5940132 0x7fffffffe3807f1d 0xfbffffffff1c03f8

def z940 : W := mkw 0x00100049e8766d01 0x000080024f43b368 0x80000000fc7fff1c 0x8400000007e3fff8

def z941 : W := mkw 0x7fefffb6b600348a 0x7bff7ffdb5b001a4 0xffffffffdc0078fb 0xfffffffffee003c7

def z942 : W := mkw 0x76c87e24b68036c8 0x33b643f125b401b6 0xfff07f38ff807fff 0xefff83f9c7fc03ff

def z943 : W := mkw 0xe0905a49e1fdef61 0x070482d24f0fef7b 0xe3807f00e3ffffff 0xef1c03f8071fffff

def z944 : W := mkw 0x7fefffb61b0b0006 0x7bff7ffdb0d85800 0xffffffff3fff8001 0xfffffffff9fffc00

def z945 : W := mkw 0x60580049e0744900 0x0302c0024f03a248 0x607c78ffe07c7f1d 0xdb03e3c7ff03e3f8

def z946 : W := mkw 0x0c6aa5b400000000 0x1063552da0000000 0x5c7fe7ff00000001 0x7ae3ff3ff8000000

def z947 : W := mkw 0x0ceaffb600000002 0x786757fdb0000000 0x00707fff00000000 0x080383fff8000000

def z948 : W := mkw 0x083281c84862c820 0x0041940e42431641 0xdc73e7f8dc63f8fb 0xfee39f3fc6e31fc7

def z949 : W := mkw 0x0da7af92048012c0 0x086d3d7c90240096 0xffffffffff807fff 0xfffffffffffc03ff

def z950 : W := mkw 0x7b7f5000fb5b2404 0x43dbfa8007dad920 0xffffe000ffffb809 0xf7ffff0007fffdc0

def z951 : W := mkw 0x7fefffb608028022 0xfbff7ffdb0401401 0x7fffffff00038001 0x7bfffffff8001c00

def z952 : W := mkw 0x7fef7e3600000002 0x7bff7bf1b0000000 0x7ffc78ff00000001 0x5bffe3c7f8000000

def z953 : W := mkw 0x001000494c66fda1 0x800080024a6337ed 0x80000000dc63fffe 0x8400000006e31fff

def z954 : W := mkw 0x1f6fa5b600000002 0x78fb7d2db0000000 0x1c7f80ff00000000 0x10e3fc07f8000000

def z955 : W := mkw 0x6058506de0746d01 0x1302c2836f03a368 0x607c78ffe07c3f0c 0x5303e3c7ff03e1f8

def z956 : W := mkw 0x80100049ffefffe8 0x840080024fff7fff 0x80000000fffffffe 0x8400000007ffffff

def z957 : W := mkw 0x8010004949efcb60 0x840080024a4f7e5b 0x8000000023ffc7f6 0x84000000011ffe3f

def z958 : W := mkw 0x0c3224484c625880 0x00619122426312c4 0xdc73e7f8dc63f8fb 0xfee39f3fc6e31fc7

def z959 : W := mkw 0x00100049e0746d01 0x000080024f03a368 0x00000000c07c3808 0x000000000603e1c0

def z960 : W := mkw 0x0defffb600000002 0x786f7ffdb0000000 0x23ffffff00000001 0x391ffffff8000000

def z961 : W := mkw 0x7fefffb604001082 0x7bff7ffdb0200084 0xffffffff1c0000e3 0x7ffffffff8e00007

def z962 : W := mkw 0x7fefffb600800242 0x7bff7ffdb0040012 0x7fffffff23800705 0x7bfffffff91c0038

def z963 : W := mkw 0x7fefffb6b68036ca 0x7bff7ffdb5b401b6 0x7fffffffff803f0d 0x7bfffffffffc01f8

def z964 : W := mkw 0x72c85a24b2802648 0x339642d125940132 0x238c180723800704 0x011c60c0391c0038

def z965 : W := mkw 0x7b7f5024fb5b2404 0x53dbfa8127dad920 0xfffff8ffffffff1d 0xffffffc7fffffff8

def z966 : W := mkw 0x7fefffb6b79936ce 0x7bff7ffdb5bcc9b6 0xffffffffff9c7fff 0xfffffffffffce3ff

def z967 : W := mkw 0x80100049fbffef65 0x040080024fdfff7b 0x80000000fffffffe 0x8400000007ffffff

def z968 : W := mkw 0x7fefffb601890242 0x7bff7ffdb00c4812 0xffffffff23ffc7f7 0xfffffffff91ffe3f

def z969 : W := mkw 0x7fefffb6b78936ca 0x7bff7ffdb5bc49b6 0xffffffffffffffff 0xffffffffffffffff

def z970 : W := mkw 0x686ad1b400000000 0x1343568da0000000 0x607ff8ff00000001 0x5b03ffc7f8000000

def z971 : W := mkw 0x7fefffb6b2002402 0x7bff7ffdb5900120 0xffffffffff807f1d 0xfffffffffffc03f8

def z972 : W := mkw 0x00900a49e0f46f41 0x000480524f07a37a 0xa3801f00e3fc7fff 0xad1c00f8071fe3ff

def z973 : W := mkw 0x60105049e0746d01 0x030082824f03a368 0x40006000e07c7f1c 0xc20003000703e3f8

def z974 : W := mkw 0x76807e00b68036c8 0x23b403f005b401b6 0xdf806700ff807ffe 0xe6fc033807fc03ff

def z975 : W := mkw 0x7b7f0000fb5b0004 0x43dbf80007dad800 0xbfff80003fff8000 0x35fffc0001fffc00

def z976 : W := mkw 0x7fefffb6b2100006 0x7bff7ffdb5908000 0x7fffffff00000001 0x7bfffffff8000000

def z977 : W := mkw 0x7efafffcfee2fee8 0xb3f7d7ffe7f717f7 0xffffffffffe3ffff 0xffffffffffff1fff

def z978 : W := mkw 0x614d502400000000 0x130a6a8120000000 0x63fff8ff00000001 0x7b1fffc7f8000000

def z979 : W := mkw 0x80100049e0f4ef61 0x040080024f07a77b 0x00000000e07c7ffe 0x800000000703e3ff

def z980 : W := mkw 0x0010506d40646d01 0x100082836a032368 0x607c78ffe07c7f1d 0xdb03e3c7ff03e3f8

def z981 : W := mkw 0x0c32a5d84c62d8a0 0x8061952ec26316c5 0xfc7fe7f8fc7ff8fb 0xffe3ff3fc7e3ffc7

def z982 : W := mkw 0x810581c3012dc120 0x0c082c0e18096e09 0x00038000007f8000 0x00001c000003fc00

def z983 : W := mkw 0x9fa7af92178992ea 0x6cfd3d7c90bc4c97 0x9f8387001f8380e2 0x24fc1c3800fc1c07

def z984 : W := mkw 0x7fefffb6048012c2 0x7bff7ffdb0240096 0xffffffffff807fff 0xfffffffffffc03ff

def z985 : W := mkw 0x6048502400000000 0x1302428120000000 0x407078ff00000000 0x4a0383c7f8000000

def z986 : W := mkw 0x76807e34b68036ca 0x33b403f1a5b401b6 0xff807f38ff807fff 0xeffc03f9c7fc03ff

def z987 : W := mkw 0x096f81b6090b0006 0x584b7c0db0485800 0x007f80ff00038000 0x1003fc07f8001c00

def z988 : W := mkw 0x7a6a502400000000 0x53d3528120000000 0x7c7c78ff00000001 0x5be3e3c7f8000000

def z989 : W := mkw 0x7fefffb6b2800242 0x7bff7ffdb5940012 0xffffffffff8047f7 0xfffffffffffc023f

def z990 : W := mkw 0x7e6a743400000002 0x73f353a1a0000000 0x5c7078ff00000000 0x4ae383c7f8000000

def z991 : W := mkw 0x7fefffb6bf8b36ce 0x7bff7ffdb5fc59b6 0xffffffffff83ffff 0xfffffffffffc1fff

def z992 : W := mkw 0x096f81b600000002 0x584b7c0db0000000 0x407fe0ff00000001 0x5a03ff07f8000000

def z993 : W := mkw 0x6058506de0746d01 0x1302c2836f03a368 0x00000000e07c7f1c 0x800000000703e3f8

def z994 : W := mkw 0x7eea7e34b68036ca 0x73f753f1a5b401b6 0xfffc7fffff807fff 0xffffe3fffffc03ff

def z995 : W := mkw 0x76807e00b68036c8 0x23b403f005b401b6 0xbf801f00ff807ffe 0xa5fc00f807fc03ff

def z996 : W := mkw 0x6c6af5b5ac16b5a1 0x936357adad60b5ad 0xbc0f9f073c1f87e6 0x25e07cf839e0fc3f

def z997 : W := mkw 0x76907e49fef6ffe9 0xa3b483f24ff7b7ff 0xff807f00ffffffff 0xeffc03f807ffffff

def z998 : W := mkw 0x00100049f6747d89 0x000080024fb3a3ec 0x00000000fc7c7f1c 0x8000000007e3e3f8

def z999 : W := mkw 0x7fef7e24b68036c8 0x73ff7bf125b401b6 0xffffffffff807fff 0xfffffffffffc03ff

def z1000 : W := mkw 0x7fefffb600000002 0x7bff7ffdb0000000 0x7fffffffc0007819 0xfbfffffffe0003c0

def z1001 : W := mkw 0x73cd5a26b280264a 0x7b9e6ad135940132 0x63fc78ffe3807f1d 0xdb1fe3c7ff1c03f8

def z1002 : W := mkw 0x0000000000000000 0x0000000000000000 0x607c78ff00000001 0x5b03e3c7f8000000

def z1003 : W := mkw 0x1b2700001b0b0004 0x40d9380000d85800 0x9f8380003fff8000 0xa4fc1c0001fffc00

def z1004 : W := mkw 0x6448742400000000 0x132243a120000000 0x7c7c7fff00000001 0x7be3e3fff8000000

def z1005 : W := mkw 0x60c85a2600000002 0x3b0642d130000000 0x607c78ff00000001 0x5b03e3c7f8000000

def z1006 : W := mkw 0x7fefffb61600108a 0x7bff7ffdb0b00084 0x7fffffff1c000001 0x7bfffffff8e00000

def z1007 : W := mkw 0x1b7f00005b5b0004 0x40dbf80002dad800 0xdfff8000dfff8001 0xf6fffc0006fffc00

def z1008 : W := mkw 0x0d6fa5b604001082 0x586b7d2db0200084 0xdc7fe7ffdc0078fb 0xfee3ff3ffee003c7

def z1009 : W := mkw 0x60585024e0502400 0x1302c28127028120 0x607c78ffe07c7f1d 0xdb03e3c7ff03e3f8

def z1010 : W := mkw 0x76802e00b68012c0 0x03b4017005b40096 0xff807f00ff807fff 0xeffc03f807fc03ff

def z1011 : W := mkw 0x0da7ffb600000002 0x386d3ffdb0000000 0x7fffffff00000001 0x7bfffffff8000000

def z1012 : W := mkw 0x0c32a5d94c66d9a0 0x8061952eca6336cd 0xdc73e7f8fc7fffff 0xfee39f3fc7e3ffff

def z1013 : W := mkw 0x76487424b6003488 0x33b243a125b001a4 0x7c7c78ffdc003809 0x5be3e3c7fee001c0

def z1014 : W := mkw 0x801000494d6fd9a0 0x840080024a6b7ecd 0x80000000dc7ff8fa 0x8400000006e3ffc7

def z1015 : W := mkw 0x0480ffb600000002 0x382407fdb0000000 0x40707fff00000001 0x5a0383fff8000000

def z1016 : W := mkw 0x7fefffb604001082 0x7bff7ffdb0200084 0x7fffffffdc003809 0x7bfffffffee001c0

def z1017 : W := mkw 0x00100049f2f46f49 0x000080024f97a37a 0x00000000e3fc7f1c 0x80000000071fe3f8

def z1018 : W := mkw 0x7bef8bb600000002 0x5bdf7c5db0000000 0x7fff9fff00000001 0x7bfffcfff8000000

def z1019 : W := mkw 0x0927819200000000 0x08493c0c90000000 0x007f80ff00000000 0x1003fc07f8000000

def z1020 : W := mkw 0x00100049ec767d81 0x800080024f63b3ec 0x00000000fc7c7f1c 0x8000000007e3e3f8

def z1021 : W := mkw 0x614d502600000002 0x5b0a6a8130000000 0x607c78ff00000001 0x5b03e3c7f8000000

def z1022 : W := mkw 0x0058006d40744901 0x1002c0036a03a248 0x607c78ffe07c7f1d 0xdb03e3c7ff03e3f8

def z1023 : W := mkw 0x6058502de0542d01 0x1302c2816f02a168 0x607c78ffe01c3f0d 0x5b03e3c7ff00e1f8

def z1024 : W := mkw 0x7fefffb600000002 0x7bff7ffdb0000000 0x5ff3ffff00000000 0x6aff9ffff8000000

def z1025 : W := mkw 0x096f81b601190006 0x584b7c0db008c800 0x007f80ff001c0000 0x1003fc07f800e000

def z1026 : W := mkw 0x7b7f00005b5b0004 0x43dbf80002dad800 0xffff80001fff8001 0x77fffc0000fffc00

def z1027 : W := mkw 0x001000494c66d9a0 0x800080024a6336cd 0x80000000fc7ffffe 0x8400000007e3ffff

def z1028 : W := mkw 0x7f6ff5b600000002 0x7bfb7fadb0000000 0x7c7ff8ff00000001 0x5be3ffc7f8000000

def z1029 : W := mkw 0x76c87e24168012c8 0x33b643f120b40096 0xfffc7fff1f8000e3 0x7fffe3fff8fc0007

def z1030 : W := mkw 0x0048002400000000 0x1002400120000000 0x207c18ff00000001 0x1903e0c7f8000000

def z1031 : W := mkw 0x014d81a600000000 0x180a6c0d30000000 0x007f80ff00000000 0x1003fc07f8000000

def z1032 : W := mkw 0x77cdffb600000002 0x7bbe6ffdb0000000 0x63fc7fff00000001 0x5b1fe3fff8000000

def z1033 : W := mkw 0xffefffb601898262 0x7fff7ffdb00c4c13 0xffffffff2383c7f7 0xfffffffff91c1e3f

def z1034 : W := mkw 0x76c87e00b69036c8 0x23b643f005b481b6 0xff8c7f00ff9c7fff 0xeffc63f807fce3ff

def z1035 : W := mkw 0x7befdba600000000 0x5bdf7edd30000000 0x7fffffff00000001 0x7bfffffff8000000

def z1036 : W := mkw 0x7fefffb6b280264a 0x7bff7ffdb5940132 0xffffffffff800705 0xfffffffffffc0038

def z1037 : W := mkw 0x7258506de0746d03 0x7392c2836f03a368 0x607c78ffe07c7f1d 0xdb03e3c7ff03e3f8

def z1038 : W := mkw 0x086a81b600000002 0x5843540db0000000 0x007000ff00000000 0x00038007f8000000

def z1039 : W := mkw 0x7b7f502cfb5b2c05 0x53dbfa8167dad960 0xfffff838ffffff1d 0xffffffc1c7fffff8

def z1040 : W := mkw 0x0010004940646d01 0x000080024a032368 0x00000000c0607f1c 0x80000000060303f8

def z1041 : W := mkw 0x7fa7ff9200000000 0x2bfd3ffc90000000 0x7fffffff00000001 0x7bfffffff8000000

def z1042 : W := mkw 0x72105049fb7f6d05 0x039082824fdbfb68 0xff807800ffffff1d 0xeffc03c007fffff8

def z1043 : W := mkw 0x6048502400000000 0x1302428120000000 0x607c78ff20004715 0xdb03e3c7f9000238

def z1044 : W := mkw 0x7b7f5000fb5b0004 0x43dbfa8007dad800 0xfffff800ffff8001 0xffffffc007fffc00

def z1045 : W := mkw 0x7fefffb6a0802642 0x7bff7ffdb5040132 0xffffffffe3807fff 0xffffffffff1c03ff

def z1046 : W := mkw 0x7befdbb600000002 0x7bdf7eddb0000000 0x63fff8ff00000001 0x5b1fffc7f8000000

def z1047 : W := mkw 0x7fefffb6b3190006 0x7bff7ffdb598c800 0xffffffffff9c0001 0xfffffffffffce000

def z1048 : W := mkw 0xffefffb601098022 0x7fff7ffdb0084c01 0x7fffffff00038001 0x7bfffffff8001c00

def z1049 : W := mkw 0x010581c1012dc120 0x00082c0e08096e09 0xa38f9fc723ffc7f7 0xbd1c7cfe391ffe3f

def z1050 : W := mkw 0x64807e00a48036c0 0x032403f0052401b6 0xff807f00ff807fff 0xeffc03f807fc03ff

def z1051 : W := mkw 0x16902e49f6f47fc9 0x20b481724fb7a3fe 0x9f800700fffc7ffe 0xa4fc003807ffe3ff

def z1052 : W := mkw 0x696f81b600000002 0x5b4b7c0db0000000 0x607f80ff00000001 0x5303fc07f8000000

def z1053 : W := mkw 0x0c22f5b400000000 0x106117ada0000000 0x5c73ffff00000001 0x7ae39ffff8000000

def z1054 : W := mkw 0x09ef8bb600800242 0x584f7c5db0040012 0xa3ff9fff238047f7 0xbd1ffcfff91c023f

def z1055 : W := mkw 0x7fefffb600000002 0x7bff7ffdb0000000 0x7ffff8ff00000000 0x53ffffc7f8000000

def z1056 : W := mkw 0x04c8ffb600000002 0x382647fdb0000000 0x007c7fff00000000 0x1803e3fff8000000

def z1057 : W := mkw 0x0c32a5d94c66d9a0 0x8061952eca6336cd 0xdc7fe7ffdc7ff8fb 0xfee3ff3ffee3ffc7

def z1058 : W := mkw 0x7b7f0008fb5b2c05 0x43dbf80047dad960 0xffff8000ffffb809 0xf7fffc0007fffdc0

def z1059 : W := mkw 0x60485024a0000000 0x1302428125000000 0x607c78ffe0000001 0xdb03e3c7ff000000

def z1060 : W := mkw 0x697f0000e95b0000 0x034bf800074ad800 0xffff8000ffff8001 0xf7fffc0007fffc00

def z1061 : W := mkw 0x7b7f0000fb5b0004 0x43dbf80007dad800 0xffffe000fffff819 0xffffff0007ffffc0

def z1062 : W := mkw 0x6058506de0746d01 0x1302c2836f03a368 0xe07ff8ffe07fff1d 0xff03ffc7ff03fff8

def z1063 : W := mkw 0x9fa7af920d8b92e2 0xecfd3d7c906c5c97 0x9f8387001f8380e2 0x24fc1c3800fc1c07

def z1064 : W := mkw 0x7b7f0000fb5b0004 0x43dbf80007dad800 0xbf8f8000ffff8000 0xa5fc7c0007fffc00

def z1065 : W := mkw 0xf6907e49ffefffe8 0xa7b483f24fff7fff 0xff807f00ffffffff 0xeffc03f807ffffff

def z1066 : W := mkw 0x7258506df2746d01 0x1392c2836f93a368 0x7c7c78fffc7c7f1d 0xdbe3e3c7ffe3e3f8

def z1067 : W := mkw 0x0d27a59200000000 0x08693d2c90000000 0x5c7fe7ff00000001 0x7ae3ff3ff8000000

def z1068 : W := mkw 0x81858bc301adc360 0x0c0c2c5e180d6e1b 0xe38fffc7e3ffffff 0xff1c7ffe3f1fffff

def z1069 : W := mkw 0x7fefffb6a0100002 0x7bff7ffdb5008000 0x7fffffff201c0001 0x7bfffffff900e000

def z1070 : W := mkw 0x76c87e00b69036cc 0x63b643f005b481b6 0xff807f00ff807fff 0xeffc03f807fc03ff

def z1071 : W := mkw 0x7b6f002400000000 0x53db780120000000 0x7fff80ff00000001 0x73fffc07f8000000

def z1072 : W := mkw 0x004881b600000002 0x1802440db0000000 0x007c00ff00000000 0x1003e007f8000000

def z1073 : W := mkw 0x6048502400000000 0x1302428120000000 0x407c60ff00000000 0x5203e307f8000000

def z1074 : W := mkw 0x7ea2ffb6b68036ca 0x3bf517fdb5b401b6 0xfff3ffffff807fff 0xffff9ffffffc03ff

def z1075 : W := mkw 0x04807e00048036c8 0x202403f0002401b6 0xff807f00ff807fff 0xeffc03f807fc03ff

def z1076 : W := mkw 0x7fefffb6bb0b0006 0x7bff7ffdb5d85800 0xffffffffff838001 0xfffffffffffc1c00

def z1077 : W := mkw 0x80100049edffffe1 0x840080024f6fffff 0x80000000fffffffe 0x8400000007ffffff

def z1078 : W := mkw 0x7b7f0000fb5b0004 0x43dbf80007dad800 0xdfff8000dfff8000 0x76fffc0006fffc00

def z1079 : W := mkw 0x897f81ef497fc925 0x5c4bfc0f7a4bfe49 0x007f80ff007f8000 0x1003fc07f803fc00

def z1080 : W := mkw 0x7b7f0000fb5b0004 0x43dbf80007dad800 0xdff38000ffff8000 0xe6ff9c0007fffc00

def z1081 : W := mkw 0x7fefffb60400348a 0x7bff7ffdb02001a4 0x7fffffff00003809 0x7bfffffff80001c0

def z1082 : W := mkw 0x80100049e17ded21 0x040080024f0bef69 0x00000000e07fff1c 0x800000000703fff8

def z1083 : W := mkw 0x7befdbb600000002 0x7bdf7eddb0000000 0x23ff9fff00000001 0x391ffcfff8000000

def z1084 : W := mkw 0x7b7f0008fb5b0804 0x43dbf80047dad840 0xffffe038ffffb809 0xf7ffff01c7fffdc0

def z1085 : W := mkw 0xffefffb601890242 0x7fff7ffdb00c4812 0x7fffffff03800001 0x7bfffffff81c0000

def z1086 : W := mkw 0x0defffb600000002 0x786f7ffdb0000000 0x5c7fffff00000001 0x7ae3fffff8000000

def z1087 : W := mkw 0x7fefffb600000002 0x7bff7ffdb0000000 0x3fff9fff00000000 0x31fffcfff8000000

def z1088 : W := mkw 0x7fefffb6be82b6ea 0xfbff7ffdb5f415b7 0xffffffffff83ffff 0xfffffffffffc1fff

def z1089 : W := mkw 0x7b370000fb4b0000 0x03d9b80007da5800 0xffff8000ffff8001 0xf7fffc0007fffc00

def z1090 : W := mkw 0x7fefffb6b6001082 0x7bff7ffdb5b00084 0xffffffffff8078fb 0xfffffffffffc03c7

def z1091 : W := mkw 0x696f502400000000 0x534b7a8120000000 0x607ff8ff00000001 0x5b03ffc7f8000000

def z1092 : W := mkw 0x096f81b608028022 0xd84b7c0db0401401 0x007f80ff00038000 0x1003fc07f8001c00

def z1093 : W := mkw 0x0048002400000000 0x1002400120000000 0x407c60ff00000001 0x5a03e307f8000000

def z1094 : W := mkw 0x76807e00b68036c8 0x23b403f005b401b6 0x7f807f00ff807ffe 0x4bfc03f807fc03ff

def z1095 : W := mkw 0xffefffb6b789b6ea 0x7fff7ffdb5bc4db7 0xffffffffff83ffff 0xfffffffffffc1fff

def z1096 : W := mkw 0x7fefffb61f8b12ce 0x7bff7ffdb0fc5896 0xffffffff1f8380e3 0x7ffffffff8fc1c07

def z1097 : W := mkw 0x014d002600000002 0x580a680130000000 0x007c00ff00000000 0x1003e007f8000000

def z1098 : W := mkw 0x7b7f0018fb5b0804 0xc3dbf800c7dad840 0xffff8038ffff8001 0xf7fffc01c7fffc00

def z1099 : W := mkw 0x7e6a743400000002 0x73f353a1a0000000 0x5c7c60ff00000000 0x52e3e307f8000000

def z1100 : W := mkw 0xffefffb600808262 0x7fff7ffdb0040413 0x7fffffff000000e3 0x7bfffffff8000007

def z1101 : W := mkw 0x0058506de0746d01 0x1002c2836f03a368 0x007c78ffe07c7f1c 0x9803e3c7ff03e3f8

def z1102 : W := mkw 0x60105049e0646d00 0x030082824f032368 0x607c78ffe07c7f1d 0xdb03e3c7ff03e3f8

def z1103 : W := mkw 0x77cdffa600000000 0x3bbe6ffd30000000 0x7fffffff00000001 0x7bfffffff8000000

def z1104 : W := mkw 0x686a503400000002 0x53435281a0000000 0x607c78ff00000001 0x5b03e3c7f8000000

def z1105 : W := mkw 0x0d6fa5b600000002 0x586b7d2db0000000 0x007fe7ff00000000 0x1803ff3ff8000000

def z1106 : W := mkw 0x7fefffb600000002 0x7bff7ffdb0000000 0xffffffff000040f3 0xfffffffff8000207

def z1107 : W := mkw 0x7fefffb61a020006 0x7bff7ffdb0d01000 0x7fffffff1c000001 0x7bfffffff8e00000

def z1108 : W := mkw 0x8480afc304a4d3e0 0x0c24057e1825269f 0x00007fc700007ffe 0x080003fe380003ff

def z1109 : W := mkw 0x00100049e474fda1 0x800080024f23a7ed 0x00000000e07c7ffe 0x800000000703e3ff

def z1110 : W := mkw 0x1fefffb600000002 0x78ff7ffdb0000000 0x1fffffff00000000 0x38fffffff8000000

def z1111 : W := mkw 0x72100049f2746d01 0x039080024f93a368 0xff800000fffc7f1d 0xe7fc000007ffe3f8

def z1112 : W := mkw 0x7b7f0000fb5b0004 0x43dbf80007dad800 0xffffe0f8ffff8001 0xffffff07c7fffc00

def z1113 : W := mkw 0x6c6af5b4a4003480 0x136357ada52001a4 0xfc7ffffffc007fff 0xffe3ffffffe003ff

def z1114 : W := mkw 0x7fefffb600000002 0x7bff7ffdb0000000 0x23ffffff00000000 0x191ffffff8000000

def z1115 : W := mkw 0x7f6ff5b600000002 0x7bfb7fadb0000000 0x5c7fe7ff00000001 0x7ae3ff3ff8000000

def z1116 : W := mkw 0x76487424b6003488 0x33b243a125b001a4 0x5c706038dc003808 0x42e38301c6e001c0

def z1117 : W := mkw 0x16802e00b68036c8 0x20b4017005b401b6 0xbf801f00ff807fff 0xadfc00f807fc03ff

def z1118 : W := mkw 0x00100049e0744901 0x000080024f03a248 0x00000000e07c0000 0x800000000703e000

def z1119 : W := mkw 0x64c8ffb6a48036ca 0x3b2647fdb52401b6 0x607c7fffe0007fff 0xdb03e3ffff0003ff

def z1120 : W := mkw 0x77cdffa6b68036c8 0x3bbe6ffd35b401b6 0xffffffffff807fff 0xfffffffffffc03ff

def z1121 : W := mkw 0x81850a03018d0340 0x0c0c2850180c681a 0xa38f9f0723ffc7f7 0xbd1c7cf8391ffe3f

def z1122 : W := mkw 0x096f002400000000 0x504b780120000000 0x007f80ff00000000 0x1003fc07f8000000

def z1123 : W := mkw 0x7b7f0034fb5b0006 0x53dbf801a7dad800 0xffff8038ffff8001 0xf7fffc01c7fffc00

def z1124 : W := mkw 0x72805a00b2802640 0x039402d005940132 0xff807f00ff807fff 0xeffc03f807fc03ff

def z1125 : W := mkw 0x8480fff704a4f7ea 0x3c2407ffb82527bf 0x00007fff00007ffe 0x080003fff80003ff

def z1126 : W := mkw 0x0c32a5984c4298a0 0x8061952cc26214c5 0xdc73e738dc63b8eb 0xf6e39f39c6e31dc7

def z1127 : W := mkw 0x77cd7e2600000002 0x7bbe6bf130000000 0x7ffc7fff00000001 0x7bffe3fff8000000

def z1128 : W := mkw 0x1b6f81b600000002 0x58db7c0db0000000 0x1fff80ff00000000 0x30fffc07f8000000

def z1129 : W := mkw 0x7258506df2746d05 0x5392c2836f93a368 0x607c78ffe07c7f1d 0xdb03e3c7ff03e3f8

def z1130 : W := mkw 0x7fefffb6168036ca 0x7bff7ffdb0b401b6 0xffffffff1f807fff 0x7ffffffff8fc03ff

def z1131 : W := mkw 0x7fefffb600000002 0x7bff7ffdb0000000 0x5fffe7ff00000000 0x72ffff3ff8000000

def z1132 : W := mkw 0x64c87e2400000000 0x332643f120000000 0x607c7fff00000001 0x5b03e3fff8000000

def z1133 : W := mkw 0x7e7a742cfe523c8d 0x73f3d3a167f291e4 0x5c706038dc003808 0x42e38301c6e001c0

def z1134 : W := mkw 0x7fefffb6168012ca 0x7bff7ffdb0b40096 0xffffffff3f8047f7 0xfffffffff9fc023f

def z1135 : W := mkw 0x0c32a5d84c62d8a0 0x8061952ec26316c5 0xdc73e7f8dc63b8ea 0x76e39f3fc6e31dc7

def z1136 : W := mkw 0x8480ffff04a4dbe2 0xbc2407fff82526df 0x00007fff00007ffe 0x080003fff80003ff

def z1137 : W := mkw 0x7fefffb60c0290a2 0xfbff7ffdb0601485 0xffffffffdc03f8fb 0xfffffffffee01fc7

def z1138 : W := mkw 0x0000502400000000 0x1000028120000000 0x407078ff00000001 0x5a0383c7f8000000

def z1139 : W := mkw 0x72c85a2400000000 0x339642d120000000 0x63fc78ff00000001 0x5b1fe3c7f8000000

def z1140 : W := mkw 0x60c8dba600000000 0x1b0646dd30000000 0x607c7fff00000001 0x5b03e3fff8000000

def z1141 : W := mkw 0x7258506df2746d01 0x1392c2836f93a368 0x63fc78ffe3fc7f1d 0xdb1fe3c7ff1fe3f8

def z1142 : W := mkw 0x7fefffb600800242 0x7bff7ffdb0040012 0xffffffff038000e3 0x7ffffffff81c0007

def z1143 : W := mkw 0x7fefffb6b68036ca 0x7bff7ffdb5b401b6 0xffffffffdf8038eb 0x7ffffffffefc01c7

def z1144 : W := mkw 0x7b6f81b600000002 0x5bdb7c0db0000000 0x23ff80ff00000000 0x111ffc07f8000000

def z1145 : W := mkw 0x89ef8bb601898262 0x5c4f7c5db00c4c13 0x83ff87ff038380e2 0x341ffc3ff81c1c07

def z1146 : W := mkw 0x7fefffb6b68012ca 0x7bff7ffdb5b40096 0xffffffffff8000e3 0xfffffffffffc0007

def z1147 : W := mkw 0x7b6f0000bb1b0004 0x43db780005d8d800 0xbf8f80003fff8001 0xb5fc7c0001fffc00

def z1148 : W := mkw 0x09a78b9200000000 0x084d3c5c90000000 0x23ff9fff00000001 0x391ffcfff8000000

def z1149 : W := mkw 0x896f81b601098022 0x5c4b7c0db0084c01 0x007f80ff00038000 0x1003fc07f8001c00

def z1150 : W := mkw 0x6defffb600000000 0x1b6f7ffdb0000000 0x7fffffff00000001 0x7bfffffff8000000

def z1151 : W := mkw 0x7fefffb6048036ca 0x7bff7ffdb02401b6 0xffffffffdc007fff 0xfffffffffee003ff

def z1152 : W := mkw 0x086a003400000002 0x50435001a0000000 0x007c00ff00000000 0x1003e007f8000000

def z1153 : W := mkw 0x6048502400000000 0x1302428120000000 0x607c78ffc0007819 0xdb03e3c7fe0003c0

def z1154 : W := mkw 0x734d502400000000 0x539a6a8120000000 0x63fc78ff00000001 0x5b1fe3c7f8000000

def z1155 : W := mkw 0x734d5024b3190004 0x539a6a812598c800 0x63fc78ff239c0001 0x5b1fe3c7f91ce000

def z1156 : W := mkw 0x01858b8201890240 0x080c2c5c100c4812 0xa38f9fc723ffc7f7 0xbd1c7cfe391ffe3f

def z1157 : W := mkw 0x8480ffdb04a4ffe8 0xac2407fed82527ff 0x00007fff00007ffe 0x080003fff80003ff

def z1158 : W := mkw 0x00100049fa766d05 0x000080024fd3b368 0x00000000fc7c7f1c 0x8000000007e3e3f8

def z1159 : W := mkw 0x7b7f5000fb5b2404 0x43dbfa8007dad920 0xffff9800ffff8705 0xf7fffcc007fffc38

def z1160 : W := mkw 0x7fefffb6b3190006 0x7bff7ffdb598c800 0xffffffff23ff8001 0xfffffffff91ffc00

def z1161 : W := mkw 0x7b7f002cfb5b0805 0x53dbf80167dad840 0xffff8038ffff8001 0xf7fffc01c7fffc00

def z1162 : W := mkw 0x00100049e0746d01 0x000080024f03a368 0x20001800e07c7f1d 0x890000c00703e3f8

def z1163 : W := mkw 0x0defafb600000002 0x586f7d7db0000000 0x7fffffff00000001 0x7bfffffff8000000

def z1164 : W := mkw 0x80100049ffffdbe4 0x840080024ffffedf 0x80000000fffffffe 0x8400000007ffffff

def z1165 : W := mkw 0x60580049e0746d01 0x0302c0024f03a368 0x200c0000e07c7f1c 0x810060000703e3f8

def z1166 : W := mkw 0x72800a00b68036c8 0x0394005005b401b6 0xff801f00ff807fff 0xeffc00f807fc03ff

def z1167 : W := mkw 0x097f0000495b0004 0x404bf800024ad800 0xffff8000ffff8001 0xf7fffc0007fffc00

def z1168 : W := mkw 0x9fa7af921f8b92e4 0xccfd3d7c90fc5c97 0x9f8387001f8380e2 0x24fc1c3800fc1c07

def z1169 : W := mkw 0x1b370000fb5b0004 0x40d9b80007dad800 0xbf8f8000ffff8001 0xb5fc7c0007fffc00

def z1170 : W := mkw 0x00100049e074ed21 0x000080024f03a769 0x80000000e07ffffe 0x840000000703ffff

def z1171 : W := mkw 0x60100049e0746d01 0x030080024f03a368 0x60000000e07c7f1d 0xc30000000703e3f8

def z1172 : W := mkw 0x00100049ff7ffda5 0x800080024ffbffed 0x80000000fffffffe 0x8400000007ffffff

def z1173 : W := mkw 0x6448f5b400000000 0x132247ada0000000 0x607c7fff00000001 0x5b03e3fff8000000

def z1174 : W := mkw 0x6048502400000000 0x1302428120000000 0x207c18ff00000000 0x1103e0c7f8000000

def z1175 : W := mkw 0x7befdbb600000002 0x7bdf7eddb0000000 0x7fff98ff00000001 0x73fffcc7f8000000

def z1176 : W := mkw 0x7b7f0000fb5b2404 0x43dbf80007dad920 0xffff8000ffffff1d 0xf7fffc0007fffff8

def z1177 : W := mkw 0x0d6ff5b600000002 0x786b7fadb0000000 0x007fe0ff00000000 0x1003ff07f8000000

def z1178 : W := mkw 0x81858bc301adc360 0x0c0c2c5e180d6e1b 0xff8f9fc7ffffc7f7 0xfffc7cfe3ffffe3f

def z1179 : W := mkw 0x81858bcb01adcb60 0x0c0c2c5e580d6e5b 0xa38fffff23ffffff 0xbd1c7ffff91fffff

def z1180 : W := mkw 0x0d6fa5b600000002 0x586b7d2db0000000 0x1c7f87ff00000000 0x30e3fc3ff8000000

def z1181 : W := mkw 0x60485024a0002400 0x1302428125000120 0x607c78ff20000705 0x5b03e3c7f9000038

def z1182 : W := mkw 0x6058506de074ed21 0x1302c2836f03a769 0xe07c78ffe07fffff 0xdf03e3c7ff03ffff

def z1183 : W := mkw 0x6c6a743400000000 0x136353a1a0000000 0x7c7c78ff00000001 0x5be3e3c7f8000000

def z1184 : W := mkw 0x7fefffb600000002 0x7bff7ffdb0000000 0x7ffc7fff00000000 0x4bffe3fff8000000

def z1185 : W := mkw 0x0410a5c84460d8a0 0x0020852e422306c5 0xdc73e7f8dc63f8fb 0xfee39f3fc6e31fc7

def z1186 : W := mkw 0x00100049fb7f4905 0x000080024fdbfa48 0x80000000ffff8000 0x8400000007fffc00

def z1187 : W := mkw 0x60c85a2400800240 0x130642d120040012 0xe3fc7fff238047f7 0xff1fe3fff91c023f

def z1188 : W := mkw 0x7b7f5024fb5b2405 0x53dbfa8127dad920 0xffff8000ffff8001 0xf7fffc0007fffc00

def z1189 : W := mkw 0x76807e00b68036c8 0x23b403f005b401b6 0xff83ff00ffe3ffff 0xfffc1ff807ff1fff

def z1190 : W := mkw 0x16807e00168036c8 0x20b403f000b401b6 0xdf807f00df807fff 0xeefc03f806fc03ff

def z1191 : W := mkw 0x7f6ff5b6b600348a 0x7bfb7fadb5b001a4 0x5c7fe0ffdc003808 0x52e3ff07fee001c0

def z1192 : W := mkw 0x7fefffb61280024a 0x7bff7ffdb0940012 0x7fffffff03800001 0x7bfffffff81c0000

def z1193 : W := mkw 0x04102449e4747d81 0x002081224f23a3ec 0xdc006700fc7c7fff 0xeee0033807e3e3ff

def z1194 : W := mkw 0x7b6f81b6b3190006 0x5bdb7c0db598c800 0x23ff80ff239c0000 0x111ffc07f91ce000

def z1195 : W := mkw 0x0480fffd04a4ffe9 0xb02407ffe82527ff 0x00007fff00007ffe 0x080003fff80003ff

def z1196 : W := mkw 0x7e7a743cfe523c85 0xd3f3d3a1e7f291e4 0x5c706038dc003808 0x42e38301c6e001c0

def z1197 : W := mkw 0x1fefafb600000002 0x78ff7d7db0000000 0x5fffe7ff00000001 0x7affff3ff8000000

def z1198 : W := mkw 0x897f81ff497fc921 0x9c4bfc0ffa4bfe49 0x007f80ff007f8000 0x1003fc07f803fc00

def z1199 : W := mkw 0x76807e00b68036c8 0x23b403f005b401b6 0xdf807f00df807ffe 0x6efc03f806fc03ff

def z1200 : W := mkw 0x7fefffb6048036ca 0x7bff7ffdb02401b6 0xffffffff23807fff 0xfffffffff91c03ff

def z1201 : W := mkw 0x0010004940744901 0x000080024a03a248 0x00000000c07c7818 0x800000000603e3c0

def z1202 : W := mkw 0x1b7f00005b5b0004 0x40dbf80002dad800 0xbfff80003fff8001 0xb5fffc0001fffc00

def z1203 : W := mkw 0x7fefffb60c021082 0xfbff7ffdb0601084 0x7fffffff1c000001 0x7bfffffff8e00000

def z1204 : W := mkw 0x696fd1b600000002 0x5b4b7e8db0000000 0x407fe0ff00000000 0x5203ff07f8000000

def z1205 : W := mkw 0x7eeaffb600000002 0x7bf757fdb0000000 0x7ff07fff00000001 0x6bff83fff8000000

def z1206 : W := mkw 0x81858bc301adc360 0x0c0c2c5e180d6e1b 0xa38f9f0723ffc7f6 0xa51c7cf8391ffe3f

def z1207 : W := mkw 0x7fefffb600000002 0x7bff7ffdb0000000 0xffffffff00638001 0xfffffffff8031c00

def z1208 : W := mkw 0xf3cd5a27b39d2745 0x5f9e6ad13d9ce93a 0x238c1807239c0704 0x011c60c0391ce038

def z1209 : W := mkw 0x7fefffb6bb1b0006 0x7bff7ffdb5d8d800 0xffffffff3f9f8001 0x7ffffffff9fcfc00

def z1210 : W := mkw 0x801000494ce6dbe0 0x840080024a6736df 0x80000000dc63fffe 0x8400000006e31fff

def z1211 : W := mkw 0x0105000001090000 0x0008280000084800 0xff8f8000ffff8001 0xf7fc7c0007fffc00

def z1212 : W := mkw 0x7fefffb612000002 0x7bff7ffdb0900000 0xffffffff1f800001 0x7ffffffff8fc0000

def z1213 : W := mkw 0x6058506de0746d01 0x1302c2836f03a368 0xfc7c78fffc7c7f1d 0xffe3e3c7ffe3e3f8

def z1214 : W := mkw 0x60c85a2400000000 0x130642d120000000 0x63fc7fff00000001 0x7b1fe3fff8000000

def z1215 : W := mkw 0x7b6f81b600000002 0x5bdb7c0db0000000 0x5c7f80ff00000000 0x52e3fc07f8000000

def z1216 : W := mkw 0xffefffb6178992ea 0x7fff7ffdb0bc4c97 0xffffffff1f8380e3 0x7ffffffff8fc1c07

def z1217 : W := mkw 0x72c85a24b2802648 0x339642d125940132 0x63fc78ff23800705 0x5b1fe3c7f91c0038

def z1218 : W := mkw 0x76807e00b68036c8 0x23b403f005b401b6 0xff8c7f00fffc7fff 0xfffc63f807ffe3ff

def z1219 : W := mkw 0x81858bc301adc360 0x0c0c2c5e180d6e1b 0xe3ffffff23ffc7f7 0xff1ffffff91ffe3f

def z1220 : W := mkw 0x9fa7af921f8b92e8 0xacfd3d7c90fc5c97 0x9f8387001f8380e2 0x24fc1c3800fc1c07

def z1221 : W := mkw 0x60105049e0746d01 0x030082824f03a368 0x20001800e07c7f1c 0x810000c00703e3f8

def z1222 : W := mkw 0x0c3224184c421880 0x80619120c26210c4 0xdc73e738dc63f8fb 0xfee39f39c6e31fc7

def z1223 : W := mkw 0x696fd1b600000002 0x5b4b7e8db0000000 0x207f98ff00000000 0x1103fcc7f8000000

def z1224 : W := mkw 0x7fefffb6040090a2 0xfbff7ffdb0200485 0x7fffffff000000e3 0x7bfffffff8000007

def z1225 : W := mkw 0x7fefffb600000002 0x7bff7ffdb0000000 0x5c7fffff00000000 0x5ae3fffff8000000

def z1226 : W := mkw 0x73cddba600000002 0x7b9e6edd30000000 0x63ffffff00000001 0x7b1ffffff8000000

def z1227 : W := mkw 0x7fefffb613090006 0x7bff7ffdb0984800 0x7fffffff03800001 0x7bfffffff81c0000

def z1228 : W := mkw 0x01cd8ba600000000 0x180e6c5d30000000 0x23ff9fff00000001 0x391ffcfff8000000

def z1229 : W := mkw 0x0010004940744901 0x000080024a03a248 0x00000000207c4714 0x800000000103e238

def z1230 : W := mkw 0x7b6f81b6b2000002 0x5bdb7c0db5900000 0xffff80ffff800001 0xf7fffc07fffc0000

def z1231 : W := mkw 0x7fefffb600000002 0x7bff7ffdb0000000 0xffffffffdc000001 0xfffffffffee00000

def z1232 : W := mkw 0x735d0000f3590000 0x039ae800079ac800 0xffff8000ffff8001 0xf7fffc0007fffc00

def z1233 : W := mkw 0x7bef5a2600000002 0x7bdf7ad130000000 0x7ffff8ff00000001 0x7bffffc7f8000000

def z1234 : W := mkw 0x086a81b400000000 0x1043540da0000000 0x007f80ff00000000 0x1003fc07f8000000

def z1235 : W := mkw 0x7fefffb6a0002402 0x7bff7ffdb5000120 0x7fffffff20000705 0x7bfffffff9000038

def z1236 : W := mkw 0x64c87e24048036c8 0x332643f1202401b6 0x607c7fff00007fff 0x5b03e3fff80003ff

def z1237 : W := mkw 0x6058506de0746d01 0x1302c2836f03a368 0x407c78ffc07c7f1c 0x5a03e3c7fe03e3f8

def z1238 : W := mkw 0x7f6ff5b400000000 0x53fb7fada0000000 0x7fffffff00000001 0x7bfffffff8000000

def z1239 : W := mkw 0x1fa7ffb600000002 0x78fd3ffdb0000000 0x5ff3ffff00000001 0x7aff9ffff8000000

def z1240 : W := mkw 0x7b7f5024fb5b0004 0x53dbfa8127dad800 0xffff9807ffff8001 0xf7fffcc03ffffc00

def z1241 : W := mkw 0x7befdbb6b280264a 0x7bdf7eddb5940132 0x23ff98ff23800704 0x111ffcc7f91c0038

def z1242 : W := mkw 0xe1cddba601898260 0x1f0e6edd300c4c13 0xe3ffffff038380e3 0x7f1ffffff81c1c07

def z1243 : W := mkw 0x0058506d40746d01 0x1002c2836a03a368 0x407c78ffc07c7f1d 0xda03e3c7fe03e3f8

def z1244 : W := mkw 0x76807e26b68036ca 0x3bb403f135b401b6 0xff807f07ff807fff 0xeffc03f83ffc03ff

def z1245 : W := mkw 0x00100049f37d6d05 0x000080024f9beb68 0x00000000e3fc7f1c 0x80000000071fe3f8

def z1246 : W := mkw 0x6ceaffb600000002 0x3b6757fdb0000000 0x7c7fffff00000001 0x7be3fffff8000000

def z1247 : W := mkw 0x8db7afdb4defdbe0 0x8c6dbd7eda6f7edf 0x9f838700fffffffe 0xa4fc1c3807ffffff

def z1248 : W := mkw 0x0defafb600000002 0x786f7d7db0000000 0x007f87ff00000000 0x1003fc3ff8000000

def z1249 : W := mkw 0x7fff7e24ffdb36cc 0x73fffbf127fed9b6 0xffffffffffffffff 0xffffffffffffffff

def z1250 : W := mkw 0x73cd5a25b39d274d 0x739e6ad12d9ce93a 0x238c1807239c0704 0x011c60c0391ce038

def z1251 : W := mkw 0x001000494c76d9a1 0x800080024a63b6cd 0x80000000dc7ff8fa 0x8400000006e3ffc7

def z1252 : W := mkw 0x1b6f81b61b0b0006 0x58db7c0db0d85800 0x9fff80ff1f838000 0x34fffc07f8fc1c00

def z1253 : W := mkw 0x0ca2ffb600000002 0x386517fdb0000000 0x5c707fff00000000 0x4ae383fff8000000

def z1254 : W := mkw 0x81858bc301adc360 0x0c0c2c5e180d6e1b 0x238f9fc723ffc7f6 0x191c7cfe391ffe3f

def z1255 : W := mkw 0x7b7f0000fb5b0004 0x43dbf80007dad800 0xffff9800ffffc715 0xfffffcc007fffe38

def z1256 : W := mkw 0x7b7f0000494b0000 0x43dbf800024a5800 0xffff8000ffff8001 0xf7fffc0007fffc00

def z1257 : W := mkw 0x6d6ff5b600000002 0x5b6b7fadb0000000 0x7c7fffff00000001 0x7be3fffff8000000

def z1258 : W := mkw 0x00100049497f4905 0x000080024a4bfa48 0x00000000007f8000 0x000000000003fc00

def z1259 : W := mkw 0x6048002400000000 0x1302400120000000 0x607c00ff00000001 0x5303e007f8000000

def z1260 : W := mkw 0x60485024b68036c8 0x1302428125b401b6 0xe07c78ffff807fff 0xdf03e3c7fffc03ff

def z1261 : W := mkw 0x7eeaffb6b68036ca 0x7bf757fdb5b401b6 0x5c707fffdc007ffe 0x4ae383fffee003ff

def z1262 : W := mkw 0x0ca2ffb600000002 0x386517fdb0000000 0x0073ffff00000000 0x18039ffff8000000

def z1263 : W := mkw 0x7b7f502cfb5b2c05 0x53dbfa8167dad960 0xfffff8ffffffb809 0xffffffc7fffffdc0

def z1264 : W := mkw 0x60485024a0100000 0x1302428125008000 0x607c78ff201c0001 0x5b03e3c7f900e000

def z1265 : W := mkw 0x7fefffb6090b0006 0x7bff7ffdb0485800 0x7fffffff00038001 0x7bfffffff8001c00

def z1266 : W := mkw 0x00100049e0746d01 0x000080024f03a368 0x200c0000e07c7f1d 0x910060000703e3f8

def z1267 : W := mkw 0x897f81ff496fc922 0xdc4bfc0ffa4b7e49 0x007f80ff007f8000 0x1003fc07f803fc00

def z1268 : W := mkw 0x8c32a5db4c66d9a0 0x8c61952eda6336cd 0xdc73e7ffdc63f8fb 0xfee39f3ffee31fc7

def z1269 : W := mkw 0x7fefffb600000002 0x7bff7ffdb0000000 0xffffffff23800001 0xfffffffff91c0000

def z1270 : W := mkw 0x7fefffb6b600348a 0x7bff7ffdb5b001a4 0xffffffffff803809 0xfffffffffffc01c0

def z1271 : W := mkw 0x7eeaffb400000000 0x33f757fda0000000 0x7fffffff00000001 0x7bfffffff8000000

def z1272 : W := mkw 0x6058506de0746d01 0x1302c2836f03a368 0x207c78ff207c7f1c 0x1903e3c7f903e3f8

def z1273 : W := mkw 0x76c87e24b68036ca 0x73b643f125b401b6 0xff807f00ff807fff 0xeffc03f807fc03ff

def z1274 : W := mkw 0x7fefffb600000002 0x7bff7ffdb0000000 0x7fffffff207c0001 0xfbfffffff903e000

def z1275 : W := mkw 0x6058506de0746d01 0x1302c2836f03a368 0xe3fc78ffe3fc7f1d 0xff1fe3c7ff1fe3f8

def z1276 : W := mkw 0x77cd7e26b68036ca 0x7bbe6bf135b401b6 0xfffc7fffff807fff 0xffffe3fffffc03ff

def z1277 : W := mkw 0x6058506dfa766d05 0x1302c2836fd3b368 0x607c78fffc7c7f1d 0xdb03e3c7ffe3e3f8

def z1278 : W := mkw 0x735d0049f37d6d05 0x439ae8024f9beb68 0x238c0000e3fc7f1c 0x811c6000071fe3f8

def z1279 : W := mkw 0xffefffb60d8b92e2 0xffff7ffdb06c5c97 0xffffffff1f8380e3 0x7ffffffff8fc1c07

def z1280 : W := mkw 0xf6907e49f7fdffe9 0x27b483f24fbfefff 0xff807f00ffffffff 0xeffc03f807ffffff

def z1281 : W := mkw 0x00100049e4747d81 0x000080024f23a3ec 0x80000000fc7c7ffe 0x8400000007e3e3ff

def z1282 : W := mkw 0x6058506de0746d01 0x1302c2836f03a368 0xe07c7fffe07c7fff 0xff03e3ffff03e3ff

def z1283 : W := mkw 0x1fefafb600000002 0x78ff7d7db0000000 0x3fff9fff00000001 0x39fffcfff8000000

def z1284 : W := mkw 0x7fefaf9200000000 0x4bff7d7c90000000 0x7fffffff00000001 0x7bfffffff8000000

def z1285 : W := mkw 0xffefffb61b8b8266 0x7fff7ffdb0dc5c13 0xffffffff1f8380e3 0x7ffffffff8fc1c07

def z1286 : W := mkw 0x0c32a5d9ec76fda1 0x8061952ecf63b7ed 0x9c038700fc7ffffe 0xa4e01c3807e3ffff

def z1287 : W := mkw 0x1fefafb6168012ca 0x78ff7d7db0b40096 0x9fff87ff1f8000e2 0x34fffc3ff8fc0007

def z1288 : W := mkw 0x6048506da0346d01 0x130242836d01a368 0x607c78ff201c7f1d 0x5b03e3c7f900e3f8

def z1289 : W := mkw 0x00105049e0746d01 0x000082824f03a368 0x00007800e07c7f1c 0x880003c00703e3f8

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z8,z3,z5,z6]),(0,[z0,z9,z1,z10,z3,z4,z6]),(0,[z0,z1,z3,z4,z11,z5,z6]),(0,[z12,z0,z1,z3,z4,z5,z6]),(0,[z13,z0,z1,z3,z4,z5,z6])],[(0,[z14,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z15]),(0,[z0,z9,z3,z4,z5,z16,z6]),(0,[z0,z1,z3,z4,z17,z16,z6]),(0,[z18,z0,z1,z3,z4,z5,z6]),(0,[z0,z19,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z20,z6]),(0,[z21,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z22,z3,z4,z5,z6]),(0,[z23,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z24])],[(0,[z0,z1,z3,z4,z5,z6,z25]),(0,[z0,z1,z26,z3,z4,z5,z6]),(0,[z0,z1,z27,z3,z4,z5,z6])],[(0,[z0,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z28,z17,z6]),(0,[z29,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z30,z6]),(0,[z31,z0,z1,z3,z4,z5,z6]),(0,[z32,z0,z1,z33,z3,z4,z6])],[(0,[z34,z0,z1,z3,z4,z5,z6]),(0,[z35,z34,z0,z1,z3,z4,z6]),(1,[z0,z1,z3,z36,z5,z6]),(0,[z37,z0,z1,z3,z4,z5,z6]),(0,[z0,z38,z1,z3,z4,z5,z6])],[(0,[z39,z0,z1,z3,z4,z5,z6]),(1,[z0,z9,z1,z40,z4,z6]),(0,[z0,z1,z3,z4,z5,z41,z6]),(0,[z42,z0,z1,z3,z4,z5,z43]),(0,[z0,z1,z3,z4,z5,z6,z44]),(0,[z45,z0,z1,z3,z4,z5,z6])],[(0,[z0,z9,z1,z46,z3,z4,z6]),(0,[z35,z47,z0,z1,z3,z4,z6]),(0,[z0,z1,z48,z3,z4,z17,z6]),(0,[z42,z0,z1,z3,z4,z49,z6]),(0,[z50,z0,z1,z3,z4,z5,z51])],[(0,[z0,z9,z1,z3,z4,z52,z6]),(0,[z35,z0,z1,z3,z4,z51,z6]),(0,[z0,z1,z3,z4,z17,z53,z6])]],
   [[(0,[z54,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z55,z6])],[(0,[z56,z1,z3,z4,z5,z6,z57]),(0,[z0,z1,z3,z4,z5,z58,z6]),(0,[z0,z1,z3,z4,z59,z5,z6]),(1,[z60,z1,z3,z4,z5,z57]),(0,[z0,z9,z1,z3,z4,z61,z6]),(0,[z0,z1,z3,z4,z62,z5,z6]),(0,[z0,z63,z1,z3,z64,z5,z6]),(0,[z65,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z46,z4,z5,z52,z6]),(0,[z0,z66,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z67])],[(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z0,z1,z3,z68,z4,z5,z6]),(0,[z29,z0,z1,z3,z4,z64,z6]),(1,[z35,z0,z1,z3,z4,z6]),(0,[z35,z0,z1,z3,z4,z69,z6]),(0,[z0,z1,z70,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z71,z6]),(0,[z0,z1,z3,z4,z72,z5,z6])],[(0,[z0,z1,z3,z4,z5,z73,z6]),(0,[z74,z0,z1,z3,z4,z5,z6]),(0,[z0,z75,z9,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z76,z5,z6]),(0,[z0,z1,z77,z3,z4,z5,z6])],[(0,[z78,z0,z9,z1,z3,z4,z6]),(0,[z79,z0,z1,z3,z4,z5,z6]),(0,[z56,z0,z9,z1,z3,z4,z6]),(0,[z32,z80,z0,z1,z3,z4,z6]),(0,[z81,z0,z1,z3,z4,z82,z6]),(0,[z0,z1,z3,z4,z5,z83,z6]),(0,[z0,z84,z1,z4,z5,z17,z6]),(0,[z0,z1,z85,z3,z4,z5,z6]),(0,[z86,z0,z1,z3,z4,z17,z6]),(0,[z0,z1,z3,z87,z5,z88,z6]),(0,[z0,z89,z1,z3,z4,z5,z6])],[(0,[z90,z0,z1,z3,z4,z5,z6]),(0,[z81,z0,z1,z3,z4,z17,z6]),(0,[z0,z91,z1,z3,z4,z17,z6]),(1,[z0,z9,z1,z3,z76,z6]),(0,[z92,z0,z9,z1,z3,z4,z6]),(0,[z0,z93,z1,z3,z4,z5,z6]),(0,[z0,z1,z94,z3,z4,z5,z6]),(0,[z0,z95,z1,z3,z4,z5,z6])],[(0,[z96,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z97,z5,z6]),(0,[z0,z1,z3,z98,z4,z17,z6]),(0,[z0,z9,z1,z3,z4,z43,z6]),(1,[z0,z1,z3,z99,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z100]),(0,[z0,z1,z3,z4,z101,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z102])]],
   [[(0,[z0,z1,z103,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z104,z6]),(0,[z105,z0,z9,z1,z3,z4,z6]),(0,[z106,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z69,z51,z6]),(0,[z0,z1,z3,z4,z5,z6,z107])],[(0,[z0,z1,z3,z4,z108,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z109]),(0,[z110,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z111])],[(0,[z0,z112,z1,z3,z4,z5,z6]),(0,[z35,z0,z1,z48,z3,z4,z6])],[(0,[z113,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z114,z4,z5,z6]),(0,[z115,z0,z1,z3,z4,z5,z6]),(0,[z80,z0,z1,z3,z4,z88,z6]),(0,[z0,z1,z116,z3,z4,z5,z6]),(0,[z117,z0,z1,z3,z4,z17,z6]),(0,[z35,z0,z1,z3,z4,z16,z6]),(0,[z0,z1,z118,z3,z4,z5,z6]),(0,[z0,z119,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z120])],[(0,[z121,z122,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z17,z58,z6]),(0,[z0,z123,z1,z3,z4,z5,z6])],[(0,[z124,z0,z1,z3,z4,z5,z6]),(0,[z35,z0,z1,z8,z3,z4,z6]),(0,[z125,z0,z1,z3,z4,z5,z6]),(0,[z0,z126,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z127,z6])],[(0,[z128,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z129]),(0,[z130,z0,z1,z3,z4,z131,z6])],[(0,[z0,z1,z3,z4,z5,z6,z132]),(0,[z0,z1,z3,z4,z5,z133,z6]),(0,[z0,z1,z3,z4,z134,z5,z6]),(0,[z0,z1,z135,z3,z4,z5,z6])]],
   [[(0,[z0,z136,z1,z3,z4,z5,z6]),(0,[z137,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z8,z3,z4,z5,z6]),(0,[z0,z84,z1,z3,z4,z17,z6]),(0,[z14,z0,z9,z1,z3,z4,z6]),(0,[z0,z122,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z138,z5,z6])],[(0,[z139,z0,z1,z3,z4,z5,z6]),(0,[z117,z0,z1,z3,z4,z5,z61]),(0,[z140,z0,z1,z3,z4,z5,z6])],[(0,[z35,z56,z0,z1,z3,z4,z6]),(0,[z141,z7,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z142,z5,z6]),(0,[z143,z0,z1,z3,z4,z5,z6]),(0,[z35,z35,z0,z1,z3,z4,z6]),(0,[z32,z47,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z144])],[(0,[z34,z0,z1,z4,z28,z5,z6]),(0,[z0,z1,z145,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z146,z5,z6]),(0,[z0,z1,z3,z4,z147,z5,z6]),(0,[z0,z38,z9,z1,z3,z4,z6]),(0,[z32,z0,z1,z3,z4,z51,z6]),(0,[z0,z1,z148,z3,z4,z5,z6])],[(0,[z149,z0,z1,z3,z5,z150,z6]),(0,[z151,z0,z1,z3,z4,z5,z6]),(0,[z152,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z153,z3,z4,z5,z6]),(0,[z154,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z17,z6,z120])],[(0,[z56,z117,z1,z3,z4,z5,z6]),(0,[z35,z0,z1,z3,z99,z4,z6]),(1,[z155,z0,z3,z4,z5,z6]),(0,[z0,z1,z156,z3,z4,z5,z6])]],
   [[(0,[z157,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z158,z4,z5,z6])],[(0,[z0,z1,z3,z4,z159,z5,z6]),(0,[z160,z0,z1,z3,z4,z5,z6]),(0,[z0,z161,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z64,z5,z88,z6]),(0,[z0,z1,z162,z3,z4,z5,z6]),(0,[z163,z0,z1,z3,z4,z5,z6]),(0,[z164,z0,z1,z3,z4,z17,z6]),(1,[z0,z66,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z17,z43,z6])],[(1,[z0,z1,z3,z4,z165,z6]),(0,[z166,z0,z1,z3,z4,z5,z6]),(0,[z0,z84,z91,z1,z4,z5,z6]),(0,[z167,z0,z1,z3,z4,z5,z6]),(0,[z168,z0,z1,z3,z4,z17,z6])],[(0,[z42,z34,z0,z1,z4,z5,z6]),(0,[z34,z0,z1,z4,z5,z43,z6]),(0,[z0,z1,z3,z4,z5,z82,z6])],[(0,[z169,z0,z1,z3,z4,z5,z6]),(0,[z141,z0,z1,z3,z4,z5,z6]),(0,[z170,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z171,z6]),(0,[z35,z0,z1,z10,z3,z4,z6]),(1,[z121,z0,z3,z4,z5,z172]),(0,[z0,z1,z3,z4,z5,z6,z172]),(0,[z0,z1,z3,z4,z5,z17,z6]),(0,[z0,z1,z3,z4,z5,z173,z6]),(0,[z50,z0,z1,z3,z4,z5,z174])],[(0,[z32,z0,z1,z175,z3,z4,z6]),(0,[z0,z1,z3,z4,z176,z5,z6]),(0,[z141,z0,z1,z8,z3,z5,z6]),(1,[z0,z3,z4,z5,z6,z177]),(0,[z0,z1,z178,z3,z4,z5,z6]),(0,[z179,z35,z0,z1,z3,z4,z6]),(0,[z180,z35,z0,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z181,z5,z6]),(0,[z0,z182,z1,z3,z4,z5,z6]),(0,[z0,z183,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z184,z5,z6]),(0,[z185,z35,z0,z1,z3,z4,z6]),(0,[z32,z0,z1,z48,z3,z4,z6]),(0,[z130,z0,z1,z3,z186,z5,z6]),(1,[z130,z0,z1,z3,z5,z120])],[(0,[z81,z50,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z187]),(0,[z188,z0,z1,z3,z4,z5,z6]),(1,[z0,z189,z1,z3,z5,z6]),(0,[z0,z9,z1,z190,z3,z4,z6]),(0,[z32,z0,z1,z3,z4,z16,z6]),(0,[z191,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z192,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z193,z6]),(0,[z0,z9,z1,z3,z4,z5,z6]),(0,[z0,z38,z9,z1,z4,z5,z6]),(1,[z154,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z194,z5,z6]),(0,[z42,z0,z1,z3,z4,z5,z195])],[(0,[z0,z1,z3,z4,z5,z196,z6]),(0,[z32,z0,z1,z8,z3,z4,z6]),(0,[z0,z197,z3,z4,z64,z5,z6]),(0,[z0,z1,z3,z186,z4,z17,z6]),(0,[z0,z1,z3,z4,z5,z6,z198])],[(0,[z0,z9,z1,z3,z76,z5,z6]),(0,[z35,z0,z1,z46,z3,z4,z6]),(0,[z130,z149,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z199]),(0,[z0,z1,z200,z3,z4,z5,z6])],[(0,[z35,z0,z1,z3,z4,z52,z6]),(0,[z32,z0,z201,z1,z3,z4,z6]),(0,[z0,z1,z3,z87,z4,z88,z6])],[(0,[z0,z202,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z203,z6]),(1,[z29,z0,z1,z3,z4,z6]),(0,[z0,z204,z1,z3,z4,z5,z6]),(0,[z0,z205,z1,z3,z4,z17,z6]),(0,[z206,z0,z1,z3,z4,z17,z6]),(0,[z0,z1,z3,z4,z5,z207,z6]),(0,[z0,z1,z3,z4,z5,z88,z6]),(0,[z130,z0,z1,z3,z4,z5,z120]),(0,[z0,z208,z1,z3,z4,z5,z6])],[(0,[z0,z209,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z210,z5,z6]),(0,[z35,z0,z1,z3,z4,z61,z6]),(0,[z211,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z195])],[(0,[z32,z56,z0,z1,z3,z4,z6]),(0,[z212,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z213]),(0,[z0,z1,z3,z4,z17,z82,z6]),(1,[z0,z1,z214,z3,z5,z6]),(0,[z0,z1,z3,z215,z4,z5,z6]),(0,[z0,z1,z3,z4,z216,z5,z6])],[(0,[z0,z1,z217,z3,z4,z5,z6]),(0,[z218,z0,z1,z3,z98,z4,z6]),(0,[z0,z1,z3,z4,z5,z219,z6]),(0,[z0,z9,z1,z3,z4,z64,z6]),(0,[z86,z0,z9,z1,z3,z4,z6]),(0,[z0,z205,z1,z3,z4,z5,z172]),(0,[z0,z1,z3,z4,z17,z6,z172]),(0,[z0,z1,z3,z3,z4,z17,z6]),(0,[z0,z1,z3,z4,z17,z17,z6])]],
   [[(0,[z1,z220,z3,z4,z28,z5,z6]),(0,[z0,z1,z221,z3,z4,z5,z6]),(0,[z81,z0,z9,z1,z3,z4,z6]),(0,[z222,z0,z1,z3,z4,z5,z6])],[(0,[z50,z80,z0,z1,z3,z4,z6]),(0,[z223,z0,z1,z4,z5,z6,z57]),(0,[z224,z35,z0,z1,z3,z4,z6]),(0,[z42,z0,z1,z48,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z225])],[(1,[z34,z1,z4,z28,z5,z6]),(0,[z226,z0,z91,z3,z4,z5,z6]),(0,[z0,z1,z227,z3,z4,z5,z6]),(0,[z0,z1,z48,z3,z4,z5,z43]),(0,[z228,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z229,z6]),(0,[z35,z0,z1,z3,z4,z43,z6])],[(0,[z230,z0,z1,z3,z4,z17,z6])],[(0,[z121,z56,z0,z3,z4,z5,z6]),(0,[z0,z1,z220,z3,z4,z17,z6]),(0,[z231,z0,z1,z3,z4,z5,z6]),(0,[z35,z0,z84,z1,z3,z4,z6]),(0,[z0,z1,z46,z3,z4,z5,z6]),(0,[z0,z232,z1,z3,z4,z5,z6]),(0,[z0,z233,z1,z3,z4,z5,z6])],[(0,[z234,z0,z1,z4,z28,z5,z6]),(0,[z0,z1,z3,z4,z235,z5,z6]),(0,[z0,z197,z1,z3,z5,z52,z6])],[(0,[z0,z1,z3,z4,z5,z6,z236]),(0,[z0,z237,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z238]),(0,[z0,z239,z1,z3,z4,z5,z6]),(0,[z121,z0,z1,z3,z4,z17,z6]),(0,[z0,z240,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z241,z3,z4,z5,z6]),(0,[z32,z0,z1,z10,z3,z4,z6]),(0,[z242,z0,z1,z3,z4,z5,z6]),(0,[z0,z9,z1,z3,z4,z53,z6]),(0,[z0,z243,z3,z4,z5,z16,z6])],[(0,[z0,z1,z3,z4,z5,z6,z244]),(0,[z141,z1,z8,z3,z4,z5,z6]),(0,[z0,z245,z1,z3,z4,z5,z6]),(0,[z0,z246,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z247,z4,z5,z6]),(0,[z0,z63,z3,z4,z64,z5,z6]),(0,[z47,z0,z1,z3,z64,z5,z6]),(0,[z0,z1,z3,z4,z248,z5,z6])],[(0,[z249,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z250]),(0,[z0,z1,z3,z4,z251,z5,z6]),(0,[z0,z84,z9,z1,z3,z4,z6]),(0,[z0,z1,z3,z252,z4,z5,z6]),(0,[z253,z0,z1,z3,z4,z5,z6]),(0,[z86,z0,z1,z3,z5,z88,z6])],[(1,[z78,z175,z3,z4,z5,z6]),(0,[z78,z1,z175,z3,z4,z5,z6]),(1,[z35,z0,z243,z3,z4,z6]),(0,[z0,z254,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z255,z3,z4,z5,z6]),(0,[z34,z0,z1,z220,z4,z5,z6]),(0,[z34,z0,z1,z3,z4,z17,z6]),(0,[z0,z1,z256,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z257]),(1,[z0,z1,z3,z4,z258,z6])],[(0,[z0,z205,z1,z3,z4,z5,z53]),(0,[z0,z1,z3,z4,z259,z5,z6])],[(0,[z0,z1,z3,z4,z5,z260,z6]),(0,[z234,z0,z1,z4,z5,z43,z6]),(0,[z0,z1,z3,z4,z5,z6,z261]),(0,[z60,z0,z1,z3,z4,z5,z57]),(0,[z262,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z76,z5,z6])],[(0,[z263,z0,z1,z3,z4,z5,z6]),(0,[z0,z9,z9,z1,z3,z4,z6]),(0,[z32,z0,z1,z3,z4,z52,z6]),(0,[z0,z1,z214,z3,z5,z6,z195])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z264]),(0,[z0,z1,z265,z3,z4,z5,z6]),(1,[z0,z266,z3,z4,z5,z6]),(0,[z151,z32,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z267])],[(0,[z268,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z269,z6]),(0,[z270,z0,z1,z3,z4,z5,z6]),(0,[z271,z0,z1,z3,z5,z6,z57]),(0,[z32,z0,z1,z3,z4,z61,z6])],[(0,[z7,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z99,z4,z5,z6]),(0,[z50,z0,z1,z3,z4,z69,z6])],[(0,[z0,z272,z1,z3,z4,z5,z6]),(0,[z273,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z131,z6])],[(0,[z1,z3,z4,z5,z61,z6,z57]),(0,[z0,z1,z3,z4,z5,z274,z6]),(0,[z0,z3,z98,z4,z64,z5,z6]),(0,[z0,z1,z98,z4,z5,z17,z6]),(0,[z0,z84,z1,z3,z4,z275,z6]),(0,[z168,z0,z9,z1,z3,z4,z6]),(0,[z0,z276,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z277])],[(0,[z0,z1,z3,z4,z5,z6,z278]),(0,[z0,z1,z3,z279,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z280]),(0,[z0,z1,z3,z4,z5,z6,z281])],[(0,[z0,z1,z3,z4,z282,z5,z6]),(0,[z0,z1,z283,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z284,z5,z6]),(1,[z0,z1,z4,z5,z6,z285]),(0,[z0,z1,z3,z4,z5,z6,z286]),(0,[z0,z1,z3,z4,z5,z6,z174])],[(0,[z0,z1,z287,z175,z3,z4,z6]),(0,[z47,z0,z197,z1,z3,z5,z6]),(0,[z0,z9,z1,z288,z3,z4,z6]),(0,[z222,z0,z9,z1,z3,z4,z6]),(0,[z289,z35,z0,z1,z3,z4,z6])]],
   [[(0,[z0,z1,z3,z4,z290,z5,z6]),(0,[z226,z0,z84,z1,z4,z5,z6]),(0,[z0,z205,z1,z3,z291,z5,z6])],[(0,[z292,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z293,z6]),(0,[z0,z1,z294,z3,z4,z5,z6]),(0,[z226,z0,z3,z4,z64,z5,z6]),(0,[z32,z0,z84,z1,z3,z4,z6]),(0,[z0,z1,z3,z40,z4,z5,z6]),(0,[z35,z0,z1,z3,z4,z295,z6]),(0,[z121,z0,z3,z4,z5,z6,z172]),(0,[z0,z126,z205,z1,z3,z5,z6]),(0,[z0,z1,z3,z296,z4,z5,z6]),(1,[z0,z1,z3,z87,z88,z6])],[(0,[z0,z112,z1,z3,z4,z17,z6]),(0,[z0,z1,z297,z3,z4,z5,z6]),(0,[z0,z1,z298,z3,z4,z5,z6])],[(0,[z121,z78,z0,z3,z4,z5,z6]),(0,[z80,z0,z1,z3,z4,z51,z6]),(0,[z0,z84,z1,z299,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z300,z6]),(0,[z0,z1,z3,z4,z5,z301,z6])],[(0,[z0,z1,z302,z3,z4,z5,z6]),(0,[z35,z0,z1,z3,z4,z5,z6]),(0,[z303,z0,z1,z3,z4,z5,z6])],[(0,[z0,z304,z91,z1,z3,z4,z6])],[(0,[z305,z0,z1,z3,z4,z5,z6]),(0,[z35,z117,z0,z1,z3,z4,z6]),(0,[z306,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z307]),(0,[z308,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z309,z4,z5,z6]),(0,[z0,z9,z1,z3,z4,z6,z120]),(0,[z310,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z311,z6])]],
   [[(0,[z0,z1,z8,z3,z4,z17,z6]),(0,[z0,z1,z3,z4,z5,z275,z6]),(0,[z0,z312,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z313,z6]),(0,[z0,z1,z3,z314,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z315]),(0,[z168,z32,z0,z1,z3,z4,z6]),(0,[z130,z0,z197,z1,z3,z5,z6]),(0,[z316,z0,z1,z3,z4,z5,z6]),(1,[z122,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z317,z5,z6]),(0,[z0,z1,z3,z4,z318,z5,z6]),(0,[z0,z319,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z320,z4,z5,z6]),(1,[z0,z38,z9,z1,z4,z6]),(0,[z0,z321,z1,z3,z4,z5,z6])],[(0,[z0,z9,z1,z220,z3,z4,z6]),(0,[z0,z1,z322,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z285,z57]),(0,[z35,z0,z1,z3,z4,z64,z6]),(0,[z0,z1,z3,z4,z5,z323,z6]),(0,[z0,z1,z3,z324,z4,z5,z6]),(0,[z0,z1,z3,z4,z17,z41,z6]),(0,[z325,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z98,z4,z17,z6]),(0,[z326,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z327,z4,z5,z6]),(0,[z222,z32,z0,z1,z3,z4,z6])],[(1,[z0,z328,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z53,z6,z286]),(0,[z0,z1,z48,z3,z4,z5,z195]),(0,[z0,z1,z3,z4,z69,z5,z6])],[(0,[z34,z0,z1,z3,z4,z260,z6]),(0,[z329,z0,z1,z3,z4,z5,z6])],[(0,[z234,z0,z1,z220,z4,z5,z6]),(0,[z0,z1,z330,z3,z4,z5,z6]),(0,[z180,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z331,z6]),(0,[z332,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z185,z0,z1,z3,z4,z5,z6]),(0,[z333,z0,z1,z3,z4,z5,z6])],[(0,[z0,z334,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z335,z6]),(0,[z7,z0,z9,z1,z3,z4,z6]),(0,[z1,z8,z3,z4,z336,z5,z6]),(0,[z81,z0,z1,z3,z4,z88,z6]),(0,[z60,z35,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z57]),(0,[z121,z0,z9,z1,z3,z4,z6])],[(0,[z0,z1,z3,z337,z4,z5,z6]),(0,[z338,z0,z1,z3,z4,z5,z6]),(0,[z339,z0,z1,z3,z4,z5,z6])],[(0,[z0,z91,z1,z3,z36,z5,z6]),(0,[z0,z340,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z341]),(0,[z342,z0,z1,z3,z4,z5,z6])],[(0,[z234,z1,z220,z3,z4,z5,z6]),(0,[z35,z0,z1,z3,z4,z53,z6])],[(0,[z343,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z344,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z345]),(0,[z0,z1,z3,z186,z5,z150,z6])],[(0,[z0,z346,z1,z3,z4,z5,z6]),(0,[z34,z0,z9,z1,z3,z4,z6]),(0,[z347,z0,z1,z3,z4,z5,z6]),(0,[z348,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z349,z4,z5,z6]),(0,[z0,z1,z3,z350,z4,z5,z6]),(0,[z253,z32,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z186,z4,z5,z120])],[(0,[z0,z1,z3,z4,z351,z5,z6]),(0,[z0,z9,z1,z3,z4,z82,z6]),(0,[z0,z243,z1,z3,z4,z5,z6]),(0,[z352,z0,z1,z3,z4,z5,z6]),(0,[z149,z47,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z353,z4,z5,z6])]],
   [[(1,[z218,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z354,z4,z5,z6]),(0,[z0,z9,z1,z3,z4,z6,z172]),(0,[z0,z9,z1,z3,z4,z17,z6]),(0,[z32,z0,z1,z3,z4,z5,z6]),(0,[z0,z355,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z356,z4,z5,z6]),(0,[z0,z9,z1,z3,z4,z336,z6]),(0,[z357,z0,z1,z3,z4,z5,z6]),(0,[z358,z0,z1,z3,z4,z5,z6]),(0,[z32,z0,z1,z3,z4,z69,z6])],[(0,[z234,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z359,z3,z4,z5,z6]),(0,[z117,z1,z3,z4,z5,z61,z6]),(0,[z32,z117,z0,z1,z3,z4,z6]),(0,[z360,z0,z1,z3,z4,z5,z6]),(0,[z0,z361,z1,z3,z4,z5,z6]),(0,[z362,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z363,z4,z5,z6])],[(0,[z224,z0,z1,z3,z4,z5,z6]),(0,[z117,z1,z175,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z364,z6])],[(0,[z78,z0,z175,z3,z4,z5,z6]),(0,[z56,z0,z175,z3,z4,z5,z6]),(0,[z0,z1,z3,z365,z4,z5,z6]),(0,[z1,z10,z3,z4,z5,z82,z6]),(1,[z35,z0,z9,z3,z4,z6]),(0,[z0,z366,z1,z3,z4,z5,z6]),(0,[z0,z367,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z368,z6]),(0,[z0,z1,z3,z4,z5,z51,z6])],[(0,[z0,z1,z3,z4,z17,z133,z6])],[(0,[z7,z32,z0,z1,z3,z4,z6]),(0,[z369,z0,z1,z3,z4,z5,z6]),(0,[z0,z370,z1,z3,z4,z5,z6]),(0,[z121,z32,z0,z1,z3,z4,z6]),(0,[z0,z1,z33,z3,z4,z5,z6])],[(0,[z0,z91,z1,z3,z4,z104,z6]),(0,[z371,z0,z1,z3,z4,z5,z6]),(0,[z32,z0,z1,z3,z4,z64,z6]),(0,[z0,z1,z3,z354,z4,z64,z6]),(0,[z0,z9,z205,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z372,z5,z6]),(1,[z0,z367,z1,z3,z4,z6])]],
   [[(0,[z34,z234,z1,z3,z4,z5,z6]),(0,[z80,z0,z1,z10,z3,z4,z6]),(0,[z0,z93,z9,z1,z3,z4,z6]),(0,[z149,z0,z1,z3,z324,z4,z6]),(0,[z222,z0,z1,z3,z4,z17,z6]),(0,[z0,z1,z3,z373,z4,z5,z6])],[(0,[z374,z0,z1,z3,z4,z5,z6]),(0,[z0,z9,z1,z3,z4,z6,z195]),(0,[z0,z375,z1,z46,z3,z4,z6])],[(0,[z376,z0,z1,z3,z4,z5,z6]),(0,[z0,z9,z1,z3,z98,z4,z6]),(1,[z0,z84,z1,z4,z17,z6]),(0,[z155,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z227,z3,z4,z17,z6]),(0,[z86,z0,z1,z3,z87,z4,z6])],[(0,[z34,z32,z0,z1,z3,z4,z6]),(0,[z0,z377,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z64,z5,z150,z6]),(0,[z35,z42,z0,z1,z3,z4,z6]),(0,[z35,z0,z1,z288,z3,z4,z6]),(0,[z0,z1,z378,z3,z4,z5,z6])],[(0,[z35,z226,z0,z1,z3,z4,z6]),(0,[z0,z1,z379,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z380]),(0,[z39,z32,z0,z1,z3,z4,z6])],[(0,[z381,z0,z1,z3,z4,z5,z6]),(0,[z80,z1,z3,z4,z5,z82,z6]),(1,[z0,z1,z3,z4,z382,z6]),(0,[z0,z1,z46,z3,z4,z17,z6]),(0,[z0,z1,z3,z383,z4,z5,z6])],[(0,[z56,z0,z1,z384,z3,z4,z6]),(0,[z0,z1,z385,z3,z4,z5,z6]),(0,[z0,z1,z386,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z387,z6])],[(0,[z0,z388,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z389]),(1,[z0,z205,z3,z4,z5,z53])]],
   [[(0,[z0,z9,z63,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z390,z6]),(0,[z35,z32,z0,z1,z3,z4,z6]),(0,[z32,z0,z1,z3,z4,z53,z6]),(0,[z391,z0,z1,z48,z3,z4,z6]),(1,[z50,z0,z1,z3,z4,z174])],[(0,[z392,z0,z1,z3,z4,z5,z6]),(0,[z393,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z394,z6]),(0,[z339,z0,z9,z1,z3,z4,z6]),(0,[z149,z0,z1,z3,z5,z52,z6])],[(0,[z0,z1,z3,z4,z395,z5,z6]),(0,[z35,z141,z0,z1,z3,z4,z6]),(0,[z168,z226,z0,z3,z4,z5,z6]),(0,[z0,z340,z9,z1,z3,z4,z6]),(0,[z86,z0,z1,z3,z4,z6,z174])],[(0,[z35,z0,z1,z3,z4,z6,z120]),(0,[z0,z1,z396,z3,z4,z6,z172]),(0,[z0,z1,z3,z4,z397,z5,z6])],[(0,[z398,z0,z1,z3,z4,z5,z6]),(1,[z149,z47,z0,z1,z5,z6]),(1,[z0,z1,z3,z4,z17,z6]),(0,[z0,z1,z3,z399,z4,z5,z6])],[(0,[z226,z0,z1,z98,z4,z5,z6]),(0,[z0,z1,z3,z400,z4,z5,z6]),(0,[z0,z197,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z259,z17,z6])],[(0,[z0,z1,z3,z4,z5,z401,z6]),(0,[z0,z1,z3,z4,z5,z150,z6])],[(0,[z402,z0,z1,z3,z4,z5,z6]),(0,[z35,z0,z1,z220,z3,z4,z6]),(0,[z0,z1,z3,z4,z403,z5,z6]),(0,[z180,z226,z0,z1,z3,z4,z6]),(0,[z0,z1,z190,z3,z4,z5,z6]),(0,[z149,z47,z0,z1,z4,z5,z6])]],
   [[(0,[z404,z0,z1,z3,z4,z5,z6]),(0,[z405,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z406,z5,z6])],[(0,[z407,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z196,z6]),(0,[z289,z0,z1,z3,z4,z5,z6]),(0,[z0,z408,z1,z3,z4,z5,z6]),(0,[z0,z1,z409,z3,z4,z5,z6]),(0,[z0,z1,z3,z410,z4,z5,z6])],[(0,[z78,z0,z112,z3,z4,z5,z6]),(0,[z0,z1,z411,z3,z4,z5,z6]),(0,[z56,z0,z112,z3,z4,z5,z6]),(0,[z7,z0,z1,z3,z4,z17,z6]),(0,[z224,z0,z9,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z17,z207,z6]),(0,[z0,z1,z3,z4,z17,z88,z6])],[(0,[z412,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z274,z6,z57]),(0,[z0,z413,z1,z3,z4,z5,z6]),(0,[z0,z1,z414,z3,z4,z5,z6]),(0,[z415,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z17,z6,z195])],[(0,[z416,z0,z1,z3,z4,z5,z6]),(0,[z168,z0,z197,z1,z3,z5,z6]),(1,[z0,z1,z3,z4,z417,z6]),(0,[z418,z35,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z419])],[(0,[z420,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z104,z6]),(0,[z0,z1,z3,z64,z5,z52,z6]),(0,[z121,z0,z1,z3,z4,z5,z172]),(0,[z0,z1,z3,z279,z4,z17,z6]),(0,[z421,z0,z1,z3,z4,z5,z6]),(0,[z0,z422,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z423])],[(0,[z424,z0,z1,z3,z4,z5,z6]),(0,[z141,z0,z9,z1,z3,z4,z6]),(0,[z0,z1,z425,z3,z4,z5,z6]),(0,[z0,z1,z396,z3,z4,z5,z6]),(0,[z0,z426,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z427,z5,z6]),(0,[z0,z189,z1,z3,z4,z5,z6]),(0,[z0,z428,z1,z3,z4,z5,z6]),(0,[z32,z0,z1,z288,z3,z4,z6])]],
   [[(0,[z429,z0,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z336,z5,z6]),(0,[z0,z1,z3,z4,z5,z430,z6]),(0,[z0,z1,z431,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z432,z6])],[(0,[z78,z35,z0,z1,z3,z4,z6]),(0,[z32,z0,z1,z46,z3,z4,z6]),(0,[z0,z433,z1,z3,z4,z5,z6])],[(0,[z86,z80,z0,z1,z3,z4,z6]),(0,[z434,z0,z1,z3,z4,z5,z6]),(0,[z435,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z288,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z150,z6,z120])],[(0,[z0,z1,z3,z4,z5,z436,z6]),(0,[z35,z0,z1,z3,z4,z82,z6]),(1,[z81,z1,z10,z3,z4,z6]),(0,[z437,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z336,z5,z6]),(0,[z0,z3,z4,z5,z6,z177,z57]),(0,[z0,z1,z3,z4,z5,z438,z6]),(0,[z0,z1,z439,z3,z4,z5,z6]),(0,[z35,z0,z1,z3,z4,z6,z172]),(0,[z35,z0,z1,z3,z4,z17,z6]),(0,[z105,z35,z0,z1,z3,z4,z6]),(0,[z0,z66,z1,z3,z4,z17,z6]),(0,[z32,z32,z0,z1,z3,z4,z6]),(0,[z50,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z440]),(0,[z35,z0,z1,z3,z4,z336,z6]),(0,[z0,z1,z3,z441,z4,z5,z6]),(0,[z0,z63,z1,z3,z4,z5,z6]),(0,[z442,z0,z1,z3,z4,z5,z6]),(0,[z358,z32,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z443,z5,z6])],[(0,[z234,z32,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z444,z6]),(0,[z130,z0,z1,z3,z64,z5,z6]),(1,[z0,z445,z9,z1,z3,z6])],[(0,[z0,z446,z1,z3,z4,z5,z6]),(0,[z0,z9,z112,z1,z3,z4,z6]),(0,[z224,z32,z0,z1,z3,z4,z6]),(0,[z32,z0,z1,z3,z4,z6,z120]),(0,[z447,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z448,z5,z6])]],
   [[(0,[z0,z1,z449,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z450,z5,z6]),(0,[z47,z0,z1,z46,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z52,z6])],[(0,[z35,z234,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z451,z6]),(0,[z0,z1,z3,z4,z5,z6,z452]),(0,[z47,z0,z1,z4,z5,z52,z6]),(0,[z149,z0,z1,z3,z4,z127,z6]),(0,[z167,z32,z0,z1,z3,z4,z6]),(0,[z453,z0,z1,z3,z4,z5,z6])],[(1,[z141,z1,z8,z3,z5,z6]),(1,[z80,z1,z3,z4,z82,z6]),(0,[z0,z1,z454,z3,z4,z5,z6]),(0,[z0,z455,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z456]),(0,[z457,z0,z1,z3,z4,z5,z6]),(0,[z32,z0,z1,z3,z4,z43,z6])],[(0,[z0,z1,z175,z3,z4,z5,z6]),(0,[z32,z0,z1,z220,z3,z4,z6]),(0,[z141,z32,z0,z1,z3,z4,z6]),(0,[z60,z0,z1,z3,z4,z5,z6]),(0,[z35,z0,z205,z1,z3,z4,z6]),(0,[z121,z0,z1,z3,z4,z5,z53]),(0,[z0,z375,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z458,z4,z5,z6]),(0,[z32,z0,z367,z1,z3,z4,z6]),(0,[z0,z1,z48,z3,z4,z258,z6])],[(0,[z0,z328,z1,z220,z3,z4,z6]),(0,[z81,z1,z10,z3,z4,z5,z6]),(0,[z459,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z460,z5,z6])],[(0,[z461,z0,z1,z3,z4,z5,z6]),(0,[z32,z0,z1,z4,z5,z17,z6]),(0,[z0,z1,z3,z4,z69,z17,z6]),(0,[z32,z0,z1,z3,z4,z6,z462]),(0,[z0,z201,z1,z3,z4,z5,z6]),(0,[z463,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z260,z6]),(0,[z117,z0,z1,z3,z4,z5,z57]),(0,[z0,z1,z3,z4,z5,z6,z464]),(0,[z35,z0,z1,z3,z98,z4,z6]),(0,[z0,z1,z465,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z64,z5,z6]),(0,[z0,z1,z3,z4,z5,z466,z6])],[(0,[z79,z0,z1,z175,z3,z4,z6]),(0,[z0,z1,z3,z4,z36,z5,z6]),(0,[z467,z0,z1,z3,z4,z5,z6]),(1,[z0,z375,z1,z3,z4,z6]),(0,[z180,z0,z1,z3,z4,z17,z6])]],
   [[(0,[z80,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z250,z57]),(0,[z0,z91,z3,z98,z4,z5,z6]),(0,[z35,z0,z243,z1,z3,z4,z6]),(0,[z468,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z469,z5,z6]),(0,[z0,z1,z3,z4,z5,z470,z6])],[(0,[z471,z0,z1,z3,z4,z5,z6]),(0,[z81,z0,z1,z3,z4,z51,z6]),(0,[z472,z0,z1,z3,z4,z5,z6])],[(0,[z78,z0,z3,z4,z5,z53,z6]),(0,[z56,z0,z3,z4,z5,z53,z6]),(0,[z0,z1,z473,z3,z4,z5,z6]),(0,[z130,z0,z1,z46,z3,z5,z6])],[(1,[z0,z1,z3,z400,z4,z6]),(0,[z86,z0,z1,z3,z4,z69,z6]),(1,[z0,z1,z3,z4,z131,z6])],[(1,[z0,z1,z3,z4,z274,z6]),(0,[z35,z0,z63,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z474,z6]),(0,[z0,z46,z266,z3,z4,z5,z6]),(0,[z0,z1,z46,z3,z4,z300,z6]),(0,[z0,z1,z3,z4,z17,z6,z174])],[(0,[z0,z1,z3,z4,z5,z193,z6]),(0,[z0,z9,z1,z3,z4,z6,z57]),(0,[z0,z1,z475,z3,z4,z5,z6]),(0,[z226,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z69,z88,z6])],[(0,[z476,z0,z1,z3,z4,z5,z6]),(0,[z477,z0,z1,z3,z4,z5,z6]),(0,[z105,z0,z1,z98,z4,z5,z6]),(0,[z0,z478,z1,z3,z4,z5,z6]),(1,[z0,z9,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z479]),(0,[z32,z0,z1,z3,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z480])],[(0,[z481,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z482,z3,z4,z5,z6]),(0,[z32,z0,z1,z3,z4,z82,z6]),(0,[z0,z1,z483,z3,z4,z5,z6]),(0,[z0,z243,z1,z3,z4,z17,z6]),(0,[z484,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z485,z0,z1,z3,z4,z5,z6]),(0,[z32,z0,z1,z3,z4,z6,z172]),(0,[z32,z0,z1,z3,z4,z17,z6])],[(0,[z32,z0,z1,z3,z4,z336,z6])],[(0,[z179,z0,z1,z3,z4,z5,z6]),(0,[z234,z0,z1,z3,z4,z17,z6]),(0,[z0,z84,z3,z98,z4,z5,z6]),(1,[z226,z0,z84,z4,z5,z6]),(0,[z0,z9,z1,z3,z186,z4,z6]),(0,[z486,z0,z1,z3,z4,z5,z6]),(0,[z487,z0,z1,z3,z4,z5,z6])],[(0,[z488,z0,z1,z3,z4,z5,z6]),(0,[z50,z0,z9,z1,z3,z4,z6]),(0,[z149,z0,z1,z46,z4,z5,z6]),(1,[z0,z1,z3,z4,z300,z6]),(0,[z224,z0,z1,z3,z4,z17,z6])],[(0,[z0,z1,z3,z4,z5,z489,z6]),(0,[z0,z1,z490,z3,z4,z5,z6])],[(0,[z491,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z492,z4,z5,z6]),(1,[z374,z0,z3,z4,z5,z6]),(0,[z35,z50,z0,z1,z3,z4,z6]),(0,[z0,z493,z1,z3,z4,z5,z6]),(0,[z494,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z495]),(0,[z0,z496,z1,z3,z4,z5,z6])],[(0,[z141,z0,z1,z3,z4,z17,z6]),(0,[z497,z0,z1,z3,z4,z5,z6]),(0,[z0,z445,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z5,z6,z199])]],
   [[(1,[z0,z1,z287,z3,z4,z6]),(0,[z498,z0,z1,z3,z4,z5,z6]),(0,[z499,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z288,z4,z17,z6]),(0,[z0,z1,z3,z500,z4,z5,z6]),(0,[z501,z0,z1,z3,z4,z5,z6])],[(0,[z34,z0,z1,z3,z4,z502,z6]),(0,[z503,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z291,z5,z6]),(0,[z0,z1,z46,z3,z5,z150,z6]),(0,[z42,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z504,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z505,z6]),(0,[z0,z1,z3,z4,z5,z506,z6]),(1,[z0,z126,z1,z3,z5,z6]),(0,[z0,z1,z507,z3,z4,z5,z6])],[(1,[z117,z1,z3,z4,z5,z61]),(1,[z32,z0,z1,z3,z4,z6])],[(0,[z0,z328,z1,z3,z4,z5,z6]),(0,[z81,z35,z0,z1,z3,z4,z6]),(0,[z32,z0,z243,z1,z3,z4,z6]),(1,[z0,z1,z3,z186,z5,z150]),(0,[z0,z1,z3,z4,z508,z5,z6])],[(0,[z509,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z510,z4,z5,z6]),(1,[z32,z0,z1,z4,z17,z6])],[(0,[z0,z1,z3,z4,z5,z6,z511]),(0,[z512,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z6]),(0,[z0,z513,z1,z3,z4,z5,z6]),(0,[z35,z0,z9,z1,z3,z4,z6]),(0,[z0,z514,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z515,z6]),(0,[z0,z1,z3,z4,z17,z6,z57]),(1,[z0,z1,z299,z3,z4,z6]),(0,[z516,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z42,z234,z0,z1,z4,z5,z6]),(0,[z517,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z518,z4,z5,z6]),(0,[z519,z0,z1,z3,z4,z5,z6]),(0,[z520,z0,z1,z3,z4,z5,z6]),(0,[z50,z32,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z87,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z521]),(0,[z0,z522,z1,z3,z4,z5,z6])],[(1,[z0,z523,z1,z3,z4,z6]),(0,[z0,z189,z91,z1,z3,z5,z6]),(1,[z0,z445,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z524,z6]),(0,[z0,z1,z3,z4,z5,z258,z6])],[(0,[z0,z9,z1,z175,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z525]),(0,[z218,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z526]),(0,[z391,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z48,z4,z5,z43,z6]),(1,[z222,z86,z0,z1,z3,z6])],[(0,[z35,z0,z112,z1,z3,z4,z6]),(0,[z527,z0,z1,z3,z4,z5,z6]),(0,[z0,z9,z1,z3,z4,z76,z6]),(0,[z0,z9,z1,z3,z4,z6,z389]),(0,[z0,z9,z1,z3,z4,z88,z6]),(0,[z0,z1,z3,z4,z17,z6,z345])],[(0,[z0,z1,z3,z4,z502,z5,z6]),(1,[z7,z1,z3,z336,z5,z6]),(0,[z226,z0,z9,z1,z3,z4,z6]),(0,[z105,z0,z84,z1,z4,z5,z6])],[(0,[z0,z1,z528,z3,z4,z5,z6]),(0,[z0,z197,z1,z3,z4,z17,z6]),(0,[z529,z0,z1,z3,z4,z5,z6]),(0,[z453,z32,z0,z1,z3,z4,z6])],[(0,[z0,z9,z1,z3,z4,z28,z6]),(0,[z7,z0,z1,z3,z5,z150,z6]),(0,[z0,z1,z3,z4,z5,z6,z530]),(0,[z81,z0,z1,z10,z3,z4,z6]),(0,[z418,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z531,z5,z6]),(1,[z0,z1,z3,z5,z6,z250]),(0,[z0,z1,z3,z4,z5,z532,z6]),(0,[z0,z1,z288,z4,z5,z17,z6])]],
   [[(0,[z0,z272,z1,z3,z4,z6,z57]),(0,[z0,z1,z3,z4,z5,z533,z6]),(0,[z149,z0,z1,z3,z4,z5,z6]),(0,[z405,z0,z1,z3,z4,z17,z6]),(0,[z0,z534,z1,z3,z4,z5,z6])],[(0,[z0,z1,z535,z3,z4,z5,z6]),(0,[z0,z523,z1,z8,z3,z4,z6]),(0,[z168,z0,z1,z3,z64,z5,z6]),(0,[z0,z205,z1,z3,z4,z5,z6]),(0,[z0,z1,z536,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z20,z6]),(0,[z0,z537,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z538]),(0,[z0,z1,z3,z4,z539,z5,z6])],[(0,[z0,z75,z1,z3,z4,z5,z6]),(0,[z0,z197,z63,z1,z3,z5,z6]),(0,[z0,z9,z1,z3,z4,z401,z6]),(0,[z0,z9,z1,z3,z4,z150,z6]),(0,[z0,z1,z3,z4,z17,z51,z6]),(0,[z0,z1,z4,z5,z43,z6,z195]),(0,[z0,z1,z3,z4,z540,z5,z6])],[(0,[z78,z0,z1,z3,z4,z5,z6]),(0,[z56,z0,z1,z3,z4,z5,z6]),(1,[z0,z63,z3,z64,z5,z6]),(0,[z0,z1,z3,z4,z5,z16,z6]),(0,[z222,z0,z1,z3,z4,z88,z6])],[(0,[z92,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z541,z6]),(0,[z32,z0,z1,z156,z3,z4,z6])],[(0,[z0,z1,z3,z4,z5,z6,z542]),(0,[z0,z543,z1,z3,z4,z5,z6]),(0,[z0,z197,z1,z3,z4,z417,z6]),(0,[z47,z0,z1,z3,z4,z5,z6]),(0,[z420,z0,z1,z3,z4,z17,z6]),(0,[z0,z544,z1,z3,z4,z5,z6])],[(0,[z0,z91,z1,z98,z4,z5,z6]),(0,[z105,z0,z1,z3,z4,z5,z6]),(0,[z32,z0,z1,z3,z4,z545,z6]),(1,[z0,z1,z48,z4,z5,z43]),(0,[z0,z1,z3,z4,z5,z6,z546])],[(0,[z0,z1,z3,z547,z4,z5,z6]),(0,[z0,z548,z1,z3,z4,z5,z6]),(0,[z0,z549,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z173,z6])]],
   [[(0,[z0,z1,z550,z3,z4,z5,z6]),(0,[z0,z1,z551,z3,z4,z5,z6]),(0,[z168,z35,z0,z1,z3,z4,z6]),(0,[z347,z0,z9,z1,z3,z4,z6]),(0,[z42,z0,z9,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z5,z552,z6]),(0,[z0,z1,z10,z3,z4,z5,z6]),(0,[z35,z0,z1,z3,z4,z6,z57]),(0,[z226,z32,z0,z1,z3,z4,z6]),(0,[z0,z243,z9,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z53,z6]),(0,[z0,z1,z3,z4,z5,z6,z553])],[(0,[z0,z1,z554,z3,z4,z5,z6]),(0,[z32,z0,z9,z1,z3,z4,z6]),(0,[z0,z1,z288,z3,z4,z17,z6]),(0,[z222,z0,z1,z3,z87,z5,z6])],[(0,[z0,z1,z3,z4,z555,z5,z6]),(0,[z35,z0,z1,z3,z4,z6,z341]),(0,[z0,z1,z3,z4,z5,z556,z6]),(0,[z557,z0,z1,z3,z4,z5,z6])],[(0,[z558,z0,z1,z3,z4,z5,z6]),(0,[z234,z0,z9,z1,z3,z4,z6]),(0,[z7,z0,z1,z3,z336,z5,z6]),(0,[z0,z1,z3,z4,z336,z17,z6]),(1,[z0,z1,z439,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z559]),(0,[z50,z0,z1,z3,z4,z17,z6]),(0,[z0,z1,z560,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z561,z6]),(0,[z0,z1,z3,z4,z562,z5,z6]),(0,[z563,z0,z1,z3,z4,z5,z6]),(0,[z0,z63,z1,z3,z4,z17,z6]),(0,[z0,z9,z1,z40,z4,z5,z6]),(1,[z0,z38,z1,z4,z5,z6]),(0,[z0,z9,z1,z3,z87,z4,z6]),(0,[z0,z1,z3,z564,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z565])],[(0,[z566,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z285]),(0,[z35,z0,z1,z3,z186,z4,z6]),(1,[z391,z0,z1,z3,z4,z6])],[(0,[z32,z0,z112,z1,z3,z4,z6]),(0,[z0,z1,z567,z3,z4,z5,z6]),(0,[z519,z0,z9,z1,z3,z4,z6]),(0,[z130,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z69,z51])]],
   [[(0,[z0,z1,z3,z4,z5,z568,z6]),(0,[z0,z9,z1,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z569]),(0,[z130,z0,z1,z3,z4,z5,z150]),(0,[z0,z570,z1,z3,z4,z5,z6])],[(0,[z0,z1,z8,z3,z4,z193,z6]),(0,[z347,z226,z0,z1,z3,z4,z6]),(0,[z571,z0,z1,z3,z4,z5,z6]),(0,[z572,z35,z0,z1,z3,z4,z6]),(0,[z573,z0,z1,z3,z4,z5,z6])],[(0,[z56,z112,z1,z3,z4,z5,z6]),(0,[z222,z0,z197,z1,z3,z5,z6]),(0,[z35,z149,z0,z1,z3,z4,z6]),(0,[z0,z574,z1,z3,z4,z5,z6]),(0,[z575,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z576,z3,z4,z5,z6])],[(0,[z0,z1,z175,z3,z4,z17,z6]),(0,[z60,z0,z1,z3,z4,z17,z6]),(0,[z0,z1,z3,z4,z5,z6,z177]),(0,[z577,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z578]),(0,[z0,z1,z3,z4,z5,z6,z579])],[(0,[z35,z0,z91,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z580,z6]),(0,[z0,z1,z3,z4,z17,z150,z6]),(0,[z0,z1,z581,z3,z4,z5,z6])],[(0,[z0,z1,z287,z3,z4,z5,z6]),(0,[z0,z582,z1,z3,z4,z5,z6]),(1,[z0,z9,z3,z4,z16,z6]),(0,[z0,z9,z1,z3,z4,z6,z174]),(0,[z155,z0,z46,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z127,z6]),(0,[z347,z32,z0,z1,z3,z4,z6]),(0,[z42,z32,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z49,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z583]),(0,[z0,z1,z3,z584,z4,z5,z6]),(0,[z0,z585,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z64,z17,z6])],[(0,[z0,z1,z586,z3,z4,z5,z6]),(0,[z587,z0,z1,z3,z4,z5,z6]),(0,[z80,z0,z1,z3,z4,z82,z6]),(0,[z149,z0,z9,z1,z3,z4,z6])]],
   [[(0,[z0,z1,z384,z3,z4,z5,z6]),(0,[z80,z0,z1,z3,z4,z17,z6]),(1,[z105,z32,z0,z1,z4,z6]),(0,[z130,z0,z1,z3,z5,z6,z120])],[(0,[z0,z588,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z589,z6]),(0,[z60,z0,z1,z3,z4,z5,z61]),(0,[z0,z388,z9,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z590,z5,z6])],[],[(0,[z0,z1,z3,z4,z28,z5,z6]),(0,[z0,z1,z591,z3,z4,z5,z6]),(0,[z0,z592,z1,z3,z4,z5,z6]),(0,[z81,z86,z0,z1,z3,z4,z6]),(0,[z35,z0,z9,z3,z4,z5,z6]),(0,[z516,z32,z0,z1,z3,z4,z6]),(0,[z0,z1,z593,z3,z4,z5,z6]),(0,[z0,z594,z1,z3,z4,z5,z6])],[(0,[z34,z1,z3,z4,z28,z5,z6]),(0,[z595,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z596,z6]),(0,[z47,z0,z9,z1,z3,z4,z6])],[(0,[z597,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z61,z6]),(0,[z32,z0,z1,z3,z4,z6,z57]),(0,[z226,z0,z1,z3,z4,z17,z6]),(0,[z0,z9,z1,z3,z40,z4,z6]),(0,[z0,z1,z598,z3,z4,z5,z6]),(0,[z121,z35,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z599,z6]),(0,[z0,z1,z3,z600,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z601,z6])],[(0,[z35,z0,z1,z175,z3,z4,z6]),(1,[z347,z0,z1,z3,z4,z6]),(0,[z0,z1,z48,z3,z4,z5,z6])],[(0,[z223,z0,z1,z3,z4,z5,z6]),(0,[z0,z197,z9,z1,z3,z4,z6]),(0,[z602,z0,z1,z3,z4,z5,z6]),(0,[z18,z35,z0,z1,z3,z4,z6]),(0,[z35,z0,z1,z3,z4,z88,z6]),(0,[z0,z1,z3,z4,z603,z5,z6])]],
   [[(0,[z35,z0,z1,z3,z4,z6,z195]),(0,[z604,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z364,z5,z6]),(0,[z605,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z606,z6]),(0,[z0,z1,z3,z4,z607,z5,z6]),(0,[z0,z1,z3,z4,z5,z608,z6]),(1,[z0,z1,z40,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z609]),(0,[z0,z1,z3,z4,z5,z6,z610]),(0,[z611,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z612,z5,z6]),(0,[z35,z0,z1,z3,z4,z28,z6]),(0,[z0,z1,z3,z4,z5,z165,z6]),(0,[z32,z0,z1,z3,z186,z4,z6])],[(0,[z0,z1,z3,z4,z613,z5,z6]),(0,[z141,z0,z1,z3,z5,z150,z6]),(1,[z0,z1,z3,z354,z4,z6]),(0,[z35,z316,z0,z1,z3,z4,z6]),(1,[z0,z1,z3,z291,z5,z6]),(0,[z0,z205,z3,z4,z5,z53,z6]),(0,[z0,z1,z3,z4,z5,z43,z6]),(0,[z0,z1,z3,z614,z4,z5,z6]),(0,[z0,z1,z3,z4,z51,z6,z174])],[(0,[z0,z1,z3,z615,z4,z5,z6]),(0,[z616,z0,z1,z3,z4,z5,z6]),(0,[z35,z130,z0,z1,z3,z4,z6]),(0,[z149,z32,z0,z1,z3,z4,z6])],[(0,[z0,z304,z1,z3,z4,z5,z6]),(0,[z617,z0,z1,z3,z4,z5,z6]),(0,[z86,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z618,z6])],[(0,[z619,z0,z1,z3,z4,z5,z6]),(0,[z81,z0,z1,z3,z4,z5,z6]),(0,[z0,z91,z1,z3,z4,z5,z6]),(0,[z130,z0,z9,z1,z3,z4,z6]),(0,[z35,z0,z1,z3,z4,z150,z6]),(0,[z0,z1,z3,z4,z382,z5,z6]),(0,[z0,z1,z3,z4,z17,z52,z6]),(0,[z0,z1,z3,z4,z5,z6,z462])],[(0,[z620,z0,z1,z3,z4,z5,z6]),(0,[z78,z32,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z621,z6]),(0,[z0,z1,z3,z4,z5,z622,z6]),(0,[z0,z1,z3,z98,z4,z5,z6]),(0,[z623,z0,z1,z3,z4,z5,z6]),(0,[z42,z0,z1,z4,z5,z6,z195]),(0,[z222,z86,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z69,z5,z51])]],
   [[(0,[z624,z0,z1,z3,z4,z5,z6]),(1,[z234,z1,z220,z4,z5,z6]),(0,[z35,z7,z0,z1,z3,z4,z6]),(0,[z625,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z17,z61,z6]),(0,[z32,z0,z91,z1,z3,z4,z6])],[(1,[z0,z1,z3,z4,z502,z6]),(0,[z0,z1,z626,z3,z4,z5,z6]),(0,[z0,z1,z3,z627,z4,z5,z6]),(1,[z0,z1,z3,z4,z6,z286]),(0,[z42,z0,z1,z3,z4,z17,z6]),(0,[z42,z0,z1,z3,z4,z173,z6]),(0,[z0,z1,z214,z3,z4,z5,z6])],[(0,[z0,z1,z1,z3,z4,z5,z6]),(0,[z130,z141,z0,z1,z3,z5,z6]),(0,[z0,z197,z1,z3,z5,z88,z6]),(0,[z105,z32,z0,z1,z3,z4,z6])],[(0,[z628,z0,z1,z3,z4,z5,z6]),(0,[z117,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z629,z4,z5,z6]),(0,[z0,z1,z630,z3,z4,z5,z6]),(0,[z35,z0,z1,z3,z4,z460,z6]),(0,[z0,z1,z3,z5,z6,z199,z195])],[(0,[z631,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z632,z3,z4,z5,z6]),(0,[z0,z1,z633,z3,z4,z5,z6]),(0,[z634,z0,z1,z3,z4,z5,z6]),(0,[z168,z0,z63,z3,z4,z5,z6])],[(0,[z0,z635,z1,z3,z4,z5,z6]),(0,[z636,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z266,z3,z4,z5,z6]),(0,[z50,z0,z1,z3,z4,z6,z174])],[(0,[z0,z637,z1,z3,z4,z5,z6]),(0,[z638,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z639,z6]),(1,[z0,z1,z396,z3,z4,z6])]],
   [[(0,[z0,z1,z3,z640,z4,z5,z6]),(0,[z0,z84,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z87,z4,z17,z6])],[(0,[z141,z0,z1,z3,z336,z5,z6]),(0,[z60,z1,z3,z4,z5,z6,z57]),(0,[z0,z1,z299,z3,z4,z5,z6]),(0,[z0,z197,z1,z3,z5,z150,z6]),(1,[z0,z1,z3,z40,z4,z6]),(0,[z35,z0,z1,z3,z87,z4,z6])],[(0,[z32,z0,z205,z1,z3,z4,z6]),(0,[z105,z0,z1,z288,z4,z5,z6]),(0,[z566,z32,z0,z1,z3,z4,z6]),(0,[z222,z86,z0,z1,z3,z4,z6]),(0,[z0,z1,z641,z3,z4,z5,z6])],[(0,[z0,z1,z220,z3,z4,z165,z6]),(1,[z0,z1,z3,z4,z275,z6]),(0,[z0,z9,z1,z3,z4,z51,z6]),(0,[z124,z35,z0,z1,z3,z4,z6]),(0,[z130,z32,z0,z1,z3,z4,z6]),(0,[z32,z0,z1,z3,z4,z88,z6]),(0,[z0,z1,z642,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z643]),(0,[z0,z1,z644,z3,z4,z5,z6])],[(1,[z79,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z645,z6]),(0,[z0,z1,z646,z3,z4,z5,z6]),(0,[z35,z0,z1,z1,z3,z4,z6]),(0,[z35,z0,z1,z379,z3,z4,z6]),(0,[z32,z0,z1,z3,z4,z6,z195]),(1,[z0,z1,z3,z4,z49,z6]),(0,[z647,z0,z1,z3,z4,z5,z6])],[(0,[z60,z0,z9,z1,z3,z4,z6]),(0,[z32,z0,z1,z3,z98,z4,z6]),(0,[z0,z648,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z649,z6]),(0,[z32,z0,z1,z3,z4,z28,z6]),(0,[z0,z1,z3,z4,z5,z650,z6]),(1,[z180,z0,z1,z3,z4,z6]),(0,[z226,z0,z84,z3,z4,z5,z6]),(0,[z0,z9,z1,z3,z4,z69,z6]),(0,[z0,z1,z3,z4,z651,z5,z6]),(0,[z0,z1,z3,z652,z4,z5,z6]),(0,[z0,z1,z3,z4,z382,z53,z6]),(0,[z130,z0,z1,z3,z4,z364,z6])],[(0,[z168,z0,z3,z98,z4,z5,z6]),(0,[z105,z32,z0,z1,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z653]),(0,[z0,z523,z1,z3,z4,z5,z6]),(0,[z374,z0,z3,z4,z5,z6,z57]),(0,[z654,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z46,z5,z52,z6]),(0,[z149,z0,z1,z3,z4,z17,z6]),(0,[z32,z0,z1,z3,z4,z655,z6])],[(0,[z112,z1,z175,z3,z4,z5,z6]),(0,[z0,z656,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z417,z6]),(0,[z35,z0,z197,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z295,z6]),(0,[z35,z0,z1,z3,z4,z6,z174]),(0,[z121,z0,z205,z3,z4,z5,z6]),(0,[z657,z0,z1,z3,z4,z5,z6]),(0,[z164,z0,z1,z3,z4,z5,z6])],[(0,[z80,z0,z9,z1,z3,z4,z6]),(0,[z658,z0,z1,z3,z4,z5,z6]),(0,[z0,z659,z1,z3,z4,z5,z6]),(0,[z168,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z660,z5,z6]),(0,[z0,z1,z3,z4,z5,z661,z6]),(0,[z32,z0,z1,z3,z4,z150,z6]),(0,[z0,z1,z3,z4,z655,z5,z6])],[(0,[z78,z56,z1,z3,z4,z5,z6]),(0,[z78,z0,z1,z3,z4,z17,z6]),(0,[z56,z0,z1,z3,z4,z17,z6]),(0,[z662,z0,z1,z3,z4,z5,z6]),(0,[z32,z0,z63,z1,z3,z4,z6]),(0,[z121,z154,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z663,z6])],[(0,[z0,z1,z3,z4,z664,z5,z6]),(0,[z0,z1,z3,z4,z5,z5,z6])],[(0,[z0,z665,z1,z3,z4,z5,z6]),(0,[z81,z80,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z666,z5,z6]),(1,[z0,z272,z1,z3,z4,z6]),(1,[z0,z304,z1,z3,z4,z6]),(0,[z0,z91,z9,z1,z3,z4,z6]),(0,[z667,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z668]),(0,[z47,z0,z1,z3,z4,z17,z6]),(0,[z0,z544,z1,z3,z4,z17,z6]),(0,[z669,z0,z1,z3,z4,z5,z6])],[(0,[z670,z0,z1,z3,z4,z5,z6]),(0,[z0,z9,z1,z48,z3,z4,z6]),(0,[z0,z445,z9,z1,z3,z5,z6]),(0,[z0,z3,z4,z5,z53,z6,z172]),(0,[z0,z1,z671,z3,z4,z5,z6]),(0,[z105,z0,z1,z3,z4,z17,z6]),(0,[z672,z0,z1,z3,z4,z5,z6])],[(0,[z168,z0,z197,z3,z4,z5,z6]),(0,[z0,z9,z1,z3,z4,z16,z6]),(0,[z673,z0,z1,z3,z4,z5,z6]),(1,[z42,z0,z1,z4,z5,z195])]],
   [[(0,[z0,z1,z3,z4,z5,z674,z6]),(0,[z56,z0,z1,z3,z4,z196,z6]),(1,[z223,z0,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z675,z6]),(0,[z676,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z677,z4,z5,z6])],[(0,[z0,z678,z1,z3,z4,z5,z6]),(0,[z0,z9,z1,z8,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z679]),(0,[z0,z1,z10,z3,z4,z17,z6]),(0,[z0,z1,z3,z186,z4,z5,z6])],[(0,[z680,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z681,z4,z5,z6]),(0,[z60,z32,z0,z1,z3,z4,z6]),(0,[z271,z0,z1,z3,z4,z5,z6]),(0,[z117,z0,z9,z1,z3,z4,z6]),(0,[z0,z1,z3,z186,z4,z5,z150])],[(0,[z0,z1,z3,z4,z5,z6,z682]),(0,[z572,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z683,z3,z4,z5,z6])],[(0,[z0,z1,z684,z3,z4,z5,z6]),(1,[z0,z1,z3,z324,z4,z6]),(0,[z206,z0,z1,z3,z4,z5,z6])],[(1,[z271,z0,z1,z3,z5,z6]),(0,[z0,z197,z1,z439,z3,z4,z6]),(0,[z685,z0,z1,z3,z4,z5,z6]),(0,[z32,z0,z1,z3,z87,z4,z6]),(0,[z686,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z69,z5,z174])],[(0,[z0,z687,z1,z3,z4,z5,z6]),(0,[z0,z688,z1,z3,z4,z5,z6]),(0,[z35,z0,z514,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z689,z6]),(0,[z0,z1,z46,z3,z5,z52,z6])],[(1,[z0,z1,z384,z3,z4,z6]),(0,[z0,z1,z3,z3,z4,z5,z6]),(0,[z60,z117,z1,z3,z4,z5,z6]),(0,[z222,z0,z1,z3,z64,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z690]),(0,[z35,z0,z1,z3,z349,z4,z6]),(0,[z0,z1,z3,z4,z691,z5,z6]),(0,[z692,z0,z1,z3,z4,z5,z6]),(0,[z130,z0,z1,z3,z4,z17,z6])]],
   [[(0,[z0,z693,z1,z3,z4,z5,z6]),(0,[z35,z0,z243,z3,z4,z5,z6])],[(0,[z35,z80,z0,z1,z3,z4,z6]),(0,[z0,z445,z9,z1,z3,z4,z6]),(0,[z0,z694,z1,z3,z4,z5,z6]),(0,[z86,z32,z0,z1,z3,z4,z6]),(0,[z695,z0,z1,z3,z4,z5,z6]),(0,[z696,z0,z1,z3,z4,z5,z6])],[(0,[z81,z32,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z400,z98,z4,z6])],[(0,[z0,z697,z1,z3,z4,z5,z6]),(1,[z168,z0,z197,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z698]),(0,[z0,z1,z3,z699,z4,z5,z6]),(0,[z0,z1,z3,z4,z700,z5,z6])],[(0,[z1,z175,z3,z4,z5,z6,z57]),(1,[z0,z91,z98,z4,z5,z6]),(0,[z230,z0,z1,z3,z4,z5,z6]),(0,[z701,z0,z1,z3,z4,z5,z6])],[(0,[z0,z702,z1,z3,z4,z5,z6]),(0,[z0,z1,z220,z3,z4,z5,z6]),(0,[z130,z7,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z703]),(0,[z32,z0,z197,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z704,z5,z6]),(0,[z32,z0,z1,z3,z4,z6,z174])],[(0,[z705,z0,z1,z3,z4,z5,z6]),(2,[z0,z1,z40,z4,z6]),(0,[z222,z35,z0,z1,z3,z4,z6]),(0,[z35,z86,z0,z1,z3,z4,z6])],[(0,[z121,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z706,z6]),(0,[z0,z1,z3,z4,z20,z6,z172]),(0,[z0,z1,z3,z4,z5,z545,z6]),(0,[z0,z1,z3,z4,z88,z6,z174])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z3,z4,z502,z6]),(0,[z0,z707,z3,z4,z5,z6]),(0,[z130,z0,z1,z3,z5,z583]),(0,[z0,z9,z1,z3,z6,z250]),(0,[z0,z1,z3,z708,z4,z6]),(0,[z0,z197,z709,z3,z5,z6]),(0,[z0,z9,z3,z677,z4,z6]),(0,[z222,z0,z1,z3,z76,z6]),(0,[z418,z0,z1,z3,z4,z341]),(0,[z710,z0,z1,z3,z4,z6]),(0,[z420,z1,z227,z3,z4,z6])],[(0,[z498,z0,z1,z4,z17,z6]),(0,[z658,z0,z9,z3,z4,z6]),(0,[z0,z1,z3,z4,z711,z6]),(0,[z0,z126,z1,z3,z17,z6])],[(0,[z268,z1,z3,z4,z5,z57]),(0,[z1,z712,z3,z4,z82,z6]),(0,[z80,z201,z1,z3,z4,z6]),(0,[z117,z1,z3,z4,z17,z61]),(0,[z713,z1,z3,z4,z5,z6]),(0,[z0,z709,z1,z3,z5,z6]),(0,[z47,z0,z1,z683,z5,z6]),(0,[z0,z1,z350,z4,z17,z6])],[(0,[z155,z0,z3,z4,z5,z6]),(0,[z0,z91,z400,z98,z4,z6]),(0,[z0,z9,z1,z3,z291,z6]),(0,[z35,z0,z1,z46,z52,z6]),(0,[z0,z1,z3,z4,z714,z6]),(0,[z715,z0,z1,z4,z17,z6])],[(0,[z0,z1,z716,z3,z4,z6]),(0,[z0,z1,z3,z4,z717,z6]),(0,[z35,z718,z1,z3,z4,z6]),(0,[z32,z0,z266,z3,z4,z6]),(0,[z0,z1,z3,z4,z69,z545])],[(0,[z60,z3,z4,z5,z177,z57]),(0,[z0,z719,z1,z3,z4,z6]),(0,[z0,z66,z1,z3,z4,z6]),(0,[z35,z0,z38,z1,z4,z6]),(0,[z0,z9,z89,z3,z4,z6]),(0,[z720,z0,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z721,z6]),(0,[z0,z1,z722,z4,z5,z6]),(0,[z0,z1,z396,z3,z4,z6]),(0,[z149,z0,z723,z1,z5,z6]),(0,[z0,z724,z1,z3,z5,z6])],[(0,[z347,z0,z1,z3,z725,z6]),(0,[z0,z1,z3,z4,z726,z6]),(0,[z0,z1,z3,z4,z727,z6])]],
   [[(0,[z0,z1,z3,z4,z728,z6]),(0,[z0,z1,z3,z4,z729,z6]),(0,[z0,z1,z3,z4,z6,z730]),(0,[z35,z0,z731,z3,z4,z6]),(0,[z121,z0,z3,z4,z5,z172])],[(0,[z732,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z53,z733])],[(0,[z0,z734,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z735,z6]),(0,[z60,z1,z4,z5,z285,z57]),(0,[z13,z32,z0,z1,z4,z6])],[(0,[z79,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z736,z4,z6]),(0,[z0,z1,z3,z4,z737,z6]),(0,[z0,z1,z3,z4,z738,z6])],[(0,[z0,z1,z3,z4,z193,z6]),(0,[z739,z1,z3,z4,z5,z6]),(0,[z35,z0,z126,z1,z3,z6]),(0,[z222,z0,z1,z3,z460,z6]),(0,[z0,z723,z1,z3,z5,z6])],[(0,[z78,z79,z175,z3,z4,z6]),(0,[z0,z1,z740,z3,z4,z6]),(0,[z180,z0,z1,z3,z4,z6]),(0,[z35,z130,z0,z1,z3,z120])],[(1,[z1,z741,z4,z5,z6]),(0,[z742,z0,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z743])],[(0,[z0,z1,z3,z4,z5,z744]),(0,[z0,z1,z745,z4,z5,z6]),(0,[z0,z1,z746,z4,z5,z6]),(0,[z234,z0,z1,z40,z4,z6]),(0,[z0,z1,z46,z5,z52,z6]),(0,[z32,z0,z1,z27,z4,z6])]],
   [[(0,[z0,z747,z1,z3,z4,z6]),(0,[z0,z1,z3,z748,z5,z6]),(0,[z35,z0,z1,z4,z6,z285]),(0,[z29,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z749,z4,z6]),(0,[z0,z445,z1,z3,z76,z6]),(0,[z0,z445,z1,z3,z88,z6]),(0,[z32,z0,z1,z3,z291,z6]),(0,[z0,z1,z3,z4,z750,z6]),(0,[z32,z0,z1,z214,z3,z6])],[(0,[z0,z1,z3,z4,z5,z751]),(0,[z271,z0,z1,z3,z17,z6]),(0,[z0,z544,z98,z4,z17,z6]),(0,[z0,z1,z3,z5,z6,z752])],[(0,[z0,z63,z3,z64,z17,z6]),(0,[z0,z243,z367,z3,z4,z6]),(0,[z0,z1,z214,z3,z5,z6]),(0,[z0,z753,z3,z4,z5,z6])],[(0,[z754,z0,z1,z3,z4,z6])],[(0,[z0,z9,z687,z3,z4,z6]),(0,[z0,z304,z1,z3,z4,z6]),(0,[z718,z1,z3,z4,z5,z6]),(0,[z0,z1,z190,z40,z4,z6]),(0,[z0,z1,z755,z40,z4,z6]),(0,[z0,z731,z3,z4,z16,z6])],[(0,[z0,z1,z3,z5,z6,z756]),(0,[z0,z757,z3,z4,z5,z6]),(0,[z0,z1,z758,z3,z5,z6])],[(0,[z34,z1,z4,z28,z5,z6]),(0,[z1,z8,z3,z759,z5,z6]),(0,[z0,z243,z1,z40,z4,z6]),(0,[z32,z0,z1,z3,z760,z6]),(0,[z42,z0,z1,z4,z5,z195])],[(0,[z761,z0,z1,z3,z4,z6]),(0,[z223,z0,z1,z4,z5,z6]),(0,[z0,z1,z762,z3,z4,z6]),(0,[z0,z1,z4,z5,z6,z763]),(0,[z29,z0,z63,z3,z64,z6]),(0,[z168,z0,z197,z3,z17,z6]),(0,[z764,z122,z1,z3,z4,z6]),(0,[z765,z0,z1,z3,z4,z6])]],
   [[(0,[z0,z1,z3,z4,z766,z6]),(0,[z0,z91,z98,z4,z17,z6]),(0,[z0,z1,z439,z3,z88,z6])],[(0,[z767,z0,z1,z3,z4,z6]),(0,[z0,z1,z400,z4,z17,z6]),(0,[z768,z0,z1,z3,z4,z5]),(0,[z168,z0,z197,z439,z3,z6])],[(0,[z60,z35,z1,z3,z4,z57]),(0,[z0,z63,z1,z40,z4,z6]),(0,[z769,z0,z1,z40,z4,z6]),(0,[z0,z1,z40,z4,z6,z770]),(0,[z0,z1,z771,z3,z4,z6]),(0,[z121,z0,z66,z3,z4,z6]),(0,[z0,z1,z46,z17,z52,z6])],[(0,[z0,z1,z3,z4,z772,z6]),(0,[z0,z1,z3,z4,z773,z6]),(0,[z0,z1,z774,z4,z5,z6]),(0,[z0,z775,z3,z4,z5,z6]),(0,[z223,z0,z1,z776,z4,z6]),(0,[z0,z1,z3,z4,z6,z777])],[(0,[z778,z0,z1,z4,z5,z6]),(0,[z0,z38,z1,z4,z17,z6])],[(0,[z0,z779,z3,z4,z6,z177]),(0,[z347,z0,z367,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z780]),(0,[z0,z388,z1,z40,z4,z6]),(0,[z121,z35,z0,z3,z4,z172]),(0,[z781,z1,z3,z4,z17,z6]),(0,[z0,z1,z410,z4,z17,z6])],[(0,[z0,z1,z384,z3,z4,z6]),(0,[z782,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z783,z6]),(0,[z0,z784,z1,z3,z5,z6]),(0,[z0,z1,z3,z785,z4,z6])],[(0,[z78,z175,z3,z4,z5,z6]),(0,[z786,z0,z1,z3,z4,z6]),(0,[z32,z0,z1,z584,z4,z6]),(0,[z0,z1,z3,z252,z5,z150]),(0,[z0,z1,z787,z4,z5,z6]),(0,[z168,z0,z197,z3,z417,z6]),(0,[z0,z1,z40,z4,z6,z120]),(0,[z92,z0,z1,z3,z4,z389]),(0,[z0,z9,z493,z3,z4,z6]),(0,[z0,z1,z788,z3,z4,z6]),(0,[z789,z1,z3,z4,z5,z6]),(0,[z0,z790,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z69,z432])]],
   [[(0,[z0,z791,z1,z3,z4,z6]),(0,[z0,z1,z3,z36,z17,z6]),(0,[z0,z493,z3,z64,z5,z6]),(0,[z164,z1,z3,z4,z58,z6]),(0,[z0,z1,z3,z4,z258,z6])],[(0,[z792,z0,z1,z3,z4,z5]),(0,[z0,z793,z1,z3,z5,z6]),(1,[z1,z712,z3,z4,z6]),(0,[z0,z1,z200,z4,z17,z6]),(0,[z105,z715,z0,z1,z4,z6]),(0,[z0,z1,z48,z4,z5,z794])],[(0,[z7,z254,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z6,z795]),(0,[z0,z9,z1,z796,z4,z6]),(0,[z0,z1,z85,z4,z17,z6]),(0,[z18,z0,z1,z3,z4,z295]),(0,[z797,z1,z3,z4,z5,z6])],[(0,[z50,z0,z1,z40,z4,z6]),(0,[z0,z1,z3,z76,z69,z6]),(0,[z35,z154,z1,z3,z4,z6]),(0,[z0,z798,z266,z3,z4,z6])],[(0,[z0,z1,z3,z799,z5,z6]),(0,[z0,z1,z3,z4,z800,z6]),(0,[z801,z374,z0,z3,z4,z6]),(0,[z0,z1,z3,z776,z4,z6]),(0,[z0,z266,z3,z4,z5,z6]),(0,[z802,z1,z3,z4,z5,z6]),(0,[z0,z723,z1,z4,z5,z6]),(0,[z0,z803,z3,z4,z17,z6])],[(0,[z60,z1,z3,z4,z17,z57]),(0,[z226,z0,z84,z4,z275,z6]),(0,[z0,z1,z804,z3,z4,z6]),(0,[z105,z0,z1,z40,z4,z6]),(0,[z35,z42,z0,z1,z4,z195]),(0,[z805,z155,z0,z3,z4,z6]),(0,[z151,z0,z1,z3,z655,z6]),(0,[z32,z0,z1,z4,z448,z6])],[(0,[z806,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z807,z6])],[(0,[z808,z0,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z809,z6]),(0,[z0,z84,z810,z4,z5,z6]),(0,[z0,z1,z40,z186,z4,z6])]],
   [[(0,[z0,z1,z3,z4,z811,z6]),(0,[z0,z1,z812,z3,z4,z6]),(0,[z0,z1,z3,z4,z813,z6]),(0,[z35,z117,z1,z3,z4,z61]),(0,[z0,z1,z3,z4,z20,z6]),(0,[z0,z814,z1,z3,z4,z6])],[(0,[z141,z1,z3,z5,z6,z267]),(0,[z0,z1,z815,z3,z4,z6]),(0,[z0,z1,z816,z3,z4,z6]),(0,[z0,z1,z3,z817,z5,z6])],[(0,[z0,z1,z3,z4,z818,z6]),(0,[z0,z1,z4,z5,z6,z285]),(0,[z0,z1,z3,z819,z4,z6]),(0,[z347,z0,z1,z3,z76,z6]),(0,[z130,z0,z9,z1,z3,z120]),(0,[z0,z1,z3,z4,z5,z733]),(0,[z0,z1,z3,z4,z820,z6])],[(0,[z60,z1,z3,z4,z5,z751]),(0,[z0,z189,z9,z1,z3,z6]),(0,[z1,z3,z4,z5,z6,z821]),(0,[z347,z0,z156,z3,z4,z6]),(0,[z822,z0,z1,z3,z4,z6])],[(0,[z563,z0,z1,z4,z17,z6]),(0,[z0,z1,z779,z3,z4,z6]),(0,[z0,z823,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z824,z6]),(0,[z0,z9,z1,z40,z4,z6]),(0,[z0,z1,z3,z825,z5,z6])],[(0,[z0,z1,z3,z4,z826,z6]),(0,[z0,z38,z445,z9,z1,z6]),(0,[z0,z1,z3,z827,z4,z6]),(0,[z0,z205,z3,z291,z5,z53]),(0,[z0,z1,z3,z828,z17,z6]),(0,[z0,z1,z3,z87,z88,z6])],[(0,[z0,z1,z3,z4,z829,z6]),(0,[z830,z0,z1,z3,z4,z6]),(0,[z831,z0,z1,z3,z4,z6])],[(0,[z0,z9,z283,z3,z4,z6]),(0,[z60,z223,z1,z4,z5,z57]),(0,[z0,z1,z3,z354,z88,z6]),(0,[z0,z1,z3,z354,z76,z6]),(0,[z347,z0,z445,z1,z3,z6])]],
   [[(0,[z0,z832,z1,z3,z5,z6]),(0,[z833,z0,z1,z3,z5,z6]),(0,[z0,z834,z9,z1,z4,z6])],[(0,[z35,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z5,z6,z835]),(0,[z0,z112,z1,z40,z4,z6]),(0,[z271,z0,z1,z3,z274,z6]),(0,[z149,z47,z0,z1,z127,z6])],[(0,[z0,z1,z3,z4,z836,z5]),(0,[z0,z66,z175,z3,z4,z6]),(0,[z0,z1,z3,z837,z5,z6]),(0,[z499,z0,z3,z64,z5,z6]),(0,[z838,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z291,z17,z6]),(0,[z0,z1,z3,z4,z839,z6]),(0,[z840,z0,z1,z3,z4,z6]),(0,[z39,z201,z1,z3,z4,z6])],[(0,[z0,z841,z3,z4,z5,z6]),(0,[z842,z0,z1,z3,z4,z6]),(0,[z32,z0,z1,z4,z450,z6]),(0,[z0,z375,z266,z3,z4,z6]),(0,[z843,z0,z1,z3,z4,z6])],[(0,[z374,z175,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z844,z6]),(0,[z0,z66,z3,z4,z16,z6]),(0,[z0,z1,z3,z4,z845,z6])],[(0,[z0,z1,z3,z4,z846,z6]),(0,[z0,z847,z1,z3,z4,z6]),(0,[z32,z0,z1,z4,z351,z6]),(0,[z0,z1,z3,z4,z848,z6]),(0,[z0,z126,z1,z849,z3,z6]),(0,[z0,z850,z1,z3,z4,z6]),(0,[z32,z715,z0,z1,z4,z6]),(0,[z851,z0,z1,z3,z4,z6])],[(0,[z0,z852,z3,z4,z5,z6]),(0,[z0,z1,z3,z99,z4,z6]),(0,[z0,z1,z853,z3,z4,z6]),(0,[z0,z9,z156,z3,z4,z6])],[(0,[z358,z1,z10,z3,z4,z6]),(0,[z0,z1,z4,z17,z6,z423]),(0,[z0,z1,z4,z5,z794,z195]),(0,[z86,z854,z0,z1,z3,z6])]],
   [[(0,[z0,z1,z3,z4,z855,z6]),(0,[z0,z367,z3,z98,z4,z6]),(0,[z0,z1,z3,z5,z6,z856]),(0,[z226,z0,z66,z3,z4,z6]),(0,[z35,z0,z63,z3,z64,z6]),(0,[z0,z1,z40,z4,z76,z6]),(0,[z0,z1,z40,z4,z88,z6]),(0,[z0,z1,z3,z4,z857,z6]),(0,[z0,z858,z66,z1,z3,z6]),(0,[z86,z0,z1,z33,z3,z6]),(0,[z0,z1,z214,z3,z859,z6])],[(0,[z0,z1,z320,z4,z17,z6]),(0,[z0,z1,z40,z4,z6,z195])],[(0,[z164,z1,z3,z4,z82,z6]),(0,[z0,z1,z40,z98,z4,z6]),(0,[z0,z9,z266,z3,z4,z6]),(0,[z155,z0,z375,z3,z4,z6]),(0,[z32,z0,z1,z399,z4,z6])],[(0,[z0,z1,z40,z4,z28,z6]),(0,[z0,z1,z3,z4,z860,z6]),(0,[z0,z1,z3,z4,z861,z6]),(0,[z0,z1,z3,z4,z862,z6]),(0,[z155,z0,z3,z4,z17,z6]),(0,[z0,z863,z3,z4,z5,z6]),(0,[z0,z864,z1,z3,z4,z6]),(0,[z0,z865,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z866,z6]),(0,[z0,z709,z3,z64,z5,z6]),(0,[z867,z0,z1,z40,z4,z6]),(0,[z0,z1,z868,z3,z4,z6]),(0,[z0,z1,z3,z4,z127,z6]),(0,[z405,z0,z1,z3,z4,z174]),(0,[z0,z869,z1,z3,z4,z6])],[(0,[z870,z0,z1,z40,z4,z6]),(0,[z0,z1,z3,z40,z76,z6]),(0,[z121,z154,z3,z4,z5,z172]),(0,[z0,z1,z3,z5,z150,z871])],[(0,[z0,z1,z3,z872,z5,z6]),(0,[z0,z9,z1,z3,z36,z6]),(0,[z0,z873,z1,z3,z4,z6]),(0,[z0,z1,z3,z64,z131,z6]),(0,[z0,z784,z9,z1,z3,z6]),(0,[z0,z9,z40,z4,z16,z6]),(0,[z874,z1,z3,z4,z5,z6])],[(0,[z0,z1,z875,z3,z4,z6]),(0,[z0,z445,z1,z40,z5,z6]),(0,[z0,z731,z9,z3,z4,z6]),(0,[z35,z0,z1,z3,z876,z6]),(0,[z0,z1,z3,z4,z6,z877])]],
   [[(0,[z0,z1,z878,z3,z5,z6]),(0,[z0,z3,z5,z6,z250,z177]),(0,[z0,z1,z3,z4,z879,z6]),(0,[z0,z1,z3,z4,z880,z6]),(0,[z0,z1,z3,z725,z5,z6]),(0,[z0,z1,z3,z881,z4,z6]),(0,[z185,z0,z1,z99,z4,z6]),(0,[z0,z1,z379,z4,z17,z6]),(0,[z121,z0,z3,z4,z17,z172]),(0,[z0,z882,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z883,z17]),(0,[z0,z1,z4,z5,z6,z794]),(0,[z0,z1,z3,z4,z51,z877])],[(0,[z0,z91,z9,z98,z4,z6]),(0,[z0,z793,z9,z1,z3,z6]),(0,[z884,z0,z1,z3,z4,z6]),(0,[z696,z0,z1,z4,z17,z6]),(0,[z885,z0,z1,z3,z4,z6])],[(0,[z0,z1,z886,z3,z4,z6]),(0,[z0,z887,z1,z4,z5,z6]),(0,[z888,z0,z1,z3,z4,z6]),(0,[z0,z93,z1,z40,z4,z6]),(0,[z391,z0,z1,z48,z4,z43]),(0,[z0,z1,z889,z3,z4,z6]),(0,[z0,z1,z3,z4,z877,z174])],[(0,[z223,z32,z0,z1,z4,z6]),(0,[z168,z0,z1,z40,z4,z6]),(0,[z0,z1,z3,z349,z88,z6]),(0,[z0,z1,z3,z4,z295,z174]),(0,[z0,z428,z1,z4,z17,z6]),(0,[z32,z0,z1,z3,z890,z6]),(0,[z891,z0,z1,z3,z4,z6])],[(0,[z0,z1,z3,z759,z5,z6]),(0,[z35,z0,z189,z1,z3,z6]),(0,[z218,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z892,z6]),(0,[z0,z1,z386,z4,z17,z6])],[(0,[z0,z588,z1,z4,z17,z6]),(0,[z0,z1,z3,z4,z893,z6]),(0,[z81,z1,z712,z3,z4,z6]),(0,[z60,z1,z3,z4,z274,z57]),(0,[z0,z1,z894,z3,z4,z6])],[(0,[z0,z4,z5,z6,z285,z177]),(0,[z0,z3,z247,z64,z5,z6]),(0,[z35,z0,z445,z9,z3,z6]),(0,[z0,z38,z1,z40,z4,z6]),(0,[z0,z445,z9,z1,z40,z6]),(0,[z0,z9,z1,z214,z3,z6]),(0,[z437,z0,z1,z3,z4,z174])],[(0,[z0,z1,z3,z4,z895,z6]),(0,[z32,z0,z1,z256,z4,z6]),(0,[z60,z9,z1,z3,z4,z57]),(0,[z223,z0,z1,z5,z6,z250]),(0,[z896,z0,z1,z40,z4,z6]),(0,[z0,z897,z9,z1,z4,z6]),(0,[z898,z0,z1,z3,z4,z6])]],
   [[(0,[z374,z56,z3,z4,z5,z6]),(0,[z316,z1,z3,z4,z82,z6]),(0,[z271,z0,z3,z5,z6,z177]),(1,[z0,z66,z98,z4,z6]),(0,[z35,z0,z9,z3,z4,z6]),(0,[z149,z0,z1,z40,z4,z6]),(0,[z0,z340,z1,z3,z76,z6]),(0,[z899,z1,z3,z4,z5,z6]),(0,[z1,z900,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z165,z6]),(0,[z0,z84,z66,z1,z4,z6]),(0,[z0,z197,z534,z3,z5,z6]),(0,[z0,z1,z901,z3,z4,z6]),(0,[z0,z1,z510,z4,z17,z6]),(0,[z155,z32,z0,z3,z4,z6]),(0,[z566,z358,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z902,z6]),(0,[z0,z91,z1,z40,z4,z6]),(0,[z0,z445,z1,z40,z4,z6]),(0,[z0,z1,z40,z87,z4,z6]),(0,[z47,z0,z723,z1,z5,z6]),(0,[z0,z1,z214,z3,z17,z6]),(0,[z0,z753,z3,z4,z17,z6]),(0,[z0,z903,z3,z4,z5,z6])],[(0,[z60,z32,z1,z3,z4,z57]),(0,[z32,z0,z1,z3,z36,z6]),(0,[z0,z93,z1,z3,z76,z6]),(0,[z0,z9,z1,z3,z186,z150]),(0,[z0,z9,z576,z3,z4,z6]),(0,[z35,z904,z1,z3,z4,z6]),(0,[z463,z86,z0,z1,z3,z6])],[(0,[z0,z3,z4,z5,z6,z177]),(0,[z905,z0,z1,z3,z4,z6]),(0,[z0,z1,z4,z274,z6,z285]),(0,[z0,z1,z906,z3,z4,z6]),(0,[z0,z197,z1,z3,z131,z6]),(0,[z0,z9,z1,z907,z4,z6]),(0,[z0,z908,z3,z4,z5,z6]),(0,[z909,z0,z3,z4,z5,z6]),(0,[z718,z1,z3,z4,z17,z6]),(0,[z910,z1,z3,z4,z5,z6])],[(0,[z271,z32,z0,z1,z3,z6]),(0,[z0,z66,z98,z4,z5,z6]),(0,[z0,z731,z3,z4,z5,z6]),(0,[z0,z723,z1,z46,z5,z6]),(0,[z130,z0,z1,z3,z5,z120])],[(0,[z35,z34,z1,z4,z28,z6]),(0,[z34,z1,z4,z28,z17,z6]),(0,[z0,z189,z1,z3,z5,z6]),(0,[z0,z84,z1,z4,z17,z6]),(0,[z121,z32,z0,z3,z4,z172]),(0,[z0,z1,z46,z614,z5,z6]),(0,[z42,z0,z1,z4,z17,z195]),(0,[z42,z0,z1,z4,z173,z195]),(0,[z130,z0,z1,z3,z5,z871])],[(0,[z154,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z911,z6]),(0,[z912,z0,z1,z3,z5,z6]),(0,[z223,z0,z1,z4,z17,z6]),(0,[z347,z226,z0,z84,z4,z6]),(0,[z168,z35,z0,z197,z3,z6]),(0,[z0,z9,z1,z913,z4,z6]),(0,[z86,z0,z445,z1,z3,z6]),(0,[z32,z0,z1,z4,z134,z6])]],
   [[(0,[z0,z1,z3,z4,z914,z6]),(0,[z0,z709,z63,z3,z5,z6]),(0,[z0,z9,z205,z3,z4,z53]),(0,[z0,z915,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z916,z6]),(0,[z453,z0,z1,z3,z4,z545])],[(0,[z0,z1,z917,z4,z5,z6]),(0,[z0,z1,z3,z918,z5,z6]),(0,[z0,z9,z449,z3,z4,z6]),(0,[z0,z919,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z382,z6]),(0,[z920,z0,z1,z3,z4,z6])],[(0,[z921,z0,z1,z3,z4,z6]),(0,[z0,z1,z40,z4,z6,z174])],[(0,[z0,z272,z3,z4,z6,z177]),(0,[z922,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z923,z6]),(0,[z0,z66,z63,z3,z4,z6]),(0,[z121,z122,z3,z4,z5,z172]),(0,[z405,z0,z1,z3,z4,z345])],[(0,[z0,z1,z175,z40,z4,z6]),(0,[z168,z0,z98,z4,z17,z6]),(0,[z0,z205,z1,z40,z4,z6]),(0,[z50,z0,z1,z3,z4,z174])],[(0,[z0,z1,z3,z4,z5,z924]),(0,[z925,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z926,z6]),(0,[z927,z0,z1,z3,z4,z6]),(0,[z0,z9,z1,z787,z4,z6]),(0,[z928,z0,z1,z3,z4,z6])],[(0,[z0,z929,z1,z3,z4,z6]),(0,[z0,z1,z3,z930,z5,z6]),(0,[z167,z0,z1,z4,z17,z6]),(0,[z0,z355,z9,z3,z4,z6]),(0,[z0,z1,z931,z3,z4,z6]),(0,[z854,z0,z1,z3,z5,z6])],[(0,[z78,z175,z3,z4,z17,z6]),(0,[z0,z3,z4,z17,z6,z177]),(0,[z0,z272,z1,z3,z6,z250]),(0,[z0,z1,z3,z4,z932,z6]),(0,[z0,z9,z1,z933,z4,z6]),(0,[z934,z0,z1,z3,z4,z6]),(0,[z0,z790,z3,z4,z17,z6]),(0,[z42,z0,z1,z214,z5,z195])]],
   [[(0,[z0,z1,z3,z4,z5,z935]),(0,[z0,z1,z3,z4,z936,z6]),(0,[z937,z0,z1,z40,z4,z6]),(0,[z273,z0,z9,z3,z4,z6]),(0,[z149,z47,z0,z1,z5,z6]),(0,[z32,z0,z1,z3,z186,z150]),(0,[z42,z0,z1,z5,z199,z195])],[(0,[z0,z9,z1,z4,z6,z285]),(0,[z0,z1,z3,z938,z5,z6])],[(0,[z0,z1,z3,z4,z939,z6]),(0,[z940,z0,z1,z3,z4,z6]),(0,[z1,z3,z759,z336,z5,z6]),(0,[z141,z1,z8,z3,z193,z6]),(0,[z0,z1,z3,z4,z941,z6]),(0,[z130,z0,z1,z40,z4,z6]),(0,[z0,z1,z40,z40,z4,z6]),(1,[z0,z445,z1,z40,z6]),(0,[z0,z9,z1,z942,z4,z6]),(0,[z326,z0,z1,z4,z17,z6]),(0,[z0,z1,z3,z4,z6,z943]),(0,[z0,z126,z1,z3,z944,z6])],[(0,[z0,z1,z547,z4,z17,z6]),(0,[z7,z9,z1,z3,z336,z6]),(0,[z32,z0,z38,z1,z4,z6]),(0,[z222,z206,z0,z1,z3,z6])],[(0,[z0,z945,z3,z4,z5,z6]),(0,[z180,z0,z1,z98,z4,z6]),(0,[z0,z946,z1,z3,z4,z6]),(0,[z0,z126,z205,z3,z5,z53]),(0,[z0,z266,z3,z4,z17,z6]),(0,[z1,z3,z4,z17,z6,z743]),(0,[z0,z947,z1,z214,z3,z6])],[(0,[z948,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z876,z5,z6]),(0,[z32,z0,z205,z3,z4,z53]),(0,[z130,z0,z266,z3,z5,z6])],[(0,[z7,z0,z1,z40,z4,z6]),(0,[z0,z949,z1,z3,z4,z6]),(0,[z0,z1,z3,z950,z5,z6]),(0,[z226,z0,z810,z4,z5,z6]),(0,[z14,z1,z190,z3,z4,z6]),(1,[z0,z731,z3,z4,z6]),(0,[z0,z9,z3,z350,z4,z6]),(0,[z0,z46,z266,z5,z52,z6])],[(0,[z0,z1,z3,z4,z951,z6]),(0,[z0,z1,z3,z4,z952,z6]),(0,[z34,z1,z741,z4,z5,z6]),(0,[z953,z0,z1,z3,z4,z6]),(0,[z899,z9,z1,z3,z4,z6]),(0,[z0,z93,z1,z3,z4,z401]),(0,[z0,z954,z1,z3,z4,z6])]],
   [[(0,[z0,z955,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z956,z6]),(0,[z0,z1,z3,z4,z957,z6]),(0,[z958,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z417,z6]),(0,[z959,z0,z1,z3,z4,z6]),(0,[z0,z960,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z961,z6]),(0,[z0,z1,z3,z4,z962,z6]),(0,[z0,z1,z3,z4,z963,z6]),(0,[z0,z1,z5,z6,z250,z285]),(0,[z0,z1,z964,z40,z4,z6]),(0,[z0,z66,z1,z3,z965,z6]),(0,[z854,z0,z1,z3,z4,z6])],[(0,[z0,z1,z3,z5,z150,z244]),(0,[z0,z1,z3,z4,z966,z6]),(1,[z0,z810,z4,z5,z6]),(0,[z0,z1,z3,z4,z967,z6]),(0,[z494,z0,z9,z3,z4,z6]),(0,[z35,z0,z243,z3,z4,z6]),(0,[z32,z0,z126,z1,z3,z6]),(0,[z155,z0,z3,z4,z300,z6]),(0,[z0,z1,z3,z4,z968,z6]),(0,[z0,z1,z3,z4,z969,z6])],[(0,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z970,z3,z4,z6]),(0,[z234,z328,z1,z220,z4,z6]),(0,[z226,z0,z1,z99,z4,z6]),(0,[z0,z1,z3,z4,z971,z6]),(0,[z972,z0,z1,z3,z4,z6]),(0,[z0,z973,z1,z3,z4,z6])],[(0,[z1,z741,z4,z28,z5,z6]),(0,[z347,z0,z1,z40,z4,z6]),(0,[z0,z455,z1,z4,z17,z6]),(0,[z0,z1,z974,z4,z5,z6]),(0,[z35,z0,z1,z3,z6,z199])],[(0,[z0,z1,z3,z975,z5,z6]),(0,[z0,z1,z3,z4,z976,z6]),(0,[z0,z1,z40,z4,z6,z57]),(0,[z0,z1,z3,z76,z5,z6]),(0,[z0,z1,z40,z4,z977,z6]),(0,[z0,z1,z978,z3,z4,z6]),(0,[z0,z1,z3,z4,z979,z6])],[(0,[z234,z1,z4,z5,z6,z480]),(0,[z980,z0,z3,z4,z5,z6]),(0,[z32,z0,z1,z4,z6,z285]),(0,[z981,z1,z3,z4,z5,z6]),(0,[z0,z1,z414,z5,z52,z6]),(0,[z35,z0,z1,z3,z76,z6]),(0,[z0,z1,z40,z4,z982,z6]),(0,[z154,z9,z1,z3,z4,z6]),(0,[z0,z3,z4,z5,z6,z983])],[(0,[z81,z1,z10,z3,z4,z6]),(0,[z81,z1,z504,z3,z4,z6]),(0,[z0,z9,z116,z3,z4,z6]),(0,[z223,z0,z1,z4,z984,z6])]],
   [[(0,[z34,z1,z4,z28,z260,z6]),(0,[z86,z0,z1,z302,z3,z6]),(0,[z0,z985,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z259,z207]),(0,[z0,z1,z986,z4,z5,z6])],[(0,[z987,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z988,z4,z6])],[(0,[z374,z0,z272,z3,z4,z6]),(0,[z223,z271,z0,z1,z5,z6]),(0,[z0,z1,z1,z40,z4,z6]),(0,[z904,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z989,z6])],[(0,[z56,z3,z4,z5,z6,z668]),(0,[z0,z1,z3,z4,z990,z6]),(0,[z35,z0,z445,z1,z3,z6]),(0,[z0,z1,z942,z4,z5,z6])],[(0,[z0,z1,z3,z4,z991,z6])],[(0,[z992,z0,z1,z3,z4,z6]),(0,[z0,z993,z1,z3,z4,z6]),(0,[z226,z0,z84,z299,z4,z6]),(0,[z14,z0,z1,z3,z76,z6]),(0,[z0,z1,z3,z4,z994,z6]),(0,[z0,z1,z4,z5,z43,z794]),(0,[z0,z1,z3,z5,z6,z871])],[(0,[z0,z1,z995,z4,z5,z6]),(0,[z80,z1,z3,z4,z82,z6]),(0,[z0,z3,z4,z274,z6,z177]),(0,[z0,z1,z815,z4,z17,z6]),(1,[z0,z1,z40,z76,z6]),(0,[z0,z9,z560,z3,z4,z6]),(0,[z0,z852,z3,z4,z17,z6])],[(0,[z1,z996,z3,z4,z5,z6]),(0,[z223,z0,z1,z4,z274,z6]),(0,[z0,z98,z4,z64,z17,z6]),(0,[z0,z897,z1,z4,z5,z6]),(0,[z0,z197,z1,z40,z4,z6])]],
   [[(0,[z0,z1,z3,z997,z4,z6]),(0,[z35,z0,z3,z4,z6,z177]),(0,[z226,z0,z3,z36,z5,z6]),(0,[z0,z197,z119,z3,z5,z6]),(0,[z0,z1,z40,z4,z51,z6]),(0,[z0,z1,z3,z87,z76,z6]),(0,[z0,z1,z4,z17,z6,z546]),(0,[z998,z0,z1,z3,z4,z6])],[],[(0,[z0,z1,z2,z4,z17,z6]),(0,[z60,z271,z1,z3,z5,z57]),(0,[z0,z197,z66,z3,z4,z6])],[(0,[z374,z0,z9,z3,z4,z6]),(0,[z0,z1,z3,z4,z999,z6])],[(0,[z0,z1,z3,z4,z1000,z6]),(0,[z0,z1,z1001,z3,z4,z6]),(0,[z1,z3,z741,z4,z5,z6]),(0,[z34,z233,z1,z4,z5,z6]),(0,[z35,z0,z1,z3,z6,z250]),(0,[z1002,z374,z0,z3,z4,z6]),(0,[z222,z0,z1,z439,z3,z6]),(0,[z0,z9,z570,z3,z4,z6]),(0,[z130,z0,z1,z3,z364,z120]),(0,[z0,z1003,z1,z3,z5,z6])],[(0,[z0,z709,z3,z4,z5,z6]),(0,[z0,z1,z3,z87,z655,z6])],[(0,[z0,z1,z1004,z3,z4,z6]),(0,[z0,z1,z1005,z3,z4,z6]),(0,[z0,z1,z3,z4,z1006,z6]),(0,[z874,z1,z3,z4,z17,z6])],[(0,[z0,z1007,z1,z3,z5,z6]),(0,[z0,z1,z593,z4,z17,z6])]],
   [[(0,[z0,z1,z615,z4,z17,z6]),(0,[z122,z1,z3,z4,z5,z6]),(0,[z0,z1008,z1,z3,z4,z6]),(0,[z0,z1,z4,z17,z6,z285]),(0,[z0,z91,z1,z99,z4,z6]),(0,[z0,z1009,z3,z4,z5,z6])],[(0,[z0,z1,z1010,z4,z5,z6]),(0,[z0,z1011,z1,z3,z4,z6]),(0,[z80,z1,z190,z3,z4,z6]),(0,[z0,z1,z425,z4,z17,z6]),(0,[z0,z810,z1,z4,z5,z6]),(0,[z0,z38,z9,z1,z4,z6]),(0,[z0,z9,z1,z3,z890,z6]),(0,[z789,z9,z1,z3,z4,z6]),(0,[z1012,z1,z3,z4,z5,z6]),(0,[z32,z154,z1,z3,z4,z6])],[(0,[z0,z9,z1,z3,z4,z6]),(0,[z1,z220,z741,z4,z5,z6]),(0,[z0,z1,z1013,z3,z4,z6]),(0,[z149,z32,z47,z0,z1,z6]),(0,[z42,z0,z1,z4,z5,z794]),(0,[z0,z1,z3,z4,z1014,z6])],[(0,[z1015,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1016,z6]),(0,[z1017,z0,z1,z3,z4,z6]),(0,[z0,z1,z98,z4,z17,z6]),(0,[z0,z1,z40,z4,z6,z389]),(0,[z0,z1,z3,z4,z1018,z6]),(0,[z42,z0,z1,z4,z49,z195])],[(0,[z0,z328,z1,z3,z4,z6]),(0,[z81,z514,z1,z3,z4,z6]),(0,[z270,z32,z0,z1,z4,z6]),(0,[z1019,z0,z1,z4,z6,z285]),(0,[z1020,z0,z1,z3,z4,z6]),(0,[z180,z0,z1,z40,z4,z6]),(0,[z35,z122,z1,z3,z4,z6]),(0,[z167,z0,z367,z3,z4,z6])],[(0,[z34,z1,z4,z502,z28,z6]),(0,[z0,z1,z1021,z3,z4,z6]),(0,[z1022,z0,z3,z4,z5,z6]),(0,[z0,z1023,z3,z4,z5,z6]),(0,[z117,z1,z3,z4,z5,z751]),(0,[z0,z1,z3,z4,z1024,z6]),(0,[z222,z0,z1,z3,z354,z6]),(0,[z50,z0,z1,z3,z4,z389]),(0,[z0,z66,z3,z4,z53,z6]),(0,[z0,z1,z798,z3,z4,z6])],[(0,[z1025,z0,z1,z3,z4,z6]),(0,[z32,z117,z1,z3,z4,z61]),(0,[z226,z0,z84,z4,z5,z6]),(0,[z0,z1,z3,z1026,z5,z6]),(0,[z0,z243,z731,z3,z4,z6]),(0,[z1027,z0,z1,z3,z4,z6]),(0,[z32,z0,z1,z758,z3,z6])],[(0,[z80,z0,z1,z40,z4,z6]),(0,[z0,z1,z3,z4,z1028,z6]),(0,[z32,z0,z1,z3,z748,z6]),(1,[z0,z1,z4,z5,z794])]],
   [[(0,[z0,z1,z741,z4,z5,z6]),(0,[z0,z1,z3,z1029,z4,z6]),(0,[z168,z32,z0,z197,z3,z6]),(0,[z168,z0,z197,z9,z3,z6]),(0,[z805,z0,z1,z3,z4,z6]),(0,[z1030,z0,z1,z3,z4,z6]),(0,[z1031,z0,z1,z3,z4,z6]),(0,[z1,z900,z3,z4,z17,z6])],[(0,[z374,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z1032,z4,z6]),(0,[z1,z3,z4,z5,z751,z57]),(0,[z223,z0,z4,z5,z6,z177]),(0,[z0,z1,z3,z4,z6,z1033]),(0,[z35,z0,z594,z3,z4,z6]),(0,[z516,z0,z1,z33,z3,z6])],[(0,[z0,z1,z1034,z4,z5,z6]),(0,[z519,z1,z10,z3,z4,z6]),(0,[z60,z0,z1,z40,z4,z6]),(0,[z0,z1,z3,z4,z1035,z6]),(0,[z0,z1,z40,z4,z150,z6]),(0,[z0,z340,z1,z40,z4,z6]),(0,[z0,z1,z40,z4,z401,z6])],[(0,[z0,z1,z3,z4,z1036,z6]),(0,[z0,z304,z91,z98,z4,z6]),(0,[z0,z266,z3,z4,z300,z6])],[(0,[z0,z1,z640,z4,z17,z6]),(0,[z0,z1037,z3,z4,z5,z6]),(0,[z0,z1,z913,z4,z5,z6]),(0,[z0,z321,z3,z64,z5,z6]),(0,[z0,z9,z1,z917,z4,z6]),(0,[z86,z0,z1,z40,z4,z6]),(0,[z0,z205,z3,z4,z382,z53]),(0,[z230,z206,z0,z1,z3,z6]),(0,[z910,z1,z3,z4,z17,z6]),(0,[z1038,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z1039,z5,z6])],[(0,[z78,z35,z175,z3,z4,z6]),(0,[z1040,z0,z1,z3,z4,z6]),(0,[z0,z66,z98,z4,z17,z6]),(0,[z35,z0,z534,z3,z4,z6]),(0,[z130,z0,z1,z3,z17,z120]),(0,[z0,z1,z3,z4,z5,z877])],[(0,[z0,z1,z3,z4,z1041,z6]),(0,[z0,z1,z3,z4,z51,z315]),(0,[z0,z9,z294,z3,z4,z6]),(0,[z0,z189,z1,z3,z17,z6]),(0,[z0,z1,z400,z40,z4,z6]),(0,[z180,z0,z84,z1,z4,z6]),(0,[z347,z0,z38,z1,z4,z6]),(0,[z339,z0,z445,z1,z3,z6]),(0,[z253,z0,z1,z3,z4,z462]),(0,[z0,z1,z3,z4,z69,z877])],[(0,[z32,z0,z1,z3,z4,z6]),(1,[z0,z709,z3,z5,z6]),(0,[z0,z1,z1042,z3,z4,z6]),(0,[z154,z1,z3,z4,z17,z6]),(0,[z0,z1043,z1,z3,z4,z6])]],
   [[(0,[z80,z0,z1,z3,z76,z6]),(0,[z0,z1,z3,z1044,z5,z6]),(0,[z0,z9,z1,z974,z4,z6]),(0,[z0,z1,z3,z4,z1045,z6]),(0,[z0,z1,z3,z186,z5,z150])],[(0,[z0,z1,z3,z4,z1046,z6]),(0,[z0,z1,z3,z4,z1047,z6]),(0,[z81,z1,z227,z3,z4,z6]),(0,[z35,z271,z0,z1,z3,z6]),(0,[z0,z1,z3,z4,z6,z1048]),(0,[z0,z1,z3,z4,z859,z6])],[(0,[z1049,z0,z1,z3,z4,z5]),(0,[z0,z1,z1050,z4,z5,z6]),(0,[z34,z0,z1,z40,z4,z6]),(0,[z0,z1051,z1,z3,z4,z6]),(0,[z0,z1,z1052,z3,z4,z6]),(0,[z1053,z0,z1,z3,z4,z6]),(0,[z0,z1,z652,z4,z17,z6]),(0,[z1054,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z364,z6])],[(0,[z0,z1,z3,z4,z1055,z6]),(0,[z374,z0,z4,z5,z6,z285]),(0,[z501,z0,z9,z3,z4,z6])],[(0,[z1,z10,z712,z3,z4,z6]),(0,[z1056,z0,z1,z3,z4,z6]),(0,[z1057,z1,z3,z4,z5,z6]),(0,[z47,z0,z1,z40,z4,z6]),(0,[z35,z0,z1,z3,z1058,z6])],[(0,[z0,z84,z1,z815,z4,z6]),(0,[z0,z445,z1,z3,z5,z6]),(0,[z0,z1059,z1,z3,z4,z6])],[(0,[z0,z1,z1060,z3,z5,z6]),(0,[z42,z0,z1,z4,z5,z653]),(0,[z0,z367,z1,z3,z4,z6]),(0,[z0,z1,z3,z890,z5,z6]),(0,[z32,z0,z63,z3,z64,z6]),(0,[z35,z0,z1,z48,z4,z43]),(0,[z222,z86,z0,z1,z3,z6]),(0,[z0,z1,z3,z4,z5,z871])],[(0,[z0,z1,z3,z1061,z5,z6]),(0,[z0,z1062,z3,z4,z5,z6]),(1,[z1,z3,z759,z5,z6]),(0,[z0,z3,z4,z5,z6,z1063]),(0,[z0,z9,z1,z3,z1064,z6]),(0,[z122,z9,z1,z3,z4,z6]),(0,[z0,z9,z1,z46,z52,z6]),(0,[z47,z0,z266,z3,z5,z6])]],
   [[(0,[z7,z1,z3,z336,z5,z6]),(0,[z0,z1,z3,z4,z6,z1065]),(0,[z0,z1,z3,z4,z51,z341]),(0,[z0,z1066,z3,z4,z5,z6]),(0,[z0,z1067,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z5,z1068]),(0,[z0,z1,z3,z4,z1069,z6]),(0,[z0,z1,z1070,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z794])],[(0,[z0,z1,z3,z1071,z4,z6]),(0,[z1072,z0,z1,z3,z4,z6]),(0,[z0,z1073,z1,z3,z4,z6])],[(0,[z0,z1,z3,z5,z6,z250]),(0,[z0,z1,z3,z4,z1074,z6]),(0,[z1075,z0,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z1076,z6]),(0,[z0,z549,z9,z3,z4,z6]),(0,[z35,z0,z694,z3,z4,z6]),(0,[z35,z155,z0,z3,z4,z6])],[(0,[z0,z1,z3,z4,z1077,z6]),(0,[z0,z1,z3,z1078,z5,z6]),(0,[z226,z0,z386,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z1079]),(0,[z0,z1,z933,z4,z5,z6]),(0,[z0,z1,z40,z4,z52,z6]),(0,[z0,z9,z1,z3,z1080,z6]),(0,[z121,z0,z3,z4,z5,z733]),(0,[z0,z1,z3,z4,z1081,z6]),(0,[z0,z1,z3,z4,z1082,z6])],[(0,[z0,z1,z3,z4,z1083,z6]),(0,[z35,z7,z1,z3,z336,z6]),(0,[z0,z1,z3,z5,z150,z380]),(0,[z149,z0,z1,z5,z6,z553])],[(0,[z0,z1,z3,z1084,z5,z6]),(0,[z0,z1,z3,z4,z6,z1085]),(0,[z0,z1086,z1,z3,z4,z6]),(0,[z374,z35,z0,z3,z4,z6]),(0,[z0,z1,z40,z4,z61,z6]),(0,[z105,z0,z1,z99,z4,z6]),(0,[z0,z205,z3,z4,z5,z53]),(0,[z854,z0,z1,z3,z88,z6])],[(0,[z0,z1,z3,z4,z1087,z6]),(0,[z0,z1,z3,z4,z1088,z6]),(0,[z0,z1,z3,z1089,z5,z6]),(0,[z0,z1,z3,z4,z1090,z6]),(0,[z0,z9,z161,z3,z4,z6]),(0,[z0,z189,z304,z1,z3,z6]),(0,[z0,z66,z1,z98,z4,z6]),(0,[z0,z1,z1091,z3,z4,z6])]],
   [[(0,[z0,z996,z3,z4,z5,z6]),(0,[z1092,z0,z1,z3,z4,z6]),(0,[z1093,z0,z1,z3,z4,z6]),(0,[z0,z1,z1094,z4,z5,z6]),(0,[z0,z1,z48,z40,z4,z6]),(0,[z0,z1,z3,z4,z6,z1095]),(0,[z0,z1,z3,z4,z1096,z6])],[(0,[z1097,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z1098,z5,z6]),(0,[z80,z123,z1,z3,z4,z6]),(0,[z0,z810,z91,z4,z5,z6])],[(0,[z80,z208,z1,z3,z4,z6]),(0,[z32,z0,z189,z1,z3,z6]),(0,[z0,z1,z3,z4,z1099,z6]),(0,[z0,z1,z3,z4,z6,z1100]),(0,[z1101,z0,z3,z4,z5,z6]),(0,[z0,z1,z48,z4,z5,z43]),(0,[z0,z1,z48,z4,z258,z43])],[(0,[z0,z1,z3,z4,z17,z6]),(0,[z0,z834,z1,z4,z5,z6]),(0,[z0,z1102,z3,z4,z5,z6]),(0,[z0,z1,z8,z40,z4,z6]),(0,[z0,z465,z3,z64,z5,z6]),(0,[z0,z1,z3,z1103,z4,z6]),(0,[z0,z9,z1,z995,z4,z6]),(0,[z0,z1,z3,z4,z173,z6]),(0,[z0,z1,z1104,z3,z4,z6])],[(0,[z0,z1105,z1,z3,z4,z6]),(0,[z32,z0,z1,z46,z52,z6])],[(0,[z0,z1,z3,z4,z1106,z6]),(0,[z0,z9,z697,z3,z4,z6]),(0,[z1019,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1107,z6]),(0,[z0,z9,z1,z3,z1044,z6]),(0,[z0,z1,z3,z76,z17,z6])],[(0,[z0,z1,z3,z5,z6,z1108]),(0,[z60,z272,z1,z3,z4,z57])],[(0,[z1109,z0,z1,z3,z4,z6]),(1,[z1,z3,z4,z5,z751]),(0,[z0,z1110,z1,z3,z4,z6]),(0,[z0,z1,z1111,z3,z4,z6])]],
   [[(0,[z0,z1,z3,z4,z196,z6]),(0,[z0,z1,z3,z1112,z5,z6]),(0,[z0,z1,z1113,z3,z4,z6]),(0,[z56,z0,z1,z40,z4,z6]),(0,[z0,z1,z3,z4,z1114,z6]),(0,[z0,z1,z3,z4,z1115,z6]),(0,[z35,z0,z91,z98,z4,z6]),(0,[z35,z0,z1,z40,z4,z6]),(0,[z0,z1,z1116,z40,z4,z6]),(0,[z149,z47,z0,z1,z324,z6])],[],[(0,[z234,z1,z220,z4,z165,z6]),(0,[z7,z32,z1,z3,z336,z6]),(0,[z124,z514,z1,z3,z4,z6]),(0,[z0,z723,z1,z5,z52,z6])],[(0,[z223,z0,z272,z1,z4,z6]),(0,[z0,z1,z4,z813,z6,z285]),(0,[z0,z38,z1,z76,z5,z6]),(0,[z35,z0,z66,z3,z4,z6]),(0,[z0,z1,z3,z4,z259,z51]),(0,[z32,z0,z1,z135,z4,z6]),(0,[z0,z1,z3,z4,z69,z51])],[(0,[z234,z9,z1,z220,z4,z6]),(0,[z81,z1,z3,z4,z6,z24]),(0,[z801,z0,z1,z3,z4,z6]),(0,[z0,z9,z1,z40,z76,z6]),(0,[z0,z445,z1,z3,z40,z6]),(0,[z0,z1117,z9,z1,z4,z6]),(0,[z1118,z0,z1,z3,z4,z6]),(0,[z35,z0,z148,z3,z4,z6]),(0,[z130,z0,z1,z3,z131,z120])],[(0,[z0,z9,z585,z3,z4,z6]),(0,[z271,z0,z1,z5,z6,z285]),(0,[z0,z319,z3,z64,z5,z6]),(0,[z0,z1,z1119,z3,z4,z6]),(0,[z0,z367,z9,z3,z4,z6])],[(0,[z0,z63,z3,z354,z64,z6]),(0,[z0,z126,z9,z1,z3,z6]),(0,[z0,z1,z3,z1120,z4,z6]),(0,[z647,z32,z0,z1,z4,z6])],[(0,[z0,z1,z3,z4,z5,z1121]),(0,[z1122,z0,z1,z3,z4,z6]),(0,[z14,z0,z1,z40,z4,z6]),(0,[z0,z1,z3,z1123,z5,z6]),(1,[z0,z1,z3,z5,z871])]],
   [[(0,[z234,z32,z1,z220,z4,z6]),(0,[z0,z91,z98,z36,z5,z6]),(0,[z0,z1,z1124,z4,z5,z6]),(0,[z0,z197,z422,z3,z5,z6]),(0,[z0,z9,z1,z3,z825,z6]),(0,[z0,z1,z378,z4,z17,z6]),(0,[z0,z1,z3,z5,z6,z1125])],[(0,[z35,z0,z359,z3,z4,z6]),(0,[z1126,z1,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z16,z6]),(1,[z854,z0,z1,z3,z6]),(1,[z0,z1,z3,z4,z877])],[(0,[z0,z1,z3,z1127,z4,z6]),(0,[z80,z1,z712,z3,z4,z6]),(0,[z0,z1,z10,z40,z4,z6]),(0,[z180,z226,z0,z84,z4,z6]),(0,[z0,z1128,z1,z3,z4,z6]),(0,[z35,z0,z581,z3,z4,z6]),(0,[z32,z0,z1,z353,z4,z6]),(0,[z222,z854,z0,z1,z3,z6])],[(0,[z0,z1129,z3,z4,z5,z6]),(0,[z374,z223,z0,z4,z5,z6]),(0,[z0,z1,z3,z4,z1130,z6]),(0,[z42,z0,z9,z1,z4,z195]),(0,[z0,z9,z3,z76,z16,z6]),(0,[z32,z0,z204,z1,z4,z6]),(0,[z831,z0,z266,z3,z4,z6])],[(0,[z121,z0,z3,z4,z5,z440]),(0,[z223,z0,z9,z1,z4,z6]),(0,[z0,z1,z3,z4,z1131,z6]),(0,[z0,z1,z1132,z3,z4,z6]),(0,[z105,z32,z0,z1,z4,z6])],[(0,[z271,z0,z272,z1,z3,z6]),(0,[z0,z1,z3,z4,z1133,z5]),(0,[z0,z445,z9,z1,z3,z6]),(0,[z0,z1,z907,z4,z5,z6]),(0,[z0,z1,z3,z4,z69,z401])],[(0,[z35,z0,z237,z3,z4,z6]),(0,[z0,z445,z9,z3,z16,z6]),(0,[z35,z0,z266,z3,z4,z6]),(0,[z0,z1,z3,z4,z1134,z6])],[(0,[z35,z56,z112,z3,z4,z6]),(0,[z149,z47,z0,z9,z1,z6]),(0,[z155,z0,z46,z5,z52,z6])]],
   [[(0,[z0,z1,z4,z5,z43,z132]),(0,[z1135,z1,z3,z4,z5,z6]),(0,[z122,z1,z3,z4,z17,z6]),(0,[z0,z1009,z3,z4,z17,z6])],[(0,[z141,z1,z8,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z1136]),(0,[z0,z1,z3,z4,z1137,z6]),(0,[z347,z0,z1,z3,z890,z6])],[(0,[z78,z9,z175,z3,z4,z6]),(0,[z1138,z0,z1,z3,z4,z6]),(0,[z347,z0,z1,z3,z4,z6]),(0,[z226,z32,z0,z84,z4,z6]),(0,[z105,z0,z1,z299,z4,z6])],[(0,[z0,z1,z1139,z3,z4,z6]),(0,[z0,z1,z3,z4,z984,z6]),(0,[z715,z0,z1,z288,z4,z6]),(0,[z0,z1,z3,z17,z6,z1125]),(0,[z0,z1,z1140,z3,z4,z6])],[(0,[z0,z1141,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z751]),(0,[z0,z91,z98,z4,z104,z6]),(0,[z0,z810,z98,z4,z5,z6]),(0,[z0,z1,z3,z4,z1142,z6]),(0,[z0,z1,z3,z4,z1143,z6]),(1,[z0,z723,z1,z5,z6]),(0,[z0,z3,z4,z17,z6,z983])],[(0,[z0,z1,z3,z4,z260,z6]),(0,[z0,z1,z3,z1144,z4,z6]),(0,[z0,z1,z3,z274,z6,z250]),(0,[z0,z1,z40,z4,z5,z6]),(0,[z179,z316,z1,z3,z4,z6])],[(0,[z78,z32,z175,z3,z4,z6]),(0,[z78,z0,z1,z40,z4,z6]),(0,[z226,z0,z84,z4,z17,z6]),(0,[z0,z1,z40,z4,z69,z6]),(0,[z35,z0,z3,z4,z6,z67]),(1,[z0,z3,z4,z5,z733]),(0,[z0,z1,z3,z4,z6,z1145]),(0,[z0,z375,z1,z3,z4,z6])],[(0,[z78,z122,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1146,z6]),(0,[z0,z66,z1,z40,z4,z6]),(0,[z0,z1,z40,z76,z5,z6]),(0,[z35,z781,z1,z3,z4,z6]),(0,[z180,z0,z544,z3,z4,z6])]],
   [[(0,[z0,z1,z3,z1147,z5,z6]),(0,[z1148,z0,z1,z3,z4,z6]),(0,[z519,z0,z1,z3,z76,z6]),(0,[z0,z1,z3,z4,z6,z1149])],[(0,[z0,z1,z1150,z3,z4,z6]),(0,[z141,z9,z1,z8,z3,z6]),(0,[z0,z1,z3,z4,z1151,z6]),(0,[z374,z0,z3,z4,z17,z6]),(0,[z1152,z0,z1,z3,z4,z6]),(0,[z0,z1,z156,z4,z17,z6]),(0,[z0,z1,z298,z4,z17,z6])],[(0,[z0,z1153,z1,z3,z4,z6]),(0,[z35,z234,z1,z220,z4,z6]),(0,[z0,z1,z1154,z3,z4,z6]),(0,[z0,z1,z1155,z3,z4,z6]),(0,[z0,z1,z3,z400,z4,z6]),(0,[z35,z1012,z1,z3,z4,z6]),(0,[z35,z0,z1,z3,z291,z6]),(0,[z35,z0,z1,z214,z3,z6]),(0,[z0,z205,z3,z4,z53,z286]),(0,[z1156,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z131,z6])],[(0,[z0,z1,z3,z5,z6,z1157]),(0,[z0,z1,z3,z4,z274,z6]),(0,[z0,z84,z1,z40,z4,z6]),(0,[z0,z84,z694,z4,z5,z6]),(0,[z339,z0,z1,z40,z4,z6]),(0,[z1158,z0,z1,z3,z4,z6])],[(0,[z0,z1,z3,z1159,z5,z6]),(0,[z234,z1,z220,z4,z5,z6]),(0,[z50,z0,z1,z3,z4,z530]),(0,[z0,z1,z3,z4,z1160,z6]),(0,[z0,z1,z3,z36,z104,z6]),(0,[z0,z1,z3,z1161,z5,z6]),(0,[z1162,z0,z1,z3,z4,z6])],[(0,[z0,z1163,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1164,z6]),(0,[z141,z32,z1,z8,z3,z6]),(0,[z0,z1165,z1,z3,z4,z6]),(0,[z0,z189,z91,z98,z5,z6]),(0,[z0,z1,z3,z4,z6,z286]),(0,[z0,z858,z1,z3,z5,z6]),(0,[z0,z1,z1166,z4,z5,z6])],[(0,[z457,z0,z9,z3,z4,z6]),(0,[z715,z0,z1,z3,z4,z6])],[(0,[z1167,z0,z1,z3,z5,z6]),(0,[z0,z3,z4,z5,z6,z1168]),(0,[z0,z75,z1,z40,z4,z6]),(0,[z0,z1169,z9,z1,z3,z6]),(0,[z0,z1,z40,z4,z16,z6]),(0,[z0,z1,z3,z76,z6,z174]),(0,[z35,z0,z1,z3,z186,z150])]],
   [[(0,[z1170,z0,z1,z3,z4,z6]),(0,[z35,z0,z9,z3,z76,z6]),(0,[z0,z1171,z1,z3,z4,z6]),(0,[z0,z1,z3,z186,z17,z150])],[(0,[z1172,z0,z1,z3,z4,z6]),(0,[z32,z0,z445,z1,z3,z6]),(0,[z130,z32,z0,z1,z3,z120])],[(0,[z0,z1,z1173,z3,z4,z6]),(0,[z180,z0,z66,z3,z4,z6]),(0,[z0,z38,z9,z4,z16,z6]),(0,[z0,z1,z3,z4,z300,z6])],[(0,[z0,z1174,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1175,z6]),(0,[z0,z1,z3,z1176,z5,z6]),(0,[z167,z0,z1,z40,z4,z6]),(0,[z0,z1177,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z5,z1178]),(0,[z0,z9,z63,z3,z64,z6]),(0,[z0,z9,z1,z3,z938,z6]),(0,[z572,z0,z1,z3,z349,z6]),(0,[z35,z0,z205,z3,z4,z53])],[(0,[z0,z1,z3,z4,z5,z1179]),(0,[z0,z1180,z1,z3,z4,z6]),(0,[z0,z9,z591,z3,z4,z6]),(0,[z0,z1181,z1,z3,z4,z6]),(0,[z0,z1182,z3,z4,z5,z6]),(0,[z0,z1,z1183,z3,z4,z6]),(0,[z0,z1,z3,z40,z4,z6]),(0,[z0,z1,z40,z4,z53,z6]),(0,[z92,z0,z1,z40,z4,z6]),(0,[z0,z445,z1,z3,z17,z6]),(0,[z0,z1,z3,z965,z5,z6])],[(0,[z0,z1,z3,z4,z1184,z6]),(0,[z32,z0,z3,z4,z6,z177]),(0,[z1185,z1,z3,z4,z5,z6]),(0,[z1186,z0,z1,z3,z4,z6]),(0,[z0,z1,z1187,z3,z4,z6]),(0,[z0,z1,z3,z5,z6,z199])],[(0,[z0,z1,z287,z3,z4,z6]),(0,[z0,z1,z796,z4,z5,z6]),(0,[z0,z1,z3,z1188,z5,z6]),(0,[z0,z1,z1189,z4,z5,z6]),(0,[z374,z32,z0,z3,z4,z6]),(0,[z0,z1,z3,z4,z275,z6]),(0,[z0,z445,z1,z439,z3,z6]),(0,[z0,z9,z3,z4,z6,z610]),(0,[z35,z0,z3,z4,z6,z144]),(0,[z0,z1,z288,z4,z17,z6])]],
   [[(0,[z0,z1190,z1,z4,z5,z6]),(0,[z7,z1,z3,z336,z17,z6]),(0,[z60,z374,z3,z4,z5,z57]),(0,[z180,z0,z1,z379,z4,z6]),(0,[z0,z1,z3,z4,z49,z6]),(0,[z0,z1,z3,z4,z1191,z6])],[(0,[z0,z1,z3,z4,z1192,z6]),(0,[z0,z126,z1,z3,z5,z6]),(0,[z1027,z122,z1,z3,z4,z6]),(0,[z1156,z0,z1,z3,z4,z17])],[(0,[z1193,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z1194,z4,z6]),(0,[z117,z1,z3,z4,z5,z61]),(0,[z32,z0,z1,z3,z6,z250]),(0,[z0,z9,z1,z3,z1112,z6]),(0,[z0,z1,z3,z279,z41,z6]),(0,[z0,z1,z4,z17,z6,z107])],[(0,[z1195,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z1196,z5]),(0,[z0,z1197,z1,z3,z4,z6]),(0,[z1,z712,z3,z4,z5,z6]),(0,[z35,z0,z592,z3,z4,z6]),(0,[z0,z375,z1,z46,z52,z6]),(0,[z715,z0,z1,z4,z5,z6])],[(0,[z0,z1,z4,z5,z6,z1198]),(0,[z141,z523,z1,z8,z3,z6]),(0,[z374,z122,z3,z4,z5,z6]),(0,[z0,z84,z98,z4,z17,z6]),(0,[z0,z1,z1199,z4,z5,z6]),(0,[z0,z1117,z1,z4,z5,z6]),(0,[z764,z0,z1,z3,z4,z6]),(0,[z32,z0,z1,z4,z17,z6]),(0,[z0,z1,z3,z4,z1200,z6])],[(0,[z1201,z0,z1,z3,z4,z6]),(0,[z121,z0,z3,z4,z20,z172])],[(0,[z0,z1,z299,z3,z4,z6]),(0,[z0,z1202,z1,z3,z5,z6]),(0,[z35,z226,z0,z84,z4,z6]),(0,[z0,z205,z3,z4,z17,z53])],[(0,[z0,z1,z3,z4,z1203,z6]),(0,[z0,z9,z1,z3,z725,z6]),(0,[z0,z1,z1204,z3,z4,z6]),(0,[z0,z1,z3,z4,z1205,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z1206]),(0,[z0,z523,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1207,z6]),(0,[z0,z1,z299,z4,z17,z6]),(0,[z1,z3,z4,z5,z6,z1208])],[(0,[z0,z1,z3,z4,z1209,z6]),(0,[z0,z272,z1,z3,z4,z6]),(0,[z0,z205,z3,z4,z5,z733]),(0,[z0,z1,z3,z17,z6,z199]),(0,[z0,z1,z3,z4,z1210,z6])],[(0,[z117,z1,z3,z4,z5,z606]),(0,[z1211,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z1212,z6]),(0,[z35,z0,z1,z3,z1176,z6]),(0,[z32,z122,z1,z3,z4,z6]),(0,[z0,z3,z4,z5,z733,z172]),(0,[z0,z1,z48,z4,z17,z43])],[(0,[z0,z3,z4,z5,z53,z236]),(0,[z0,z1213,z3,z4,z5,z6]),(0,[z0,z38,z1,z299,z4,z6]),(0,[z0,z266,z3,z5,z150,z6]),(0,[z0,z1,z46,z300,z52,z6]),(0,[z149,z47,z0,z1,z17,z6]),(0,[z0,z1,z1214,z3,z4,z6]),(0,[z0,z947,z1,z3,z4,z6]),(0,[z0,z1,z3,z1215,z4,z6])],[(0,[z141,z1,z3,z759,z5,z6]),(0,[z117,z0,z1,z40,z4,z6]),(0,[z0,z1,z98,z4,z104,z6]),(0,[z0,z810,z3,z4,z5,z6]),(0,[z168,z0,z709,z3,z5,z6]),(0,[z121,z0,z1,z40,z4,z6]),(0,[z0,z1,z26,z4,z17,z6]),(0,[z0,z1,z3,z4,z6,z1216])],[(0,[z996,z175,z3,z4,z5,z6]),(0,[z0,z1,z1217,z3,z4,z6]),(0,[z35,z0,z433,z3,z4,z6])],[(0,[z0,z1,z322,z4,z17,z6]),(0,[z0,z1,z712,z3,z4,z6]),(0,[z180,z781,z1,z3,z4,z6]),(0,[z0,z1,z1218,z4,z5,z6]),(0,[z0,z38,z445,z1,z5,z6]),(0,[z50,z0,z1,z3,z4,z877])],[(0,[z0,z1,z3,z4,z5,z1219]),(0,[z0,z3,z4,z5,z6,z1220]),(0,[z0,z1221,z1,z3,z4,z6]),(0,[z81,z0,z1,z40,z4,z6]),(0,[z105,z0,z1,z400,z4,z6]),(0,[z226,z0,z84,z9,z4,z6]),(0,[z0,z693,z1,z4,z17,z6]),(0,[z0,z9,z1,z48,z4,z43]),(0,[z0,z1,z849,z3,z4,z6])]],
   [[(0,[z0,z304,z1,z3,z36,z6]),(0,[z0,z1,z3,z1080,z5,z6]),(0,[z0,z1,z3,z324,z4,z6]),(0,[z1222,z1,z3,z4,z5,z6])],[(0,[z0,z1,z1223,z3,z4,z6]),(0,[z271,z0,z1,z3,z5,z6]),(0,[z374,z0,z3,z4,z274,z6])],[(0,[z35,z0,z245,z3,z4,z6]),(0,[z0,z63,z3,z64,z5,z6]),(0,[z0,z9,z3,z4,z700,z6])],[(0,[z78,z287,z175,z3,z4,z6]),(0,[z0,z1,z3,z4,z1224,z6]),(0,[z1,z3,z4,z5,z61,z751]),(0,[z35,z0,z544,z3,z4,z6]),(0,[z0,z1,z3,z4,z1225,z6]),(0,[z0,z66,z3,z4,z133,z6])],[(0,[z32,z0,z1,z3,z725,z6])],[(0,[z0,z1,z1226,z3,z4,z6]),(0,[z0,z1,z247,z4,z17,z6]),(0,[z0,z1,z3,z5,z871,z120])],[(0,[z0,z1,z3,z4,z1227,z6]),(0,[z1228,z0,z1,z3,z4,z6]),(0,[z1229,z0,z1,z3,z4,z6]),(0,[z854,z0,z1,z3,z87,z6])],[(0,[z0,z189,z1,z3,z104,z6]),(0,[z168,z0,z197,z3,z5,z6]),(0,[z0,z1,z40,z4,z43,z6]),(0,[z0,z1,z3,z1230,z4,z6])]],
   [[(0,[z0,z1,z3,z4,z1231,z6]),(0,[z1,z3,z759,z4,z5,z6]),(0,[z81,z0,z1,z3,z76,z6]),(0,[z0,z91,z98,z4,z5,z6]),(0,[z180,z718,z1,z3,z4,z6]),(0,[z35,z0,z38,z9,z4,z6])],[(0,[z0,z1,z3,z17,z6,z250]),(0,[z117,z9,z1,z3,z4,z61]),(0,[z0,z1,z1232,z3,z5,z6])],[(0,[z0,z1,z3,z4,z1233,z6]),(0,[z0,z1169,z1,z3,z5,z6]),(0,[z35,z149,z47,z0,z1,z6])],[(0,[z1234,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1235,z6]),(0,[z0,z1,z439,z3,z4,z6]),(0,[z0,z1,z1236,z3,z4,z6]),(0,[z0,z1237,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1238,z6]),(0,[z56,z122,z3,z4,z5,z6]),(0,[z234,z1,z741,z4,z5,z6]),(0,[z0,z38,z1,z4,z5,z6]),(0,[z0,z414,z98,z4,z5,z6]),(0,[z130,z0,z1,z3,z5,z526]),(0,[z32,z0,z1,z48,z4,z43]),(0,[z50,z0,z1,z3,z4,z462])],[(0,[z0,z1239,z1,z3,z4,z6]),(0,[z0,z1,z3,z1240,z5,z6]),(0,[z0,z3,z98,z36,z5,z6]),(0,[z781,z1,z3,z4,z5,z6]),(0,[z0,z9,z1,z3,z1240,z6]),(0,[z0,z731,z1,z3,z4,z6]),(0,[z0,z266,z3,z5,z52,z6]),(0,[z391,z0,z1,z3,z4,z6])],[(0,[z78,z996,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1241,z6]),(0,[z0,z1,z3,z4,z6,z1242]),(0,[z0,z1,z99,z4,z17,z6])],[(0,[z1243,z0,z3,z4,z5,z6]),(0,[z0,z1,z1244,z4,z5,z6]),(0,[z1245,z0,z1,z3,z4,z6]),(0,[z0,z9,z1,z3,z4,z1206])]],
   [[(0,[z0,z1,z1246,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1247]),(0,[z0,z1,z3,z36,z5,z6]),(0,[z0,z1248,z1,z3,z4,z6]),(0,[z0,z1,z3,z76,z6,z389])],[(0,[z141,z1,z8,z3,z17,z6]),(0,[z0,z1,z550,z4,z17,z6]),(0,[z0,z1,z40,z4,z1249,z6])],[(0,[z0,z84,z1,z4,z104,z6]),(0,[z1,z1250,z3,z4,z5,z6]),(0,[z1251,z0,z1,z3,z4,z6]),(0,[z289,z0,z1,z3,z460,z6])],[(0,[z0,z1,z3,z760,z5,z6]),(0,[z0,z1252,z1,z3,z4,z6])],[(0,[z34,z9,z1,z4,z28,z6]),(0,[z0,z803,z3,z4,z5,z6]),(0,[z0,z1,z40,z4,z82,z6]),(0,[z0,z1253,z1,z3,z4,z6]),(0,[z168,z0,z3,z441,z5,z6]),(0,[z0,z9,z3,z4,z406,z6])],[(0,[z0,z1,z3,z4,z5,z1254]),(0,[z60,z1,z3,z4,z5,z57]),(0,[z0,z1,z3,z1255,z5,z6]),(0,[z0,z1,z40,z4,z17,z6]),(0,[z180,z0,z1,z99,z4,z6]),(0,[z0,z1,z40,z4,z6,z172]),(0,[z0,z1,z3,z363,z88,z6])],[(0,[z0,z1,z40,z4,z336,z6]),(0,[z0,z1,z3,z1256,z5,z6]),(0,[z374,z271,z0,z3,z5,z6]),(0,[z226,z0,z367,z3,z4,z6]),(0,[z0,z9,z1,z3,z4,z1219]),(0,[z224,z0,z1,z40,z4,z6]),(0,[z0,z1,z3,z1058,z5,z6]),(0,[z121,z0,z396,z3,z4,z172]),(0,[z0,z1,z3,z4,z883,z5])],[(0,[z0,z1,z1257,z3,z4,z6]),(0,[z1258,z0,z1,z3,z4,z6]),(0,[z0,z1259,z1,z3,z4,z6]),(0,[z0,z1260,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1261,z6])]],
   [[(0,[z34,z32,z1,z4,z28,z6]),(0,[z0,z1262,z1,z3,z4,z6]),(0,[z0,z9,z1,z3,z6,z199]),(0,[z0,z1,z3,z1263,z5,z6])],[(0,[z0,z1264,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1265,z6]),(0,[z42,z0,z1,z40,z4,z6]),(0,[z0,z38,z9,z1,z76,z6]),(0,[z0,z1,z288,z40,z4,z6]),(0,[z0,z1,z3,z279,z88,z6]),(0,[z32,z0,z1,z3,z1123,z6]),(0,[z1266,z0,z1,z3,z4,z6])],[(0,[z0,z1,z4,z5,z6,z1267]),(0,[z0,z66,z3,z98,z4,z6]),(0,[z226,z0,z1,z40,z4,z6]),(0,[z519,z0,z1,z40,z4,z6]),(0,[z0,z9,z1,z3,z76,z6]),(0,[z1,z3,z4,z5,z6,z1268]),(1,[z715,z0,z1,z4,z6])],[(0,[z0,z272,z1,z4,z6,z285]),(0,[z0,z1,z46,z40,z4,z6]),(0,[z0,z1,z3,z4,z1269,z6]),(0,[z0,z1,z3,z4,z1270,z6])],[(0,[z234,z1,z220,z4,z17,z6]),(0,[z1002,z0,z1,z3,z4,z6]),(0,[z374,z0,z3,z5,z6,z250]),(0,[z0,z1,z3,z4,z104,z6]),(0,[z35,z0,z321,z3,z4,z6]),(0,[z0,z1,z3,z4,z944,z6])],[(0,[z35,z0,z1,z3,z36,z6]),(0,[z519,z388,z1,z3,z4,z6]),(0,[z155,z0,z9,z3,z4,z6]),(0,[z0,z858,z1,z3,z17,z6]),(0,[z0,z1,z3,z828,z5,z6]),(0,[z0,z1,z3,z186,z5,z871])],[(0,[z0,z1,z3,z4,z1271,z6]),(0,[z218,z0,z91,z98,z4,z6]),(0,[z32,z0,z91,z98,z4,z6]),(1,[z0,z1,z40,z4,z6]),(0,[z130,z0,z1,z3,z5,z559]),(0,[z32,z0,z1,z40,z4,z6]),(0,[z0,z3,z4,z5,z6,z733])],[(0,[z0,z1272,z3,z4,z5,z6]),(0,[z7,z1,z3,z759,z5,z6]),(0,[z35,z141,z1,z8,z3,z6]),(0,[z0,z1,z1273,z4,z5,z6]),(0,[z0,z1,z3,z4,z1274,z6]),(0,[z222,z0,z1,z40,z4,z6]),(0,[z0,z1275,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z1276,z4,z6]),(0,[z141,z0,z1,z40,z4,z6]),(0,[z35,z0,z240,z3,z4,z6]),(0,[z0,z1277,z3,z4,z5,z6])],[(0,[z0,z1,z1278,z3,z4,z6]),(0,[z271,z0,z9,z1,z3,z6]),(0,[z0,z3,z4,z6,z177,z1279]),(0,[z0,z1,z3,z4,z6,z1280])],[(0,[z0,z1,z3,z1064,z5,z6]),(0,[z1281,z0,z1,z3,z4,z6]),(0,[z0,z1282,z3,z4,z5,z6]),(0,[z0,z1,z3,z354,z4,z6]),(0,[z0,z1,z3,z291,z5,z6]),(0,[z35,z0,z9,z40,z4,z6]),(0,[z121,z0,z9,z3,z4,z172])],[(0,[z60,z1,z3,z5,z250,z57])],[(0,[z0,z9,z3,z4,z6,z177]),(0,[z0,z1283,z1,z3,z4,z6]),(0,[z934,z155,z0,z3,z4,z6])],[(0,[z0,z1,z220,z40,z4,z6]),(0,[z0,z1,z3,z4,z1284,z6]),(0,[z0,z1,z3,z4,z6,z1279]),(0,[z0,z1,z3,z965,z17,z6]),(0,[z32,z0,z1,z3,z6,z199]),(0,[z0,z1,z3,z4,z6,z1285])],[(0,[z0,z1286,z1,z3,z4,z6]),(0,[z35,z223,z0,z1,z4,z6]),(0,[z0,z1287,z1,z3,z4,z6]),(0,[z35,z0,z1,z3,z1026,z6]),(0,[z0,z1,z77,z4,z17,z6])],[(0,[z0,z66,z112,z3,z4,z6]),(0,[z0,z1288,z3,z4,z5,z6]),(0,[z0,z1,z3,z518,z88,z6]),(0,[z0,z1,z40,z4,z64,z6]),(0,[z32,z0,z1,z3,z76,z6]),(0,[z1289,z0,z1,z3,z4,z6]),(0,[z42,z32,z0,z1,z4,z195])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 514) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 514).take 509) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1023).take 317) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1340)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [514, 509, 317] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 74).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 74).take 69).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 143).take 76).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 219).take 37).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [74, 69, 76, 37] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

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

end PEqualNP.Outside.L_meta_45632

theorem PEqualNP.Outside.L_meta_45632 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241376 * 2 ^ 32 + 4004046848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241376 * 2 ^ 32 + 4004046848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_45632.solve