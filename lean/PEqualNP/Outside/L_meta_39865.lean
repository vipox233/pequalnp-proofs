import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39865

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
  Nat.testBit (4008636136 * 2 ^ 32 + 4008241888) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x40000c08b022c2c6#64 ++ 0x100003022c08b0b1#64 ++ 0xfe151d19f467cfcf#64 ++ 0xff8547467d19f3f3#64 : BitVec 256),
   (0x9400606251895650#64 ++ 0x2500181894625594#64 ++ 0xffeae2e67b99f673#64 ++ 0xfffab8b99ee67d9c#64 : BitVec 256),
   (0x283303050c142828#64 ++ 0xca0cc0c143050a0a#64 ++ 0xaa3303078c1e387f#64 ++ 0x6a8cc0c1e3078e1f#64 : BitVec 256),
   (0x303c03b00ec03d00#64 ++ 0x8c0f00ec03b00f40#64 ++ 0x66fc03f80fe03f82#64 ++ 0xd9bf00fe03f80fe0#64 : BitVec 256),
   (0xc07fb4000f7f8000#64 ++ 0xf01fed0003dfe000#64 ++ 0x1f7ffc000fffc001#64 ++ 0xc7dfff0003fff000#64 : BitVec 256),
   (0x00bfdbdfe0000003#64 ++ 0x002ff6f7f8000000#64 ++ 0xffbffffff0000000#64 ++ 0x3feffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [3, 8]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [6, 11]⟩, ⟨.or, [12, 8]⟩, ⟨.and, [1, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xaa3303078c1e387f 0x6a8cc0c1e3078e1f

def z1 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x66fc03f80fe03f82 0xd9bf00fe03f80fe0

def z2 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0xfe151d19f467cfcf 0xff8547467d19f3f3

def z3 : W := mkw 0x9400606251895650 0x2500181894625594 0xffeae2e67b99f673 0xfffab8b99ee67d9c

def z4 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x1f7ffc000fffc001 0xc7dfff0003fff000

def z5 : W := mkw 0xd400242011abd6d4 0x35000908046af5b5 0x0040000003e1c780 0x8010000000f871e0

def z6 : W := mkw 0x008cd8dae0000003 0x00233636b8000000 0x558cfcf870000000 0x15633f3e1c000000

def z7 : W := mkw 0x283343474c142828 0xca0cd0d1d3050a0a 0xffbbe3e7fc1e387f 0x7feef8f9ff078e1f

def z8 : W := mkw 0x00bfdbdfe2400003 0x002ff6f7f8900000 0xfffffffff3e00000 0xbffffffffcf80000

def z9 : W := mkw 0xd400242011abd6d4 0x35000908046af5b5 0x0040000007e7cfcf 0xc010000001f9f3f3

def z10 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffbffffff0000000 0x3feffffffc000000

def z11 : W := mkw 0x303f03b50ec03d00 0x8c0fc0ed43b00f40 0xeeff03ff8fe03f82 0xfbbfc0ffe3f80fe0

def z12 : W := mkw 0xc07fb7050f7f8000 0xf01fedc143dfe000 0xbf7fff078fffc001 0xefdfffc1e3fff000

def z13 : W := mkw 0x00804bdfe0000003 0x002012f7f8000000 0xe08003fff0000000 0x382000fffc000000

def z14 : W := mkw 0xc07c24000f7f8000 0xf01f090003dfe000 0x067c00000fffc001 0xc19f000003fff000

def z15 : W := mkw 0x14bfdbfff0805653 0x052ff6fffc201594 0xffbffffff0003672 0x3feffffffc000d9c

def z16 : W := mkw 0x383f03b50ed43d28 0xce0fc0ed43b50f4a 0xeeff03ff8ffe3fff 0xfbbfc0ffe3ff8fff

def z17 : W := mkw 0xe87fb7050f7fa828 0xfa1fedc143dfea0a 0xbf7fff078ffff87f 0xefdfffc1e3fffe1f

def z18 : W := mkw 0xfc7ff7675ffffe78 0xff1ffdd9d7ffff9e 0xffffffe7fffffe7f 0xfffffff9ffffff9f

def z19 : W := mkw 0xe873b7050d3fa828 0xfa1cedc1434fea0a 0xbb33ff078c1ff87f 0x6eccffc1e307fe1f

def z20 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa3303078c1e387f 0x6a8cc0c1e3078e1f

def z21 : W := mkw 0xbc3363675d9d7e78 0xef0cd8d9d7675f9e 0xfffbe3e7ff9ffe7f 0xfffef8f9ffe7ff9f

def z22 : W := mkw 0x00bfd8dae0000003 0x002ff636b8000000 0x5fbffcf870000000 0x17efff3e1c000000

def z23 : W := mkw 0x383c03b50ec03d28 0x8e0f00ed43b00f4a 0xe6fc03ff8fe03ffe 0xf9bf00ffe3f80fff

def z24 : W := mkw 0xf04024201fffffc4 0xfc10090807fffff1 0x004000000fffffcf 0xc010000003fffff3

def z25 : W := mkw 0xe87fb4000f7fa828 0xfa1fed0003dfea0a 0x1f7ffc000ffff87f 0xc7dfff0003fffe1f

def z26 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0x99abfee7f0000000 0x266affb9fc000000

def z27 : W := mkw 0x100c00b002c01500 0x0403002c00b00540 0x44cc00f803e00780 0x9133003e00f801e0

def z28 : W := mkw 0xc0002400012b8000 0x30000900004ae000 0xbf7fff078ffff87f 0xefdfffc1e3fffe1f

def z29 : W := mkw 0x1400486af08056d6 0x0500121abc2015b5 0xe08002e7f000367e 0x382000b9fc000d9f

def z30 : W := mkw 0x1000002000801400 0x0400000800200500 0x66fc03f80fe03f82 0xd9bf00fe03f80fe0

def z31 : W := mkw 0xc0002400012b8000 0x30000900004ae000 0x1f7ffc000fffc001 0xc7dfff0003fff000

def z32 : W := mkw 0x547fd4625ef6d650 0xd51ff51897bdb594 0xe0951ee674663672 0x382547b99d198d9c

def z33 : W := mkw 0x8000200001090000 0x2000080000424000 0x1f6ae0000b99c001 0xc7dab80002e67000

def z34 : W := mkw 0x008fd8dfe0000003 0x0023f637f8000000 0xdd8ffcfff0000000 0x3763ff3ffc000000

def z35 : W := mkw 0x300c03b002c03d00 0x0c0300ec00b00f40 0x44cc01f803e00f80 0x9133007e00f803e0

def z36 : W := mkw 0x28bfdbdfec14282b 0xca2ff6f7fb050a0a 0xffbffffffc1e387f 0x7fefffffff078e1f

def z37 : W := mkw 0x703c0fb8bee2ffc6 0x9c0f03ee2fb8bff1 0xfefd1ff9ffe7ffcf 0xffbf47fe7ff9fff3

def z38 : W := mkw 0x103c03b002c01500 0x040f00ec00b00540 0x66fc03f807e00f82 0xd9bf00fe01f803e0

def z39 : W := mkw 0x30bfdbffeec03d03 0x8c2ff6fffbb00f40 0xffffffffffe03f82 0xfffffffffff80fe0

def z40 : W := mkw 0xc0ffffdfef7f8003 0xf03ffff7fbdfe000 0xffffffffffffc001 0xfffffffffffff000

def z41 : W := mkw 0xf07fb7b00fffbd00 0xfc1fedec03ffef40 0x7ffffff80fffff83 0xdffffffe03ffffe0

def z42 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffbffffff8183073 0x7feffffffe060c1c

def z43 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0xbf7ffe060ffff073 0xefdfff8183fffc1c

def z44 : W := mkw 0x0803000500140028 0x4200c0014005000a 0x88030007801e007d 0x2200c001e007801f

def z45 : W := mkw 0x28bfdbdfe000282b 0x0a2ff6f7f8000a0a 0xffbffffff000387e 0x3feffffffc000e1f

def z46 : W := mkw 0x9400606251895650 0x2500181894625594 0x55c8e0e07381c600 0x957238381ce07180

def z47 : W := mkw 0xd4006c6af1abd6d6 0x35001b1abc6af5b5 0xffeefefe7bf9f7f3 0xfffbbfbf9efe7dfc

def z48 : W := mkw 0x003300000c140000 0xc00cc00003050000 0x0a3300000c1e0001 0x428cc00003078000

def z49 : W := mkw 0x008cdbdfe0000003 0x002336f7f8000000 0xf58cfffff0000000 0x3d633ffffc000000

def z50 : W := mkw 0x103c03b002c01500 0x040f00ec00b00540 0x44dc01f803e00780 0x9137007e00f801e0

def z51 : W := mkw 0x0080dbdfe0000003 0x002036f7f8000000 0xf180fffff0000000 0x3c603ffffc000000

def z52 : W := mkw 0x1000002000801400 0x0400000800200500 0x66dc01f807e00f82 0xd9b7007e01f803e0

def z53 : W := mkw 0x283300050c142828 0xca0cc00143050a0a 0x8a3300078c1e387f 0x628cc001e3078e1f

def z54 : W := mkw 0x807fb0000f5d0000 0xe01fec0003d74000 0x1f7ffc000b99c001 0xc7dfff0002e67000

def z55 : W := mkw 0x0083d84fe0000003 0x0020f613f8000000 0xffabfee7f0000000 0x3feaffb9fc000000

def z56 : W := mkw 0xc043b400013f8000 0x7010ed00004fe000 0x1f6bfc000b9fc001 0xc7daff0002e7f000

def z57 : W := mkw 0x003fd04240000000 0x000ff41090000000 0xffbffee670000000 0x3fefffb99c000000

def z58 : W := mkw 0xd47ff4625fffd650 0xf51ffd1897fff594 0xfffffee67ffff673 0xffffffb99ffffd9c

def z59 : W := mkw 0x003f900000000000 0x000fe40000000000 0x1f3ffc0000000000 0x07cfff0000000000

def z60 : W := mkw 0x2000030000002800 0x080000c000000a00 0x2000030000003802 0x080000c000000e00

def z61 : W := mkw 0x9400606251895650 0x2500181894625594 0xffeee2fe7bf9f7f3 0xfffbb8bf9efe7dfc

def z62 : W := mkw 0x00bcdbdae0000003 0x002f36f6b8000000 0x559cfdf870000000 0x15673f7e1c000000

def z63 : W := mkw 0x1400486af08056d6 0x0500121abc2015b5 0xe08003fff0003ffe 0x382000fffc000fff

def z64 : W := mkw 0x0803000500140028 0x4200c0014005000a 0x88230207881e307d 0x2208c081e2078c1f

def z65 : W := mkw 0xe87fb7050f7fa828 0xfa1fedc143dfea0a 0x1f7ffe060ffff031 0xc7dfff8183fffc0c

def z66 : W := mkw 0xe07fb7000f7fa800 0xf81fedc003dfea00 0x3f7fff000ffff803 0xcfdfffc003fffe00

def z67 : W := mkw 0x00bfd84fe0000003 0x002ff613f8000000 0x9f3ffc07f0000000 0x27cfff01fc000000

def z68 : W := mkw 0x300000200ec03d00 0x8c00000803b00f40 0x004000000fe03f82 0xc010000003f80fe0

def z69 : W := mkw 0x00bfd3d740000001 0x002ff4f5d0000000 0x01aae2e600000000 0x006ab8b980000000

def z70 : W := mkw 0x28bfdbdfec14282b 0xca2ff6f7fb050a0a 0xffbffffff8183030 0x3feffffffe060c0c

def z71 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0x0022020608183030 0x0008808182060c0c

def z72 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0x54041c187061c780 0x950107061c1871e0

def z73 : W := mkw 0xc04cb400036b8000 0x30132d0000dae000 0x1f5dfc0007e7c001 0xc7d77f0001f9f000

def z74 : W := mkw 0x9400606251895650 0x2500181894625594 0xfffee3fe7ff9fff3 0xffffb8ff9ffe7ffc

def z75 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x7f7ffd180fffcf83 0xdfdfff4603fff3e0

def z76 : W := mkw 0xc07cb4000f6b8000 0xb01f2d0003dae000 0x177cfc000fe1c000 0xc5df3f0003f87000

def z77 : W := mkw 0x300003b00ec03d00 0x8c0000ec03b00f40 0x60c003f80fe03f82 0xd83000fe03f80fe0

def z78 : W := mkw 0x803fb00001090000 0x200fec0000424000 0x1f7ffc000b99c001 0xc7dfff0002e67000

def z79 : W := mkw 0xd4006c6af1abd6d6 0x35001b1abc6af5b5 0xffffffffffffffff 0xffffffffffffffff

def z80 : W := mkw 0x283f03050e542828 0xca0fc0c143950a0a 0xaa3703078c7e387f 0x6a8dc0c1e31f8e1f

def z81 : W := mkw 0xc07fb705036b8000 0x301fedc140dae000 0xbf7fff0783e1c000 0xafdfffc1e0f87000

def z82 : W := mkw 0x9400606241891410 0x2500181890624504 0x01eae2e60b983030 0x007ab8b982e60c0c

def z83 : W := mkw 0x0000000000000000 0x0000000000000000 0xee15011984660fcf 0xfb854046611983f3

def z84 : W := mkw 0xc04cb400036b8000 0x30132d0000dae000 0x154cfc0003e1c000 0x85533f0000f87000

def z85 : W := mkw 0x280000000c142828 0xca00000003050a0a 0xaa1101018c1e387f 0x6a84404063078e1f

def z86 : W := mkw 0x003c00000e400000 0x800f000003900000 0x067c00000fe00000 0xc19f000003f80000

def z87 : W := mkw 0x0803000500140028 0x4200c0014005000a 0xaa230207881e307f 0x6a88c081e2078c1f

def z88 : W := mkw 0x280000000c142828 0xca00000003050a0a 0x000000000c1e387f 0x4000000003078e1f

def z89 : W := mkw 0x288cd8daec14282b 0xca233636bb050a0a 0x558cfcf87c1e387f 0x55633f3e1f078e1f

def z90 : W := mkw 0x68330f0dbc36eaee 0xda0cc3c36f0dbabb 0xfe371f1ffc7fffff 0xff8dc7c7ff1fffff

def z91 : W := mkw 0x9400606251895650 0x2500181894625594 0xfffbe3e7ff9ffe7f 0xfffef8f9ffe7ff9f

def z92 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0x001101018406080c 0x0004404061018203

def z93 : W := mkw 0x00bf9b9da0000003 0x002fe6e768000000 0x00151d1980000000 0x0005474660000000

def z94 : W := mkw 0x9400202011895650 0x2500080804625594 0x004000000b99f673 0xc010000002e67d9c

def z95 : W := mkw 0x303f93b00ec03d00 0x8c0fe4ec03b00f40 0x7ffffff80fe03f82 0xdffffffe03f80fe0

def z96 : W := mkw 0xd440242013ebd650 0x3510090804faf594 0x004000000bf9f673 0xc010000002fe7d9c

def z97 : W := mkw 0x20bfdbdfee402903 0x882ff6f7fb900a40 0xffbffffff4600980 0x3feffffffd180260

def z98 : W := mkw 0x203c03900e402900 0x880f00e403900a40 0x0014011804600980 0x0005004601180260

def z99 : W := mkw 0xc04cb400036b8000 0x30132d0000dae000 0x1f5dfc0003e1c000 0x87d77f0000f87000

def z100 : W := mkw 0xfc4024201ffffe78 0xff10090807ffff9e 0x004000000ffffe7f 0xc010000003ffff9f

def z101 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0x559dfdf9f0000000 0x15677f7e7c000000

def z102 : W := mkw 0xc043b4000f7f8000 0xf010ed0003dfe000 0x1943fc000fffc001 0xc650ff0003fff000

def z103 : W := mkw 0x60300f08bc22eac6 0x980c03c22f08bab1 0xfe351f19fc67ffcf 0xff8d47c67f19fff3

def z104 : W := mkw 0x283f03050e542828 0xca0fc0c143950a0a 0xae7f03078ffe387f 0xeb9fc0c1e3ff8e1f

def z105 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0x88230207881e307d 0x2208c081e2078c1f

def z106 : W := mkw 0x0083d84fe0000003 0x0020f613f8000000 0x9903fc07f0000000 0x2640ff01fc000000

def z107 : W := mkw 0x94bfbbbdb1895653 0x252feeef6c625594 0x00551d198b99f673 0xc015474662e67d9c

def z108 : W := mkw 0x283f93050c142828 0xca0fe4c143050a0a 0xbf3fff078c1e387f 0x6fcfffc1e3078e1f

def z109 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x156efc000bf9c000 0x855bbf0002fe7000

def z110 : W := mkw 0x300c03b002c03d00 0x0c0300ec00b00f40 0x64cc03f803e03f82 0x993300fe00f80fe0

def z111 : W := mkw 0x9400202011895650 0x2500080804625594 0x004000000381c600 0x8010000000e07180

def z112 : W := mkw 0x38bfdbffeed43d2b 0xce2ff6fffbb50f4a 0xfffffffffffe3fff 0xffffffffffff8fff

def z113 : W := mkw 0x9400202011895650 0x2500080804625594 0xaa6202060b99f673 0xea98808182e67d9c

def z114 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffbffffff0003072 0x3feffffffc000c1c

def z115 : W := mkw 0x40000c08a0228086 0x100003022808a021 0x66151d1984660f8e 0xd9854746611983e3

def z116 : W := mkw 0x280300050c142828 0xca00c00143050a0a 0x880300078c1e387f 0x6200c001e3078e1f

def z117 : W := mkw 0x203c03000e402800 0x880f00c003900a00 0x267c03000fe03802 0xc99f00c003f80e00

def z118 : W := mkw 0x283003050c002828 0x8a0c00c143000a0a 0xa23003078c00387e 0x688c00c1e3000e1f

def z119 : W := mkw 0x0000404240000000 0x0000101090000000 0xffaae2e670000000 0x3feab8b99c000000

def z120 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0x8a3302078c1e307d 0x628cc081e3078c1f

def z121 : W := mkw 0x0083dbdfe0000003 0x0020f6f7f8000000 0xf983fffff0000000 0x3e60fffffc000000

def z122 : W := mkw 0x2803030500142828 0x4a00c0c140050a0a 0xa8030307801e387f 0x2a00c0c1e0078e1f

def z123 : W := mkw 0x00bfdbdfec140003 0xc02ff6f7fb050000 0xffbffffffc1e0001 0x7fefffffff078000

def z124 : W := mkw 0x0033030500000000 0x000cc0c140000000 0xaa33030780000000 0x2a8cc0c1e0000000

def z125 : W := mkw 0x28bfd3d74c142829 0xca2ff4f5d3050a0a 0x01aae2e608183030 0x006ab8b982060c0c

def z126 : W := mkw 0x288cdbdfe000282b 0x0a2336f7f8000a0a 0xf58cfffff000387e 0x3d633ffffc000e1f

def z127 : W := mkw 0xc0ccfcdae36b8003 0x30333f36b8dae000 0x55ccfcf873e1c000 0x95733f3e1cf87000

def z128 : W := mkw 0xc04fb400037f8000 0x7013ed0000dfe000 0x1d4ffc0003ffc001 0x8753ff0000fff000

def z129 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x00e802e00b803000 0x003a00b802e00c00

def z130 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0xba111d01f407c84f 0x6e8447407d01f213

def z131 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffbffffff406080c 0x3feffffffd018203

def z132 : W := mkw 0x0000000010004240 0x0000000004001090 0xfe1401187461cfc3 0xff8500461d1873f0

def z133 : W := mkw 0x1400406250805650 0x0500101894201594 0xe08002e670003672 0x382000b99c000d9c

def z134 : W := mkw 0x407f94000e768000 0xd01fe500039da000 0x00151c0004660000 0x0005470001198000

def z135 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0xeefe03fe0ff83ff3 0xfbbf80ff83fe0ffc

def z136 : W := mkw 0x0883d84fe014002b 0x4220f613f805000a 0x9903fc07f01e007d 0x2640ff01fc07801f

def z137 : W := mkw 0x008048dae0000003 0x00201236b8000000 0x408000f870000000 0x1020003e1c000000

def z138 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x44dc01f807e00f80 0x9137007e01f803e0

def z139 : W := mkw 0xe84cb705036ba828 0x3a132dc140daea0a 0xb54cff0783e1f87e 0xad533fc1e0f87e1f

def z140 : W := mkw 0x003c039000000000 0x000f00e400000000 0x66bc03f800000000 0x19af00fe00000000

def z141 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xbe371f078c1e387f 0x6f8dc7c1e3078e1f

def z142 : W := mkw 0xc04024000f7f8000 0xf010090003dfe000 0x004000000fffc001 0xc010000003fff000

def z143 : W := mkw 0x20bfdbdfec002803 0x882ff6f7fb000a00 0xffbffffffc003802 0x7fefffffff000e00

def z144 : W := mkw 0x00bcdbdae0000003 0x002f36f6b8000000 0xffbefffe70000000 0x3fefbfff9c000000

def z145 : W := mkw 0x100c00b002c01500 0x0403002c00b00540 0x66fc03f80fe03f82 0xd9bf00fe03f80fe0

def z146 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0x0a3301018c1e080d 0x428cc04063078203

def z147 : W := mkw 0xc04cb400036b8000 0x30132d0000dae000 0x1f6efc000bf9c001 0xc7dbbf0002fe7000

def z148 : W := mkw 0xc040b400012b8000 0x30102d00004ae000 0x1100fc000001c000 0x04403f0000007000

def z149 : W := mkw 0xd400242011abd6d4 0x35000908046af5b5 0x004000000fffffff 0xc010000003ffffff

def z150 : W := mkw 0x008fd8dae0000003 0x0023f636b8000000 0x5d8ffcf870000000 0x1763ff3e1c000000

def z151 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z152 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffbffffff006004d 0x3feffffffc018013

def z153 : W := mkw 0x0000000010004240 0x0000000004001090 0xfe0000007001c643 0xff8000001c007190

def z154 : W := mkw 0xc4006c4af12bc2d6 0x31001b12bc4af0b5 0x9903fc07f01fc07d 0x2640ff01fc07f01f

def z155 : W := mkw 0x303c00b00ec03d00 0x8c0f002c03b00f40 0x46fc00f80fe03f82 0xd1bf003e03f80fe0

def z156 : W := mkw 0xe84024000f7fa828 0xfa10090003dfea0a 0x004000000ffff87f 0xc010000003fffe1f

def z157 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa22020608183073 0x6a88808182060c1c

def z158 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa1101018406084f 0x6a84404061018213

def z159 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffbffffff406084f 0x7feffffffd018213

def z160 : W := mkw 0x100c00b002c01500 0x0403002c00b00540 0x66dc01f807e00f82 0xd9b7007e01f803e0

def z161 : W := mkw 0x0000000000000000 0x0000000000000000 0x6614011804600f82 0xd9850046011803e0

def z162 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffbffffff4600f82 0xffeffffffd1803e0

def z163 : W := mkw 0x20bfdbdfee402903 0x882ff6f7fb900a40 0xffbffffff0000000 0x3feffffffc000000

def z164 : W := mkw 0x103c03b002c01500 0x040f00ec00b00540 0x66fc03f803e00780 0x99bf00fe00f801e0

def z165 : W := mkw 0xc04cb400036b8000 0x30132d0000dae000 0x154cfc000bf9c001 0xc5533f0002fe7000

def z166 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xee37031f8c7e3fff 0xfb8dc0c7e31f8fff

def z167 : W := mkw 0xd48cfcfaf1abd6d7 0x35233f3ebc6af5b5 0x55ccfcf873e1c780 0x95733f3e1cf871e0

def z168 : W := mkw 0x28bf93950c142829 0xca2fe4e543050a0a 0xaa3303078c1e387f 0x6a8cc0c1e3078e1f

def z169 : W := mkw 0x2800030500002828 0x0a0000c140000a0a 0xaa1103078406387f 0x6a8440c1e1018e1f

def z170 : W := mkw 0xd44024201fffd650 0xf510090807fff594 0x004000000ffff673 0xc010000003fffd9c

def z171 : W := mkw 0x4000040000228000 0x100001000008a000 0x1e151c000467c001 0xc78547000119f000

def z172 : W := mkw 0xc07fbc08bf7fc2c6 0xf01fef022fdff0b1 0xff7ffd19ffffcfcf 0xffdfff467ffff3f3

def z173 : W := mkw 0xc04fb4000f7f8000 0xf013ed0003dfe000 0x1d4ffc000fffc001 0xc753ff0003fff000

def z174 : W := mkw 0xc04cb4000f7f8000 0xf0132d0003dfe000 0x1f6efc000fffc001 0xc7dbbf0003fff000

def z175 : W := mkw 0x003303050c140000 0xc00cc0c143050000 0xaa3303078c1e0001 0x6a8cc0c1e3078000

def z176 : W := mkw 0xc073b4000f7f8000 0xf01ced0003dfe000 0x1b73fc000fffc001 0xc6dcff0003fff000

def z177 : W := mkw 0x280000000c142828 0xca00000003050a0a 0xaa2202060c1e387f 0x6a88808183078e1f

def z178 : W := mkw 0x180f00b502d41528 0x4603c02d40b5054a 0xcccf00ff83fe07fd 0xb333c03fe0ff81ff

def z179 : W := mkw 0xc043b400013f8000 0x7010ed00004fe000 0x1903fc00001fc001 0x0640ff000007f000

def z180 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffbffffff8003002 0x7feffffffe000c00

def z181 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0xfe371f1ffc7fffff 0xff8dc7c7ff1fffff

def z182 : W := mkw 0x103f00b00ed41500 0xc40fc02c03b50540 0x4eff00f80ffe0781 0xd3bfc03e03ff81e0

def z183 : W := mkw 0x2800030500002828 0x0a0000c140000a0a 0xa00003078000387e 0x280000c1e0000e1f

def z184 : W := mkw 0x9400606251895650 0x2500181894625594 0x55eae2e67b99f630 0x957ab8b99ee67d8c

def z185 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x44ec02f80be03780 0x913b00be02f80de0

def z186 : W := mkw 0x9400606251895650 0x2500181894625594 0xddcae0e67399c671 0xb772b8399ce6719c

def z187 : W := mkw 0x00bcdbdae0000003 0x002f36f6b8000000 0x77bcfff870000000 0x1def3ffe1c000000

def z188 : W := mkw 0xd400646251abd6d4 0x35001918946af5b5 0xffeae2e67fffffff 0xfffab8b99fffffff

def z189 : W := mkw 0x283f03950e542928 0xca0fc0e543950a4a 0xaa37031f8c7e39ff 0x6a8dc0c7e31f8e7f

def z190 : W := mkw 0x2800030500002828 0x0a0000c140000a0a 0xaa3303078c1e387f 0x6a8cc0c1e3078e1f

def z191 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x116afc000b99c000 0x045abf0002e67000

def z192 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0xeefd03f98fe63fcf 0xfbbf40fe63f98ff3

def z193 : W := mkw 0x0083d84fe0000003 0x0020f613f8000000 0x99abfee7f0000000 0x266affb9fc000000

def z194 : W := mkw 0x300c00b00ec03d00 0x8c03002c03b00f40 0x44cc00f80fe03f82 0xd133003e03f80fe0

def z195 : W := mkw 0xc04cb4000f7f8000 0xf0132d0003dfe000 0x154cfc000fffc001 0xc5533f0003fff000

def z196 : W := mkw 0xc07cb4000f6b8000 0xb01f2d0003dae000 0x1f7efc000ff9c001 0xc7dfbf0003fe7000

def z197 : W := mkw 0x00bfdbdfee400003 0x802ff6f7fb900000 0xffffffffffe00000 0xfffffffffff80000

def z198 : W := mkw 0x00000808b00042c6 0x000002022c0010b1 0xe6140119f4600fce 0xf98500467d1803f3

def z199 : W := mkw 0x807fb0000f5d0000 0xe01fec0003d74000 0x016ae0000b980000 0x005ab80002e60000

def z200 : W := mkw 0x683307051c36eaec 0xda0cc1c1470dbabb 0xaa3303078c7fffff 0xea8cc0c1e31fffff

def z201 : W := mkw 0x00000808a0000002 0x0000020228000000 0xfe151d19f0000000 0x3f8547467c000000

def z202 : W := mkw 0x40bfdfdff022c2c7 0x102ff7f7fc08b0b1 0xffbffffff467cfcf 0xffeffffffd19f3f3

def z203 : W := mkw 0x203c03900c002800 0x880f00e403000a00 0x66bc03f80c003802 0x59af00fe03000e00

def z204 : W := mkw 0x380c03b502c03d28 0x0e0300ed40b00f4a 0xe4cc03ff83e03ffe 0xb93300ffe0f80fff

def z205 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0xbf7ffd018fffc84f 0xefdfff4063fff213

def z206 : W := mkw 0x28bfdbdfe014282b 0x4a2ff6f7f8050a0a 0xffbffffff01e387f 0x3feffffffc078e1f

def z207 : W := mkw 0x008cd8dae0000003 0x00233636b8000000 0xff9dfdf9f0000000 0x3fe77f7e7c000000

def z208 : W := mkw 0x1000002000801400 0x0400000800200500 0xeeff03ff8ffe3fff 0xfbbfc0ffe3ff8fff

def z209 : W := mkw 0x00b3db4fe0000003 0x002cf6d3f8000000 0xffbbffe7f0000000 0x3feefff9fc000000

def z210 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0x55aefefe70000000 0x156bbfbf9c000000

def z211 : W := mkw 0x100c00b002c01500 0x0403002c00b00540 0x66ec02f80be03782 0xd9bb00be02f80de0

def z212 : W := mkw 0x9400686af18956d6 0x25001a1abc6255b5 0xffeae3fffb99ffff 0xfffab8fffee67fff

def z213 : W := mkw 0xc07fb4900f7f8100 0xf01fed2403dfe040 0x1f7ffc180fffc181 0xc7dfff0603fff060

def z214 : W := mkw 0x9400606251895650 0x2500181894625594 0x99eae2e67b99f071 0x267ab8b99ee67c1c

def z215 : W := mkw 0x303f03b50ec03d00 0x8c0fc0ed43b00f40 0x66fd03f98fe03f82 0xd9bf40fe63f80fe0

def z216 : W := mkw 0x383f03b50ed43d28 0xce0fc0ed43b50f4a 0x66fe03fe0ff83fb2 0xd9bf80ff83fe0fec

def z217 : W := mkw 0x008cdbdfe0000003 0x002336f7f8000000 0xff9dfffff0000000 0x3fe77ffffc000000

def z218 : W := mkw 0x103f03b502c01500 0x040fc0ed40b00540 0xeeff03ff83e00780 0xbbbfc0ffe0f801e0

def z219 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x46fc01f80fe00f80 0xd1bf007e03f803e0

def z220 : W := mkw 0x94bffbfff1895653 0x252ffefffc625594 0xfffffffffb99f673 0xfffffffffee67d9c

def z221 : W := mkw 0xc07fb7900f7f8000 0xf01fede403dfe000 0x7ffffff80fffc001 0xdffffffe03fff000

def z222 : W := mkw 0x2833030500142828 0x4a0cc0c140050a0a 0xaa330307801e387f 0x2a8cc0c1e0078e1f

def z223 : W := mkw 0x28b3dbdfec14282b 0xca2cf6f7fb050a0a 0xfbb3fffffc1e387f 0x7eecffffff078e1f

def z224 : W := mkw 0x283f03950e542928 0xca0fc0e543950a4a 0xee37031f8c7e3fff 0xfb8dc0c7e31f8fff

def z225 : W := mkw 0x383f03b50ed43d28 0xce0fc0ed43b50f4a 0x6eff03f98ffe3f8f 0xdbbfc0fe63ff8fe3

def z226 : W := mkw 0xc4006c4af12bc2d6 0x31001b12bc4af0b5 0x9902fc067019c071 0x2640bf019c06701c

def z227 : W := mkw 0x303c03b000803d00 0x0c0f00ec00200f40 0x66bc03f800003f82 0x19af00fe00000fe0

def z228 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x155dfc0007e7c000 0x85577f0001f9f000

def z229 : W := mkw 0x28bfdbdfe000282b 0x0a2ff6f7f8000a0a 0xffbffffff000080c 0x3feffffffc000203

def z230 : W := mkw 0xd4006c6af1abd6d6 0x35001b1abc6af5b5 0x55ccfcf873e1c780 0x95733f3e1cf871e0

def z231 : W := mkw 0x8000200001090000 0x2000080000424000 0xbf6ae2060b99f073 0xefdab88182e67c1c

def z232 : W := mkw 0xc04cb400036b8000 0x30132d0000dae000 0x1148fc000381c000 0x04523f0000e07000

def z233 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0x88130107841e087d 0x2204c041e107821f

def z234 : W := mkw 0x1000002000801400 0x0400000800200500 0x66e802e00b803602 0xd9ba00b802e00d80

def z235 : W := mkw 0x68ff9f9dae76a82b 0xda3fe7e76b9daa0a 0x00151d198466080c 0x0005474661198203

def z236 : W := mkw 0x687f97050e76a828 0xda1fe5c1439daa0a 0x00151d018466080c 0x0005474061198203

def z237 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x1f7ffc000fffcf83 0xc7dfff0003fff3e0

def z238 : W := mkw 0x283303050e542828 0xca0cc0c143950a0a 0xaa7303078ffe387f 0xea9cc0c1e3ff8e1f

def z239 : W := mkw 0xc84fb405037f8028 0x7213ed0140dfe00a 0x9d4ffc0783ffc07d 0xa753ff01e0fff01f

def z240 : W := mkw 0x08bfdbdfe014002b 0x422ff6f7f805000a 0xffbffffff01e007d 0x3feffffffc07801f

def z241 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x177dfc000fe7c000 0xc5df7f0003f9f000

def z242 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x1b7bfc000f9fc001 0x46deff0003e7f000

def z243 : W := mkw 0x68330f0dbc36eaee 0xda0cc3c36f0dbabb 0x54261e1e7879f7b0 0x950987879e1e7dec

def z244 : W := mkw 0x50000c28b0a2d6c6 0x1400030a2c28b5b1 0xfefd1ff9ffe7ffcf 0xffbf47fe7ff9fff3

def z245 : W := mkw 0x34004bfaf0807fd6 0x0d0012febc201ff5 0xe08003fff0003ffe 0x382000fffc000fff

def z246 : W := mkw 0x0000484ae0000002 0x00001212b8000000 0xff9dfdf9f0000000 0x3fe77f7e7c000000

def z247 : W := mkw 0xbcbffbfffd9d7e7b 0xef2ffeffff675f9e 0xffffffffff9ffe7f 0xffffffffffe7ff9f

def z248 : W := mkw 0x203003000c002800 0x880c00c003000a00 0x223003000c003802 0x488c00c003000e00

def z249 : W := mkw 0x203003000c002800 0x880c00c003000a00 0xaa3203060c183873 0x6a8c80c183060e1c

def z250 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffbffffff4660fcf 0xffeffffffd1983f3

def z251 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x44fc03f80fe03f80 0x913f00fe03f80fe0

def z252 : W := mkw 0xbc3323251d9d7e78 0xef0cc8c947675f9e 0xaa7303078f9ffe7f 0xea9cc0c1e3e7ff9f

def z253 : W := mkw 0x280003050c142828 0xca0000c143050a0a 0xaa2203078c1e387f 0x6a8880c1e3078e1f

def z254 : W := mkw 0x2803030500142828 0x4a00c0c140050a0a 0xaa130307841e387f 0x6a84c0c1e1078e1f

def z255 : W := mkw 0x20bfdbdfee402903 0x882ff6f7fb900a40 0xffbffffff4600f82 0xffeffffffd1803e0

def z256 : W := mkw 0xc07fb4900f7f8000 0xf01fed2403dfe000 0x5ffffcf80fffc001 0xd7ffff3e03fff000

def z257 : W := mkw 0x283300000c142828 0xca0cc00003050a0a 0x0a3300000c1e387f 0x428cc00003078e1f

def z258 : W := mkw 0x9400606251895650 0x2500181894625594 0xffebe2e7fb9ff67f 0xfffaf8b9fee7fd9f

def z259 : W := mkw 0x28804bdfe000282b 0x0a2012f7f8000a0a 0xe08003fff000387e 0x382000fffc000e1f

def z260 : W := mkw 0x00000808b00042c6 0x000002022c0010b1 0x4000001870000780 0x100000061c0001e0

def z261 : W := mkw 0x28bfdbdfec14282b 0xca2ff6f7fb050a0a 0xffbffffff406080c 0x3feffffffd018203

def z262 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xaa3303078c7e3fff 0xea8cc0c1e31f8fff

def z263 : W := mkw 0xc07ff4424f7f8000 0xf01ffd1093dfe000 0xfffffee67fffc001 0xffffffb99ffff000

def z264 : W := mkw 0x3cb34bfffc947e7b 0xcf2cd2ffff251f9e 0xeab303fffc1e3e7f 0x7aacc0ffff078f9f

def z265 : W := mkw 0x9400606251895650 0x2500181894625594 0x5feae0e07b99c601 0xd7fab8381ee67180

def z266 : W := mkw 0x383f03b50ed43d28 0xce0fc0ed43b50f4a 0x66fd03f98fe63f8e 0xd9bf40fe63f98fe3

def z267 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0x99bffffff0000000 0x266ffffffc000000

def z268 : W := mkw 0x300003b000803d00 0x0c0000ec00200f40 0x66fc03f80fe03f82 0xd9bf00fe03f80fe0

def z269 : W := mkw 0x40000c08a0228086 0x100003022808a021 0x00151d198466098c 0x0005474661198263

def z270 : W := mkw 0xd4006c6ae1ab9496 0x35001b1ab86ae525 0x01ffffff8ffe39bc 0x007fffffe3ff8e6f

def z271 : W := mkw 0xc04cb4000f7f8000 0xf0132d0003dfe000 0x154cfc000bf9c000 0x85533f0002fe7000

def z272 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xaa22020608183073 0x6a88808182060c1c

def z273 : W := mkw 0x003f039500000000 0x000fc0e540000000 0xeebf03ff80000000 0x3bafc0ffe0000000

def z274 : W := mkw 0x300003b002c03d00 0x0c0000ec00b00f40 0x60c003f803e03f82 0x983000fe00f80fe0

def z275 : W := mkw 0x383303250ed43d28 0xce0cc0c943b50f4a 0xaa7303078ffe3fff 0xea9cc0c1e3ff8fff

def z276 : W := mkw 0xc07324000f7f8000 0xf01cc90003dfe000 0x0a7300000fffc001 0xc29cc00003fff000

def z277 : W := mkw 0x14804bfff08056d7 0x052012fffc2015b5 0xe08003fff0003ffe 0x382000fffc000fff

def z278 : W := mkw 0x400004001022c2c4 0x100001000408b0b1 0x000000000467cfcf 0xc00000000119f3f3

def z279 : W := mkw 0x00bfdbdfec140003 0xc02ff6f7fb050000 0xffbffffffc1e084f 0x7fefffffff078213

def z280 : W := mkw 0x0003000500000000 0x0000c00140000000 0x8803000780000000 0x2200c001e0000000

def z281 : W := mkw 0x20bcdbdaec002803 0x882f36f6bb000a00 0x77bcfff87c003802 0x5def3ffe1f000e00

def z282 : W := mkw 0xc0002400012b8000 0x30000900004ae000 0x154cfc0003e1c000 0x85533f0000f87000

def z283 : W := mkw 0xc0fffcdaef7f8003 0xf03fff36bbdfe000 0x5ffffcf87fffc001 0xd7ffff3e1ffff000

def z284 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0x54151d19f467cf8c 0x950547467d19f3e3

def z285 : W := mkw 0x408cdcdaf022c2c7 0x10233736bc08b0b1 0xff9dfdf9f467cfcf 0xffe77f7e7d19f3f3

def z286 : W := mkw 0x943ff06251895650 0x250ffc1894625594 0xfffffee67b99f673 0xffffffb99ee67d9c

def z287 : W := mkw 0xf87fb7b50fffbd28 0xfe1feded43ffef4a 0xffffffff8fffffff 0xffffffffe3ffffff

def z288 : W := mkw 0x9400606251895650 0x2500181894625594 0xffeae2e67f9ffe7f 0xfffab8b99fe7ff9f

def z289 : W := mkw 0x280003050c142828 0xca0000c143050a0a 0xa00003078c1e387f 0x680000c1e3078e1f

def z290 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x196bfc000b9fc001 0x065aff0002e7f000

def z291 : W := mkw 0x383c03b00ec03d28 0x8e0f00ec03b00f4a 0x66fc03f80fe03ffe 0xd9bf00fe03f80fff

def z292 : W := mkw 0x003f00000e540000 0xc00fc00003950000 0x0e7f00000ffe0001 0xc39fc00003ff8000

def z293 : W := mkw 0xa87fb3050f5d2828 0xea1fecc143d74a0a 0x016ae2060b983030 0x005ab88182e60c0c

def z294 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0xe6fc03f98fe03fce 0xf9bf00fe63f80ff3

def z295 : W := mkw 0x303f03b00ed43d00 0xcc0fc0ec03b50f40 0x6eff03f80ffe3f83 0xdbbfc0fe03ff8fe0

def z296 : W := mkw 0x28bfdbdfec14282b 0xca2ff6f7fb050a0a 0xffbffffff41e087d 0x3feffffffd07821f

def z297 : W := mkw 0xb43c63f25fc97f50 0xad0f18fc97f25fd4 0xfffee3fe7ff9fff3 0xffffb8ff9ffe7ffc

def z298 : W := mkw 0x0080d84ae0000003 0x00203612b8000000 0xffaafee670000000 0x3feabfb99c000000

def z299 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x196bfc000fffc001 0xc65aff0003fff000

def z300 : W := mkw 0x3083d86feec03d03 0x8c20f61bfbb00f40 0x9943fc07ffe03f82 0xe650ff01fff80fe0

def z301 : W := mkw 0x00b3db4fe0000003 0x002cf6d3f8000000 0xbb33ff07f0000000 0x2eccffc1fc000000

def z302 : W := mkw 0xe87fbf0dbf7feaee 0xfa1fefc36fdffabb 0xff7fff1fffffffff 0xffdfffc7ffffffff

def z303 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0x98011c01f007c04d 0x260047007c01f013

def z304 : W := mkw 0x28b34bdfec14282b 0xca2cd2f7fb050a0a 0xeab303fffc1e387f 0x7aacc0ffff078e1f

def z305 : W := mkw 0x003c00000e400000 0x800f000003900000 0x667c01180fe00f82 0xd99f004603f803e0

def z306 : W := mkw 0x283303950c142828 0xca0cc0e543050a0a 0xeab303ff8c1e387f 0x7aacc0ffe3078e1f

def z307 : W := mkw 0x380000200ed43d28 0xce00000803b50f4a 0x004000000ffe3fff 0xc010000003ff8fff

def z308 : W := mkw 0xe07fb7000f7fa800 0xf81fedc003dfea00 0x7f7fff180fffff83 0xdfdfffc603ffffe0

def z309 : W := mkw 0x383f03b50ed43d28 0xce0fc0ed43b50f4a 0xe6fd03ff8fe63ffe 0xf9bf40ffe3f98fff

def z310 : W := mkw 0x28bfdbdfee54282b 0xca2ff6f7fb950a0a 0xfffffffffffe387f 0xffffffffffff8e1f

def z311 : W := mkw 0x383c03b00ed43d28 0xce0f00ec03b50f4a 0x66fc03f80ffe3fff 0xd9bf00fe03ff8fff

def z312 : W := mkw 0xe87fb7050f7fa828 0xfa1fedc143dfea0a 0x1f7ffd018fffc80d 0xc7dfff4063fff203

def z313 : W := mkw 0xe843b4050f7fa828 0xfa10ed0143dfea0a 0x9943fc078ffff87f 0xe650ff01e3fffe1f

def z314 : W := mkw 0x8003b00001090000 0x2000ec0000424000 0x1f6bfc000b99c001 0xc7daff0002e67000

def z315 : W := mkw 0x28bfdbdfee54292b 0xca2ff6f7fb950a4a 0xffbffffff466098c 0x3feffffffd198263

def z316 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0x223203060c183832 0x488c80c183060e0c

def z317 : W := mkw 0x1400406250805650 0x0500101894201594 0xeaa202e678183673 0x7aa880b99e060d9c

def z318 : W := mkw 0x383f03b50ed43d28 0xce0fc0ed43b50f4a 0x44dd01f987e60f8c 0x9137407e61f983e3

def z319 : W := mkw 0x00bfdbdfee540003 0xc02ff6f7fb950000 0xfffffffffffe0001 0xffffffffffff8000

def z320 : W := mkw 0xe07cb7000f6ba800 0xb81f2dc003daea00 0x377cff000fe1f802 0xcddf3fc003f87e00

def z321 : W := mkw 0xc03fb400012b8000 0x300fed00004ae000 0x1f7ffc000fffc001 0xc7dfff0003fff000

def z322 : W := mkw 0x380003b50ed43d28 0xce0000ed43b50f4a 0xe0c003ff8ffe3fff 0xf83000ffe3ff8fff

def z323 : W := mkw 0x088fd8dfe014002b 0x4223f637f805000a 0xdd8ffcfff01e007d 0x3763ff3ffc07801f

def z324 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xa02203078818387e 0x280880c1e2060e1f

def z325 : W := mkw 0x0800000000140028 0x420000000005000a 0x00000000001e007d 0x000000000007801f

def z326 : W := mkw 0xc07cb4000f6b8000 0xb01f2d0003dae000 0x156cfc000be1c000 0x855b3f0002f87000

def z327 : W := mkw 0x9400606251895650 0x2500181894625594 0xffeae2e67381c600 0xbffab8b99ce07180

def z328 : W := mkw 0x28bfdbdfec14282b 0xca2ff6f7fb050a0a 0xffbffffffc7e3fff 0xffefffffff1f8fff

def z329 : W := mkw 0x303f03b00ed43d00 0xcc0fc0ec03b50f40 0x66fe03f80ff83f82 0xd9bf80fe03fe0fe0

def z330 : W := mkw 0xc04cb400036b8000 0x30132d0000dae000 0x554cfc1803e1c780 0x95533f0600f871e0

def z331 : W := mkw 0x008cd8dae0000003 0x00233636b8000000 0x5faefcf870000000 0x17ebbf3e1c000000

def z332 : W := mkw 0x9400686af1895652 0x25001a1abc625594 0xfffffffffb99f673 0xfffffffffee67d9c

def z333 : W := mkw 0x00b34bdfe0000003 0x002cd2f7f8000000 0xeab303fff0000000 0x3aacc0fffc000000

def z334 : W := mkw 0xe83327050d3fa828 0xfa0cc9c1434fea0a 0xbf7fff078ffff87f 0xefdfffc1e3fffe1f

def z335 : W := mkw 0x10bfdbffe2c01503 0x042ff6fff8b00540 0xfffffffff3e00780 0xbffffffffcf801e0

def z336 : W := mkw 0xd4002c28b1abd6d6 0x35000b0a2c6af5b5 0xfe551d19ffffffff 0xff9547467fffffff

def z337 : W := mkw 0x0803000500140028 0x4200c0014005000a 0xaa3303078c1e387f 0x6a8cc0c1e3078e1f

def z338 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x44ec02f80fe03f82 0xd13b00be03f80fe0

def z339 : W := mkw 0x283f03950c142828 0xca0fc0e543050a0a 0xeebf03ff8c1e387f 0x7bafc0ffe3078e1f

def z340 : W := mkw 0x300003b00ec03d00 0x8c0000ec03b00f40 0x66d403f80fe03f82 0xd9b500fe03f80fe0

def z341 : W := mkw 0x3c804bfff0807e7b 0x0f2012fffc201f9e 0xe08003fff0003e7e 0x382000fffc000f9f

def z342 : W := mkw 0xfc3327251dbffefc 0xff0cc9c9476fffbf 0xaa7303078fffffff 0xea9cc0c1e3ffffff

def z343 : W := mkw 0x00bfd8dae0000003 0x002ff636b8000000 0x559dfcf870000000 0x15677f3e1c000000

def z344 : W := mkw 0x28bfd3d74c142829 0xca2ff4f5d3050a0a 0xabbbe3e78c1e387f 0x6aeef8f9e3078e1f

def z345 : W := mkw 0x100c00b002c01500 0x0403002c00b00540 0x66ec02f803e00780 0x99bb00be00f801e0

def z346 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffbffffff0000602 0xffeffffffc000180

def z347 : W := mkw 0x9400606251895650 0x2500181894625594 0xfffee2e67ff9f673 0xffffb8b99ffe7d9c

def z348 : W := mkw 0x303f03b50ec03d00 0x8c0fc0ed43b00f40 0xeeff03ff8ff83ff3 0xfbbfc0ffe3fe0ffc

def z349 : W := mkw 0x28bf9b9dac14282b 0xca2fe6e76b050a0a 0xaa371f1f8c1e387f 0x6a8dc7c7e3078e1f

def z350 : W := mkw 0x000cd04240000000 0x0003341090000000 0x558cfce070000000 0x15633f381c000000

def z351 : W := mkw 0xe07fb7050f7fa800 0xf81fedc143dfea00 0xbf7fff078ffff803 0xefdfffc1e3fffe00

def z352 : W := mkw 0x283f03950e542928 0xca0fc0e543950a4a 0x001501198466098c 0x0005404661198263

def z353 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0xfe171d1ff47fcfff 0xff85c747fd1ff3ff

def z354 : W := mkw 0xc07fb400037f8000 0x701fed0000dfe000 0x1f7ffc0003ffc001 0x87dfff0000fff000

def z355 : W := mkw 0x948cf8faf1895653 0x25233e3ebc625594 0x55ccfcf87381c600 0x95733f3e1ce07180

def z356 : W := mkw 0x000000000c140000 0xc000000003050000 0x000000000c1e0001 0x4000000003078000

def z357 : W := mkw 0x300003b000803d00 0x0c0000ec00200f40 0x608003f800003f82 0x182000fe00000fe0

def z358 : W := mkw 0xc07fb400013f8000 0x701fed00004fe000 0x1f3ffc00001fc001 0x07cfff000007f000

def z359 : W := mkw 0xd47ff4625fffd650 0xf51ffd1897fff594 0x5ffffce07fffc601 0xd7ffff381ffff180

def z360 : W := mkw 0x0083dbdfe0000003 0x0020f6f7f8000000 0x9983fee7f0000000 0x2660ffb9fc000000

def z361 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x60d403f80fe03f82 0xd83500fe03f80fe0

def z362 : W := mkw 0x9400606251895650 0x2500181894625594 0x77eae2e67b99f632 0xddfab8b99ee67d8c

def z363 : W := mkw 0xc07fb7050f7f8000 0xf01fedc143dfe000 0xbf7fff078fffc84f 0xefdfffc1e3fff213

def z364 : W := mkw 0x300c00b00ec03d00 0x8c03002c03b00f40 0x44cc00f807e00f80 0x9133003e01f803e0

def z365 : W := mkw 0x383f93b50ed43d28 0xce0fe4ed43b50f4a 0xffffffff8ffe3fff 0xffffffffe3ff8fff

def z366 : W := mkw 0x303f03b00ed43d00 0xcc0fc0ec03b50f40 0x66fd03f80fe63f82 0xd9bf40fe03f98fe0

def z367 : W := mkw 0x00bcd8dae0000003 0x002f3636b8000000 0x57bcfcf870000000 0x15ef3f3e1c000000

def z368 : W := mkw 0xd440242013ebd650 0x3510090804faf594 0x0040000003e1c600 0x8010000000f87180

def z369 : W := mkw 0x303003b00ec03d00 0x8c0c00ec03b00f40 0x62f003f80fe03f82 0xd8bc00fe03f80fe0

def z370 : W := mkw 0xc07fb7900f7f8000 0xf01fede403dfe000 0x1f7ffd180fffc001 0xc7dfff4603fff000

def z371 : W := mkw 0x00bfd8dae0000003 0x002ff636b8000000 0xffbffdf9f0000000 0x3fefff7e7c000000

def z372 : W := mkw 0x28000b0db0006aee 0x0a0002c36c001abb 0xe000031ff0003ffe 0x380000c7fc000fff

def z373 : W := mkw 0x00bfdbdfec140003 0xc02ff6f7fb050000 0xffbffffff4060000 0x3feffffffd018000

def z374 : W := mkw 0x0800000500000028 0x020000014000000a 0x800000078000007c 0x20000001e000001f

def z375 : W := mkw 0xe87fb7050f7fa828 0xfa1fedc143dfea0a 0xff7fff1f8fffffff 0xffdfffc7e3ffffff

def z376 : W := mkw 0x008cd8dae0000003 0x00233636b8000000 0xffaefefe70000000 0x3febbfbf9c000000

def z377 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x609403f804603f82 0x182500fe01180fe0

def z378 : W := mkw 0x0000484ae0000002 0x00001212b8000000 0xffbffffff0000000 0x3feffffffc000000

def z379 : W := mkw 0x283303051c146a68 0xca0cc0c147051a9a 0xfe330307fc1ffe7f 0xff8cc0c1ff07ff9f

def z380 : W := mkw 0x283f03950e542828 0xca0fc0e543950a0a 0xeeff03ff8ffe387f 0xfbbfc0ffe3ff8e1f

def z381 : W := mkw 0x000c900000000000 0x0003240000000000 0x150cfc0000000000 0x05433f0000000000

def z382 : W := mkw 0xc0ffffdfe36b8003 0x303ffff7f8dae000 0xfffffffff3e1c000 0xbffffffffcf87000

def z383 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xa8230307881e387f 0x2a08c0c1e2078e1f

def z384 : W := mkw 0x008cd8dae0000003 0x00233636b8000000 0x1188fce070000000 0x04623f381c000000

def z385 : W := mkw 0x380003b500803d28 0x0e0000ed40200f4a 0xe08003ff80003ffe 0x382000ffe0000fff

def z386 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x1f5dfc0007e7c001 0xc7d77f0001f9f000

def z387 : W := mkw 0x100c00b002c01500 0x0403002c00b00540 0x64cc02f803e03782 0x993300be00f80de0

def z388 : W := mkw 0x0080d8dae0000003 0x00203636b8000000 0x5180fcf870000000 0x14603f3e1c000000

def z389 : W := mkw 0x1480486ff0805653 0x0520121bfc201594 0xe08002e7f0003672 0x382000b9fc000d9c

def z390 : W := mkw 0x300000200ec03d00 0x8c00000803b00f40 0x665401180fe03f82 0xd995004603f80fe0

def z391 : W := mkw 0x303c00200ec03d00 0x8c0f000803b00f40 0x067c00000fe03f82 0xc19f000003f80fe0

def z392 : W := mkw 0x2833030500002828 0x0a0cc0c140000a0a 0xaa3303078000387e 0x2a8cc0c1e0000e1f

def z393 : W := mkw 0x1000002000801400 0x0400000800200500 0x44c800e003800600 0x9132003800e00180

def z394 : W := mkw 0x940c60f253c95750 0x2503183c94f255d4 0xffeee2fe7bf9f7f3 0xfffbb8bf9efe7dfc

def z395 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffbffffff4000802 0x7feffffffd000200

def z396 : W := mkw 0x9400606251895650 0x2500181894625594 0xffeae3fe7b99fff3 0xfffab8ff9ee67ffc

def z397 : W := mkw 0x383303250c943c28 0xce0cc0c943250f0a 0xeeff03ff8ffe3fff 0xfbbfc0ffe3ff8fff

def z398 : W := mkw 0x0080d84ae0000003 0x00203612b8000000 0x1100fc0070000000 0x04403f001c000000

def z399 : W := mkw 0x08bfdbdfe014002b 0x422ff6f7f805000a 0xffbffffff81e307f 0x7feffffffe078c1f

def z400 : W := mkw 0xc07fb400036b8000 0x301fed0000dae000 0x156efc0003e1c000 0x855bbf0000f87000

def z401 : W := mkw 0x500c0cb8b2e2d7c6 0x1403032e2cb8b5f1 0xfedd1df9f7e7cfcf 0xffb7477e7df9f3f3

def z402 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0x10001c007001c000 0x040007001c007000

def z403 : W := mkw 0x1400406250805650 0x0500101894201594 0x408000e070000600 0x102000381c000180

def z404 : W := mkw 0x8000604241090000 0x2000181090424000 0xffeae2e67b99f073 0xfffab8b99ee67c1c

def z405 : W := mkw 0x283f03950c142828 0xca0fc0e543050a0a 0xeebf03ff8c7e3fff 0xfbafc0ffe31f8fff

def z406 : W := mkw 0xe07fb7000f7fa800 0xf81fedc003dfea00 0xbf7fff060ffff873 0xefdfffc183fffe1c

def z407 : W := mkw 0x008cd8dae2400003 0x00233636b8900000 0x55ccfcf873e00000 0x95733f3e1cf80000

def z408 : W := mkw 0x303c03b50ec03d00 0x8c0f00ed43b00f40 0xe6fc03ff8fe03f82 0xf9bf00ffe3f80fe0

def z409 : W := mkw 0x383c03b00ed43d28 0xce0f00ec03b50f4a 0x66fc03f80ff83fb2 0xd9bf00fe03fe0fec

def z410 : W := mkw 0x203303000c142800 0xc80cc0c003050a00 0x2a3303000c1e3803 0x4a8cc0c003078e00

def z411 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x1f6efc000bf9c001 0xc7dbbf0002fe7000

def z412 : W := mkw 0x9400606251895650 0x2500181894625594 0x11eae2e67b99f030 0x047ab8b99ee67c0c

def z413 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffbffffff0000043 0x7feffffffc000010

def z414 : W := mkw 0x303f93b50ec03d00 0x8c0fe4ed43b00f40 0xffffffff8fe03f82 0xffffffffe3f80fe0

def z415 : W := mkw 0x0080d84ae0000003 0x00203612b8000000 0x5588fce070000000 0x15623f381c000000

def z416 : W := mkw 0x100000b000801500 0x0400002c00200540 0x408000f800000780 0x1020003e000001e0

def z417 : W := mkw 0x00334b4fe0000002 0x000cd2d3f8000000 0xffbffffff0000000 0x3feffffffc000000

def z418 : W := mkw 0x28bfdbdfec14282b 0xca2ff6f7fb050a0a 0xffbffffffc06380e 0x7fefffffff018e03

def z419 : W := mkw 0x9400606251895650 0x2500181894625594 0xffeae2e67b99f630 0xbffab8b99ee67d8c

def z420 : W := mkw 0xc07fb400036b8000 0x301fed0000dae000 0x1f7ffc0003e1c000 0x87dfff0000f87000

def z421 : W := mkw 0x280303050c142828 0xca00c0c143050a0a 0xa80303078c1e387f 0x6a00c0c1e3078e1f

def z422 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0x558cfcf870000000 0x15633f3e1c000000

def z423 : W := mkw 0x28bfdbdfe000282b 0x0a2ff6f7f8000a0a 0xffbffffff818387f 0x7feffffffe060e1f

def z424 : W := mkw 0xc87fb4050f7f8028 0xf21fed0143dfe00a 0x9f7ffc078fffc07d 0xe7dfff01e3fff01f

def z425 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0x001101018c1e387f 0x4004404063078e1f

def z426 : W := mkw 0x9400606251895650 0x2500181894625594 0xffffe3ffffffffff 0xfffff8ffffffffff

def z427 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0x76151d19f467cf8e 0xdd8547467d19f3e3

def z428 : W := mkw 0xf07cb7b00febbd00 0xbc1f2dec03faef40 0x77fcfff80fe1ff82 0xddff3ffe03f87fe0

def z429 : W := mkw 0x103c00b00ec01500 0x840f002c03b00540 0x46fc00f80fe00780 0xd1bf003e03f801e0

def z430 : W := mkw 0x807fb808bf5d42c6 0xe01fee022fd750b1 0xe16ae119fb980fce 0x385ab8467ee603f3

def z431 : W := mkw 0xc07cb790036b8000 0x301f2de400dae000 0x77fcfff803e1c000 0x9dff3ffe00f87000

def z432 : W := mkw 0xd44024201fffd6d4 0xf510090807fff5b5 0x004000000fffffff 0xc010000003ffffff

def z433 : W := mkw 0x300c03b002c03d00 0x0c0300ec00b00f40 0x66ec03f80be03f82 0xd9bb00fe02f80fe0

def z434 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x66fc03f80be03780 0x99bf00fe02f80de0

def z435 : W := mkw 0xfc7327251ffffe78 0xff1cc9c947ffff9e 0xaa7303078ffffe7f 0xea9cc0c1e3ffff9f

def z436 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffbffffff0600780 0xbfeffffffc1801e0

def z437 : W := mkw 0xc040b400012b8000 0x30102d00004ae000 0x1548fc000381c000 0x85523f0000e07000

def z438 : W := mkw 0x008cd8dfe0000003 0x00233637f8000000 0xd58cfcfff0000000 0x35633f3ffc000000

def z439 : W := mkw 0xc0ffb7950f7f8001 0xf03fede543dfe000 0x1f7ffc000fffc001 0xc7dfff0003fff000

def z440 : W := mkw 0x9400606241891410 0x2500181890624504 0xffeae2e67b99f031 0xfffab8b99ee67c0c

def z441 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0x76141d187461cf82 0xdd8507461d1873e0

def z442 : W := mkw 0x003f90000c140000 0xc00fe40003050000 0x1f3ffc000c1e0001 0x47cfff0003078000

def z443 : W := mkw 0xc07fb7950f7f8000 0xf01fede543dfe000 0xffffffff8fffc001 0xffffffffe3fff000

def z444 : W := mkw 0x1000002000801400 0x0400000800200500 0xeeea02e60b983673 0xfbba80b982e60d9c

def z445 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xea33031f8c1e3fff 0x7a8cc0c7e3078fff

def z446 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0xfe7d1d19ffe7cfcf 0xff9f47467ff9f3f3

def z447 : W := mkw 0x383f03b50ed43d28 0xce0fc0ed43b50f4a 0xe6fe03ff8ff83ffe 0xf9bf80ffe3fe0fff

def z448 : W := mkw 0x100c00b002c01500 0x0403002c00b00540 0xeedd01f987e60fcf 0xfbb7407e61f983f3

def z449 : W := mkw 0xc04cbc08b36bc2c6 0x30132f022cdaf0b1 0xff5dfd19f7e7cfcf 0xffd77f467df9f3f3

def z450 : W := mkw 0x203303050c002800 0x880cc0c143000a00 0xaa3303078c003802 0x6a8cc0c1e3000e00

def z451 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x1d6ffc000bffc001 0x875bff0002fff000

def z452 : W := mkw 0xf043b7b001bfbd00 0x7c10edec006fef40 0x7983fff8001fff83 0x1e60fffe0007ffe0

def z453 : W := mkw 0x1400486af0805652 0x0500121abc201594 0xe08003fff0003672 0x382000fffc000d9c

def z454 : W := mkw 0x28bf9b9dac14282b 0xca2fe6e76b050a0a 0x00151d198406080c 0x0005474661018203

def z455 : W := mkw 0xc040b4000f7f8000 0xf0102d0003dfe000 0x1140fc000fffc001 0xc4503f0003fff000

def z456 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0x003303078c1e387f 0x400cc0c1e3078e1f

def z457 : W := mkw 0x00bfdbdfec140003 0xc02ff6f7fb050000 0xffbffffff8180000 0x3feffffffe060000

def z458 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0xff7ffc007fffc001 0xffdfff001ffff000

def z459 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0x9fbffee7f0000000 0x27efffb9fc000000

def z460 : W := mkw 0x203003000c002800 0x880c00c003000a00 0xaa3303078c1e387f 0x6a8cc0c1e3078e1f

def z461 : W := mkw 0x0000000010004240 0x0000000004001090 0x540000007001c600 0x950000001c007180

def z462 : W := mkw 0x00000808b00042c6 0x000002022c0010b1 0xea110119f4060fcf 0x7a8440467d0183f3

def z463 : W := mkw 0x804cb00003490000 0x20132c0000d24000 0x0148e00003800000 0x0052380000e00000

def z464 : W := mkw 0xa43c63d25f496b50 0xa90f18f497d25ad4 0x9916e11e7479c9f1 0x2645b8479d1e727c

def z465 : W := mkw 0x103c03b000801400 0x040f00ec00200500 0x66fc03f80fe03f82 0xd9bf00fe03f80fe0

def z466 : W := mkw 0xc0002400012b8000 0x30000900004ae000 0x1f6bfc000b9fc001 0xc7daff0002e7f000

def z467 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xa02203078c1e387f 0x680880c1e3078e1f

def z468 : W := mkw 0x000c000002400000 0x0003000000900000 0x044c000003e00000 0x8113000000f80000

def z469 : W := mkw 0xd07fb4b00fff9500 0xf41fed2c03ffe540 0x5ffffcf80fffc781 0xd7ffff3e03fff1e0

def z470 : W := mkw 0xd40c6cfaf3ebd7d6 0x35031b3ebcfaf5f5 0x55ccfcf873e1c780 0x95733f3e1cf871e0

def z471 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0x002202060c1e387f 0x4008808183078e1f

def z472 : W := mkw 0x283003000c142828 0xca0c00c003050a0a 0x223003000c1e387f 0x488c00c003078e1f

def z473 : W := mkw 0x28330b0dac14282a 0xca0cc2c36b050a0a 0xfe371f1ffc1e387f 0x7f8dc7c7ff078e1f

def z474 : W := mkw 0x003300000c140000 0xc00cc00003050000 0xaa3301018c1e084f 0x6a8cc04063078213

def z475 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffbffffff4600980 0x3feffffffd180260

def z476 : W := mkw 0xe07fb7900f7fa900 0xf81fede403dfea40 0x1f7ffd180fffc981 0xc7dfff4603fff260

def z477 : W := mkw 0x00bcd8daee400003 0x802f3636bb900000 0x57fcfcf87fe00000 0xd5ff3f3e1ff80000

def z478 : W := mkw 0x008cdbdfe0000003 0x002336f7f8000000 0x558cfdf9f0000000 0x15633f7e7c000000

def z479 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0xfe371d19fc7fcfcf 0xff8dc7467f1ff3f3

def z480 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0xf4151d19f467cfce 0xbd0547467d19f3f3

def z481 : W := mkw 0x003f9b98a0000002 0x000fe6e628000000 0xffbffff9f0000000 0x3feffffe7c000000

def z482 : W := mkw 0xe873b7050d3fa828 0xfa1cedc1434fea0a 0xbf7bff078f9ff87f 0xefdeffc1e3e7fe1f

def z483 : W := mkw 0x148048faf0805653 0x0520123ebc201594 0xe08002fe70003672 0x382000bf9c000d9c

def z484 : W := mkw 0x94006062518956d4 0x25001818946255b5 0xffeae2e67b99ffff 0xfffab8b99ee67fff

def z485 : W := mkw 0x20bfdbdfec142803 0xc82ff6f7fb050a00 0xffbffffffc1e3803 0x7fefffffff078e00

def z486 : W := mkw 0x100c00b002c01500 0x0403002c00b00540 0xeeee02fe0bf837f3 0xfbbb80bf82fe0dfc

def z487 : W := mkw 0xe87fb7050f7fa828 0xfa1fedc143dfea0a 0x156efe060bf9f030 0x855bbf8182fe7c0c

def z488 : W := mkw 0xc04cb400036b8000 0x30132d0000dae000 0xbf6efe060bf9f073 0xefdbbf8182fe7c1c

def z489 : W := mkw 0x100c00b002c01500 0x0403002c00b00540 0x44dc01f807e00f80 0x9137007e01f803e0

def z490 : W := mkw 0x303f03b00ed43d00 0xcc0fc0ec03b50f40 0xeeff03fe0ffe3ff3 0xfbbfc0ff83ff8ffc

def z491 : W := mkw 0x303f03b50ec03d00 0x8c0fc0ed43b00f40 0x66fe03fe0fe03f82 0xd9bf80ff83f80fe0

def z492 : W := mkw 0x1000002002c01500 0x0400000800b00540 0x0040000003e00780 0x8010000000f801e0

def z493 : W := mkw 0xc04fb400036b8000 0x3013ed0000dae000 0x1d4ffc0003e1c000 0x8753ff0000f87000

def z494 : W := mkw 0xc04cb400036b8000 0x30132d0000dae000 0x1f6efc0003e1c000 0x87dbbf0000f87000

def z495 : W := mkw 0xc0c06fdfef7f8003 0xf0301bf7fbdfe000 0xe0c003ffffffc001 0xf83000fffffff000

def z496 : W := mkw 0xc843b405013f8028 0x7210ed01404fe00a 0x9903fc07801fc07d 0x2640ff01e007f01f

def z497 : W := mkw 0xc4006c4af12bc2d6 0x31001b12bc4af0b5 0x1100fc007001c000 0x04403f001c007000

def z498 : W := mkw 0x103c00b00ec01500 0x840f002c03b00540 0x66fc02f80fe03782 0xd9bf00be03f80de0

def z499 : W := mkw 0x00bcdbdae0000003 0x002f36f6b8000000 0x55acfef870000000 0x156b3fbe1c000000

def z500 : W := mkw 0x0883d84fe014002b 0x4220f613f805000a 0xffabfee7f81e307f 0x7feaffb9fe078c1f

def z501 : W := mkw 0xc07fb7050f7f8000 0xf01fedc143dfe000 0x1f7ffe060fffc001 0xc7dfff8183fff000

def z502 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x66ec02f80be03782 0xd9bb00be02f80de0

def z503 : W := mkw 0xe8ffffdfef7fa82b 0xfa3ffff7fbdfea0a 0xfffffffffffff87f 0xfffffffffffffe1f

def z504 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xff9dfdf9f0000000 0x3fe77f7e7c000000

def z505 : W := mkw 0x283f03050e542828 0xca0fc0c143950a0a 0xee7f031f8ffe3fff 0xfb9fc0c7e3ff8fff

def z506 : W := mkw 0xc04cb400036b8000 0x30132d0000dae000 0x154cfc0007e7c001 0xc5533f0001f9f000

def z507 : W := mkw 0xa83323050d1d2828 0xea0cc8c143474a0a 0xbf7be3078f9ff87f 0xefdef8c1e3e7fe1f

def z508 : W := mkw 0x1400486af08056d6 0x0500121abc2015b5 0x408000f870000780 0x1020003e1c0001e0

def z509 : W := mkw 0x003f930500000000 0x000fe4c140000000 0xbf3fff0780000000 0x2fcfffc1e0000000

def z510 : W := mkw 0x403f94000e628000 0x900fe5000398a000 0x1f7ffc000fe7c001 0xc7dfff0003f9f000

def z511 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0xfefc03f87fe03f82 0xffbf00fe1ff80fe0

def z512 : W := mkw 0x8400604251094250 0x2100181094425094 0x9902e0067019c071 0x2640b8019c06701c

def z513 : W := mkw 0x383303b50c943d28 0xce0cc0ed43250f4a 0xeab303ff8c1e3fff 0x7aacc0ffe3078fff

def z514 : W := mkw 0xc04fb400037f8000 0x7013ed0000dfe000 0x154efc0003f9c000 0x8553bf0000fe7000

def z515 : W := mkw 0x008cd8dae0000003 0x00233636b8000000 0x55aefefe70000000 0x156bbfbf9c000000

def z516 : W := mkw 0x0000484ae0000002 0x00001212b8000000 0xffbffffffc1e387f 0x7fefffffff078e1f

def z517 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xbbbbffe7f0000000 0x2eeefff9fc000000

def z518 : W := mkw 0x00000808b00042c6 0x000002022c0010b1 0xe0000119f0000fce 0x380000467c0003f3

def z519 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x66fd03f98fe63f8e 0xd9bf40fe63f98fe3

def z520 : W := mkw 0x00bfdbdfe0000087 0x002ff6f7f8000021 0xffbffffff000098c 0x3feffffffc000263

def z521 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0xeefd03f98fe03f82 0xfbbf40fe63f80fe0

def z522 : W := mkw 0x0033030500000000 0x000cc0c140000000 0xaa3303078406084f 0x6a8cc0c1e1018213

def z523 : W := mkw 0xc043b4000f7f8000 0xf010ed0003dfe000 0x1f6bfc000fffc001 0xc7daff0003fff000

def z524 : W := mkw 0x008fd8dfe0000003 0x0023f637f8000000 0xff9ffdfff0000000 0x3fe7ff7ffc000000

def z525 : W := mkw 0x8400604251094250 0x2100181094425094 0xbb22e2067819f073 0x6ec8b8819e067c1c

def z526 : W := mkw 0x00b3dbdfe0000003 0x002cf6f7f8000000 0xfbb3fffff0000000 0x3eecfffffc000000

def z527 : W := mkw 0x383f03b50ed43d28 0xce0fc0ed43b50f4a 0x44ee02fe0bf837b0 0x913b80bf82fe0dec

def z528 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0x003303078c1e383c 0x000cc0c1e3078e0f

def z529 : W := mkw 0x280000000c142828 0xca00000003050a0a 0xaa3303078c1e387f 0x6a8cc0c1e3078e1f

def z530 : W := mkw 0x283f93050c142828 0xca0fe4c143050a0a 0xaa371f078c1e387f 0x6a8dc7c1e3078e1f

def z531 : W := mkw 0x20bfdbdfec002803 0x882ff6f7fb000a00 0xffbffffffc183873 0x7fefffffff060e1c

def z532 : W := mkw 0xd440242011bfd650 0x75100908046ff594 0x004000000b9ff673 0xc010000002e7fd9c

def z533 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xf59dfffff0000000 0x3d677ffffc000000

def z534 : W := mkw 0x680004001c36eaec 0xda000100070dbabb 0x000000000c7fffff 0xc0000000031fffff

def z535 : W := mkw 0x20bfdbdfee402803 0x882ff6f7fb900a00 0xffffffffffe03802 0xfffffffffff80e00

def z536 : W := mkw 0x2803030500142828 0x4a00c0c140050a0a 0xaa230307881e387f 0x6a88c0c1e2078e1f

def z537 : W := mkw 0x28bfdbdfe000282b 0x0a2ff6f7f8000a0a 0xffbffffff0003030 0x3feffffffc000c0c

def z538 : W := mkw 0x28bfdbdfe000282b 0x0a2ff6f7f8000a0a 0xffbffffff406387f 0x7feffffffd018e1f

def z539 : W := mkw 0x0803000500140028 0x4200c0014005000a 0xa8030207801e307f 0x2a00c081e0078c1f

def z540 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0x11aafee670000000 0x046abfb99c000000

def z541 : W := mkw 0x0000404240000000 0x0000101090000000 0xffaae2e678183073 0x7feab8b99e060c1c

def z542 : W := mkw 0x00000808a0000002 0x0000020228000000 0x54041c1870000000 0x150107061c000000

def z543 : W := mkw 0x100c00b002c01500 0x0403002c00b00540 0x66dc01f803e00780 0x99b7007e00f801e0

def z544 : W := mkw 0x94806bfff1895653 0x25201afffc625594 0xffeae3fffb99f673 0xfffab8fffee67d9c

def z545 : W := mkw 0xd47324201fffd650 0xf51cc90807fff594 0xaa7302060ffff673 0xea9cc08183fffd9c

def z546 : W := mkw 0x003c03900e400000 0x800f00e403900000 0x66fc03f80fe00f82 0xd9bf00fe03f803e0

def z547 : W := mkw 0xe07fb7000f7fa800 0xf81fedc003dfea00 0xbf7fff018ffff84f 0xefdfffc063fffe13

def z548 : W := mkw 0x008fdbdfe0000003 0x0023f6f7f8000000 0xfd8ffffff0000000 0x3f63fffffc000000

def z549 : W := mkw 0x20bfdbdfee402903 0x882ff6f7fb900a40 0xffffffffffe00980 0xfffffffffff80260

def z550 : W := mkw 0x2800030500002828 0x0a0000c140000a0a 0x0000020600003030 0x0000008180000c0c

def z551 : W := mkw 0x607f97900e76a900 0xd81fe5e4039daa40 0x00151d1804660980 0x0005474601198260

def z552 : W := mkw 0x383f03b50ec03d28 0x8e0fc0ed43b00f4a 0xeeff03ff8fe03ffe 0xfbbfc0ffe3f80fff

def z553 : W := mkw 0xbc3f63f75fdd7f78 0xef0fd8fdd7f75fde 0xffffe3ffffffffff 0xfffff8ffffffffff

def z554 : W := mkw 0x00bfd8dae0000003 0x002ff636b8000000 0xffbffefe70000000 0x3fefffbf9c000000

def z555 : W := mkw 0x20bfdbdfe0002903 0x082ff6f7f8000a40 0xffbffffff0000980 0x3feffffffc000260

def z556 : W := mkw 0x280000050c142828 0xca00000143050a0a 0x800000078c1e387f 0x60000001e3078e1f

def z557 : W := mkw 0x0000404240000000 0x0000101090000000 0x5588e0e070000000 0x156238381c000000

def z558 : W := mkw 0x948cf8faf1895653 0x25233e3ebc625594 0xffeefefe7b99f673 0xfffbbfbf9ee67d9c

def z559 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x1f7ffc000b9fc001 0x07dfff0002e7f000

def z560 : W := mkw 0xc4006c4af12bc2d6 0x31001b12bc4af0b5 0xff17fd1ff47fcfff 0xffc5ff47fd1ff3ff

def z561 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffbffffff001c001 0xffeffffffc007000

def z562 : W := mkw 0xc0402400036b8000 0x3010090000dae000 0x0040000003e1c000 0x8010000000f87000

def z563 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xfe330307fc1e387f 0x7f8cc0c1ff078e1f

def z564 : W := mkw 0x203003000c002800 0x880c00c003000a00 0x663403180c603f82 0xd98d00c603180fe0

def z565 : W := mkw 0xd4006c6af1abd6d6 0x35001b1abc6af5b5 0xffddfdf9f7e7cfcf 0xfff77f7e7df9f3f3

def z566 : W := mkw 0xe87fb7050f7fa828 0xfa1fedc143dfea0a 0x3f7fff060ffff833 0xcfdfffc183fffe0c

def z567 : W := mkw 0xe07fb4000f7fa900 0xf81fed0003dfea40 0x1f7ffc000fffc981 0xc7dfff0003fff260

def z568 : W := mkw 0x000cd04240000000 0x0003341090000000 0xffaefee670000000 0x3febbfb99c000000

def z569 : W := mkw 0x687f97050e76a828 0xda1fe5c1439daa0a 0xaa371f078c7e387f 0x6a8dc7c1e31f8e1f

def z570 : W := mkw 0xe87fb7050f7fa828 0xfa1fedc143dfea0a 0x9f7ffe078ffff07d 0xe7dfff81e3fffc1f

def z571 : W := mkw 0x28bfdbdfec14282b 0xca2ff6f7fb050a0a 0x559dfdf9f406080c 0x15677f7e7d018203

def z572 : W := mkw 0x383c03b50ec03d28 0x8e0f00ed43b00f4a 0x66fc03fe0fe03fb2 0xd9bf00ff83f80fec

def z573 : W := mkw 0x303c93b00ec03d00 0x8c0f24ec03b00f40 0x77fcfff80fe03f82 0xddff3ffe03f80fe0

def z574 : W := mkw 0x203c03900e402900 0x880f00e403900a40 0x223403180c603982 0x488d00c603180e60

def z575 : W := mkw 0x8400604251094250 0x2100181094425094 0x1100e0007001c000 0x044038001c007000

def z576 : W := mkw 0x283f03050c142828 0xca0fc0c143050a0a 0xae3f03078c1e387f 0x6b8fc0c1e3078e1f

def z577 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0xbf7ffe060fffc001 0xefdfff8183fff000

def z578 : W := mkw 0x000c009000000000 0x0003002400000000 0x448c00f800000000 0x1123003e00000000

def z579 : W := mkw 0x30bcdbfaeec03d03 0x8c2f36febbb00f40 0x77fcfff87fe03f82 0xddff3ffe1ff80fe0

def z580 : W := mkw 0x100000b002c01500 0x0400002c00b00540 0x40c000f803e00780 0x9030003e00f801e0

def z581 : W := mkw 0x40bfd7d75022c2c5 0x102ff5f5d408b0b1 0x01aae2e60467cfcf 0xc06ab8b98119f3f3

def z582 : W := mkw 0x4000040000228000 0x100001000008a000 0x14041c000061c000 0x8501070000187000

def z583 : W := mkw 0xe87fb7050f7fa828 0xfa1fedc143dfea0a 0x1f7ffe060ffff87f 0xc7dfff8183fffe1f

def z584 : W := mkw 0xc04cb4000f7f8000 0xf0132d0003dfe000 0x154cfc0007e7c000 0x85533f0001f9f000

def z585 : W := mkw 0xd400242011abd6d4 0x35000908046af5b5 0x004000000b9ff67f 0xc010000002e7fd9f

def z586 : W := mkw 0x68000c08bc36eaee 0xda0003022f0dbabb 0xfe151d19fc7fffff 0xff8547467f1fffff

def z587 : W := mkw 0xc07fb7900f7f8000 0xf01fede403dfe000 0x7ffffff80fffcf83 0xdffffffe03fff3e0

def z588 : W := mkw 0xc07cb4000f6b8000 0xb01f2d0003dae000 0x155cfc0007e1c000 0x85573f0001f87000

def z589 : W := mkw 0x00bfdbdae0000003 0x002ff6f6b8000000 0x7fbffff870000000 0x1feffffe1c000000

def z590 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xaa33030788183030 0x2a8cc0c1e2060c0c

def z591 : W := mkw 0x100c00b002c01500 0x0403002c00b00540 0x00c800e003800000 0x0032003800e00000

def z592 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x005401180fe03f82 0xc015004603f80fe0

def z593 : W := mkw 0x28334b4fec14282a 0xca0cd2d3fb050a0a 0xffbffffffc1e387f 0x7fefffffff078e1f

def z594 : W := mkw 0x303f03b00ec03d00 0x8c0fc0ec03b00f40 0x6eff03f80fe03f82 0xdbbfc0fe03f80fe0

def z595 : W := mkw 0x30bf93b50ec03d01 0x8c2fe4ed43b00f40 0x66fc03f80fe03f82 0xd9bf00fe03f80fe0

def z596 : W := mkw 0x68330f0dac36a8ae 0xda0cc3c36b0daa2b 0xaa371f1f8c7e39ff 0x6a8dc7c7e31f8e7f

def z597 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0x882302078c1e387f 0x6208c081e3078e1f

def z598 : W := mkw 0x803fb0000f490000 0xa00fec0003d24000 0x1f7ffc000ff9c001 0xc7dfff0003fe7000

def z599 : W := mkw 0x00bfdbdfec000003 0x802ff6f7fb000000 0xffbffffffc000000 0x7fefffffff000000

def z600 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xbf3be3078c1e387f 0x6fcef8c1e3078e1f

def z601 : W := mkw 0x383f03b50ed43d28 0xce0fc0ed43b50f4a 0x00ea02e60b983030 0x003a80b982e60c0c

def z602 : W := mkw 0xe87fb7050f7fa828 0xfa1fedc143dfea0a 0xbf7fff078fffc80d 0xefdfffc1e3fff203

def z603 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x44cc00f803e00780 0x9133003e00f801e0

def z604 : W := mkw 0x103c00b00ec01500 0x840f002c03b00540 0x44dc00f807e00780 0x9137003e01f801e0

def z605 : W := mkw 0x28330b0dbc146aee 0xca0cc2c36f051abb 0xea33031ffc1e3fff 0x7a8cc0c7ff078fff

def z606 : W := mkw 0xc03c24000f6b8000 0xb00f090003dae000 0x1f7ffc000fffc001 0xc7dfff0003fff000

def z607 : W := mkw 0xc07fb7050f7f8000 0xf01fedc143dfe000 0xbf7fff078ffff073 0xefdfffc1e3fffc1c

def z608 : W := mkw 0xd4006c6af1abd6d6 0x35001b1abc6af5b5 0xffebfee7fb9ff67f 0xfffaffb9fee7fd9f

def z609 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xfffffffffb800000 0xfffffffffee00000

def z610 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0xbf7fff078ffff87f 0xefdfffc1e3fffe1f

def z611 : W := mkw 0x34804bfff0807f53 0x0d2012fffc201fd4 0xe08003fff0003ff2 0x382000fffc000ffc

def z612 : W := mkw 0x9400606251895650 0x2500181894625594 0xffc8e0e07381c643 0xfff238381ce07190

def z613 : W := mkw 0xc04cb400036b8000 0x30132d0000dae000 0xbf5dfd0187e7c84f 0xefd77f4061f9f213

def z614 : W := mkw 0xe87fb7050f7fa828 0xfa1fedc143dfea0a 0x155dfd0187e7c80c 0x85577f4061f9f203

def z615 : W := mkw 0x703c0fb8bee2ffc6 0x9c0f03ee2fb8bff1 0x98e91ee1fb87f04d 0x263a47b87ee1fc13

def z616 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0xeeff03ff8ffe3fff 0xfbbfc0ffe3ff8fff

def z617 : W := mkw 0x2800030500142828 0x4a0000c140050a0a 0xa0000307801e387f 0x280000c1e0078e1f

def z618 : W := mkw 0x383f03b50ed43d28 0xce0fc0ed43b50f4a 0x66fd03f98ffe3fff 0xd9bf40fe63ff8fff

def z619 : W := mkw 0x300c00b00ec03d00 0x8c03002c03b00f40 0x66ec02f80fe03f82 0xd9bb00be03f80fe0

def z620 : W := mkw 0x383f03b50ed43d28 0xce0fc0ed43b50f4a 0xaafb03e78f9e387f 0x6abec0f9e3e78e1f

def z621 : W := mkw 0x083300050c140028 0xc20cc0014305000a 0xaa3302078c1e307f 0x6a8cc081e3078c1f

def z622 : W := mkw 0xd04cb4b003eb9500 0x34132d2c00fae540 0x55ccfcf803e1c780 0x95733f3e00f871e0

def z623 : W := mkw 0x0000484ae0000002 0x00001212b8000000 0x558cfcf870000000 0x15633f3e1c000000

def z624 : W := mkw 0x400004001022c2c4 0x100001000408b0b1 0x000000000061c780 0x80000000001871e0

def z625 : W := mkw 0xc073b4000d3f8000 0xf01ced00034fe000 0x1b33fc000c1fc001 0x46ccff000307f000

def z626 : W := mkw 0x00bfdbdfee400003 0x802ff6f7fb900000 0xfffffffffb800000 0x3ffffffffee00000

def z627 : W := mkw 0x00000808a0000002 0x0000020228000000 0xfe151d19f406084f 0x7f8547467d018213

def z628 : W := mkw 0x003f939000000000 0x000fe4e400000000 0x7fbffff800000000 0x1feffffe00000000

def z629 : W := mkw 0x008cdbdfe0000003 0x002336f7f8000000 0x558cfefe70000000 0x15633fbf9c000000

def z630 : W := mkw 0x008c9898a0000003 0x0023262628000000 0x00041c1800000000 0x0001070600000000

def z631 : W := mkw 0xa83fb3050d1d2828 0xea0fecc143474a0a 0xbf7fff078f9ff87f 0xefdfffc1e3e7fe1f

def z632 : W := mkw 0x383303250c943c28 0xce0cc0c943250f0a 0xeefb03e78f9e3e7f 0xfbbec0f9e3e78f9f

def z633 : W := mkw 0x0003900000000000 0x0000e40000000000 0x1903fc0000000000 0x0640ff0000000000

def z634 : W := mkw 0x683307050c36a828 0xda0cc1c1430daa0a 0xbe371f078c7ff87f 0xef8dc7c1e31ffe1f

def z635 : W := mkw 0xe87fb4000f7fa828 0xfa1fed0003dfea0a 0xbf7ffe060ffff87f 0xefdfff8183fffe1f

def z636 : W := mkw 0x300003b000803d00 0x0c0000ec00200f40 0x669403f804603f82 0xd9a500fe01180fe0

def z637 : W := mkw 0x383f03b50ed43d28 0xce0fc0ed43b50f4a 0x66ff03ff8ffe3fbe 0xd9bfc0ffe3ff8fef

def z638 : W := mkw 0xe87fb7050f7fa828 0xfa1fedc143dfea0a 0xbf7ffe060ffff073 0xefdfff8183fffc1c

def z639 : W := mkw 0x383f03b50ed43d28 0xce0fc0ed43b50f4a 0xeeff03ff8ff83fb2 0xfbbfc0ffe3fe0fec

def z640 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0xff7ffd198fffcfcf 0xffdfff4663fff3f3

def z641 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0xfe151d19f467cf8c 0xbf8547467d19f3e3

def z642 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000020600003072 0x2800008180000c1c

def z643 : W := mkw 0xc04cb400036b8000 0x30132d0000dae000 0x176cfc000be1c000 0xc5db3f0002f87000

def z644 : W := mkw 0xc07fb7000f7f8000 0xf01fedc003dfe000 0x3f7fff000fffc001 0xcfdfffc003fff000

def z645 : W := mkw 0x280000000c142828 0xca00000003050a0a 0x0000000008183030 0x0000000002060c0c

def z646 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xaa230207881e307f 0x6a88c081e2078c1f

def z647 : W := mkw 0x003fd0424c140000 0xc00ff41093050000 0xffbffee67c1e3073 0x7fefffb99f078c1c

def z648 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xae7b03078f9e387f 0xeb9ec0c1e3e78e1f

def z649 : W := mkw 0x408cdcdaf022c2c7 0x10233736bc08b0b1 0x558cfcf87061c780 0x95633f3e1c1871e0

def z650 : W := mkw 0x008cdbdfe0000003 0x002336f7f8000000 0xffaefffff0000000 0x3febbffffc000000

def z651 : W := mkw 0x40000c08a0228086 0x100003022808a021 0xaa151d19846609cf 0x6a85474661198273

def z652 : W := mkw 0xc07fb4000f6b8000 0xb01fed0003dae000 0x1f7ffc000fe1c000 0xc7dfff0003f87000

def z653 : W := mkw 0xe07fb7000f7fa800 0xf81fedc003dfea00 0x1f7ffe000ffff001 0xc7dfff8003fffc00

def z654 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffbffffffc1e387f 0x7fefffffff078e1f

def z655 : W := mkw 0x68bfdfdffc36eaef 0xda2ff7f7ff0dbabb 0xffbffffffc7fffff 0xffefffffff1fffff

def z656 : W := mkw 0x400004001022c2c4 0x100001000408b0b1 0x661401180467cfcf 0xd98500460119f3f3

def z657 : W := mkw 0x1400486af08056d6 0x0500121abc2015b5 0xe08002fe700037f2 0x382000bf9c000dfc

def z658 : W := mkw 0xc040b400036b8000 0x30102d0000dae000 0x1140fc0003e1c000 0x84503f0000f87000

def z659 : W := mkw 0x28bfdbdfec14282b 0xca2ff6f7fb050a0a 0xffbffffff0000000 0x3feffffffc000000

def z660 : W := mkw 0x008cd8dae0000003 0x00233636b8000000 0x558cfcf870600780 0x95633f3e1c1801e0

def z661 : W := mkw 0x28bfdbdfec14282b 0xca2ff6f7fb050a0a 0xffbffffff406084f 0x7feffffffd018213

def z662 : W := mkw 0x500c0cb8b2e2d7c6 0x1403032e2cb8b5f1 0x54cc1cf873e1c780 0x9533073e1cf871e0

def z663 : W := mkw 0x0833030500140028 0x420cc0c14005000a 0xaa330307801e007d 0x2a8cc0c1e007801f

def z664 : W := mkw 0x280003050c142828 0xca0000c143050a0a 0xaa1103078c1e387f 0x6a8440c1e3078e1f

def z665 : W := mkw 0xd44064625fffd650 0xf510191897fff594 0xffeae2e67ffff673 0xfffab8b99ffffd9c

def z666 : W := mkw 0x283f93950c142828 0xca0fe4e543050a0a 0xffbfffff8c1e387f 0x7fefffffe3078e1f

def z667 : W := mkw 0xe07fb7000f7fa800 0xf81fedc003dfea00 0x1f7ffd000fffc801 0xc7dfff4003fff200

def z668 : W := mkw 0x083300050c140028 0xc20cc0014305000a 0x8a3300078c1e007d 0x628cc001e307801f

def z669 : W := mkw 0xc043b400013f8000 0x7010ed00004fe000 0x1d4bfc00039fc001 0x8752ff0000e7f000

def z670 : W := mkw 0x28bfdbdfec14282b 0xca2ff6f7fb050a0a 0xffbffffff81e307d 0x3feffffffe078c1f

def z671 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x177efc000ff9c000 0xc5dfbf0003fe7000

def z672 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0xfe151f1ff467ffff 0xff8547c7fd19ffff

def z673 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x44dc01f80fe03f82 0xd137007e03f80fe0

def z674 : W := mkw 0x003fd84ae0000002 0x000ff612b8000000 0xffbffffff0000000 0x3feffffffc000000

def z675 : W := mkw 0x00bfdbdfee400003 0x802ff6f7fb900000 0xffffffffffe00f82 0xfffffffffff803e0

def z676 : W := mkw 0xc043b400013f8000 0x7010ed00004fe000 0x1943fc000b9fc001 0xc650ff0002e7f000

def z677 : W := mkw 0x300000b00ec03d00 0x8c00002c03b00f40 0x40c000f80fe03f82 0xd030003e03f80fe0

def z678 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xf997fffff0000000 0x3e65fffffc000000

def z679 : W := mkw 0xc040b400012b8000 0x30102d00004ae000 0x1f6afc000b99c001 0xc7dabf0002e67000

def z680 : W := mkw 0x28bfdbdfee54292b 0xca2ff6f7fb950a4a 0xffbffffffc7e39ff 0x7fefffffff1f8e7f

def z681 : W := mkw 0xc843b405013f8028 0x7210ed01404fe00a 0xbf6bfe078b9ff07f 0xefdaff81e2e7fc1f

def z682 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x7f7ffc000fffc603 0xdfdfff0003fff180

def z683 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffbffffff0000f82 0x3feffffffc0003e0

def z684 : W := mkw 0x148048faf0805653 0x0520123ebc201594 0x408000f870000600 0x1020003e1c000180

def z685 : W := mkw 0x0083d8dfe0000003 0x0020f637f8000000 0xd983fcfff0000000 0x3660ff3ffc000000

def z686 : W := mkw 0x00bfd8daec140003 0xc02ff636bb050000 0x5fbffcf87c1e0001 0x57efff3e1f078000

def z687 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x7ffffee00fffc001 0xdfffffb803fff000

def z688 : W := mkw 0xe87fb7050f7fa828 0xfa1fedc143dfea0a 0xbf7fff078ffff031 0xefdfffc1e3fffc0c

def z689 : W := mkw 0x00bfdbdfe2400103 0x002ff6f7f8900040 0xffbffffff0600180 0x3feffffffc180060

def z690 : W := mkw 0x9400606251895650 0x2500181894625594 0xfffbe3e7fb99f673 0xfffef8f9fee67d9c

def z691 : W := mkw 0x303003200ec03d00 0x8c0c00c803b00f40 0x227003000fe03f82 0xc89c00c003f80fe0

def z692 : W := mkw 0xe87fb4050f7fa828 0xfa1fed0143dfea0a 0x9f7ffc078ffff87f 0xe7dfff01e3fffe1f

def z693 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x9f7ffc060fffc071 0xe7dfff0183fff01c

def z694 : W := mkw 0xc04cb400036b8000 0x30132d0000dae000 0x775cfd1807e1cf82 0xddd73f4601f873e0

def z695 : W := mkw 0x28b3db4fec14282b 0xca2cf6d3fb050a0a 0xbb33ff07fc1e387f 0x6eccffc1ff078e1f

def z696 : W := mkw 0x103f90b002c01500 0x040fe42c00b00540 0x5ffffcf803e00780 0x97ffff3e00f801e0

def z697 : W := mkw 0x283393050c142828 0xca0ce4c143050a0a 0xbb33ff078c1e387f 0x6eccffc1e3078e1f

def z698 : W := mkw 0x28bfdbdfec14282b 0xca2ff6f7fb050a0a 0xffbffffffc1e080d 0x7fefffffff078203

def z699 : W := mkw 0x003f90000e400000 0x800fe40003900000 0x1f7ffc000fe00000 0xc7dfff0003f80000

def z700 : W := mkw 0xc87fb7050f7f8028 0xf21fedc143dfe00a 0xbf7fff078fffc07d 0xefdfffc1e3fff01f

def z701 : W := mkw 0x2800030500002828 0x0a0000c140000a0a 0xaa2203078818387f 0x6a8880c1e2060e1f

def z702 : W := mkw 0x08bfdbdfe014002b 0x422ff6f7f805000a 0xffbffffff41e087f 0x7feffffffd07821f

def z703 : W := mkw 0x0000000000000000 0x0000000000000000 0x4404001800600780 0x91010006001801e0

def z704 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x157ffc000fffc000 0x855fff0003fff000

def z705 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0x98151d19f467cfcf 0xe60547467d19f3f3

def z706 : W := mkw 0x9400606251895650 0x2500181894625594 0xffeae2e67b99f071 0x3ffab8b99ee67c1c

def z707 : W := mkw 0x103c00b002c01500 0x040f002c00b00540 0x46fc00f803e00780 0x91bf003e00f801e0

def z708 : W := mkw 0x283003050c142828 0xca0c00c143050a0a 0xa23003078c1e387f 0x688c00c1e3078e1f

def z709 : W := mkw 0x9400606251895650 0x2500181894625594 0xffeae2e67ff9fff3 0xfffab8b99ffe7ffc

def z710 : W := mkw 0x9400606251895650 0x2500181894625594 0xfffffee67b99f673 0xffffffb99ee67d9c

def z711 : W := mkw 0x1400002010805650 0x0500000804201594 0x0000000000003672 0x0000000000000d9c

def z712 : W := mkw 0x9400606251895650 0x2500181894625594 0xfffae3e67f99fe73 0xfffeb8f99fe67f9c

def z713 : W := mkw 0x9400606251895650 0x2500181894625594 0x9feae2e67b99f071 0xe7fab8b99ee67c1c

def z714 : W := mkw 0xc03324000d3f8000 0xf00cc900034fe000 0x1f7ffc000fffc001 0xc7dfff0003fff000

def z715 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x66fc03f80fe63fcf 0xd9bf00fe03f98ff3

def z716 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffbffffff000084e 0x3feffffffc000213

def z717 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0xeefc03f80fe03fc3 0xfbbf00fe03f80ff0

def z718 : W := mkw 0xc04cb400036b8000 0x30132d0000dae000 0x1f7ffc000fffc001 0xc7dfff0003fff000

def z719 : W := mkw 0x383c03b00ed43d28 0xce0f00ec03b50f4a 0xeefd03f98ffe3fff 0xfbbf40fe63ff8fff

def z720 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x64ec03f80be03f82 0x993b00fe02f80fe0

def z721 : W := mkw 0x303c03b002c03d00 0x0c0f00ec00b00f40 0x66fc03f803e03f82 0x99bf00fe00f80fe0

def z722 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x1f7ffe060ffff031 0xc7dfff8183fffc0c

def z723 : W := mkw 0x383c03b50ec03d28 0x8e0f00ed43b00f4a 0x66fc03f98fe03f8e 0xd9bf00fe63f80fe3

def z724 : W := mkw 0xe87fb7050f7fa828 0xfa1fedc143dfea0a 0x9f7ffd078fffc87d 0xe7dfff41e3fff21f

def z725 : W := mkw 0x307f93b00ed43d00 0xcc1fe4ec03b50f40 0x66fc03f80fe03f82 0xd9bf00fe03f80fe0

def z726 : W := mkw 0x100c00b002c01500 0x0403002c00b00540 0x46dc00f807e00780 0xd1b7003e01f801e0

def z727 : W := mkw 0xe07cb7900f6ba900 0xb81f2de403daea40 0x155cfd1807e1c980 0x85573f4601f87260

def z728 : W := mkw 0x103c00200ec01400 0x840f000803b00500 0x66fc03f80fe03f82 0xd9bf00fe03f80fe0

def z729 : W := mkw 0xe873b7050f7fa828 0xfa1cedc143dfea0a 0xbb73ff078ffff87f 0xeedcffc1e3fffe1f

def z730 : W := mkw 0xe87fb7950f7fa928 0xfa1fede543dfea4a 0x1f7ffd198fffc98d 0xc7dfff4663fff263

def z731 : W := mkw 0x008fd8dfe0000003 0x0023f637f8000000 0x558efcfe70000000 0x1563bf3f9c000000

def z732 : W := mkw 0x28bfdbdfec14282b 0xca2ff6f7fb050a0a 0x55aefefe78183030 0x156bbfbf9e060c0c

def z733 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x154cfc0003e1c000 0x85533f0000f87000

def z734 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0xeefe03fe0fe03f82 0xfbbf80ff83f80fe0

def z735 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xee37031f8c1e387f 0x7b8dc0c7e3078e1f

def z736 : W := mkw 0x383f03b50ed43d28 0xce0fc0ed43b50f4a 0x66fc03f80fe03f82 0xd9bf00fe03f80fe0

def z737 : W := mkw 0x400004001022c2c4 0x100001000408b0b1 0xaa1101018467cfcf 0xea8440406119f3f3

def z738 : W := mkw 0x8000200001090000 0x2000080000424000 0x1548e0000381c000 0x8552380000e07000

def z739 : W := mkw 0xd44cf46253ebd650 0x35133d1894faf594 0xffeefee67bf9f673 0xfffbbfb99efe7d9c

def z740 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xae3703078c7e387f 0xeb8dc0c1e31f8e1f

def z741 : W := mkw 0xd400242011abd650 0x35000908046af594 0x004000000ffff673 0xc010000003fffd9c

def z742 : W := mkw 0x00bfd8dae0000003 0x002ff636b8000000 0x55aefcf870000000 0x156bbf3e1c000000

def z743 : W := mkw 0x14804bfff0805653 0x052012fffc201594 0xe08003fff0003672 0x382000fffc000d9c

def z744 : W := mkw 0x800cb00001090000 0x20032c0000424000 0x154cfc000381c000 0x85533f0000e07000

def z745 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0x0a3302060c1e3031 0x428cc08183078c0c

def z746 : W := mkw 0xbc3363675d9d7e78 0xef0cd8d9d7675f9e 0x55d9e1e1f787ce0c 0x957678787de1f383

def z747 : W := mkw 0xc04cb400036b8000 0x30132d0000dae000 0x1f4cfc0003e1c001 0xc7d33f0000f87000

def z748 : W := mkw 0x008cd0d240000001 0x0023343490000000 0x0188e0e000000000 0x0062383800000000

def z749 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x5f7ffc180fffc781 0xd7dfff0603fff1e0

def z750 : W := mkw 0x08bfdbdfec14002b 0xc22ff6f7fb05000a 0xffbffffffc1e007d 0x7fefffffff07801f

def z751 : W := mkw 0xc07fb7900f7f8000 0xf01fede403dfe000 0x1ffffee00fffc001 0xc7ffffb803fff000

def z752 : W := mkw 0xc0002c08b12bc2c6 0x30000b022c4af0b1 0xff7ffd19ffffcfcf 0xffdfff467ffff3f3

def z753 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0x881301078c1e387f 0x6204c041e3078e1f

def z754 : W := mkw 0x9400606251895650 0x2500181894625594 0xbbeae2e67b99f073 0x6efab8b99ee67c1c

def z755 : W := mkw 0x283f93050e542828 0xca0fe4c143950a0a 0xbf7fff078ffe387f 0xefdfffc1e3ff8e1f

def z756 : W := mkw 0x383c03b50ed43d28 0xce0f00ed43b50f4a 0xe6fc03ff8ffe3fff 0xf9bf00ffe3ff8fff

def z757 : W := mkw 0xe87fb7050f7fa828 0xfa1fedc143dfea0a 0x1f7fff078ffff83d 0xc7dfffc1e3fffe0f

def z758 : W := mkw 0x0033030500000000 0x000cc0c140000000 0xaa33030788183073 0x6a8cc0c1e2060c1c

def z759 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x3f7ffe000ffff003 0xcfdfff8003fffc00

def z760 : W := mkw 0x0083d84fe0000003 0x0020f613f8000000 0xf983fee7f0000000 0x3e60ffb9fc000000

def z761 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0xfe351f19fc67ffcf 0xff8d47c67f19fff3

def z762 : W := mkw 0x4000040000228000 0x100001000008a000 0xbe151d018467c84f 0xef8547406119f213

def z763 : W := mkw 0x00bcdbdfe0000003 0x002f36f7f8000000 0xf7bcfffff0000000 0x3def3ffffc000000

def z764 : W := mkw 0x008fd8dfe0000003 0x0023f637f8000000 0x558dfcf9f0000000 0x15637f3e7c000000

def z765 : W := mkw 0xc04cb400036b8000 0x30132d0000dae000 0x1d4dfc0003e7c001 0x87537f0000f9f000

def z766 : W := mkw 0x287f93050e542828 0xca1fe4c143950a0a 0xaa3303078c1e387f 0x6a8cc0c1e3078e1f

def z767 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xeebb03e78c1e387f 0x7baec0f9e3078e1f

def z768 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x3f7ffd000fffc803 0xcfdfff4003fff200

def z769 : W := mkw 0x008cd8dae0000003 0x00233636b8000000 0x779cfdf870000000 0x1de73f7e1c000000

def z770 : W := mkw 0xc07fb4050f7f8000 0xf01fed0143dfe000 0x9f7ffc078fffc001 0xe7dfff01e3fff000

def z771 : W := mkw 0x0083d84fe0000003 0x0020f613f8000000 0xdd8bfce7f0000000 0x3762ff39fc000000

def z772 : W := mkw 0x0000484ae0000002 0x00001212b8000000 0xffabfee7f0000000 0x3feaffb9fc000000

def z773 : W := mkw 0x8000604241090000 0x2000181090424000 0xffeae2e67b99c001 0xfffab8b99ee67000

def z774 : W := mkw 0x800cb00001090000 0x20032c0000424000 0x1f6efc000b99c001 0xc7dbbf0002e67000

def z775 : W := mkw 0xe07fb4000f7fa800 0xf81fed0003dfea00 0x1f7ffc000ffff803 0xc7dfff0003fffe00

def z776 : W := mkw 0x383f03b00ed43d28 0xce0fc0ec03b50f4a 0x6eff03f80ffe3fff 0xdbbfc0fe03ff8fff

def z777 : W := mkw 0xe87fb7050f7fa828 0xfa1fedc143dfea0a 0x996bfe078b9ff07d 0x265aff81e2e7fc1f

def z778 : W := mkw 0xc483fc4ff12bc2d7 0x3120ff13fc4af0b5 0x9903fc07f01fc07d 0x2640ff01fc07f01f

def z779 : W := mkw 0x0803000500140028 0x4200c0014005000a 0xaa130107841e087f 0x6a84c041e107821f

def z780 : W := mkw 0x20bfdbdfec002803 0x882ff6f7fb000a00 0xffbffffffc06384f 0x7fefffffff018e13

def z781 : W := mkw 0x303f03b00ed43d00 0xcc0fc0ec03b50f40 0xeeff03f98ffe3fcf 0xfbbfc0fe63ff8ff3

def z782 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0xfebd1ff9f467cfcf 0xffaf47fe7d19f3f3

def z783 : W := mkw 0xc04cb400037f8000 0x70132d0000dfe000 0x154cfc0003ffc001 0x85533f0000fff000

def z784 : W := mkw 0x0083d84fe0000003 0x0020f613f8000000 0xffbffffff0000000 0x3feffffffc000000

def z785 : W := mkw 0x28bfdbdfec14282b 0xca2ff6f7fb050a0a 0xffbffffff8183073 0x7feffffffe060c1c

def z786 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x66fc03f807e00f80 0x99bf00fe01f803e0

def z787 : W := mkw 0x28bfdbdfec14282b 0xca2ff6f7fb050a0a 0xffbffffffc183832 0x7fefffffff060e0c

def z788 : W := mkw 0xe87fb7050f7fa828 0xfa1fedc143dfea0a 0x3f7fff018ffff80f 0xcfdfffc063fffe03

def z789 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x1f7ffc000fffc84f 0xc7dfff0003fff213

def z790 : W := mkw 0x94bffbfff1895653 0x252ffefffc625594 0xfffffffff381c600 0xbffffffffce07180

def z791 : W := mkw 0x303c03b00ed43d00 0xcc0f00ec03b50f40 0x66fc03f80ffe3f83 0xd9bf00fe03ff8fe0

def z792 : W := mkw 0x008fd8dfe0000003 0x0023f637f8000000 0xffaffefff0000000 0x3febffbffc000000

def z793 : W := mkw 0x00bc4bdfe0000003 0x002f12f7f8000000 0xe6bc03fff0000000 0x39af00fffc000000

def z794 : W := mkw 0x003300000c140000 0xc00cc00003050000 0xaa3303078c1e387f 0x6a8cc0c1e3078e1f

def z795 : W := mkw 0x00000808a0000002 0x0000020228000000 0xfe151d19f4600f82 0xff8547467d1803e0

def z796 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x1d5ffc0007ffc001 0x8757ff0001fff000

def z797 : W := mkw 0x203c03900e402900 0x880f00e403900a40 0x067c01180fe00980 0xc19f004603f80260

def z798 : W := mkw 0xc4006c4af12bc2d6 0x31001b12bc4af0b5 0xbb33ff07fc1ff87f 0x6eccffc1ff07fe1f

def z799 : W := mkw 0x803fb00001090000 0x200fec0000424000 0x1f7ffc000381c000 0x87dfff0000e07000

def z800 : W := mkw 0x0000484ae0000002 0x00001212b8000000 0xffaefefe70000000 0x3febbfbf9c000000

def z801 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x1957fc000fffc001 0xc655ff0003fff000

def z802 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x017ffc000fffc001 0xc05fff0003fff000

def z803 : W := mkw 0x9400606241891410 0x2500181890624504 0xabeae2e60b983073 0x6afab8b982e60c1c

def z804 : W := mkw 0xc87fb4050f7f8028 0xf21fed0143dfe00a 0xbf7ffe078ffff07f 0xefdfff81e3fffc1f

def z805 : W := mkw 0x404c940002628000 0x101325000098a000 0x00041c0000600000 0x0001070000180000

def z806 : W := mkw 0xc043b400013f8000 0x7010ed00004fe000 0x1f7ffc000fffc001 0xc7dfff0003fff000

def z807 : W := mkw 0xe07fb7900f7fa900 0xf81fede403dfea40 0x7f7ffd180fffcf83 0xdfdfff4603fff3e0

def z808 : W := mkw 0x103c00b00ec01500 0x840f002c03b00540 0x44ec00f80be00780 0x913b003e02f801e0

def z809 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xa01103078c1e387f 0x680440c1e3078e1f

def z810 : W := mkw 0xc073b4000d3f8000 0xf01ced00034fe000 0x1f7bfc000f9fc001 0xc7deff0003e7f000

def z811 : W := mkw 0x383f03b50ed43d28 0xce0fc0ed43b50f4a 0x66fe03fe0ffe3fff 0xd9bf80ff83ff8fff

def z812 : W := mkw 0xc043b400037f8000 0x7010ed0000dfe000 0x1943fc0003ffc001 0x8650ff0000fff000

def z813 : W := mkw 0xe07fb7900f7fa900 0xf81fede403dfea40 0x7ffffff80fffc981 0xdffffffe03fff260

def z814 : W := mkw 0x3c3343675c947e78 0xcf0cd0d9d7251f9e 0xeab303e7fc1e3e7f 0x7aacc0f9ff078f9f

def z815 : W := mkw 0x383f03b50ed43d28 0xce0fc0ed43b50f4a 0xeefe03fe0ff83ff3 0xfbbf80ff83fe0ffc

def z816 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xdd9ffdfff0000000 0x3767ff7ffc000000

def z817 : W := mkw 0x003c4bdae0000002 0x000f12f6b8000000 0xffbffffff0000000 0x3feffffffc000000

def z818 : W := mkw 0x383c03b00ed43d28 0xce0f00ec03b50f4a 0x66fc03f80fe63f8e 0xd9bf00fe03f98fe3

def z819 : W := mkw 0x08bfdbdfe014002b 0x422ff6f7f805000a 0xffbffffff0180030 0x3feffffffc06000c

def z820 : W := mkw 0xc87fb4050f7f8028 0xf21fed0143dfe00a 0xbf7ffd078fffc87f 0xefdfff41e3fff21f

def z821 : W := mkw 0x00bfd84fe0000003 0x002ff613f8000000 0xffbffee7f0000000 0x3fefffb9fc000000

def z822 : W := mkw 0x283303950c142928 0xca0cc0e543050a4a 0xaa33031f8c1e39ff 0x6a8cc0c7e3078e7f

def z823 : W := mkw 0xe87fb7000f7fa828 0xfa1fedc003dfea0a 0x3f7fff000ffff87f 0xcfdfffc003fffe1f

def z824 : W := mkw 0xc04cb400036b8000 0x30132d0000dae000 0x175cfc0007e1c000 0xc5d73f0001f87000

def z825 : W := mkw 0x100c00b002c01500 0x0403002c00b00540 0x44cc00f80be03782 0xd133003e02f80de0

def z826 : W := mkw 0x100c00b00ec01500 0x8403002c03b00540 0x44cc00f80fe00780 0xd133003e03f801e0

def z827 : W := mkw 0x40004c4af022c2c6 0x10001312bc08b0b1 0xffbffffff467cfcf 0xffeffffffd19f3f3

def z828 : W := mkw 0x783f0fbdbef6ffee 0xde0fc3ef6fbdbffb 0xfeff1fffffffffff 0xffbfc7ffffffffff

def z829 : W := mkw 0x003fd34740000000 0x000ff4d1d0000000 0xffbfffe7f0000000 0x3feffff9fc000000

def z830 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x7efc03f80fe1ff83 0xdfbf00fe03f87fe0

def z831 : W := mkw 0x1000002000801400 0x0400000800200500 0x66ec02f80be03782 0xd9bb00be02f80de0

def z832 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x1f7ffd180fffc981 0xc7dfff4603fff260

def z833 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xf9abfffff0000000 0x3e6afffffc000000

def z834 : W := mkw 0x0000000000000000 0x0000000000000000 0x0022020608183030 0x0008808182060c0c

def z835 : W := mkw 0x28b3db4fec14282b 0xca2cf6d3fb050a0a 0xffbbffe7fc1e387f 0x7feefff9ff078e1f

def z836 : W := mkw 0x4000040000228000 0x100001000008a000 0x7e151d180467cf83 0xdf8547460119f3e0

def z837 : W := mkw 0x0003d04240000000 0x0000f41090000000 0xffabfee670000000 0x3feaffb99c000000

def z838 : W := mkw 0xc07fb7050f7f8000 0xf01fedc143dfe000 0x1f7ffd018fffc001 0xc7dfff4063fff000

def z839 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xa01103078406387e 0x280440c1e1018e1f

def z840 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x1f7ffd018fffc80d 0xc7dfff4063fff203

def z841 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffbffffff8183030 0x3feffffffe060c0c

def z842 : W := mkw 0x0000404240000000 0x0000101090000000 0xffbffee670000000 0x3fefffb99c000000

def z843 : W := mkw 0x20bf9b9dae402903 0x882fe6e76b900a40 0x00151d1984600980 0x0005474661180260

def z844 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0xbf7ffc000fffc043 0xefdfff0003fff010

def z845 : W := mkw 0x28bfdbdfec14282b 0xca2ff6f7fb050a0a 0xffbffffff818387e 0x3feffffffe060e1f

def z846 : W := mkw 0xc04fb400037f8000 0x7013ed0000dfe000 0x1f6ffc000bffc001 0xc7dbff0002fff000

def z847 : W := mkw 0x940c60f253c95750 0x2503183c94f255d4 0x55cce0f873e1c780 0x9573383e1cf871e0

def z848 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x6efe03f80ff83f83 0xdbbf80fe03fe0fe0

def z849 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x1f6bfc000b9fc001 0xc7daff0002e7f000

def z850 : W := mkw 0x283f93050c142828 0xca0fe4c143050a0a 0xab3be3078c1e387f 0x6acef8c1e3078e1f

def z851 : W := mkw 0xc07fb400036b8000 0x301fed0000dae000 0x1f7ffc000bf9c001 0xc7dfff0002fe7000

def z852 : W := mkw 0x00bfdbdfec140003 0xc02ff6f7fb050000 0xffbffffffc1e3073 0x7fefffffff078c1c

def z853 : W := mkw 0xe84cb4000f7fa828 0xfa132d0003dfea0a 0x154cfc000ffff87f 0xc5533f0003fffe1f

def z854 : W := mkw 0x30804bfff0807fc7 0x0c2012fffc201ff1 0xe08003fff0003fce 0x382000fffc000ff3

def z855 : W := mkw 0xe87fb7050f7fa828 0xfa1fedc143dfea0a 0x1f7ffc000fffc001 0xc7dfff0003fff000

def z856 : W := mkw 0x20bfdbdfe0002803 0x082ff6f7f8000a00 0xffbffffff0003802 0x3feffffffc000e00

def z857 : W := mkw 0xa87fb3050f5d2828 0xea1fecc143d74a0a 0xab7be3078f9e387f 0x6adef8c1e3e78e1f

def z858 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffaefefe70000000 0x3febbfbf9c000000

def z859 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xf5aefffff0000000 0x3d6bbffffc000000

def z860 : W := mkw 0x100c00b002c01500 0x0403002c00b00540 0x64cc01f803e00f82 0x9933007e00f803e0

def z861 : W := mkw 0xe87327050f7fa828 0xfa1cc9c143dfea0a 0xaa7303078ffff87f 0xea9cc0c1e3fffe1f

def z862 : W := mkw 0x008cd8dae0000003 0x00233636b8000000 0xff8cfcf870000000 0x3fe33f3e1c000000

def z863 : W := mkw 0x303003200c803c00 0x8c0c00c803200f00 0x66fc03f80fe03f82 0xd9bf00fe03f80fe0

def z864 : W := mkw 0xe87fb7050f7fa828 0xfa1fedc143dfea0a 0xbf7ffd018fffc84f 0xefdfff4063fff213

def z865 : W := mkw 0x283f03950e542928 0xca0fc0e543950a4a 0xae7f031f8ffe39ff 0xeb9fc0c7e3ff8e7f

def z866 : W := mkw 0x108cd8fae2c01503 0x0423363eb8b00540 0x55ccfcf873e00780 0x95733f3e1cf801e0

def z867 : W := mkw 0x203003000c002800 0x880c00c003000a00 0xaa3103018c06384f 0x6a8c40c063018e13

def z868 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x6efd03f80fe63f83 0xdbbf40fe03f98fe0

def z869 : W := mkw 0xc0002400012b8000 0x30000900004ae000 0x1f5dfc0007e7c001 0xc7d77f0001f9f000

def z870 : W := mkw 0x003fd3d240000000 0x000ff4f490000000 0xffbffffe70000000 0x3fefffff9c000000

def z871 : W := mkw 0x003300000c140000 0xc00cc00003050000 0xaa3302060c1e3073 0x6a8cc08183078c1c

def z872 : W := mkw 0x300c03b002c03d00 0x0c0300ec00b00f40 0x66dc03f807e03f82 0xd9b700fe01f80fe0

def z873 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xaa1101018406084f 0x6a84404061018213

def z874 : W := mkw 0x303003b00c803d00 0x8c0c00ec03200f40 0x62b003f80c003f82 0x58ac00fe03000fe0

def z875 : W := mkw 0x008cd8dae0000003 0x00233636b8000000 0xf58cfdf9f0000000 0x3d633f7e7c000000

def z876 : W := mkw 0x008cd8dae2400103 0x00233636b8900040 0x558cfcf870600180 0x15633f3e1c180060

def z877 : W := mkw 0x003fd04240000000 0x000ff41090000000 0x5fbffce070000000 0x17efff381c000000

def z878 : W := mkw 0xc043b400013f8000 0x7010ed00004fe000 0x196bfc000b9fc001 0x065aff0002e7f000

def z879 : W := mkw 0xe07fb7900f7fa900 0xf81fede403dfea40 0x3f7fff180ffff983 0xcfdfffc603fffe60

def z880 : W := mkw 0xc04cbc08b36bc2c6 0x30132f022cdaf0b1 0x554cfc1873e1c780 0x95533f061cf871e0

def z881 : W := mkw 0x300c03b002c03d00 0x0c0300ec00b00f40 0x44cc02f803e03780 0x913300be00f80de0

def z882 : W := mkw 0x0083dbdfe0000003 0x0020f6f7f8000000 0xff97fffff0000000 0x3fe5fffffc000000

def z883 : W := mkw 0x008cd8dae0000003 0x00233636b8000000 0xf58cfefe70000000 0x3d633fbf9c000000

def z884 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0xbf7ffd018fffc001 0xefdfff4063fff000

def z885 : W := mkw 0x100c03b002c01500 0x040300ec00b00540 0x64cc03f803e00780 0x993300fe00f801e0

def z886 : W := mkw 0x280300050c142828 0xca00c00143050a0a 0xaa2302078c1e387f 0x6a88c081e3078e1f

def z887 : W := mkw 0x280300050c142828 0xca00c00143050a0a 0x88030007881e307d 0x2200c001e2078c1f

def z888 : W := mkw 0xc04cb490036b8100 0x30132d2400dae040 0x154cfc1803e1c180 0x85533f0600f87060

def z889 : W := mkw 0x303f03b50ec03d00 0x8c0fc0ed43b00f40 0xeeff03ff8fe63fcf 0xfbbfc0ffe3f98ff3

def z890 : W := mkw 0x300c00b00ec03d00 0x8c03002c03b00f40 0x44cc00f80be03780 0x9133003e02f80de0

def z891 : W := mkw 0x20bfdbdfec002803 0x882ff6f7fb000a00 0xffbffffff8003000 0x3feffffffe000c00

def z892 : W := mkw 0x28bfdbdfec14282b 0xca2ff6f7fb050a0a 0xffbffffffc1e3031 0x7fefffffff078c0c

def z893 : W := mkw 0x9400606241891410 0x2500181890624504 0x01c8e0e003800000 0x0072383800e00000

def z894 : W := mkw 0xc07cb4000f6b8000 0xb01f2d0003dae000 0x1f7dfc000fe7c001 0xc7df7f0003f9f000

def z895 : W := mkw 0xf44024201fffff50 0xfd10090807ffffd4 0x004000000ffffff3 0xc010000003fffffc

def z896 : W := mkw 0xc443fc4af13fc2d6 0x7110ff12bc4ff0b5 0x9903fc07f01fc07d 0x2640ff01fc07f01f

def z897 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x1f7ffc000bf9c000 0x87dfff0002fe7000

def z898 : W := mkw 0x9400606251895650 0x2500181894625594 0xe1eae2e67b99f673 0xf87ab8b99ee67d9c

def z899 : W := mkw 0xd400646251abd650 0x35001918946af594 0xfffffee67ffff673 0xffffffb99ffffd9c

def z900 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x9f7ffc018fffc04d 0xe7dfff0063fff013

def z901 : W := mkw 0x9400606251895650 0x2500181894625594 0x55eae2e67b99f673 0xd57ab8b99ee67d9c

def z902 : W := mkw 0x303f93b00ec03d00 0x8c0fe4ec03b00f40 0x66fd1ff80fe03f82 0xd9bf47fe03f80fe0

def z903 : W := mkw 0x383303b50ed43d28 0xce0cc0ed43b50f4a 0xeaf303ff8ffe3fff 0xfabcc0ffe3ff8fff

def z904 : W := mkw 0x100c00b002c01500 0x0403002c00b00540 0x46ec00f80be00780 0xd1bb003e02f801e0

def z905 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0x223103018c06380e 0x488c40c063018e03

def z906 : W := mkw 0xd47fb4201fffd650 0xf51fed0807fff594 0x1f7ffc000ffff673 0xc7dfff0003fffd9c

def z907 : W := mkw 0xc87fb4050f7f8028 0xf21fed0143dfe00a 0x1f7ffc060fffc031 0xc7dfff0183fff00c

def z908 : W := mkw 0x00ffdbdfee540003 0xc03ff6f7fb950000 0xffbffffff0000000 0x3feffffffc000000

def z909 : W := mkw 0xc07cb4000f7f8000 0xf01f2d0003dfe000 0x177cfc000fffc001 0xc5df3f0003fff000

def z910 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x155dfc000fffc001 0xc5577f0003fff000

def z911 : W := mkw 0x008cdbdae0000003 0x002336f6b8000000 0x758cfff870000000 0x1d633ffe1c000000

def z912 : W := mkw 0x00804bdfe0000003 0x002012f7f8000000 0xffbffffff0000000 0x3feffffffc000000

def z913 : W := mkw 0x383c03b50ec03d28 0x8e0f00ed43b00f4a 0xeefe03ff8ff83fff 0xfbbf80ffe3fe0fff

def z914 : W := mkw 0x0803000500140028 0x4200c0014005000a 0x88030007881e307f 0x6200c001e2078c1f

def z915 : W := mkw 0xe87fb7950f7fa928 0xfa1fede543dfea4a 0xbf7fff1f8ffff9ff 0xefdfffc7e3fffe7f

def z916 : W := mkw 0x28bfdbdfec14282b 0xca2ff6f7fb050a0a 0xffbffffff406387e 0x3feffffffd018e1f

def z917 : W := mkw 0x0000000000000000 0x0000000000000000 0x2220020008003002 0x4888008002000c00

def z918 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0x77bdfff9f0000000 0x1def7ffe7c000000

def z919 : W := mkw 0x0000000010004240 0x0000000004001090 0xfe2202067819f673 0xff8880819e067d9c

def z920 : W := mkw 0xec336f4ffd3feafe 0xfb0cdbd3ff4ffabf 0xbb33ff07fc1ff87f 0x6eccffc1ff07fe1f

def z921 : W := mkw 0x9400606251895650 0x2500181894625594 0xddeae2e67b99f671 0xb77ab8b99ee67d9c

def z922 : W := mkw 0x00bfdbdfe0140003 0x402ff6f7f8050000 0xffbffffff01e0001 0x3feffffffc078000

def z923 : W := mkw 0x20bfdbdfec002803 0x882ff6f7fb000a00 0xffbffffffc603f82 0xffefffffff180fe0

def z924 : W := mkw 0x103c00b00ec01500 0x840f002c03b00540 0x66fc01f80fe00f82 0xd9bf007e03f803e0

def z925 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xbe3303078c1ff87f 0xef8cc0c1e307fe1f

def z926 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000008183073 0x4000000002060c1c

def z927 : W := mkw 0xe87fb4000f7fa828 0xfa1fed0003dfea0a 0xbf7ffd018ffff87f 0xefdfff4063fffe1f

def z928 : W := mkw 0x9400606251895650 0x2500181894625594 0xfffbe2e67f9ff673 0xfffef8b99fe7fd9c

def z929 : W := mkw 0xf40024201febffd4 0xbd00090807fafff5 0x004000000fffffff 0xc010000003ffffff

def z930 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffbffffff4060001 0x7feffffffd018000

def z931 : W := mkw 0x803fb0000d1d0000 0xe00fec0003474000 0x1f7ffc000f9fc001 0xc7dfff0003e7f000

def z932 : W := mkw 0x008cd8dae0000003 0x00233636b8000000 0x779cfdf874600f82 0xdde73f7e1d1803e0

def z933 : W := mkw 0x0003000000140000 0x4000c00000050000 0x08030000001e0001 0x0200c00000078000

def z934 : W := mkw 0x383c03b50ec03d28 0x8e0f00ed43b00f4a 0xeefd03ff8fe63fff 0xfbbf40ffe3f98fff

def z935 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffabfee7f0000000 0x3feaffb9fc000000

def z936 : W := mkw 0x28bfdbdfec14282b 0xca2ff6f7fb050a0a 0x99abfee7f81e307d 0x266affb9fe078c1f

def z937 : W := mkw 0xc043b4000f7f8000 0xf010ed0003dfe000 0x1f57fc000fffc001 0xc7d5ff0003fff000

def z938 : W := mkw 0x008cd8dae0000003 0x00233636b8000000 0xdd8dfcf9f0000000 0x37637f3e7c000000

def z939 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xa03303078c1e387e 0x280cc0c1e3078e1f

def z940 : W := mkw 0x54004c6af0a2d6d6 0x1500131abc28b5b5 0xfe951ffff467ffff 0xffa547fffd19ffff

def z941 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xaa3303078406080c 0x2a8cc0c1e1018203

def z942 : W := mkw 0x103c03b002c01500 0x040f00ec00b00540 0x66fc03f80be03782 0xd9bf00fe02f80de0

def z943 : W := mkw 0x103c03b00ec01500 0x840f00ec03b00540 0x66fc03f80fe00780 0xd9bf00fe03f801e0

def z944 : W := mkw 0xe87fb4000f7fa828 0xfa1fed0003dfea0a 0x1f7ffc000fffc80d 0xc7dfff0003fff203

def z945 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xaa37031f8c7e39ff 0x6a8dc0c7e31f8e7f

def z946 : W := mkw 0xd4006c6af1abd6d6 0x35001b1abc6af5b5 0x55c8fce07381c600 0x95723f381ce07180

def z947 : W := mkw 0x383f03b50ed43d28 0xce0fc0ed43b50f4a 0x6eff03fe0ffe3fb3 0xdbbfc0ff83ff8fec

def z948 : W := mkw 0x303f03b50ed43d00 0xcc0fc0ed43b50f40 0xeeff03ff8ffe3f83 0xfbbfc0ffe3ff8fe0

def z949 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffbffffff0180071 0x3feffffffc06001c

def z950 : W := mkw 0x0000000010004240 0x0000000004001090 0xfe110101f407ce4f 0xff8440407d01f393

def z951 : W := mkw 0x303f93b00ed43d00 0xcc0fe4ec03b50f40 0x7ffffff80ffe3f83 0xdffffffe03ff8fe0

def z952 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x1f7ffc000ffff073 0xc7dfff0003fffc1c

def z953 : W := mkw 0x8000200001090000 0x2000080000424000 0x1f7ffc000b99c001 0xc7dfff0002e67000

def z954 : W := mkw 0x100c90b002c01500 0x0403242c00b00540 0x55ccfcf803e00780 0x95733f3e00f801e0

def z955 : W := mkw 0xc07cb400036b8000 0x301f2d0000dae000 0x177cfc0003e1c000 0x85df3f0000f87000

def z956 : W := mkw 0x9400606251895650 0x2500181894625594 0xf9eae2e67b99f673 0x3e7ab8b99ee67d9c

def z957 : W := mkw 0x0000030500000000 0x000000c140000000 0xa000030780000000 0x280000c1e0000000

def z958 : W := mkw 0x008fd8dfe0000003 0x0023f637f8000000 0x998bfce7f0000000 0x2662ff39fc000000

def z959 : W := mkw 0xc04cb400036b8000 0x30132d0000dae000 0x155dfc0007e7c000 0x85577f0001f9f000

def z960 : W := mkw 0x283f03950c142828 0xca0fc0e543050a0a 0xaa37031f8c1e387f 0x6a8dc0c7e3078e1f

def z961 : W := mkw 0xc04cb4000f7f8000 0xf0132d0003dfe000 0x1f5dfc000fffc001 0xc7d77f0003fff000

def z962 : W := mkw 0x283f03950e542928 0xca0fc0e543950a4a 0xeebf03ff8c7e39ff 0x7bafc0ffe31f8e7f

def z963 : W := mkw 0xd44cf46253ebd650 0x35133d1894faf594 0x55ccfce073e1c600 0x95733f381cf87180

def z964 : W := mkw 0x383f03b50ed43d28 0xce0fc0ed43b50f4a 0xeefd03f98fe63fcf 0xfbbf40fe63f98ff3

def z965 : W := mkw 0x300c03b00ec03d00 0x8c0300ec03b00f40 0x64cc03f80fe03f82 0xd93300fe03f80fe0

def z966 : W := mkw 0x0000039000000000 0x000000e400000000 0x608003f800000000 0x182000fe00000000

def z967 : W := mkw 0x803fb30501090000 0x200fecc140424000 0xbf7fff078b99f073 0xefdfffc1e2e67c1c

def z968 : W := mkw 0x68000f0db022eaee 0x1a0003c36c08babb 0xfe151f1ff467ffff 0xff8547c7fd19ffff

def z969 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xe1bffffff0000000 0x386ffffffc000000

def z970 : W := mkw 0x203c03900e402900 0x880f00e403900a40 0x66bc03f804600980 0x19af00fe01180260

def z971 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0x883303078c1e387d 0x220cc0c1e3078e1f

def z972 : W := mkw 0xc04cb400036b8000 0x30132d0000dae000 0x156efc000bf9c000 0x855bbf0002fe7000

def z973 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0x54151d19f467cfcf 0xd50547467d19f3f3

def z974 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffbffffff8180001 0x7feffffffe060000

def z975 : W := mkw 0xc0c3fc4ff13fc2c7 0x7030ff13fc4ff0b1 0x9903fc07f01fc04d 0x2640ff01fc07f013

def z976 : W := mkw 0xc0002400012b8000 0x30000900004ae000 0x1f6efc000bf9c001 0xc7dbbf0002fe7000

def z977 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x197ffc000fffc001 0x065fff0003fff000

def z978 : W := mkw 0x300c00b00ec03d00 0x8c03002c03b00f40 0x66dc01f80fe03f82 0xd9b7007e03f80fe0

def z979 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0xff3ffd19f467cfcf 0xffcfff467d19f3f3

def z980 : W := mkw 0x1400486af08056d6 0x0500121abc2015b5 0xe08001f9f0000fce 0x3820007e7c0003f3

def z981 : W := mkw 0xe87fb7050f7fa828 0xfa1fedc143dfea0a 0x1f7ffd018ffff87f 0xc7dfff4063fffe1f

def z982 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0x77befffe70000000 0x1defbfff9c000000

def z983 : W := mkw 0x283303050e542928 0xca0cc0c143950a4a 0xaa3303078c7e39ff 0x6a8cc0c1e31f8e7f

def z984 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x60e803f80fe03f82 0xd83a00fe03f80fe0

def z985 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0x5e151d19f467cf8d 0xd78547467d19f3e3

def z986 : W := mkw 0x28bfdbdfec00282b 0x8a2ff6f7fb000a0a 0xffbffffffc00387e 0x7fefffffff000e1f

def z987 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0xe6fc03fe0fe03ff2 0xf9bf00ff83f80ffc

def z988 : W := mkw 0xc04cb4000f6b8000 0xb0132d0003dae000 0x154cfc000fe1c000 0xc5533f0003f87000

def z989 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xee3303078c1e3e7f 0xfb8cc0c1e3078f9f

def z990 : W := mkw 0x00bfd3d740000001 0x002ff4f5d0000000 0xffbffee670000000 0x3fefffb99c000000

def z991 : W := mkw 0x9483f86ff1895653 0x2520fe1bfc625594 0xffebfee7fb99f673 0xfffaffb9fee67d9c

def z992 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x7efd1ff80fe03f82 0xdfbf47fe03f80fe0

def z993 : W := mkw 0x383c03b00ed43d28 0xce0f00ec03b50f4a 0xeefe03fe0ffe3fff 0xfbbf80ff83ff8fff

def z994 : W := mkw 0xc87fb4050f7f8028 0xf21fed0143dfe00a 0x1f7ffc018fffc00d 0xc7dfff0063fff003

def z995 : W := mkw 0x9400606251895650 0x2500181894625594 0xffeae3e7fb99fe7f 0xfffab8f9fee67f9f

def z996 : W := mkw 0xe07fb7900f7fa800 0xf81fede403dfea00 0x7ffffff80ffff803 0xdffffffe03fffe00

def z997 : W := mkw 0x283f03950c142828 0xca0fc0e543050a0a 0xaabb03e78c1e387f 0x6aaec0f9e3078e1f

def z998 : W := mkw 0xc04024000f7f8000 0xf010090003dfe000 0x1f7ffc000fffc001 0xc7dfff0003fff000

def z999 : W := mkw 0x1400486af08056d6 0x0500121abc2015b5 0xeab303fffc1e3fff 0x7aacc0ffff078fff

def z1000 : W := mkw 0x283f03950e542928 0xca0fc0e543950a4a 0xaa3303078c1e387f 0x6a8cc0c1e3078e1f

def z1001 : W := mkw 0x280300050c142828 0xca00c00143050a0a 0xaa1301078c1e387f 0x6a84c041e3078e1f

def z1002 : W := mkw 0x003c03900e400000 0x800f00e403900000 0x66fc03f80fe00000 0xd9bf00fe03f80000

def z1003 : W := mkw 0x20bfdbdfec002803 0x882ff6f7fb000a00 0xffbffffff4000800 0x3feffffffd000200

def z1004 : W := mkw 0xc043b4000f7f8000 0xf010ed0003dfe000 0x1943fc000b9fc001 0x0650ff0002e7f000

def z1005 : W := mkw 0x100c00b002c01500 0x0403002c00b00540 0x44cc00f807e00f82 0xd133003e01f803e0

def z1006 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0xfe371f1ff467cfcf 0xff8dc7c7fd19f3f3

def z1007 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xaa330307881e307d 0x2a8cc0c1e2078c1f

def z1008 : W := mkw 0x000000000e400000 0x8000000003900000 0x004000000fe00000 0xc010000003f80000

def z1009 : W := mkw 0x103c03b002c01500 0x040f00ec00b00540 0x44ec02f803e00780 0x913b00be00f801e0

def z1010 : W := mkw 0x0083dbdfe0000003 0x0020f6f7f8000000 0xffabfffff0000000 0x3feafffffc000000

def z1011 : W := mkw 0x008cd8dae0000003 0x00233636b8000000 0xdd8efcfe70000000 0x3763bf3f9c000000

def z1012 : W := mkw 0xc04cb490036b8000 0x30132d2400dae000 0x55ccfcf803e1c000 0x95733f3e00f87000

def z1013 : W := mkw 0x1000002000801400 0x0400000800200500 0x44cc00f803e00780 0x9133003e00f801e0

def z1014 : W := mkw 0x0033030500000000 0x000cc0c140000000 0xaa3303078c1e387f 0x6a8cc0c1e3078e1f

def z1015 : W := mkw 0xc04fb400037f8000 0x7013ed0000dfe000 0x1f5ffc0007ffc001 0xc7d7ff0001fff000

def z1016 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0xf8151d19f467cfcf 0x3e0547467d19f3f3

def z1017 : W := mkw 0xe87fb4000f7fa828 0xfa1fed0003dfea0a 0x1f7ffc000ffff031 0xc7dfff0003fffc0c

def z1018 : W := mkw 0xd44cfc6af3ebd6d6 0x35133f1abcfaf5b5 0x55ccfcf873e1c780 0x95733f3e1cf871e0

def z1019 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0xfe151d19fc7fffff 0xff8547467f1fffff

def z1020 : W := mkw 0xe87fb7950f7fa828 0xfa1fede543dfea0a 0xffffffff8ffff87f 0xffffffffe3fffe1f

def z1021 : W := mkw 0x00bfd8dfe0000003 0x002ff637f8000000 0xdfbffcfff0000000 0x37efff3ffc000000

def z1022 : W := mkw 0x08bfdbdfe014002b 0x422ff6f7f805000a 0xffbffffff006000c 0x3feffffffc018003

def z1023 : W := mkw 0xc87fb4000f7f8028 0xf21fed0003dfe00a 0x1f7ffc000fffc07d 0xc7dfff0003fff01f

def z1024 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x7ffee3f80fe03f82 0xdfffb8fe03f80fe0

def z1025 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0xdc151d19f467cfcd 0xb70547467d19f3f3

def z1026 : W := mkw 0xd400242011abd6d4 0x35000908046af5b5 0xaa7303078fffffff 0xea9cc0c1e3ffffff

def z1027 : W := mkw 0x9400606251895650 0x2500181894625594 0xfffee3fe7b99f673 0xffffb8ff9ee67d9c

def z1028 : W := mkw 0x303f93b00ec03d00 0x8c0fe4ec03b00f40 0x67fee3f80fe03f82 0xd9ffb8fe03f80fe0

def z1029 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xddaffefff0000000 0x376bffbffc000000

def z1030 : W := mkw 0xe87fb7050f7fa828 0xfa1fedc143dfea0a 0xbb7bff078f9ff87f 0x6edeffc1e3e7fe1f

def z1031 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa230207881e307f 0x6a88c081e2078c1f

def z1032 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x60fc03f80fe03f82 0x183f00fe03f80fe0

def z1033 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x46fc02f80fe03780 0xd1bf00be03f80de0

def z1034 : W := mkw 0x0833030500140028 0x420cc0c14005000a 0xaa330307881e307f 0x6a8cc0c1e2078c1f

def z1035 : W := mkw 0x100c00b002c01500 0x0403002c00b00540 0x66cc00f803e00782 0xd9b3003e00f801e0

def z1036 : W := mkw 0x14b34bfff0805653 0x052cd2fffc201594 0xeab303fff8183673 0x7aacc0fffe060d9c

def z1037 : W := mkw 0x100c00b002c01500 0x0403002c00b00540 0x44ec02f80be03780 0x913b00be02f80de0

def z1038 : W := mkw 0xc07fb400036b8000 0x301fed0000dae000 0x1f7ffc0007e7c001 0xc7dfff0001f9f000

def z1039 : W := mkw 0xe07fb7900f7fa900 0xf81fede403dfea40 0x1f7ffc000fffc001 0xc7dfff0003fff000

def z1040 : W := mkw 0x008cd8dae0000003 0x00233636b8000000 0xffaefefe78183073 0x7febbfbf9e060c1c

def z1041 : W := mkw 0x2800000000002828 0x0a00000000000a0a 0x000000000000387e 0x0000000000000e1f

def z1042 : W := mkw 0x28bfdbdfec14282b 0xca2ff6f7fb050a0a 0xffbffffffc1e383c 0x3fefffffff078e0f

def z1043 : W := mkw 0x40000c08b022c2c6 0x100003022c08b0b1 0xe0151d19f467cfcf 0xf80547467d19f3f3

def z1044 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0x5fbffdf9f0000000 0x17efff7e7c000000

def z1045 : W := mkw 0x08bfdbdfe000002b 0x022ff6f7f800000a 0xffbffffff000007c 0x3feffffffc00001f

def z1046 : W := mkw 0x283fd3474c142828 0xca0ff4d1d3050a0a 0xffbfffe7fc1e387f 0x7feffff9ff078e1f

def z1047 : W := mkw 0xc04cb400036b8000 0x30132d0000dae000 0x1d4efc0003f9c001 0x8753bf0000fe7000

def z1048 : W := mkw 0x28bfdbdfec14282b 0xca2ff6f7fb050a0a 0xbbbbffe7fc1e387f 0x6eeefff9ff078e1f

def z1049 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0x5fbffefe70000000 0x17efffbf9c000000

def z1050 : W := mkw 0xac3363475d1d6a78 0xeb0cd8d1d7475a9e 0xbb33e307fc1ff87f 0x6eccf8c1ff07fe1f

def z1051 : W := mkw 0x2803000500142828 0x4a00c00140050a0a 0x88030007801e387f 0x2200c001e0078e1f

def z1052 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0x55bffffff0000000 0x156ffffffc000000

def z1053 : W := mkw 0x003c039000000000 0x000f00e400000000 0x66bc03f804600f82 0xd9af00fe011803e0

def z1054 : W := mkw 0x283f03050e542828 0xca0fc0c143950a0a 0xaa7b03078f9e387f 0x6a9ec0c1e3e78e1f

def z1055 : W := mkw 0x008cd8dae0000003 0x00233636b8000000 0x5f9dfcf870000000 0x17e77f3e1c000000

def z1056 : W := mkw 0x9400606251895650 0x2500181894625594 0x99eae2e67b99f673 0xe67ab8b99ee67d9c

def z1057 : W := mkw 0x300000200ec03d00 0x8c00000803b00f40 0x66fc03f80fe03f82 0xd9bf00fe03f80fe0

def z1058 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x66dc01f807e00f82 0xd9b7007e01f803e0

def z1059 : W := mkw 0x008cd8dae0000003 0x00233636b8000000 0x559dfdf9f0000000 0x15677f7e7c000000

def z1060 : W := mkw 0xc07fb400013f8000 0x701fed00004fe000 0x1f7ffc000b9fc001 0xc7dfff0002e7f000

def z1061 : W := mkw 0x008cd8dae0000003 0x00233636b8000000 0xff9dfdf9f406084f 0x7fe77f7e7d018213

def z1062 : W := mkw 0x200000000c002800 0x8800000003000a00 0x000000000c003802 0x4000000003000e00

def z1063 : W := mkw 0xc04fb400037f8000 0x7013ed0000dfe000 0x194bfc00039fc001 0x0652ff0000e7f000

def z1064 : W := mkw 0xc04fb400037f8000 0x7013ed0000dfe000 0x154dfc0003e7c000 0x85537f0000f9f000

def z1065 : W := mkw 0x20bcdbdaee402903 0x882f36f6bb900a40 0x559cfdf874600980 0x15673f7e1d180260

def z1066 : W := mkw 0x300003b00ec03d00 0x8c0000ec03b00f40 0x66e803f80fe03f82 0xd9ba00fe03f80fe0

def z1067 : W := mkw 0x383f03b50ed43d28 0xce0fc0ed43b50f4a 0xeeff03ff8fe63f8e 0xfbbfc0ffe3f98fe3

def z1068 : W := mkw 0x203003000c002800 0x880c00c003000a00 0x0020020008003000 0x0008008002000c00

def z1069 : W := mkw 0x2803030500142828 0x4a00c0c140050a0a 0x88030207801e307d 0x2200c081e0078c1f

def z1070 : W := mkw 0xc07fb400036b8000 0x301fed0000dae000 0x155dfc0003e1c000 0x85577f0000f87000

def z1071 : W := mkw 0x9400606251895650 0x2500181894625594 0xf5eae2e67b99f672 0xbd7ab8b99ee67d9c

def z1072 : W := mkw 0x14804bfff0805653 0x052012fffc201594 0xe08003fff0000600 0x382000fffc000180

def z1073 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x64dc03f807e03f82 0x993700fe01f80fe0

def z1074 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x1f7ffc0007e7c000 0x87dfff0001f9f000

def z1075 : W := mkw 0x68330f0dbc36eaee 0xda0cc3c36f0dbabb 0xba331f07fc1ff87f 0x6e8cc7c1ff07fe1f

def z1076 : W := mkw 0x00bcdbdae0000003 0x002f36f6b8000000 0xffbdfff9f0000000 0x3fef7ffe7c000000

def z1077 : W := mkw 0x9c036067519d5678 0x6700d819d467559e 0xffebe2e7fb9ff67f 0xfffaf8b9fee7fd9f

def z1078 : W := mkw 0xd400242011abd6d4 0x35000908046af5b5 0x004000000bf9f7f3 0xc010000002fe7dfc

def z1079 : W := mkw 0xd44024201fffd650 0xf510090807fff594 0x004000000fffc601 0xc010000003fff180

def z1080 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x66fc03f80ff83ff3 0xd9bf00fe03fe0ffc

def z1081 : W := mkw 0xfc0024201dbffefc 0xff000908076fffbf 0x004000000fffffff 0xc010000003ffffff

def z1082 : W := mkw 0xc4006c4af12bc2d6 0x31001b12bc4af0b5 0x9901fc01f007c04d 0x26407f007c01f013

def z1083 : W := mkw 0xd443f46251bfd650 0x7510fd18946ff594 0xffebfee67b9ff673 0xfffaffb99ee7fd9c

def z1084 : W := mkw 0x008cd8dae0000003 0x00233636b8000000 0xffbffffff0000000 0x3feffffffc000000

def z1085 : W := mkw 0x00bfdbdfe0000003 0x002ff6f7f8000000 0xffbffffff4600000 0xffeffffffd180000

def z1086 : W := mkw 0x3c334b6ffc947efe 0xcf0cd2dbff251fbf 0xeab303fffc1e3fff 0x7aacc0ffff078fff

def z1087 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x00fc03f80fe03f82 0xc03f00fe03f80fe0

def z1088 : W := mkw 0x300c00b002c03d00 0x0c03002c00b00f40 0x44cc00f803e03f82 0x9133003e00f80fe0

def z1089 : W := mkw 0x303c03b00ec03d00 0x8c0f00ec03b00f40 0x66fe03fe0ff83fb2 0xd9bf80ff83fe0fec

def z1090 : W := mkw 0x9400606251895650 0x2500181894625594 0x5feae2e67b99f631 0xd7fab8b99ee67d8c

def z1091 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x156efc000fffc001 0xc55bbf0003fff000

def z1092 : W := mkw 0xc07fb4000f7f8084 0xf01fed0003dfe021 0x1f7ffc000fffc98d 0xc7dfff0003fff263

def z1093 : W := mkw 0x80bffbdfe1090003 0x202ffef7f8424000 0xfffffffffb99c001 0xfffffffffee67000

def z1094 : W := mkw 0x3c004b6ff0807efe 0x0f0012dbfc201fbf 0xe08003fff0003ffe 0x382000fffc000fff

def z1095 : W := mkw 0x283303050c142828 0xca0cc0c143050a0a 0xa8130307841e387f 0x2a04c0c1e1078e1f

def z1096 : W := mkw 0xcc036c4ff13fc2fe 0x7300db13fc4ff0bf 0x9903fc07f01fc07d 0x2640ff01fc07f01f

def z1097 : W := mkw 0x00bfdbdfee400003 0x802ff6f7fb900000 0xffbffffff4600000 0x3feffffffd180000

def z1098 : W := mkw 0x008cd8dae0000003 0x00233636b8000000 0x77acfef870000000 0x1deb3fbe1c000000

def z1099 : W := mkw 0x380c00b00ed43d28 0xce03002c03b50f4a 0x44cc00f80ffe3fff 0xd133003e03ff8fff

def z1100 : W := mkw 0x20bfdbdfee402903 0x882ff6f7fb900a40 0xffbffffffc603982 0x7fefffffff180e60

def z1101 : W := mkw 0xc07fb4000f7f8000 0xf01fed0003dfe000 0x7f7ffd180fffc001 0xdfdfff4603fff000

def z1102 : W := mkw 0x2883dbdfe014282b 0x4a20f6f7f8050a0a 0xf983fffff01e387f 0x3e60fffffc078e1f

def z1103 : W := mkw 0xe8c06fdfef7fa82b 0xfa301bf7fbdfea0a 0xe0c003fffffff87f 0xf83000fffffffe1f

def z1104 : W := mkw 0xf873b7b50dbfbd28 0xfe1ceded436fef4a 0xfbb3ffff8c1fffff 0x7eecffffe307ffff

def z1105 : W := mkw 0x1883d86fe2d4152b 0x4620f61bf8b5054a 0x9943fc07f3fe07fd 0xa650ff01fcff81ff

def z1106 : W := mkw 0x30b3db6feec03d03 0x8c2cf6dbfbb00f40 0xbb73ff07ffe03f82 0xeedcffc1fff80fe0

def z1107 : W := mkw 0x380003b502c03d28 0x0e0000ed40b00f4a 0xe0c003ff83e03ffe 0xb83000ffe0f80fff

def z1108 : W := mkw 0x28bfd8daec14282b 0xca2ff636bb050a0a 0x5fbffcf87c1e387f 0x57efff3e1f078e1f

def z1109 : W := mkw 0xc0f36fdfef7f8003 0xf03cdbf7fbdfe000 0xeaf303ffffffc001 0xfabcc0fffffff000

def z1110 : W := mkw 0xe840b4000f7fa828 0xfa102d0003dfea0a 0x1140fc000ffff87f 0xc4503f0003fffe1f

def z1111 : W := mkw 0xd043b4b001bf9500 0x7410ed2c006fe540 0x5983fcf8001fc781 0x1660ff3e0007f1e0

def z1112 : W := mkw 0xd040b4b001ab9500 0x34102d2c006ae540 0x5180fcf80001c780 0x14603f3e000071e0

def z1113 : W := mkw 0xc0c06cdae36b8003 0x30301b36b8dae000 0x40c000f873e1c000 0x9030003e1cf87000

def z1114 : W := mkw 0xd4006c6ae1ab9496 0x35001b1ab86ae525 0xabffffff8ffe39ff 0x6affffffe3ff8e7f

def z1115 : W := mkw 0xf040b7b001abbd00 0x3c102dec006aef40 0x7180fff80001ff82 0x1c603ffe00007fe0

def z1116 : W := mkw 0xc843b405037f8028 0x7210ed0140dfe00a 0x9943fc0783ffc07d 0xa650ff01e0fff01f

def z1117 : W := mkw 0x804cb808b34942c6 0x20132e022cd250b1 0xeb59e119f7860fcf 0x7ad678467de183f3

def z1118 : W := mkw 0xe8f36fdfef7fa82b 0xfa3cdbf7fbdfea0a 0xeaf303fffffff87f 0xfabcc0fffffffe1f

def z1119 : W := mkw 0x544cd46252e2d650 0x1513351894b8b594 0xeaa61ee678783673 0x7aa987b99e1e0d9c

def z1120 : W := mkw 0xa87fbb0dbf5d6aee 0xea1feec36fd75abb 0x416ae21e7b9837b0 0x105ab8879ee60dec

def z1121 : W := mkw 0xd843b4b501bf9528 0x7610ed2d406fe54a 0xd983fcff801fc7fd 0x3660ff3fe007f1ff

def z1122 : W := mkw 0x3880d86aeed43d2b 0xce20361abbb50f4a 0x1140fc007ffe3fff 0xc4503f001fff8fff

def z1123 : W := mkw 0xf840b7b501abbd28 0x3e102ded406aef4a 0xf180ffff8001fffe 0x3c603fffe0007fff

def z1124 : W := mkw 0x28bfdbdfec14282b 0xca2ff6f7fb050a0a 0x11aafee678183030 0x046abfb99e060c0c

def z1125 : W := mkw 0xc0c06fdfe36b8003 0x30301bf7f8dae000 0xe0c003fff3e1c000 0xb83000fffcf87000

def z1126 : W := mkw 0x1083d86fe2c01503 0x0420f61bf8b00540 0x9943fc07f3e00780 0xa650ff01fcf801e0

def z1127 : W := mkw 0xbcbfbbbdbd9d7e7b 0xef2feeef6f675f9e 0x00551d198787ce0c 0x8015474661e1f383

def z1128 : W := mkw 0x180f00b502d41528 0x4603c02d40b5054a 0xeedf01ff87fe0fff 0xfbb7c07fe1ff83ff

def z1129 : W := mkw 0xd073b4b00dbf9500 0xf41ced2c036fe540 0x5bb3fcf80c1fc781 0x56ecff3e0307f1e0

def z1130 : W := mkw 0x183f03b502d41528 0x460fc0ed40b5054a 0xeeff03ff83fe07fd 0xbbbfc0ffe0ff81ff

def z1131 : W := mkw 0x0883d8dfe014002b 0x4220f637f805000a 0xd983fcfff01e007d 0x3660ff3ffc07801f

def z1132 : W := mkw 0xf070b7b00dabbd00 0xbc1c2dec036aef40 0x73b0fff80c01ff82 0x5cec3ffe03007fe0

def z1133 : W := mkw 0xe8c06fdfe36ba82b 0x3a301bf7f8daea0a 0xe0c003fff3e1f87e 0xb83000fffcf87e1f

def z1134 : W := mkw 0xc0f36fdfe36b8003 0x303cdbf7f8dae000 0xeaf303fff3e1c000 0xbabcc0fffcf87000

def z1135 : W := mkw 0x183f00b50ed41528 0xc60fc02d43b5054a 0xceff00ff8ffe07fd 0xf3bfc03fe3ff81ff

def z1136 : W := mkw 0xf07fb7b001bfbd00 0x7c1fedec006fef40 0x7fbffff8001fff83 0x1feffffe0007ffe0

def z1137 : W := mkw 0xe87fb705036ba828 0x3a1fedc140daea0a 0xbf7fff0783e1f87e 0xafdfffc1e0f87e1f

def z1138 : W := mkw 0x0080d84ae0000003 0x00203612b8000000 0xffaafee678183073 0x7feabfb99e060c1c

def z1139 : W := mkw 0xc040b400012b8000 0x30102d00004ae000 0xbf6afe060b99f073 0xefdabf8182e67c1c

def z1140 : W := mkw 0x3080d86aeec03d03 0x8c20361abbb00f40 0x1140fc007fe03f82 0xc4503f001ff80fe0

def z1141 : W := mkw 0x283f03950e542828 0xca0fc0e543950a0a 0xeeff03ff8ffe3fff 0xfbbfc0ffe3ff8fff

def z1142 : W := mkw 0x68bfd7d75c36eaed 0xda2ff5f5d70dbabb 0x01aae2e60879f7b0 0x806ab8b9821e7dec

def z1143 : W := mkw 0x30b0db6aeec03d03 0x8c2c36dabbb00f40 0x3370ff007fe03f82 0xccdc3fc01ff80fe0

def z1144 : W := mkw 0x2880dbdfe000282b 0x0a2036f7f8000a0a 0xf180fffff000387e 0x3c603ffffc000e1f

def z1145 : W := mkw 0x3883d86feed43d2b 0xce20f61bfbb50f4a 0x9943fc07fffe3fff 0xe650ff01ffff8fff

def z1146 : W := mkw 0x10b3db6fe2c01503 0x042cf6dbf8b00540 0xbb73ff07f3e00780 0xaedcffc1fcf801e0

def z1147 : W := mkw 0xe87cb7050f6ba828 0xba1f2dc143daea0a 0xb77cff078fe1f87e 0xeddf3fc1e3f87e1f

def z1148 : W := mkw 0xc0c06cdaef7f8003 0xf0301b36bbdfe000 0x40c000f87fffc001 0xd030003e1ffff000

def z1149 : W := mkw 0x948cb8b8b1895653 0x25232e2e2c625594 0xaa661e1e0b99f673 0xea99878782e67d9c

def z1150 : W := mkw 0x38b3db6feed43d2b 0xce2cf6dbfbb50f4a 0xbb73ff07fffe3fff 0xeedcffc1ffff8fff

def z1151 : W := mkw 0xf843b7b501bfbd28 0x7e10eded406fef4a 0xf983ffff801fffff 0x3e60ffffe007ffff

def z1152 : W := mkw 0x7c7fd7675ef6fe78 0xdf1ff5d9d7bdbf9e 0x40951de1f4660e0c 0x102547787d198383

def z1153 : W := mkw 0x380000b00ed43d28 0xce00002c03b50f4a 0x40c000f80ffe3fff 0xd030003e03ff8fff

def z1154 : W := mkw 0x28bcdbdaec14282b 0xca2f36f6bb050a0a 0x77bcfff87c1e387f 0x5def3ffe1f078e1f

def z1155 : W := mkw 0x1080d86ae2c01503 0x0420361ab8b00540 0x1140fc0073e00780 0x84503f001cf801e0

def z1156 : W := mkw 0x30bfd86feec03d03 0x8c2ff61bfbb00f40 0x9f7ffc07ffe03f82 0xe7dfff01fff80fe0

def z1157 : W := mkw 0xe8c06cdaef7fa82b 0xfa301b36bbdfea0a 0x40c000f87ffff87f 0xd030003e1ffffe1f

def z1158 : W := mkw 0x143f902010805650 0x050fe40804201594 0x1f3ffc0000003672 0x07cfff0000000d9c

def z1159 : W := mkw 0x783f0fbdbef6ffee 0xde0fc3ef6fbdbffb 0x10ea1ee67b99f030 0x043a87b99ee67c0c

def z1160 : W := mkw 0xe87fb7050f7fa828 0xfa1fedc143dfea0a 0x116afe060b99f030 0x045abf8182e67c0c

def z1161 : W := mkw 0x500c0cb8b2e2d7c6 0x1403032e2cb8b5f1 0xbad91de1f787c84f 0x6eb647787de1f213

def z1162 : W := mkw 0xc0fc6fdfef7f8003 0xf03f1bf7fbdfe000 0xe6fc03ffffffc001 0xf9bf00fffffff000

def z1163 : W := mkw 0xc0f36cdaef7f8003 0xf03cdb36bbdfe000 0x4af300f87fffc001 0xd2bcc03e1ffff000

def z1164 : W := mkw 0x383f03b50ed43d28 0xce0fc0ed43b50f4a 0xccdf01ff87fe0ffd 0xb337c07fe1ff83ff

def z1165 : W := mkw 0x408cd4d25022c2c5 0x102335349408b0b1 0xab99e1e18467cfcf 0xeae678786119f3f3

def z1166 : W := mkw 0xf073b7b00dbfbd00 0xfc1cedec036fef40 0x7bb3fff80c1fff83 0x5eecfffe0307ffe0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5]),(0,[z6,z7,z1,z2,z3,z4]),(0,[z8,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z9])],[(0,[z10,z0,z11,z2,z3,z12]),(0,[z13,z0,z1,z2,z3,z14]),(0,[z13,z15,z0,z1,z2,z3]),(0,[z10,z16,z2,z3,z17,z18]),(0,[z10,z16,z2,z3,z4,z19]),(0,[z20,z10,z1,z2,z21,z4]),(0,[z22,z0,z23,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z24])],[(1,[z10,z16,z2,z3,z25]),(0,[z26,z27,z0,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z28]),(0,[z10,z29,z0,z1,z2,z3]),(0,[z10,z30,z0,z2,z3,z31]),(0,[z10,z0,z1,z2,z32,z33])],[(0,[z34,z0,z1,z2,z3,z4])],[(0,[z10,z0,z35,z2,z3,z4])],[(0,[z6,z0,z1,z2,z3,z12]),(0,[z36,z16,z2,z37,z3,z4]),(0,[z10,z38,z0,z2,z3,z4]),(0,[z0,z39,z2,z3,z40,z41]),(0,[z10,z42,z16,z2,z3,z4]),(0,[z10,z16,z2,z3,z4,z43]),(0,[z44,z45,z1,z2,z3,z4]),(0,[z10,z1,z2,z46,z4,z47]),(0,[z48,z49,z1,z2,z3,z17])],[(0,[z10,z50,z0,z2,z3,z4]),(0,[z51,z0,z16,z2,z3,z4]),(0,[z10,z52,z0,z2,z3,z4])],[(0,[z10,z53,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z54,z3]),(0,[z55,z0,z1,z2,z3,z56]),(0,[z57,z0,z1,z2,z33,z58])],[(0,[z6,z0,z1,z2,z3,z31]),(0,[z59,z0,z16,z2,z3,z40]),(0,[z10,z60,z16,z2,z3,z4]),(0,[z10,z0,z1,z2,z61,z4]),(0,[z62,z0,z1,z2,z3,z4]),(0,[z10,z30,z63,z0,z2,z3]),(0,[z10,z64,z1,z2,z3,z4])],[(0,[z0,z36,z1,z2,z3,z65]),(0,[z6,z0,z1,z2,z3,z66]),(0,[z67,z0,z68,z2,z3,z4]),(0,[z69,z10,z16,z2,z3,z17]),(0,[z0,z70,z1,z2,z3,z65]),(0,[z10,z71,z1,z72,z3,z73]),(0,[z10,z0,z1,z2,z74,z75])],[(0,[z0,z36,z1,z2,z3,z76]),(0,[z6,z0,z77,z2,z3,z4]),(0,[z10,z0,z16,z2,z78,z3]),(0,[z10,z1,z72,z46,z4,z79]),(0,[z10,z80,z1,z2,z3,z4])],[(0,[z10,z0,z1,z2,z3,z81]),(0,[z36,z1,z2,z82,z3,z17]),(0,[z83,z10,z0,z37,z3,z4]),(0,[z10,z30,z0,z2,z3,z84])],[(0,[z44,z36,z1,z2,z3,z84]),(0,[z10,z85,z16,z2,z3,z4]),(0,[z86,z10,z16,z2,z3,z17]),(0,[z10,z87,z1,z2,z3,z84])],[(0,[z10,z0,z11,z2,z3,z84]),(0,[z59,z36,z1,z2,z3,z17]),(0,[z88,z89,z1,z2,z3,z4]),(0,[z10,z16,z2,z3,z4,z65]),(0,[z10,z0,z1,z90,z91,z4]),(0,[z10,z92,z1,z2,z46,z84])],[(0,[z93,z27,z0,z2,z94,z4]),(0,[z10,z0,z95,z2,z3,z84]),(0,[z0,z1,z2,z3,z4,z96]),(0,[z87,z97,z1,z2,z3,z4])],[(0,[z36,z1,z2,z3,z4,z12]),(0,[z98,z36,z16,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z99]),(0,[z10,z0,z1,z2,z91,z84]),(0,[z0,z1,z2,z3,z4,z100])]],
   [[(0,[z101,z0,z1,z2,z3,z4]),(0,[z10,z27,z0,z2,z3,z102]),(0,[z10,z16,z2,z103,z3,z4]),(0,[z10,z104,z2,z3,z4,z41])],[(0,[z6,z0,z1,z2,z3,z84]),(0,[z10,z105,z1,z2,z74,z4])],[(0,[z106,z36,z1,z2,z3,z17]),(0,[z0,z1,z2,z3,z107,z4]),(0,[z10,z108,z16,z2,z3,z4]),(0,[z10,z0,z16,z2,z3,z109])],[(0,[z0,z36,z110,z2,z3,z4]),(0,[z10,z16,z2,z111,z3,z4]),(0,[z10,z1,z112,z2,z3,z17]),(0,[z93,z0,z1,z2,z113,z4]),(0,[z114,z0,z1,z2,z3,z4]),(0,[z10,z0,z1,z115,z82,z4])],[(0,[z10,z116,z1,z2,z3,z4]),(0,[z117,z36,z1,z2,z3,z17]),(0,[z118,z36,z1,z2,z3,z4]),(0,[z119,z36,z16,z2,z3,z4]),(0,[z10,z120,z1,z2,z3,z4]),(0,[z121,z122,z1,z2,z3,z4])],[(0,[z10,z27,z92,z2,z46,z4]),(0,[z123,z1,z2,z3,z4,z17])],[(0,[z124,z36,z1,z2,z3,z12]),(0,[z125,z36,z16,z2,z3,z4]),(0,[z0,z126,z1,z2,z3,z4]),(0,[z10,z1,z2,z3,z127,z17]),(0,[z10,z0,z1,z2,z3,z128]),(0,[z10,z0,z129,z130,z3,z4]),(0,[z27,z97,z0,z2,z3,z4]),(0,[z131,z0,z1,z2,z3,z4]),(0,[z132,z10,z0,z1,z4,z79])],[(0,[z93,z36,z1,z2,z3,z17]),(1,[z0,z1,z2,z107,z4]),(0,[z10,z105,z1,z2,z3,z4]),(0,[z10,z133,z0,z16,z2,z134]),(0,[z10,z0,z135,z2,z3,z84])],[(0,[z136,z36,z16,z2,z3,z4]),(0,[z137,z36,z1,z2,z3,z17]),(0,[z10,z87,z138,z2,z3,z4]),(0,[z10,z1,z2,z3,z4,z139])],[(0,[z140,z36,z16,z2,z3,z4]),(0,[z10,z141,z1,z2,z3,z4]),(0,[z13,z0,z16,z2,z3,z142]),(0,[z44,z143,z1,z2,z3,z4]),(0,[z144,z0,z1,z2,z3,z4]),(0,[z10,z145,z0,z2,z3,z4]),(0,[z10,z0,z135,z2,z3,z43]),(0,[z10,z146,z1,z2,z3,z17])],[(0,[z36,z1,z2,z37,z3,z17]),(0,[z10,z88,z16,z2,z3,z84]),(0,[z10,z0,z16,z2,z3,z147]),(0,[z10,z16,z2,z3,z148,z17]),(0,[z27,z0,z2,z3,z4,z149]),(0,[z10,z104,z1,z2,z3,z41]),(0,[z150,z0,z1,z2,z3,z4])],[(0,[z151,z36,z16,z2,z3,z4]),(0,[z6,z1,z16,z2,z3,z17]),(0,[z152,z0,z1,z2,z3,z4]),(0,[z153,z10,z0,z4,z154,z79])],[(0,[z10,z0,z155,z2,z3,z4]),(0,[z36,z1,z2,z3,z156,z17]),(0,[z157,z42,z16,z2,z3,z4]),(0,[z10,z16,z2,z46,z4,z79]),(0,[z158,z159,z1,z90,z3,z4]),(0,[z158,z10,z1,z90,z3,z4]),(0,[z160,z0,z70,z2,z3,z4]),(0,[z0,z1,z2,z3,z17,z100]),(0,[z161,z162,z0,z37,z3,z4]),(0,[z163,z0,z1,z2,z3,z4])],[(0,[z36,z16,z2,z3,z148,z4]),(0,[z6,z0,z138,z2,z3,z4]),(0,[z10,z44,z164,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z165]),(0,[z10,z166,z1,z2,z3,z84])],[(0,[z13,z36,z16,z2,z3,z4]),(0,[z10,z1,z2,z3,z4,z167]),(0,[z10,z168,z1,z2,z3,z4]),(0,[z0,z1,z2,z78,z94,z3]),(0,[z10,z169,z16,z2,z3,z4]),(0,[z0,z16,z2,z3,z4,z170]),(0,[z10,z0,z1,z2,z3,z56]),(0,[z10,z0,z1,z171,z3,z172])],[(0,[z10,z0,z1,z2,z3,z173]),(0,[z10,z0,z1,z2,z3,z174]),(0,[z175,z36,z1,z2,z3,z4]),(0,[z6,z0,z1,z2,z3,z176]),(0,[z10,z177,z16,z2,z3,z4]),(0,[z10,z44,z178,z2,z3,z4]),(0,[z10,z30,z0,z2,z3,z17]),(0,[z10,z104,z1,z2,z3,z179])]],
   [[(0,[z44,z36,z1,z2,z3,z17]),(0,[z180,z0,z1,z2,z3,z4]),(0,[z10,z0,z16,z181,z3,z4]),(0,[z10,z182,z183,z2,z3,z4]),(0,[z10,z27,z0,z2,z184,z4]),(0,[z158,z10,z185,z90,z3,z4])],[(0,[z159,z0,z1,z2,z3,z4]),(0,[z10,z16,z2,z186,z3,z4]),(0,[z187,z44,z27,z2,z3,z4]),(0,[z10,z92,z1,z2,z46,z17])],[(0,[z124,z36,z1,z2,z3,z84]),(0,[z164,z0,z36,z2,z3,z4]),(0,[z0,z1,z2,z94,z4,z188]),(0,[z10,z189,z1,z2,z3,z84]),(0,[z10,z190,z1,z2,z3,z4])],[(0,[z108,z1,z2,z94,z3,z4]),(0,[z10,z0,z16,z2,z3,z191]),(0,[z10,z192,z2,z46,z3,z4]),(0,[z10,z0,z1,z2,z91,z17]),(0,[z10,z63,z0,z2,z3,z154]),(0,[z193,z0,z1,z2,z3,z4])],[(0,[z10,z0,z194,z2,z3,z195]),(0,[z36,z1,z2,z3,z21,z17]),(0,[z10,z16,z2,z3,z17,z41]),(0,[z10,z0,z1,z2,z3,z196]),(0,[z86,z197,z0,z2,z3,z41]),(0,[z198,z10,z0,z1,z199,z3])],[(0,[z6,z0,z1,z2,z3,z17]),(0,[z36,z1,z2,z200,z3,z4]),(0,[z201,z0,z16,z202,z3,z4]),(0,[z159,z0,z185,z2,z3,z4])],[(0,[z6,z36,z1,z2,z3,z84]),(0,[z133,z36,z16,z2,z3,z4]),(0,[z140,z0,z112,z2,z3,z4]),(0,[z10,z203,z16,z2,z3,z4]),(0,[z10,z0,z204,z2,z3,z4]),(0,[z158,z10,z1,z90,z3,z205]),(0,[z122,z206,z1,z2,z3,z4])],[(0,[z207,z0,z1,z2,z3,z4]),(0,[z10,z208,z0,z2,z3,z4]),(0,[z209,z27,z0,z2,z3,z4]),(0,[z210,z0,z1,z2,z184,z4]),(0,[z10,z211,z0,z2,z3,z17]),(0,[z10,z133,z0,z1,z2,z212])],[(0,[z10,z0,z1,z2,z3,z213]),(0,[z10,z105,z1,z2,z214,z4])],[(0,[z10,z0,z215,z2,z3,z4]),(0,[z10,z0,z216,z2,z3,z65]),(0,[z217,z0,z1,z2,z3,z4])],[(0,[z10,z218,z88,z2,z3,z4]),(0,[z10,z0,z219,z2,z3,z4])],[(0,[z36,z16,z2,z3,z220,z4]),(0,[z10,z0,z68,z2,z3,z221]),(0,[z10,z222,z1,z2,z3,z4]),(0,[z49,z0,z16,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z205]),(0,[z10,z0,z135,z2,z3,z17]),(0,[z0,z223,z1,z2,z3,z4]),(0,[z10,z224,z1,z2,z3,z4]),(0,[z10,z0,z225,z2,z3,z4])],[(0,[z36,z1,z2,z46,z3,z17]),(0,[z10,z0,z2,z3,z4,z226])],[(0,[z10,z0,z227,z2,z3,z179])],[(0,[z22,z36,z1,z2,z3,z4]),(0,[z10,z88,z16,z2,z3,z17]),(0,[z157,z10,z16,z2,z3,z228]),(0,[z0,z229,z1,z2,z3,z4]),(0,[z10,z1,z2,z3,z230,z17]),(0,[z10,z0,z1,z2,z231,z58]),(0,[z10,z166,z1,z2,z3,z232])],[(0,[z10,z0,z185,z2,z3,z205]),(0,[z157,z10,z1,z181,z21,z4]),(0,[z10,z233,z1,z2,z3,z17]),(1,[z10,z0,z1,z2,z32])]],
   [[(0,[z234,z36,z1,z2,z3,z17]),(0,[z136,z0,z68,z2,z3,z4]),(0,[z10,z0,z1,z2,z235,z4]),(0,[z42,z44,z1,z2,z3,z4]),(0,[z10,z133,z0,z1,z2,z236]),(0,[z162,z105,z1,z2,z3,z4])],[],[(0,[z10,z0,z1,z2,z3,z237]),(0,[z10,z238,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z239]),(0,[z240,z0,z1,z2,z3,z84]),(0,[z10,z0,z1,z2,z3,z241]),(0,[z10,z0,z1,z2,z3,z242]),(0,[z10,z1,z243,z90,z3,z4]),(0,[z161,z10,z0,z244,z3,z4]),(0,[z10,z0,z1,z245,z2,z3])],[(0,[z10,z44,z1,z181,z3,z4]),(0,[z10,z0,z216,z2,z3,z17]),(0,[z246,z0,z1,z2,z3,z4])],[(0,[z10,z88,z11,z2,z3,z4]),(0,[z36,z1,z2,z3,z247,z17]),(0,[z57,z0,z1,z2,z3,z4]),(0,[z10,z248,z16,z2,z3,z4]),(0,[z10,z249,z16,z2,z3,z4]),(0,[z250,z0,z1,z2,z3,z4]),(0,[z10,z0,z251,z2,z3,z4])],[(0,[z71,z36,z16,z2,z3,z4]),(0,[z108,z36,z1,z2,z3,z17]),(0,[z36,z1,z2,z3,z252,z4]),(0,[z10,z253,z1,z2,z3,z4]),(0,[z71,z70,z16,z2,z3,z4]),(0,[z10,z166,z129,z2,z3,z4]),(0,[z10,z254,z1,z2,z3,z4]),(0,[z197,z122,z1,z2,z3,z4]),(0,[z255,z0,z1,z2,z3,z4])],[(0,[z124,z36,z1,z2,z3,z17]),(0,[z0,z36,z1,z2,z3,z56]),(0,[z10,z0,z1,z2,z3,z256]),(0,[z10,z257,z16,z2,z3,z4]),(0,[z10,z0,z1,z2,z258,z4]),(0,[z10,z189,z1,z2,z3,z17]),(0,[z1,z2,z3,z4,z149,z230])],[(0,[z70,z1,z16,z2,z3,z4]),(0,[z10,z0,z1,z2,z33,z58])],[(0,[z6,z88,z1,z2,z3,z4]),(0,[z259,z36,z16,z2,z3,z4]),(0,[z260,z36,z1,z2,z3,z17]),(0,[z0,z261,z1,z2,z3,z4]),(0,[z10,z262,z1,z2,z3,z4]),(0,[z59,z0,z1,z2,z3,z263]),(0,[z10,z122,z1,z2,z3,z4]),(0,[z20,z10,z1,z181,z3,z4])],[(0,[z69,z36,z16,z2,z3,z4]),(0,[z6,z0,z1,z2,z3,z75]),(0,[z10,z0,z1,z2,z107,z4])],[(0,[z6,z36,z1,z2,z3,z17]),(0,[z36,z68,z1,z2,z3,z17]),(0,[z10,z0,z1,z264,z2,z3]),(0,[z10,z16,z2,z46,z3,z4]),(0,[z10,z16,z2,z265,z3,z4]),(0,[z10,z266,z2,z46,z3,z4]),(0,[z267,z0,z1,z2,z3,z4]),(0,[z10,z0,z268,z2,z3,z4]),(0,[z10,z0,z1,z269,z4,z270])],[(0,[z10,z27,z0,z2,z3,z12]),(0,[z0,z39,z2,z3,z4,z221]),(0,[z10,z0,z1,z2,z3,z271]),(0,[z10,z272,z1,z72,z3,z4])],[(0,[z86,z36,z16,z2,z3,z4]),(0,[z273,z36,z1,z2,z3,z4]),(0,[z10,z0,z274,z2,z3,z4]),(0,[z10,z1,z72,z243,z3,z4])],[(0,[z36,z1,z275,z2,z3,z4]),(0,[z88,z36,z1,z2,z3,z17]),(0,[z13,z0,z1,z2,z3,z276]),(0,[z10,z277,z0,z1,z2,z3]),(0,[z69,z0,z1,z278,z3,z84]),(0,[z279,z0,z1,z2,z3,z4])],[(0,[z280,z36,z1,z2,z3,z4]),(0,[z281,z0,z1,z2,z3,z4]),(0,[z10,z0,z110,z2,z3,z4]),(0,[z10,z27,z0,z2,z3,z31]),(0,[z10,z0,z1,z2,z3,z282])],[(0,[z36,z1,z2,z3,z4,z283]),(0,[z6,z0,z1,z284,z3,z4]),(0,[z201,z0,z1,z285,z3,z4]),(0,[z10,z0,z1,z2,z33,z286]),(0,[z10,z27,z0,z2,z3,z66])]],
   [[(0,[z10,z0,z16,z2,z3,z195]),(0,[z36,z1,z2,z3,z220,z17]),(0,[z6,z0,z2,z3,z4,z154]),(0,[z121,z0,z1,z2,z3,z4]),(0,[z10,z16,z2,z3,z17,z287]),(0,[z10,z0,z266,z2,z3,z84]),(0,[z10,z0,z1,z2,z231,z18])],[(0,[z6,z16,z2,z3,z4,z17]),(0,[z10,z0,z1,z2,z288,z4]),(0,[z97,z0,z1,z2,z3,z4]),(0,[z10,z289,z77,z2,z3,z4]),(0,[z187,z0,z16,z2,z3,z4]),(0,[z153,z10,z27,z0,z4,z79]),(0,[z10,z105,z1,z2,z3,z290])],[(0,[z10,z0,z291,z2,z3,z4]),(0,[z292,z10,z0,z2,z3,z41])],[(0,[z0,z36,z1,z2,z3,z205]),(0,[z10,z108,z1,z2,z3,z84]),(0,[z10,z16,z2,z3,z293,z4]),(0,[z10,z0,z294,z2,z3,z4]),(0,[z49,z0,z295,z2,z3,z4]),(0,[z0,z206,z1,z2,z3,z4])],[(0,[z123,z27,z0,z2,z3,z4]),(0,[z10,z27,z63,z0,z2,z3]),(0,[z0,z296,z1,z2,z3,z4])],[(0,[z36,z16,z2,z3,z297,z4]),(0,[z298,z0,z1,z2,z3,z4]),(0,[z10,z0,z135,z284,z3,z4]),(0,[z10,z166,z1,z2,z3,z75])],[(0,[z10,z0,z1,z2,z3,z299]),(0,[z0,z300,z39,z2,z3,z4]),(0,[z301,z0,z68,z2,z3,z4]),(0,[z10,z178,z0,z2,z3,z4]),(0,[z10,z16,z2,z3,z4,z302]),(0,[z240,z0,z1,z2,z3,z17]),(0,[z10,z0,z129,z303,z3,z84]),(0,[z161,z10,z166,z37,z3,z4])],[(0,[z6,z304,z1,z2,z3,z4]),(0,[z10,z27,z0,z2,z3,z84]),(0,[z305,z10,z0,z2,z3,z41])],[(0,[z0,z36,z1,z2,z235,z4]),(0,[z10,z306,z1,z2,z3,z4]),(0,[z106,z0,z307,z2,z3,z4]),(0,[z10,z289,z1,z2,z3,z84]),(0,[z10,z0,z1,z2,z3,z308]),(0,[z10,z0,z309,z2,z3,z4])],[(0,[z124,z89,z1,z2,z3,z4]),(0,[z10,z0,z138,z2,z3,z228]),(0,[z153,z0,z1,z4,z149,z79])],[(0,[z92,z36,z16,z2,z3,z4]),(0,[z0,z36,z1,z2,z214,z4]),(0,[z0,z310,z1,z2,z3,z4]),(0,[z10,z0,z311,z2,z3,z84]),(0,[z10,z164,z116,z2,z3,z4]),(0,[z0,z261,z1,z2,z3,z312])],[(0,[z0,z36,z1,z2,z3,z312]),(0,[z10,z0,z1,z2,z3,z313]),(0,[z10,z0,z1,z2,z314,z3]),(0,[z0,z315,z16,z2,z3,z4]),(0,[z10,z316,z16,z2,z3,z4]),(0,[z10,z1,z2,z3,z84,z19]),(0,[z10,z317,z0,z1,z2,z134])],[(1,[z0,z300,z2,z3,z4]),(0,[z10,z0,z318,z2,z3,z4]),(0,[z319,z0,z16,z2,z3,z4]),(0,[z10,z0,z23,z2,z3,z4]),(0,[z10,z44,z1,z2,z3,z320])],[(0,[z6,z89,z1,z2,z3,z4]),(0,[z55,z0,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z321]),(0,[z10,z0,z322,z2,z3,z4]),(0,[z10,z183,z16,z2,z3,z84]),(0,[z10,z0,z1,z269,z82,z4])],[(0,[z323,z0,z1,z2,z3,z4]),(0,[z324,z36,z1,z2,z3,z4]),(0,[z6,z164,z88,z2,z3,z4]),(0,[z10,z325,z1,z2,z3,z17]),(0,[z140,z0,z39,z2,z3,z221]),(0,[z157,z10,z16,z2,z21,z4]),(0,[z10,z16,z2,z82,z46,z4]),(0,[z210,z0,z1,z2,z3,z84]),(0,[z10,z0,z1,z2,z3,z326]),(0,[z104,z310,z1,z2,z3,z4]),(0,[z86,z10,z104,z2,z3,z41])],[(0,[z0,z36,z1,z2,z33,z58]),(0,[z10,z16,z2,z327,z3,z4]),(0,[z10,z169,z1,z2,z3,z84]),(0,[z10,z234,z0,z2,z74,z4])]],
   [[(0,[z0,z328,z1,z2,z3,z4]),(0,[z0,z1,z95,z2,z3,z40]),(0,[z157,z101,z16,z2,z3,z4]),(0,[z10,z44,z27,z2,z3,z84]),(0,[z10,z0,z329,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z330]),(0,[z331,z0,z1,z2,z3,z4])],[(0,[z119,z0,z1,z2,z332,z4]),(0,[z69,z0,z1,z278,z3,z17]),(0,[z10,z0,z1,z181,z3,z84])],[(0,[z333,z0,z1,z2,z3,z142]),(0,[z10,z0,z1,z2,z3,z334])],[(0,[z248,z36,z1,z2,z3,z17]),(0,[z36,z16,z2,z3,z4,z172]),(0,[z10,z16,z2,z3,z17,z302]),(0,[z10,z117,z16,z2,z3,z4]),(0,[z10,z27,z233,z2,z3,z4])],[(0,[z0,z36,z274,z2,z3,z4]),(0,[z140,z335,z0,z2,z3,z4]),(0,[z10,z0,z192,z2,z184,z4])],[(1,[z27,z36,z2,z3,z17]),(0,[z0,z1,z278,z3,z4,z336]),(0,[z10,z27,z0,z2,z3,z176]),(0,[z10,z337,z1,z2,z3,z4])],[(0,[z10,z0,z338,z2,z3,z4]),(0,[z10,z339,z1,z2,z3,z4]),(0,[z6,z0,z1,z2,z3,z43]),(0,[z201,z0,z1,z202,z3,z84]),(0,[z10,z0,z340,z2,z3,z4])],[(0,[z0,z36,z1,z341,z2,z3]),(0,[z20,z10,z16,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z342]),(0,[z343,z0,z1,z2,z3,z4])],[(0,[z6,z88,z1,z2,z3,z25]),(0,[z10,z344,z1,z2,z3,z17]),(0,[z10,z345,z0,z2,z3,z4]),(0,[z10,z1,z2,z3,z4,z230]),(0,[z346,z0,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z347,z4])],[(0,[z119,z36,z1,z2,z3,z17]),(0,[z10,z0,z348,z2,z3,z4]),(0,[z10,z349,z16,z2,z3,z4])],[(0,[z44,z36,z1,z2,z3,z76]),(0,[z36,z1,z2,z3,z297,z17]),(0,[z350,z0,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z351]),(0,[z10,z352,z16,z2,z46,z4]),(0,[z10,z0,z1,z353,z3,z4]),(0,[z10,z0,z129,z303,z3,z17])],[(0,[z125,z36,z1,z2,z3,z17]),(0,[z10,z125,z16,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z354]),(0,[z10,z27,z0,z2,z3,z17])],[(0,[z36,z1,z2,z3,z17,z18]),(0,[z36,z1,z2,z3,z355,z4]),(0,[z36,z1,z2,z3,z4,z19]),(0,[z356,z10,z1,z2,z3,z17]),(0,[z10,z289,z1,z2,z3,z17]),(1,[z45,z16,z2,z3,z4])],[(0,[z10,z39,z16,z2,z3,z17]),(0,[z10,z0,z357,z2,z3,z358]),(0,[z0,z1,z2,z3,z4,z149]),(0,[z10,z16,z2,z3,z4,z359]),(0,[z10,z0,z138,z181,z3,z4]),(0,[z360,z0,z1,z2,z3,z4])],[(0,[z140,z36,z1,z2,z3,z17]),(0,[z6,z0,z1,z2,z3,z65]),(0,[z10,z0,z311,z2,z3,z17]),(0,[z10,z0,z361,z2,z3,z4]),(0,[z292,z10,z0,z2,z3,z287]),(0,[z10,z0,z1,z2,z362,z4]),(0,[z10,z0,z1,z243,z3,z4]),(0,[z10,z0,z1,z2,z74,z4])],[(0,[z122,z36,z1,z2,z3,z4]),(0,[z6,z0,z1,z2,z3,z76]),(0,[z10,z0,z1,z2,z3,z363]),(0,[z10,z0,z364,z2,z3,z4]),(0,[z10,z0,z1,z2,z184,z109]),(0,[z121,z104,z1,z2,z3,z4])]],
   [[(0,[z36,z39,z16,z2,z3,z4]),(0,[z10,z108,z365,z2,z3,z4]),(0,[z42,z0,z16,z2,z3,z4]),(0,[z10,z0,z366,z2,z3,z4])],[(0,[z197,z0,z1,z2,z3,z4]),(0,[z10,z183,z16,z2,z3,z17]),(0,[z10,z1,z2,z3,z84,z17]),(0,[z367,z122,z1,z2,z3,z4]),(0,[z10,z133,z0,z1,z2,z134])],[(0,[z0,z1,z2,z3,z4,z368]),(0,[z10,z0,z369,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z370]),(0,[z10,z307,z16,z2,z3,z17]),(0,[z10,z324,z16,z2,z3,z4]),(0,[z210,z0,z1,z2,z3,z17]),(0,[z371,z0,z1,z2,z3,z4])],[(0,[z160,z0,z36,z2,z3,z4]),(0,[z0,z36,z1,z2,z3,z290]),(0,[z13,z36,z1,z2,z3,z17]),(0,[z10,z372,z16,z2,z3,z4]),(0,[z373,z0,z1,z2,z3,z4]),(0,[z10,z87,z1,z2,z3,z17])],[(0,[z10,z0,z1,z2,z3,z4]),(0,[z10,z0,z11,z2,z3,z17]),(0,[z374,z36,z1,z2,z3,z4]),(0,[z0,z36,z23,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z375]),(0,[z153,z10,z0,z1,z31,z79])],[(0,[z36,z307,z16,z2,z3,z4]),(0,[z10,z0,z95,z2,z3,z17]),(0,[z376,z0,z1,z2,z3,z84]),(0,[z10,z0,z377,z2,z3,z179]),(0,[z378,z30,z0,z2,z3,z4])],[(0,[z10,z0,z379,z1,z4,z79])],[(0,[z10,z380,z1,z2,z3,z4]),(0,[z381,z0,z1,z2,z3,z382]),(0,[z10,z383,z1,z2,z3,z4])],[(0,[z384,z0,z1,z2,z3,z4]),(0,[z119,z27,z0,z2,z220,z4]),(0,[z10,z0,z185,z2,z3,z4]),(0,[z10,z385,z16,z2,z3,z17]),(0,[z10,z0,z1,z2,z3,z386]),(0,[z10,z387,z0,z2,z3,z4])],[(0,[z388,z0,z1,z2,z3,z4]),(0,[z10,z389,z0,z1,z2,z3]),(0,[z106,z0,z390,z2,z3,z4]),(0,[z106,z0,z391,z2,z3,z4]),(0,[z10,z392,z16,z2,z3,z4]),(0,[z10,z393,z0,z2,z394,z4])],[(0,[z27,z36,z2,z3,z4,z17]),(0,[z201,z0,z1,z202,z3,z17]),(0,[z395,z0,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z396,z4]),(0,[z10,z0,z397,z2,z3,z4])],[(0,[z6,z71,z16,z2,z3,z4]),(0,[z398,z10,z16,z2,z3,z17]),(0,[z10,z0,z1,z284,z3,z228]),(0,[z48,z123,z1,z2,z3,z17]),(0,[z399,z0,z1,z2,z3,z4])],[(0,[z234,z0,z36,z2,z297,z4]),(0,[z10,z0,z1,z2,z3,z400]),(0,[z10,z16,z2,z401,z3,z4]),(0,[z10,z16,z402,z2,z3,z17])],[(0,[z403,z36,z1,z2,z3,z17]),(0,[z0,z36,z1,z2,z404,z4]),(0,[z10,z405,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z406]),(0,[z407,z0,z1,z2,z3,z4])],[(0,[z10,z0,z408,z2,z3,z4]),(0,[z10,z0,z409,z2,z3,z4]),(0,[z10,z0,z300,z2,z3,z4]),(0,[z26,z0,z16,z2,z3,z4]),(0,[z10,z410,z16,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z411]),(0,[z10,z1,z2,z3,z139,z17])],[(0,[z36,z16,z402,z2,z3,z4]),(0,[z10,z0,z1,z2,z412,z4]),(0,[z10,z27,z0,z2,z3,z75]),(0,[z413,z0,z1,z2,z3,z4]),(0,[z10,z0,z414,z2,z3,z17]),(0,[z415,z189,z1,z2,z3,z4])]],
   [[(0,[z416,z36,z1,z2,z3,z17]),(1,[z143,z16,z2,z3,z4]),(0,[z48,z10,z16,z2,z3,z17]),(0,[z417,z0,z1,z2,z3,z4]),(0,[z183,z45,z1,z2,z3,z84]),(0,[z62,z87,z1,z2,z3,z4]),(0,[z0,z418,z1,z2,z3,z4])],[(0,[z10,z0,z1,z2,z419,z4]),(0,[z10,z183,z1,z2,z3,z420]),(0,[z10,z421,z1,z2,z3,z4])],[(0,[z36,z1,z2,z3,z4,z17]),(0,[z187,z0,z1,z2,z3,z84]),(0,[z20,z422,z1,z2,z3,z4]),(0,[z0,z423,z1,z2,z3,z4])],[(1,[z36,z1,z2,z3,z424]),(0,[z10,z425,z1,z2,z3,z17]),(0,[z10,z0,z1,z2,z426,z4]),(0,[z10,z0,z1,z427,z3,z4]),(0,[z10,z1,z2,z3,z17,z428]),(0,[z10,z429,z0,z2,z3,z84]),(0,[z10,z0,z1,z430,z3,z172])],[(0,[z27,z36,z1,z2,z3,z17]),(0,[z10,z0,z1,z2,z3,z431]),(0,[z292,z10,z16,z2,z3,z17]),(0,[z10,z166,z1,z2,z3,z17]),(0,[z0,z1,z2,z3,z4,z432])],[(0,[z59,z0,z77,z2,z3,z40]),(0,[z10,z27,z0,z284,z3,z4]),(0,[z10,z0,z433,z2,z3,z4]),(0,[z10,z0,z1,z2,z214,z4]),(1,[z10,z0,z1,z430,z3])],[(0,[z36,z1,z385,z2,z3,z4]),(0,[z0,z36,z1,z2,z74,z4]),(0,[z10,z0,z434,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z312]),(0,[z0,z1,z2,z3,z4,z435])],[(0,[z10,z27,z36,z2,z3,z17]),(0,[z10,z71,z16,z72,z3,z4]),(0,[z436,z0,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z437]),(0,[z162,z0,z1,z2,z74,z4]),(0,[z10,z234,z189,z2,z3,z4]),(0,[z438,z0,z1,z2,z3,z4])],[(0,[z10,z16,z2,z202,z3,z17]),(0,[z10,z0,z1,z2,z3,z439]),(0,[z10,z0,z1,z2,z440,z4]),(0,[z10,z178,z16,z2,z3,z4]),(0,[z10,z71,z1,z441,z3,z4])],[(0,[z442,z0,z1,z2,z3,z40]),(0,[z10,z0,z16,z2,z3,z443]),(0,[z10,z27,z16,z2,z3,z84]),(0,[z10,z444,z16,z2,z46,z4]),(0,[z22,z27,z0,z2,z3,z4]),(0,[z376,z0,z1,z2,z3,z17])],[(0,[z10,z1,z16,z2,z3,z25]),(0,[z93,z0,z16,z2,z94,z4]),(0,[z22,z289,z1,z2,z3,z4]),(0,[z10,z16,z2,z3,z142,z17]),(0,[z10,z445,z1,z2,z3,z4]),(0,[z10,z0,z1,z446,z3,z4])],[(0,[z36,z16,z2,z202,z3,z4]),(0,[z10,z0,z192,z2,z3,z84]),(0,[z10,z0,z447,z2,z3,z4])],[(0,[z0,z36,z1,z2,z3,z4]),(0,[z0,z70,z1,z2,z3,z4]),(0,[z10,z0,z16,z2,z3,z102]),(0,[z10,z448,z0,z2,z3,z4]),(0,[z10,z0,z1,z171,z3,z449])],[(0,[z30,z0,z36,z2,z3,z4]),(0,[z153,z6,z0,z1,z4,z79]),(0,[z162,z0,z1,z2,z3,z4]),(0,[z10,z450,z16,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z451]),(0,[z10,z98,z16,z2,z3,z17]),(0,[z10,z0,z2,z3,z179,z452]),(0,[z10,z0,z1,z430,z3,z4])],[(0,[z379,z36,z1,z2,z3,z4]),(0,[z69,z36,z1,z2,z3,z17]),(0,[z10,z453,z0,z1,z2,z3])],[(0,[z454,z36,z16,z2,z3,z4]),(0,[z36,z1,z2,z3,z17,z17]),(0,[z36,z1,z2,z3,z17,z41]),(0,[z10,z108,z77,z2,z3,z4]),(0,[z143,z0,z16,z2,z3,z4]),(0,[z22,z183,z16,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z455]),(0,[z20,z10,z1,z2,z3,z31])]],
   [[(0,[z89,z36,z1,z2,z3,z4]),(0,[z0,z36,z185,z2,z3,z4]),(0,[z104,z36,z1,z2,z3,z4]),(0,[z10,z456,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z424]),(0,[z240,z0,z1,z2,z3,z76]),(0,[z457,z0,z1,z2,z3,z4]),(0,[z197,z104,z1,z2,z3,z4])],[(0,[z137,z36,z1,z2,z3,z4]),(0,[z0,z454,z1,z2,z94,z4]),(0,[z6,z116,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z458]),(0,[z0,z45,z16,z2,z3,z4]),(0,[z10,z1,z307,z2,z3,z17]),(0,[z459,z0,z1,z2,z3,z4]),(0,[z10,z460,z1,z2,z3,z4])],[(1,[z36,z23,z2,z3,z4]),(0,[z10,z0,z1,z341,z2,z3]),(0,[z10,z1,z2,z3,z420,z17]),(0,[z119,z0,z1,z2,z107,z4]),(0,[z461,z10,z0,z1,z4,z79]),(0,[z462,z10,z0,z1,z463,z3]),(0,[z10,z0,z2,z3,z464,z4])],[(0,[z10,z259,z16,z2,z3,z4]),(0,[z6,z0,z1,z2,z3,z128]),(0,[z93,z0,z1,z2,z107,z4]),(0,[z10,z104,z1,z2,z3,z4]),(0,[z101,z0,z135,z2,z3,z4])],[(0,[z10,z0,z1,z2,z3,z25]),(0,[z6,z105,z1,z2,z3,z4]),(0,[z10,z465,z0,z2,z3,z4]),(0,[z10,z416,z0,z2,z3,z179]),(0,[z10,z234,z0,z2,z297,z84]),(0,[z10,z0,z1,z2,z3,z466])],[(0,[z10,z467,z1,z2,z3,z4]),(0,[z157,z10,z16,z181,z3,z4]),(0,[z468,z10,z0,z2,z3,z469]),(0,[z10,z1,z2,z3,z4,z470])],[(0,[z10,z471,z1,z2,z3,z17]),(0,[z10,z87,z1,z2,z3,z56]),(0,[z10,z2,z3,z4,z154,z230])],[(0,[z10,z133,z16,z2,z3,z17]),(0,[z158,z10,z1,z90,z91,z4]),(0,[z10,z429,z0,z2,z3,z17])],[(0,[z6,z472,z1,z2,z3,z4]),(0,[z10,z0,z295,z2,z3,z84]),(0,[z48,z10,z295,z2,z3,z17]),(0,[z20,z10,z1,z2,z3,z84]),(0,[z10,z0,z1,z2,z74,z290]),(0,[z388,z104,z1,z2,z3,z4])],[(0,[z6,z473,z1,z2,z3,z4]),(0,[z474,z10,z1,z2,z3,z17]),(0,[z475,z0,z1,z2,z3,z4]),(0,[z97,z0,z1,z2,z3,z476])],[(0,[z477,z0,z1,z2,z3,z4]),(1,[z10,z1,z243,z3,z4]),(0,[z478,z0,z1,z2,z3,z4])],[(0,[z10,z0,z194,z2,z3,z12]),(0,[z6,z0,z1,z2,z3,z56]),(0,[z6,z0,z1,z171,z3,z172]),(0,[z10,z16,z2,z3,z172,z17]),(0,[z10,z0,z1,z479,z3,z4]),(0,[z10,z0,z1,z480,z3,z4]),(0,[z481,z0,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z482])],[(0,[z10,z0,z16,z2,z184,z4]),(0,[z240,z183,z1,z2,z3,z4]),(0,[z10,z27,z0,z2,z3,z43]),(0,[z159,z0,z1,z2,z91,z4]),(0,[z57,z0,z1,z2,z33,z3])],[(0,[z367,z0,z1,z2,z3,z4])],[(0,[z36,z1,z2,z3,z4,z287]),(0,[z10,z483,z0,z1,z2,z3]),(0,[z10,z0,z1,z2,z484,z4]),(0,[z10,z272,z16,z2,z3,z4]),(0,[z162,z0,z1,z2,z214,z4]),(0,[z10,z0,z1,z2,z3,z290])],[(0,[z92,z36,z1,z2,z3,z17]),(1,[z10,z16,z181,z3,z4]),(0,[z10,z44,z138,z2,z3,z4]),(0,[z10,z0,z192,z2,z3,z17]),(0,[z485,z0,z1,z2,z3,z4])]],
   [[(0,[z10,z211,z0,z2,z3,z4]),(0,[z10,z486,z0,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z487]),(0,[z10,z0,z1,z2,z3,z488]),(0,[z10,z489,z0,z2,z3,z4]),(0,[z10,z0,z490,z2,z3,z4])],[(0,[z10,z16,z2,z94,z3,z17]),(0,[z42,z0,z1,z2,z3,z84]),(0,[z10,z403,z0,z1,z2,z236])],[(0,[z10,z0,z491,z2,z3,z4]),(0,[z492,z36,z16,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z493]),(0,[z10,z0,z1,z2,z3,z494]),(0,[z10,z16,z2,z3,z40,z17]),(0,[z0,z1,z2,z3,z142,z495])],[(0,[z36,z1,z2,z3,z4,z496]),(0,[z42,z0,z1,z2,z3,z43]),(0,[z10,z324,z1,z2,z3,z84]),(0,[z10,z2,z3,z4,z497,z230])],[(0,[z10,z85,z1,z2,z3,z17]),(0,[z10,z27,z0,z2,z3,z65]),(0,[z57,z27,z0,z2,z3,z4]),(0,[z10,z160,z0,z2,z3,z84]),(0,[z10,z498,z0,z2,z3,z4])],[(0,[z10,z36,z1,z2,z3,z424]),(0,[z10,z27,z0,z2,z3,z76]),(0,[z158,z10,z1,z243,z3,z4]),(0,[z55,z0,z1,z2,z3,z476])],[(0,[z281,z36,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z91,z205]),(0,[z10,z0,z1,z181,z3,z43]),(0,[z499,z0,z1,z2,z3,z4])],[(0,[z10,z0,z194,z2,z3,z84]),(0,[z98,z36,z1,z2,z3,z17]),(0,[z500,z0,z1,z2,z3,z4]),(0,[z10,z164,z0,z2,z3,z84]),(0,[z10,z0,z266,z2,z3,z17])],[(0,[z10,z0,z1,z2,z3,z501]),(0,[z0,z36,z1,z2,z3,z424]),(0,[z10,z0,z1,z2,z404,z4]),(0,[z6,z0,z1,z2,z3,z205]),(0,[z83,z10,z1,z90,z3,z4]),(0,[z10,z0,z502,z2,z3,z4]),(0,[z10,z234,z0,z2,z297,z17])],[(0,[z442,z0,z1,z2,z3,z503]),(0,[z187,z88,z1,z2,z3,z4]),(0,[z10,z87,z27,z2,z3,z4]),(0,[z504,z0,z1,z2,z3,z4]),(0,[z10,z505,z1,z2,z3,z4])],[(0,[z10,z108,z1,z2,z3,z17]),(0,[z10,z0,z1,z2,z3,z506]),(0,[z10,z16,z2,z3,z507,z4]),(0,[z10,z508,z1,z2,z3,z230])],[(0,[z398,z36,z16,z2,z3,z4]),(0,[z36,z1,z2,z3,z17,z287]),(0,[z509,z36,z1,z2,z3,z17]),(0,[z6,z88,z311,z2,z3,z4]),(0,[z106,z339,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z510,z3]),(0,[z10,z0,z511,z2,z3,z4]),(0,[z10,z16,z2,z512,z3,z17]),(0,[z10,z0,z513,z2,z3,z179])],[(0,[z0,z36,z1,z2,z3,z25]),(0,[z10,z16,z2,z3,z4,z469]),(0,[z10,z0,z216,z2,z3,z4]),(0,[z260,z10,z0,z1,z3,z293]),(0,[z10,z0,z1,z2,z3,z514]),(0,[z10,z189,z1,z2,z3,z56]),(0,[z515,z0,z1,z2,z3,z4])],[(0,[z516,z0,z1,z2,z3,z4]),(1,[z6,z16,z2,z3,z17]),(0,[z42,z0,z138,z2,z3,z4])],[(0,[z108,z36,z1,z2,z3,z4]),(0,[z517,z27,z0,z2,z3,z4]),(0,[z518,z10,z27,z0,z199,z3]),(0,[z10,z0,z519,z2,z3,z4]),(0,[z520,z0,z1,z2,z3,z4])],[(0,[z10,z0,z521,z2,z3,z4]),(0,[z522,z36,z1,z2,z3,z4]),(0,[z10,z116,z1,z2,z3,z221]),(0,[z10,z0,z1,z2,z3,z523]),(0,[z524,z0,z1,z2,z3,z4]),(0,[z10,z16,z2,z525,z3,z4]),(0,[z10,z71,z16,z2,z3,z73]),(0,[z526,z27,z0,z2,z3,z4]),(0,[z10,z27,z133,z0,z2,z134]),(0,[z49,z0,z1,z2,z3,z84]),(0,[z26,z0,z1,z2,z3,z84]),(0,[z153,z10,z0,z1,z84,z79]),(0,[z10,z0,z1,z2,z214,z290])]],
   [[(0,[z48,z36,z16,z2,z3,z4]),(0,[z136,z36,z1,z2,z3,z17]),(0,[z10,z0,z527,z2,z3,z4]),(0,[z10,z528,z16,z2,z3,z4]),(0,[z10,z416,z0,z2,z3,z496]),(1,[z10,z0,z2,z3,z452])],[(0,[z153,z0,z36,z1,z4,z79]),(0,[z6,z248,z16,z2,z3,z4]),(0,[z10,z529,z1,z2,z3,z4]),(0,[z10,z530,z1,z2,z3,z4]),(0,[z378,z27,z0,z2,z3,z4]),(0,[z531,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z532])],[(0,[z339,z36,z16,z2,z3,z4]),(0,[z10,z7,z16,z2,z3,z4]),(0,[z10,z16,z171,z2,z3,z17]),(0,[z86,z10,z0,z2,z3,z469]),(0,[z207,z0,z216,z2,z3,z4]),(0,[z533,z0,z1,z2,z3,z4]),(0,[z10,z211,z0,z2,z3,z312])],[(0,[z151,z36,z1,z2,z3,z17]),(0,[z6,z0,z1,z2,z3,z256]),(0,[z10,z16,z2,z534,z3,z4]),(0,[z8,z27,z0,z2,z3,z4]),(0,[z535,z0,z1,z2,z3,z17]),(0,[z10,z536,z1,z2,z3,z4])],[(0,[z292,z36,z16,z2,z3,z4]),(0,[z10,z36,z23,z2,z3,z4]),(0,[z6,z0,z1,z2,z33,z58]),(0,[z10,z183,z311,z2,z3,z4]),(0,[z0,z537,z1,z2,z3,z4]),(0,[z0,z538,z1,z2,z3,z4]),(0,[z10,z539,z1,z2,z3,z4])],[(0,[z6,z122,z1,z2,z3,z4]),(0,[z540,z0,z1,z2,z3,z4]),(0,[z42,z0,z1,z2,z3,z17]),(0,[z0,z1,z2,z3,z170,z17])],[(1,[z36,z16,z2,z3,z84]),(0,[z541,z0,z1,z2,z247,z4]),(0,[z542,z0,z1,z285,z3,z4]),(0,[z157,z6,z1,z2,z21,z4]),(0,[z10,z543,z0,z2,z3,z4]),(0,[z10,z133,z0,z1,z2,z544]),(0,[z34,z27,z0,z2,z3,z4])],[(0,[z10,z0,z16,z2,z3,z12]),(0,[z211,z0,z36,z2,z3,z4]),(0,[z6,z16,z2,z46,z3,z4]),(0,[z0,z1,z2,z3,z4,z545]),(0,[z0,z1,z39,z2,z3,z221]),(0,[z546,z10,z0,z2,z3,z4]),(0,[z10,z177,z1,z2,z3,z17]),(0,[z10,z379,z16,z2,z3,z4]),(0,[z10,z44,z27,z2,z3,z17]),(0,[z158,z210,z1,z90,z3,z4]),(0,[z162,z0,z1,z2,z3,z290]),(0,[z10,z0,z1,z2,z3,z547])],[(0,[z548,z0,z1,z2,z3,z4]),(0,[z518,z10,z16,z2,z3,z17]),(0,[z10,z71,z1,z72,z3,z84]),(0,[z10,z0,z1,z181,z3,z17]),(0,[z549,z0,z1,z2,z3,z4])],[(0,[z10,z550,z16,z2,z3,z4]),(0,[z101,z0,z1,z2,z3,z228]),(0,[z10,z133,z0,z1,z2,z551])],[(0,[z10,z0,z16,z2,z3,z31])],[(0,[z10,z0,z194,z2,z3,z17]),(0,[z6,z0,z110,z2,z3,z4]),(0,[z6,z88,z1,z2,z3,z420]),(0,[z10,z164,z0,z2,z3,z17]),(0,[z93,z0,z1,z2,z94,z84]),(0,[z10,z0,z552,z2,z3,z4]),(0,[z10,z0,z16,z2,z3,z66]),(0,[z10,z444,z0,z2,z553,z4]),(0,[z10,z27,z0,z2,z61,z4]),(0,[z554,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z84,z170]),(0,[z10,z0,z2,z464,z297,z4]),(0,[z555,z0,z1,z2,z3,z4]),(0,[z10,z556,z1,z2,z3,z4])],[(0,[z0,z36,z135,z2,z3,z4]),(0,[z557,z0,z1,z2,z558,z4]),(0,[z10,z0,z1,z2,z3,z559]),(0,[z10,z0,z303,z3,z4,z560]),(0,[z10,z0,z1,z2,z3,z476]),(0,[z561,z0,z1,z2,z3,z4])],[(0,[z36,z16,z2,z3,z562,z4]),(0,[z10,z563,z1,z2,z3,z4]),(0,[z10,z564,z16,z2,z3,z4]),(0,[z10,z27,z71,z72,z3,z4]),(0,[z10,z1,z72,z3,z4,z565]),(0,[z10,z0,z1,z2,z3,z566]),(0,[z153,z10,z0,z1,z4,z270])],[(0,[z36,z385,z16,z2,z3,z4]),(0,[z36,z1,z2,z3,z17,z302]),(0,[z133,z36,z1,z2,z3,z17]),(0,[z10,z0,z1,z2,z3,z567]),(0,[z10,z448,z16,z2,z3,z4]),(0,[z568,z0,z1,z2,z3,z4])],[(0,[z20,z6,z1,z2,z3,z4]),(0,[z10,z16,z2,z569,z3,z4]),(0,[z10,z105,z1,z2,z3,z570])]],
   [[(0,[z0,z571,z1,z2,z3,z4]),(0,[z143,z0,z1,z2,z3,z84]),(0,[z123,z0,z16,z2,z3,z4]),(0,[z10,z0,z572,z2,z3,z4])],[(0,[z157,z10,z318,z2,z3,z4]),(0,[z10,z416,z16,z2,z3,z17])],[(0,[z36,z16,z2,z3,z4,z79]),(0,[z541,z0,z1,z2,z220,z4]),(0,[z36,z16,z2,z3,z4,z40]),(0,[z10,z0,z573,z2,z3,z4]),(0,[z10,z574,z16,z2,z3,z4]),(0,[z0,z45,z1,z2,z3,z84]),(0,[z10,z1,z2,z3,z282,z230])],[(0,[z398,z0,z68,z2,z3,z4]),(0,[z106,z0,z300,z2,z3,z4]),(0,[z10,z0,z16,z2,z3,z84]),(0,[z101,z27,z0,z2,z3,z4]),(0,[z49,z0,z1,z2,z3,z17]),(0,[z26,z0,z1,z2,z3,z17]),(0,[z10,z410,z1,z2,z3,z17])],[(0,[z0,z36,z216,z2,z3,z4]),(0,[z6,z27,z0,z2,z3,z84]),(0,[z10,z16,z2,z575,z3,z17]),(0,[z10,z16,z2,z231,z3,z17]),(0,[z0,z70,z216,z2,z3,z4]),(0,[z10,z0,z1,z171,z430,z3])],[(0,[z166,z36,z1,z2,z3,z4]),(0,[z10,z576,z1,z2,z3,z4]),(0,[z10,z0,z16,z2,z3,z43])],[(0,[z10,z0,z1,z2,z3,z577]),(0,[z578,z0,z579,z2,z3,z4]),(0,[z10,z580,z0,z2,z3,z4])],[(1,[z0,z1,z581,z3,z4]),(0,[z45,z1,z16,z2,z3,z4]),(0,[z10,z0,z1,z582,z3,z449]),(0,[z20,z10,z2,z3,z4,z154])],[(0,[z10,z0,z1,z2,z3,z583]),(0,[z0,z1,z278,z581,z3,z4]),(0,[z10,z0,z1,z2,z3,z584])],[(0,[z6,z0,z23,z2,z3,z4]),(0,[z10,z27,z0,z2,z3,z128]),(0,[z0,z1,z2,z3,z4,z585])],[(1,[z36,z16,z2,z3,z17])],[(0,[z10,z16,z2,z586,z3,z4]),(0,[z10,z393,z16,z2,z3,z4])],[],[(0,[z71,z36,z1,z2,z3,z17]),(0,[z10,z0,z1,z2,z3,z587]),(0,[z10,z0,z1,z2,z3,z588])],[(0,[z10,z27,z339,z2,z3,z4]),(0,[z10,z257,z1,z2,z3,z17]),(0,[z10,z44,z1,z2,z3,z66]),(0,[z589,z0,z1,z2,z3,z4]),(0,[z10,z166,z2,z37,z3,z4]),(0,[z10,z234,z166,z2,z3,z4])],[(0,[z590,z36,z1,z2,z3,z4]),(0,[z137,z0,z1,z2,z3,z142]),(0,[z10,z16,z2,z3,z4,z565]),(0,[z42,z0,z1,z284,z3,z4]),(0,[z97,z189,z1,z2,z3,z4])]],
   [[(1,[z36,z11,z2,z3,z4]),(0,[z259,z36,z1,z2,z3,z17]),(0,[z36,z16,z2,z3,z142,z4]),(0,[z381,z0,z1,z2,z3,z283]),(0,[z10,z591,z16,z2,z3,z4]),(0,[z159,z0,z1,z2,z3,z109])],[(0,[z106,z0,z592,z2,z3,z4]),(0,[z10,z45,z16,z2,z3,z4]),(0,[z10,z27,z0,z171,z3,z172]),(0,[z10,z27,z0,z2,z3,z56])],[(0,[z36,z1,z2,z3,z562,z17]),(0,[z157,z10,z1,z2,z21,z84]),(0,[z0,z593,z1,z2,z3,z4])],[(0,[z10,z0,z594,z2,z3,z4]),(0,[z6,z339,z1,z2,z3,z4]),(0,[z10,z0,z595,z2,z3,z4])],[(0,[z454,z36,z1,z2,z3,z17]),(0,[z86,z36,z1,z2,z3,z17]),(0,[z0,z36,z1,z2,z3,z476]),(0,[z0,z36,z1,z2,z3,z221]),(0,[z153,z10,z16,z2,z3,z17]),(0,[z10,z16,z2,z596,z3,z4]),(0,[z159,z27,z0,z2,z3,z4]),(0,[z157,z10,z1,z2,z21,z43])],[(0,[z6,z1,z2,z3,z4,z230]),(0,[z10,z597,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z598,z3]),(0,[z599,z0,z1,z2,z3,z4]),(0,[z333,z0,z1,z2,z3,z562]),(0,[z10,z30,z0,z2,z74,z4])],[(0,[z10,z600,z1,z2,z3,z4])],[(0,[z10,z0,z16,z2,z3,z17]),(0,[z10,z0,z601,z402,z3,z4]),(0,[z26,z0,z1,z2,z3,z75])],[(0,[z10,z36,z16,z2,z3,z84]),(0,[z6,z27,z0,z2,z3,z17]),(0,[z48,z6,z1,z2,z3,z17]),(0,[z10,z0,z1,z2,z3,z602]),(0,[z10,z44,z1,z2,z3,z43]),(0,[z207,z0,z1,z2,z3,z73]),(0,[z123,z0,z295,z2,z3,z4]),(0,[z10,z30,z0,z2,z512,z4]),(0,[z20,z10,z603,z2,z3,z4]),(0,[z10,z604,z0,z2,z3,z4])],[(0,[z10,z605,z16,z2,z3,z4]),(0,[z187,z0,z1,z2,z3,z17]),(0,[z20,z10,z1,z90,z3,z4])],[(0,[z207,z27,z0,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z606]),(0,[z10,z0,z1,z4,z270,z79])],[(0,[z210,z0,z1,z2,z3,z4]),(0,[z0,z36,z16,z2,z3,z84]),(0,[z6,z0,z1,z2,z74,z4]),(0,[z10,z0,z1,z2,z3,z607]),(0,[z10,z27,z0,z2,z3,z213]),(0,[z10,z30,z0,z2,z3,z4]),(0,[z10,z0,z2,z512,z4,z608]),(0,[z609,z0,z1,z2,z3,z4]),(0,[z55,z189,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z610])],[(0,[z44,z36,z1,z2,z3,z4]),(0,[z10,z492,z339,z2,z3,z4]),(0,[z140,z0,z39,z2,z3,z102]),(0,[z10,z0,z1,z611,z2,z3]),(0,[z10,z87,z1,z2,z3,z4]),(0,[z10,z16,z2,z612,z3,z4]),(0,[z153,z10,z0,z16,z4,z79]),(0,[z44,z70,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z613]),(0,[z10,z0,z1,z2,z3,z614]),(0,[z166,z328,z1,z2,z3,z4])],[(0,[z10,z0,z11,z2,z3,z4]),(1,[z10,z311,z2,z3,z17]),(0,[z10,z92,z1,z2,z46,z4]),(0,[z10,z0,z1,z199,z430,z3])],[(0,[z6,z1,z2,z3,z84,z17]),(0,[z6,z133,z0,z1,z2,z134]),(0,[z10,z0,z95,z2,z3,z4]),(0,[z10,z27,z0,z2,z3,z205]),(0,[z157,z10,z138,z2,z21,z4]),(1,[z10,z0,z615,z3,z4]),(0,[z0,z2,z3,z4,z154,z149]),(0,[z10,z0,z616,z2,z3,z4])],[(0,[z203,z0,z39,z2,z3,z4]),(0,[z6,z0,z369,z2,z3,z4]),(0,[z10,z617,z1,z2,z3,z4]),(0,[z10,z0,z618,z2,z3,z4]),(0,[z34,z0,z16,z2,z3,z4]),(0,[z210,z0,z185,z2,z3,z4]),(0,[z10,z0,z1,z2,z91,z4]),(0,[z20,z10,z30,z2,z3,z4])]],
   [[(0,[z10,z0,z619,z2,z3,z4]),(0,[z10,z27,z16,z2,z3,z17]),(0,[z10,z44,z1,z2,z3,z65]),(0,[z10,z27,z620,z2,z3,z4]),(0,[z10,z621,z1,z2,z3,z4])],[(0,[z6,z0,z1,z2,z3,z4]),(0,[z10,z138,z16,z2,z3,z4]),(0,[z10,z1,z2,z3,z622,z17]),(0,[z623,z1,z2,z3,z4,z230])],[(0,[z36,z16,z624,z2,z3,z4]),(0,[z36,z16,z2,z3,z4,z503]),(0,[z0,z36,z1,z2,z3,z228]),(0,[z10,z16,z2,z90,z3,z84]),(0,[z10,z416,z0,z2,z3,z625]),(0,[z626,z0,z1,z2,z3,z4])],[(0,[z36,z1,z2,z202,z3,z17]),(0,[z627,z0,z1,z202,z3,z4]),(0,[z628,z0,z1,z2,z3,z40]),(0,[z10,z0,z185,z2,z91,z4]),(0,[z629,z0,z1,z2,z3,z4])],[(0,[z630,z0,z1,z2,z113,z4]),(0,[z119,z0,z16,z2,z220,z4]),(0,[z10,z0,z1,z2,z3,z631]),(0,[z10,z27,z632,z2,z3,z4]),(0,[z0,z261,z266,z2,z3,z4])],[(0,[z6,z0,z185,z2,z3,z4]),(0,[z633,z0,z1,z2,z3,z40]),(0,[z10,z143,z16,z2,z3,z4]),(0,[z10,z16,z2,z634,z3,z4]),(0,[z10,z27,z0,z2,z3,z242]),(0,[z210,z0,z1,z2,z3,z205]),(0,[z10,z183,z1,z2,z3,z139])],[(0,[z10,z0,z1,z2,z3,z635]),(0,[z157,z10,z1,z2,z21,z17]),(0,[z10,z1,z2,z634,z3,z84]),(0,[z10,z0,z636,z2,z3,z179]),(0,[z10,z0,z637,z2,z3,z4]),(0,[z30,z0,z2,z3,z4,z149]),(0,[z10,z0,z1,z2,z3,z638])],[(0,[z10,z0,z1,z2,z3,z420]),(0,[z36,z16,z2,z94,z3,z4]),(0,[z10,z0,z639,z2,z3,z4]),(0,[z10,z0,z135,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z640])],[(0,[z518,z36,z16,z2,z3,z4]),(0,[z10,z0,z1,z641,z3,z4]),(0,[z642,z10,z16,z2,z3,z4])],[(0,[z10,z0,z1,z581,z3,z4]),(0,[z10,z27,z0,z2,z3,z256]),(0,[z10,z0,z1,z2,z3,z643])],[(0,[z10,z88,z16,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z644]),(0,[z0,z36,z1,z2,z3,z73]),(0,[z518,z6,z0,z1,z199,z3]),(0,[z10,z645,z16,z2,z3,z4]),(0,[z10,z44,z1,z2,z3,z17]),(1,[z240,z1,z2,z3,z17]),(0,[z10,z27,z0,z2,z33,z58]),(0,[z0,z70,z1,z2,z3,z73]),(0,[z161,z10,z0,z37,z3,z84])],[(0,[z10,z1,z2,z3,z148,z17]),(0,[z10,z0,z16,z2,z3,z75]),(0,[z10,z646,z1,z2,z3,z4])],[(0,[z10,z36,z16,z2,z3,z17])],[(0,[z647,z0,z1,z2,z3,z4]),(0,[z623,z0,z1,z2,z3,z4]),(0,[z10,z0,z77,z2,z3,z84]),(0,[z10,z392,z1,z2,z3,z84]),(0,[z10,z166,z1,z2,z3,z4]),(0,[z10,z166,z1,z2,z3,z375]),(0,[z10,z648,z1,z2,z3,z4])],[(0,[z36,z1,z2,z649,z3,z4]),(0,[z650,z0,z1,z2,z3,z4]),(0,[z10,z1,z2,z3,z507,z84])],[(0,[z0,z36,z16,z2,z3,z17]),(0,[z0,z36,z311,z2,z3,z4]),(0,[z27,z0,z2,z3,z4,z170]),(0,[z0,z261,z1,z2,z3,z147]),(0,[z10,z92,z1,z2,z46,z312]),(0,[z10,z0,z1,z651,z82,z4]),(0,[z10,z0,z295,z2,z3,z17]),(0,[z137,z0,z1,z2,z3,z156]),(0,[z20,z10,z1,z2,z3,z17]),(0,[z10,z0,z1,z2,z32,z58])]],
   [[(0,[z10,z0,z1,z2,z3,z652]),(0,[z10,z133,z0,z95,z2,z3]),(0,[z10,z0,z1,z2,z3,z653]),(0,[z20,z654,z1,z2,z3,z4])],[(0,[z36,z16,z2,z512,z3,z4]),(0,[z10,z339,z1,z2,z3,z221]),(0,[z10,z349,z1,z2,z3,z17]),(0,[z10,z0,z16,z284,z3,z4]),(0,[z10,z44,z27,z2,z3,z76]),(0,[z10,z27,z122,z2,z3,z4]),(0,[z10,z160,z0,z2,z3,z65]),(0,[z123,z0,z1,z2,z3,z84]),(0,[z384,z166,z1,z2,z3,z4])],[(0,[z124,z36,z1,z2,z3,z4]),(0,[z10,z36,z11,z2,z3,z4]),(0,[z36,z16,z2,z655,z3,z4]),(0,[z6,z0,z1,z2,z214,z4]),(0,[z187,z116,z1,z2,z3,z4]),(0,[z10,z189,z1,z2,z3,z4])],[(0,[z6,z0,z1,z2,z3,z312]),(0,[z10,z16,z2,z3,z4,z25]),(0,[z69,z0,z1,z656,z3,z4]),(0,[z121,z27,z0,z2,z3,z4]),(0,[z10,z657,z0,z1,z2,z3])],[(0,[z10,z339,z1,z2,z3,z658]),(0,[z0,z659,z1,z2,z3,z4]),(0,[z48,z10,z1,z2,z3,z139]),(0,[z660,z0,z1,z2,z3,z4]),(0,[z161,z10,z0,z615,z3,z4]),(0,[z10,z63,z1,z2,z3,z230]),(0,[z0,z661,z1,z2,z3,z4])],[(0,[z0,z36,z11,z2,z3,z4]),(0,[z10,z27,z88,z2,z3,z17]),(0,[z22,z0,z16,z2,z3,z4]),(0,[z10,z16,z2,z662,z3,z4])],[(0,[z6,z36,z1,z2,z3,z4]),(0,[z36,z1,z2,z3,z172,z17]),(0,[z0,z36,z95,z2,z3,z4]),(0,[z10,z104,z16,z2,z3,z17])],[(0,[z0,z36,z1,z2,z91,z4]),(0,[z36,z1,z624,z2,z3,z17]),(0,[z10,z663,z1,z2,z3,z17]),(0,[z10,z664,z1,z2,z3,z4]),(0,[z10,z7,z1,z2,z3,z17]),(0,[z0,z1,z2,z94,z4,z665]),(0,[z10,z0,z303,z615,z3,z4]),(0,[z10,z666,z1,z2,z3,z4])],[(0,[z36,z16,z171,z2,z3,z4]),(0,[z44,z36,z1,z2,z3,z424]),(0,[z10,z0,z1,z2,z3,z667]),(0,[z10,z403,z16,z2,z3,z17]),(0,[z10,z129,z16,z2,z3,z17]),(0,[z10,z591,z0,z130,z3,z4]),(0,[z22,z429,z0,z2,z3,z4])],[(0,[z668,z36,z1,z2,z3,z4]),(0,[z10,z304,z16,z2,z3,z4]),(0,[z10,z601,z16,z90,z3,z4]),(0,[z10,z71,z1,z243,z3,z4]),(0,[z10,z0,z1,z2,z3,z669]),(0,[z105,z670,z1,z2,z3,z4])],[(1,[z0,z1,z2,z3,z495]),(0,[z10,z0,z1,z2,z3,z671]),(0,[z10,z0,z1,z672,z3,z4])],[(0,[z10,z0,z673,z2,z3,z4]),(0,[z143,z0,z1,z2,z3,z66]),(0,[z10,z160,z0,z2,z3,z17]),(0,[z674,z0,z1,z2,z3,z4]),(0,[z675,z0,z1,z2,z3,z4])],[(0,[z36,z1,z2,z94,z3,z17]),(0,[z10,z0,z1,z2,z3,z676]),(0,[z10,z0,z677,z2,z3,z17]),(0,[z678,z0,z1,z2,z3,z4])],[(0,[z6,z0,z1,z2,z3,z424]),(0,[z10,z16,z16,z2,z3,z17]),(0,[z10,z0,z16,z2,z3,z679]),(0,[z189,z680,z1,z2,z3,z4])],[(1,[z123,z1,z2,z3,z17]),(0,[z161,z10,z0,z37,z3,z17]),(0,[z10,z0,z1,z2,z3,z681]),(0,[z10,z166,z1,z2,z214,z4]),(0,[z10,z0,z1,z2,z3,z682]),(0,[z683,z0,z1,z2,z3,z4]),(0,[z10,z393,z189,z2,z3,z4])],[(0,[z0,z36,z1,z2,z3,z420]),(0,[z10,z0,z1,z2,z3,z221]),(0,[z10,z684,z0,z1,z2,z3]),(0,[z685,z0,z1,z2,z3,z17])]],
   [[(0,[z686,z183,z1,z2,z3,z4]),(0,[z6,z104,z1,z2,z3,z4]),(0,[z55,z27,z0,z2,z3,z4]),(0,[z10,z0,z138,z2,z3,z84]),(0,[z157,z10,z1,z284,z21,z4]),(0,[z20,z1,z2,z3,z4,z149])],[(0,[z6,z0,z1,z2,z3,z25]),(0,[z106,z0,z1,z2,z3,z221]),(0,[z10,z0,z1,z2,z3,z687]),(0,[z10,z0,z1,z2,z3,z688]),(0,[z689,z0,z1,z2,z3,z4])],[(0,[z10,z0,z1,z2,z690,z4]),(0,[z240,z0,z1,z2,z3,z4]),(0,[z106,z0,z691,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z658]),(0,[z10,z116,z1,z2,z3,z692]),(0,[z10,z0,z1,z2,z3,z693])],[(0,[z10,z16,z2,z3,z4,z156]),(0,[z158,z10,z192,z90,z3,z4]),(0,[z22,z183,z1,z2,z3,z84]),(0,[z10,z0,z1,z2,z3,z694]),(0,[z10,z1,z2,z569,z3,z84])],[(0,[z153,z36,z16,z2,z3,z4]),(0,[z6,z695,z1,z2,z3,z4]),(0,[z10,z696,z0,z2,z3,z4]),(0,[z376,z0,z1,z2,z3,z312])],[(0,[z36,z1,z2,z3,z507,z4]),(0,[z273,z0,z39,z2,z3,z4]),(0,[z10,z697,z1,z2,z3,z4]),(0,[z10,z71,z1,z72,z3,z65]),(0,[z10,z189,z1,z2,z3,z437]),(0,[z0,z698,z1,z2,z3,z4])],[(0,[z36,z1,z2,z512,z3,z17]),(0,[z699,z0,z1,z2,z3,z40]),(0,[z10,z0,z1,z2,z3,z700]),(0,[z49,z0,z110,z2,z3,z4]),(0,[z162,z166,z1,z2,z3,z4])],[(0,[z36,z1,z2,z3,z4,z424]),(0,[z701,z36,z1,z2,z3,z4]),(0,[z10,z701,z16,z2,z3,z4]),(0,[z51,z0,z1,z2,z3,z4]),(0,[z10,z591,z166,z2,z3,z4])],[(0,[z159,z0,z192,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z139]),(0,[z702,z0,z1,z2,z3,z4]),(0,[z55,z87,z1,z2,z3,z4])],[(0,[z59,z0,z1,z2,z3,z40]),(0,[z703,z10,z0,z401,z3,z4]),(0,[z10,z0,z1,z2,z3,z704])],[(0,[z36,z16,z2,z575,z3,z4]),(0,[z10,z88,z16,z2,z3,z25]),(0,[z10,z0,z1,z705,z3,z4]),(0,[z10,z0,z1,z2,z706,z4]),(0,[z10,z707,z0,z2,z3,z4]),(0,[z27,z0,z261,z2,z3,z4])],[(0,[z6,z483,z0,z1,z2,z3]),(0,[z6,z0,z1,z2,z3,z290]),(0,[z10,z708,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z78,z3]),(0,[z10,z30,z2,z3,z4,z230])],[(0,[z392,z36,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z570])],[(0,[z10,z136,z1,z2,z3,z17]),(0,[z6,z211,z0,z2,z3,z4]),(0,[z10,z0,z1,z2,z709,z4]),(0,[z69,z0,z1,z278,z3,z4]),(0,[z10,z0,z1,z2,z710,z4]),(0,[z59,z711,z0,z1,z2,z3]),(0,[z0,z1,z2,z3,z495,z40]),(0,[z10,z0,z1,z2,z712,z4]),(0,[z10,z0,z1,z2,z3,z228]),(0,[z10,z0,z1,z2,z713,z4]),(0,[z10,z0,z357,z2,z3,z452])],[(0,[z518,z0,z36,z1,z199,z3]),(0,[z201,z0,z1,z581,z3,z4]),(0,[z158,z10,z1,z90,z3,z109]),(0,[z10,z0,z1,z2,z3,z714])],[(0,[z10,z88,z1,z2,z3,z12]),(0,[z140,z0,z300,z2,z3,z4]),(0,[z10,z601,z16,z2,z3,z17]),(0,[z10,z71,z1,z72,z3,z17])]],
   [[(0,[z119,z0,z1,z2,z558,z4]),(0,[z10,z0,z715,z2,z3,z4]),(0,[z10,z0,z16,z2,z3,z65]),(0,[z250,z0,z16,z2,z3,z4]),(0,[z57,z0,z16,z2,z3,z4]),(0,[z10,z16,z303,z2,z3,z17]),(0,[z10,z0,z266,z2,z3,z4]),(0,[z10,z0,z1,z2,z184,z84]),(0,[z716,z0,z1,z2,z3,z4]),(0,[z101,z0,z1,z181,z3,z4])],[(0,[z541,z36,z16,z2,z3,z4]),(0,[z27,z0,z36,z2,z3,z84]),(0,[z6,z0,z135,z2,z3,z4]),(0,[z161,z6,z0,z37,z3,z4]),(0,[z10,z16,z2,z181,z3,z4]),(0,[z10,z0,z16,z2,z3,z76]),(0,[z10,z27,z0,z2,z74,z4]),(0,[z10,z0,z717,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z718])],[(1,[z339,z39,z2,z3,z4]),(0,[z10,z0,z719,z2,z3,z4]),(0,[z93,z0,z1,z2,z94,z17]),(0,[z10,z0,z192,z2,z3,z205]),(0,[z10,z0,z720,z2,z3,z4]),(0,[z161,z10,z0,z37,z3,z75]),(0,[z10,z0,z1,z3,z4,z270])],[(0,[z10,z108,z1,z2,z3,z4]),(0,[z10,z0,z721,z2,z3,z4]),(0,[z140,z0,z39,z2,z3,z84]),(0,[z187,z0,z1,z2,z3,z76]),(0,[z10,z0,z1,z2,z3,z109]),(0,[z654,z0,z1,z2,z3,z4])],[(0,[z6,z44,z1,z2,z3,z17]),(0,[z197,z27,z0,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z722]),(0,[z10,z0,z138,z2,z3,z17]),(0,[z10,z0,z723,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z724]),(0,[z10,z0,z725,z2,z3,z4]),(0,[z10,z726,z0,z2,z3,z4])],[(0,[z442,z36,z16,z2,z3,z4]),(0,[z119,z0,z1,z2,z220,z84]),(0,[z10,z0,z1,z2,z3,z73]),(0,[z10,z0,z1,z2,z3,z727]),(0,[z10,z728,z0,z2,z3,z4])],[(0,[z183,z36,z16,z2,z3,z4]),(0,[z157,z36,z1,z2,z21,z4]),(0,[z10,z0,z1,z2,z3,z729]),(0,[z10,z580,z108,z2,z3,z4]),(0,[z10,z0,z16,z2,z3,z730]),(0,[z10,z27,z178,z2,z3,z4]),(0,[z10,z668,z1,z2,z3,z17]),(0,[z10,z0,z129,z303,z3,z4]),(0,[z731,z0,z1,z2,z3,z4]),(0,[z10,z0,z2,z3,z452,z41])],[(0,[z10,z27,z0,z2,z3,z4]),(0,[z0,z732,z1,z2,z3,z4]),(0,[z36,z1,z39,z2,z3,z17]),(0,[z27,z143,z0,z2,z3,z4]),(0,[z143,z0,z1,z2,z3,z17]),(0,[z10,z16,z2,z236,z3,z17]),(0,[z10,z1,z16,z181,z3,z4]),(0,[z10,z16,z2,z3,z179,z17]),(0,[z10,z0,z185,z2,z3,z109]),(0,[z10,z166,z1,z2,z3,z290]),(0,[z10,z0,z1,z2,z3,z733])],[(0,[z10,z0,z734,z2,z3,z4]),(0,[z10,z289,z1,z2,z3,z4]),(0,[z10,z27,z513,z2,z3,z4])],[(0,[z6,z0,z216,z2,z3,z4]),(0,[z10,z735,z1,z2,z3,z4]),(0,[z628,z0,z39,z2,z3,z4]),(0,[z10,z0,z736,z2,z3,z4]),(0,[z0,z45,z1,z2,z3,z17]),(0,[z10,z0,z104,z2,z3,z41])],[(0,[z10,z0,z311,z2,z3,z4]),(0,[z36,z16,z2,z3,z179,z4]),(0,[z69,z0,z1,z737,z3,z4]),(0,[z13,z0,z1,z2,z3,z142]),(0,[z10,z0,z1,z2,z738,z739]),(0,[z10,z740,z1,z2,z3,z4])],[(0,[z10,z27,z105,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z147]),(1,[z10,z295,z2,z3,z17]),(1,[z197,z0,z2,z3,z41]),(0,[z0,z1,z2,z3,z4,z741])],[(0,[z10,z0,z1,z2,z3,z495]),(0,[z10,z44,z160,z2,z3,z4]),(0,[z535,z0,z1,z2,z3,z4]),(0,[z742,z0,z1,z2,z3,z4])],[(0,[z10,z183,z16,z2,z3,z4]),(0,[z378,z0,z16,z2,z3,z4]),(0,[z10,z429,z122,z2,z3,z4])],[(0,[z240,z0,z1,z2,z3,z424]),(0,[z10,z605,z1,z2,z3,z17])],[(0,[z36,z1,z2,z231,z3,z17]),(0,[z20,z36,z1,z2,z3,z4]),(0,[z743,z0,z36,z1,z2,z3]),(0,[z10,z0,z1,z2,z744,z3]),(0,[z10,z745,z16,z2,z3,z4]),(0,[z10,z1,z2,z243,z3,z4]),(0,[z10,z0,z1,z2,z746,z4]),(0,[z10,z0,z1,z2,z3,z747])]],
   [[(0,[z0,z36,z192,z2,z3,z4]),(0,[z36,z1,z23,z2,z3,z4]),(0,[z748,z0,z1,z737,z3,z4]),(0,[z10,z44,z27,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z749]),(0,[z750,z0,z1,z2,z3,z4])],[(0,[z10,z0,z1,z181,z3,z4])],[(0,[z10,z0,z1,z2,z3,z751]),(0,[z10,z0,z1,z284,z3,z84]),(0,[z10,z0,z266,z2,z3,z312]),(0,[z10,z295,z2,z3,z4,z17]),(0,[z26,z105,z1,z2,z3,z4]),(0,[z10,z0,z1,z171,z3,z752])],[(0,[z0,z36,z1,z2,z78,z3]),(0,[z10,z753,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z754,z4])],[(0,[z10,z755,z1,z2,z3,z4]),(0,[z10,z27,z108,z2,z3,z4]),(0,[z10,z0,z756,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z191]),(0,[z10,z0,z1,z2,z184,z17]),(0,[z10,z87,z1,z2,z3,z476])],[(0,[z27,z0,z36,z2,z3,z17]),(0,[z20,z10,z27,z2,z3,z4])],[(0,[z0,z68,z300,z2,z3,z4]),(0,[z201,z0,z1,z202,z3,z4]),(0,[z10,z16,z278,z2,z3,z17]),(0,[z398,z0,z307,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z757]),(0,[z153,z10,z0,z1,z4,z79])],[(0,[z140,z0,z39,z2,z3,z17]),(0,[z758,z10,z16,z2,z3,z4]),(0,[z153,z10,z63,z0,z1,z79])],[(0,[z0,z36,z266,z2,z3,z4]),(0,[z36,z1,z2,z3,z142,z17]),(0,[z248,z143,z16,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z759]),(0,[z10,z16,z72,z2,z3,z17]),(0,[z157,z10,z16,z2,z3,z84]),(0,[z10,z27,z0,z2,z214,z4]),(0,[z0,z1,z2,z33,z170,z58]),(0,[z760,z0,z1,z2,z3,z4])],[(0,[z36,z16,z278,z2,z3,z4]),(0,[z6,z0,z1,z2,z3,z476]),(0,[z119,z0,z1,z2,z220,z17]),(0,[z10,z27,z0,z2,z3,z312]),(0,[z87,z399,z1,z2,z3,z4]),(0,[z10,z416,z104,z2,z3,z4])],[(0,[z492,z36,z1,z2,z3,z17]),(1,[z10,z16,z2,z3,z66]),(0,[z10,z416,z16,z2,z3,z4]),(0,[z157,z10,z16,z2,z3,z43]),(0,[z436,z27,z0,z2,z3,z4]),(0,[z10,z166,z1,z2,z74,z4])],[(0,[z36,z16,z72,z2,z3,z4]),(0,[z0,z36,z1,z2,z3,z109]),(0,[z0,z454,z1,z2,z111,z4]),(0,[z10,z0,z1,z761,z3,z4]),(0,[z273,z10,z16,z2,z3,z17]),(0,[z10,z16,z762,z2,z3,z17]),(0,[z763,z0,z1,z2,z3,z4]),(0,[z10,z0,z414,z2,z3,z4]),(0,[z10,z0,z2,z512,z74,z4])],[(0,[z49,z0,z1,z2,z3,z4]),(0,[z764,z0,z1,z2,z3,z4])],[(0,[z10,z116,z1,z2,z3,z102]),(0,[z10,z0,z129,z615,z3,z4])],[(0,[z0,z36,z129,z303,z3,z4]),(0,[z10,z0,z138,z284,z3,z4]),(0,[z10,z0,z1,z2,z3,z765]),(0,[z10,z766,z1,z2,z3,z4])],[(0,[z10,z88,z1,z2,z3,z17]),(0,[z6,z0,z573,z2,z3,z4]),(0,[z578,z0,z39,z2,z3,z4]),(0,[z10,z767,z1,z2,z3,z4]),(0,[z101,z0,z16,z2,z3,z4]),(0,[z10,z0,z385,z2,z3,z148]),(1,[z10,z0,z1,z4,z270])]],
   [[(0,[z6,z0,z16,z2,z3,z84]),(0,[z10,z0,z1,z2,z3,z768]),(0,[z162,z27,z0,z2,z3,z4]),(0,[z769,z105,z1,z2,z3,z4])],[(0,[z10,z0,z95,z2,z3,z142]),(0,[z10,z0,z1,z2,z33,z739])],[(0,[z10,z0,z1,z2,z3,z770]),(0,[z36,z36,z16,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z170]),(0,[z143,z0,z1,z2,z3,z128])],[(0,[z0,z36,z1,z2,z3,z147]),(0,[z10,z116,z16,z2,z3,z4]),(0,[z10,z27,z0,z2,z3,z424]),(0,[z771,z0,z1,z2,z3,z4]),(0,[z772,z0,z1,z2,z3,z4])],[(0,[z10,z339,z39,z2,z3,z4]),(0,[z59,z0,z1,z2,z773,z3]),(1,[z10,z16,z2,z3,z43])],[(0,[z376,z0,z1,z2,z3,z4]),(0,[z203,z36,z16,z2,z3,z4]),(0,[z161,z0,z36,z37,z3,z4]),(0,[z106,z0,z68,z2,z3,z84]),(0,[z10,z0,z16,z2,z3,z128]),(0,[z10,z183,z295,z2,z3,z4]),(0,[z10,z87,z1,z2,z3,z588])],[(0,[z10,z0,z1,z2,z774,z3]),(0,[z10,z0,z1,z2,z3,z775]),(0,[z10,z0,z776,z2,z3,z4]),(0,[z10,z105,z16,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z777])],[(0,[z627,z36,z16,z2,z3,z4]),(0,[z10,z27,z0,z2,z3,z25]),(0,[z0,z339,z39,z2,z3,z4]),(0,[z10,z0,z2,z3,z4,z778]),(0,[z10,z779,z1,z2,z3,z17]),(0,[z780,z0,z1,z2,z3,z4]),(0,[z10,z0,z781,z2,z3,z4])],[(0,[z48,z36,z1,z2,z3,z17]),(0,[z10,z1,z2,z3,z562,z17]),(0,[z10,z0,z1,z782,z3,z4]),(0,[z10,z0,z1,z2,z3,z783]),(0,[z10,z1,z2,z3,z746,z4]),(0,[z10,z528,z1,z2,z3,z17]),(0,[z784,z0,z1,z2,z3,z4]),(0,[z378,z63,z0,z1,z2,z3]),(0,[z0,z785,z1,z2,z3,z4])],[(0,[z0,z36,z1,z181,z3,z4]),(0,[z10,z0,z786,z2,z3,z4]),(0,[z10,z16,z2,z90,z3,z17])],[(0,[z10,z0,z311,z2,z3,z25]),(0,[z10,z472,z16,z2,z3,z4]),(0,[z10,z0,z1,z762,z3,z302]),(0,[z0,z787,z1,z2,z3,z4]),(0,[z10,z189,z1,z2,z3,z476]),(0,[z10,z0,z1,z2,z3,z788])],[(0,[z10,z0,z1,z2,z3,z789]),(0,[z10,z473,z16,z2,z3,z4]),(0,[z158,z10,z16,z90,z3,z4]),(0,[z10,z16,z2,z3,z790,z4])],[(0,[z36,z16,z2,z90,z3,z4]),(0,[z10,z0,z791,z2,z3,z4]),(0,[z157,z10,z16,z2,z3,z17]),(0,[z10,z44,z27,z2,z3,z424]),(0,[z92,z261,z1,z2,z46,z4])],[(0,[z663,z36,z1,z2,z3,z4]),(0,[z792,z0,z1,z2,z3,z4]),(0,[z10,z0,z16,z171,z3,z172]),(0,[z10,z0,z16,z2,z3,z56]),(0,[z10,z0,z135,z2,z3,z228]),(0,[z10,z197,z0,z2,z3,z41])],[(0,[z36,z129,z16,z2,z3,z4]),(0,[z6,z344,z1,z2,z3,z4]),(0,[z10,z304,z1,z2,z3,z17]),(0,[z793,z0,z1,z2,z3,z142]),(0,[z794,z10,z1,z2,z3,z4])],[(0,[z795,z0,z1,z202,z3,z4]),(0,[z119,z0,z1,z2,z286,z4]),(0,[z10,z0,z1,z2,z3,z796]),(0,[z10,z379,z1,z2,z3,z17]),(0,[z10,z797,z0,z2,z3,z41])]],
   [[(0,[z36,z1,z2,z634,z3,z4]),(0,[z36,z1,z2,z3,z40,z17]),(0,[z159,z0,z16,z2,z3,z4]),(0,[z10,z0,z2,z3,z4,z798]),(0,[z10,z0,z1,z2,z799,z3])],[(0,[z10,z0,z1,z2,z3,z195]),(0,[z10,z27,z0,z2,z3,z290]),(0,[z800,z0,z1,z2,z3,z4])],[(0,[z187,z0,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z801]),(0,[z10,z0,z1,z2,z3,z802]),(0,[z10,z1,z72,z181,z3,z4])],[(0,[z36,z16,z16,z2,z3,z4]),(0,[z10,z429,z0,z2,z3,z4]),(0,[z10,z0,z1,z2,z430,z3])],[(0,[z36,z1,z16,z2,z3,z84]),(0,[z289,z36,z1,z2,z3,z4]),(0,[z6,z0,z16,z2,z3,z17]),(0,[z10,z0,z77,z2,z3,z17]),(0,[z157,z10,z1,z2,z91,z4]),(0,[z10,z0,z1,z269,z803,z4]),(0,[z10,z0,z1,z2,z3,z804])],[(0,[z10,z164,z88,z2,z3,z17]),(0,[z10,z0,z138,z2,z3,z43]),(0,[z10,z317,z0,z1,z2,z805]),(0,[z10,z0,z1,z2,z3,z806]),(1,[z10,z104,z2,z3,z41]),(0,[z378,z0,z1,z2,z3,z31])],[(1,[z10,z16,z2,z3,z17]),(0,[z207,z0,z16,z2,z3,z4]),(0,[z210,z0,z1,z2,z91,z4]),(0,[z1,z2,z3,z4,z5,z230]),(0,[z10,z0,z1,z2,z3,z807]),(0,[z10,z808,z0,z2,z3,z4])],[(0,[z183,z36,z1,z2,z3,z84]),(0,[z0,z125,z1,z278,z3,z4]),(0,[z10,z809,z1,z2,z3,z4]),(0,[z10,z178,z248,z2,z3,z4]),(0,[z10,z0,z357,z2,z3,z148]),(0,[z27,z0,z70,z2,z3,z4]),(0,[z10,z27,z2,z3,z4,z230]),(0,[z10,z0,z1,z2,z3,z810])],[(0,[z10,z16,z2,z3,z4,z503]),(0,[z6,z30,z0,z2,z3,z4]),(0,[z10,z0,z811,z2,z3,z4]),(0,[z123,z0,z1,z2,z3,z17])],[(0,[z153,z36,z1,z2,z3,z17]),(0,[z0,z36,z1,z2,z3,z812]),(0,[z6,z87,z1,z2,z3,z4]),(0,[z106,z0,z68,z2,z3,z17]),(0,[z10,z0,z1,z2,z3,z813]),(0,[z10,z27,z16,z2,z3,z4]),(0,[z10,z16,z2,z134,z3,z17]),(0,[z10,z118,z16,z2,z3,z4]),(0,[z10,z1,z814,z2,z3,z17]),(0,[z10,z0,z815,z2,z3,z4])],[(0,[z6,z0,z11,z2,z3,z4]),(0,[z36,z1,z2,z655,z3,z17]),(0,[z627,z0,z1,z655,z3,z4]),(0,[z541,z10,z16,z2,z3,z4]),(0,[z6,z92,z1,z2,z46,z4]),(0,[z816,z0,z1,z2,z3,z4]),(0,[z10,z0,z16,z2,z3,z205]),(0,[z159,z0,z1,z2,z184,z4]),(0,[z817,z0,z1,z2,z3,z4])],[(0,[z6,z0,z95,z2,z3,z4]),(0,[z10,z0,z818,z2,z3,z4]),(0,[z34,z0,z1,z2,z3,z66]),(0,[z10,z0,z192,z2,z3,z4]),(0,[z819,z0,z1,z2,z3,z4]),(0,[z48,z10,z110,z2,z3,z17])],[(0,[z6,z0,z1,z2,z91,z4]),(0,[z10,z668,z27,z2,z3,z4]),(0,[z526,z0,z1,z2,z3,z84]),(0,[z10,z0,z1,z2,z3,z820]),(0,[z821,z0,z1,z2,z3,z4]),(0,[z10,z822,z1,z2,z3,z4])],[(0,[z22,z88,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z823]),(0,[z319,z0,z1,z2,z3,z4]),(0,[z10,z27,z183,z2,z3,z84]),(0,[z10,z0,z216,z2,z3,z73]),(0,[z10,z160,z71,z72,z3,z4]),(0,[z10,z0,z2,z3,z154,z17])],[(0,[z10,z71,z16,z2,z3,z84]),(0,[z10,z92,z16,z2,z3,z17]),(0,[z10,z0,z601,z303,z3,z4]),(0,[z10,z183,z1,z2,z3,z84]),(0,[z378,z0,z1,z2,z3,z84]),(0,[z10,z105,z1,z2,z3,z824])],[(0,[z157,z6,z16,z2,z3,z4]),(0,[z0,z1,z2,z107,z220,z4]),(0,[z10,z825,z0,z2,z3,z4]),(0,[z10,z240,z1,z2,z3,z17])]],
   [[(0,[z36,z1,z171,z2,z3,z17]),(0,[z10,z826,z0,z2,z3,z4]),(0,[z10,z27,z2,z3,z84,z17]),(0,[z10,z1,z2,z3,z382,z17]),(0,[z8,z0,z1,z2,z3,z84])],[(0,[z86,z6,z0,z2,z3,z41]),(0,[z201,z0,z1,z827,z3,z4]),(0,[z158,z10,z16,z2,z3,z17]),(0,[z10,z16,z2,z828,z3,z17]),(0,[z829,z0,z1,z2,z3,z17]),(0,[z10,z234,z0,z2,z464,z4]),(0,[z10,z0,z830,z2,z3,z4])],[(0,[z10,z0,z1,z2,z3,z692]),(0,[z10,z16,z2,z199,z3,z17]),(0,[z10,z831,z0,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z832]),(0,[z833,z0,z1,z2,z3,z4])],[(0,[z34,z0,z1,z2,z3,z84]),(0,[z422,z0,z1,z2,z3,z4])],[(0,[z6,z0,z1,z2,z3,z420]),(1,[z0,z95,z2,z3,z40]),(0,[z834,z10,z16,z2,z3,z4]),(0,[z10,z63,z0,z16,z2,z3]),(0,[z10,z444,z0,z2,z297,z4]),(0,[z10,z508,z0,z1,z2,z3]),(0,[z10,z234,z0,z2,z297,z4])],[(0,[z36,z601,z16,z2,z3,z4]),(0,[z10,z1,z311,z2,z3,z17]),(0,[z10,z16,z2,z3,z17,z503]),(0,[z10,z1,z620,z2,z3,z17]),(0,[z0,z835,z1,z2,z3,z4]),(0,[z10,z0,z1,z836,z3,z172]),(0,[z837,z0,z1,z2,z3,z4])],[(0,[z10,z0,z1,z2,z3,z838]),(0,[z36,z16,z303,z2,z3,z4]),(0,[z541,z36,z1,z2,z3,z17]),(0,[z157,z10,z16,z284,z3,z4]),(0,[z10,z839,z16,z2,z3,z4]),(0,[z10,z0,z16,z2,z33,z58]),(0,[z10,z0,z1,z2,z3,z840]),(0,[z841,z0,z1,z2,z3,z4]),(0,[z10,z0,z1,z181,z46,z4])],[(0,[z10,z492,z16,z2,z3,z4]),(0,[z187,z36,z1,z2,z3,z4]),(0,[z509,z36,z1,z2,z3,z4]),(0,[z6,z88,z16,z2,z3,z4]),(0,[z0,z261,z16,z2,z3,z4]),(0,[z42,z1,z16,z2,z3,z4]),(0,[z10,z122,z16,z2,z3,z4]),(0,[z842,z0,z1,z2,z3,z4])],[(0,[z0,z36,z16,z2,z3,z4]),(0,[z36,z1,z16,z2,z3,z17]),(0,[z36,z1,z620,z2,z3,z4]),(0,[z10,z16,z2,z655,z3,z4]),(0,[z843,z0,z1,z2,z94,z4]),(0,[z59,z0,z1,z2,z3,z127]),(0,[z0,z70,z16,z2,z3,z4]),(0,[z10,z0,z295,z2,z3,z4]),(0,[z10,z0,z1,z72,z91,z4]),(0,[z20,z10,z1,z2,z3,z4]),(0,[z153,z10,z1,z4,z230,z79])],[(0,[z0,z36,z1,z2,z3,z195]),(0,[z124,z27,z36,z2,z3,z4]),(0,[z6,z425,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z844]),(0,[z10,z1,z632,z2,z3,z17])],[(0,[z36,z1,z579,z2,z3,z4]),(0,[z6,z166,z1,z2,z3,z4]),(0,[z0,z845,z1,z2,z3,z4])],[(0,[z124,z36,z11,z2,z3,z4]),(0,[z183,z36,z1,z2,z3,z17]),(0,[z273,z36,z16,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z846]),(0,[z10,z16,z2,z3,z847,z4]),(0,[z10,z352,z1,z2,z46,z4]),(0,[z10,z0,z357,z2,z3,z19])],[(0,[z59,z0,z1,z2,z3,z495]),(0,[z161,z10,z16,z2,z3,z17]),(0,[z10,z0,z848,z2,z3,z4])],[(0,[z36,z1,z2,z569,z3,z4]),(0,[z10,z88,z16,z2,z3,z420]),(0,[z10,z0,z1,z2,z3,z849])],[(0,[z36,z1,z11,z2,z3,z4]),(0,[z10,z850,z1,z2,z3,z4]),(0,[z137,z108,z1,z2,z3,z4]),(0,[z187,z0,z1,z2,z3,z424])],[(0,[z6,z189,z1,z2,z3,z4]),(0,[z121,z0,z16,z2,z3,z4]),(0,[z44,z240,z1,z2,z3,z17]),(0,[z157,z10,z27,z2,z21,z4]),(0,[z10,z27,z0,z2,z3,z476]),(0,[z63,z0,z1,z2,z3,z149])]],
   [[(0,[z10,z0,z1,z2,z3,z851]),(0,[z97,z0,z16,z2,z3,z4]),(0,[z101,z0,z1,z2,z3,z84]),(0,[z10,z0,z1,z2,z464,z4]),(0,[z852,z0,z1,z2,z3,z4])],[(0,[z10,z0,z1,z2,z3,z853]),(0,[z42,z0,z1,z2,z3,z4]),(0,[z10,z0,z1,z854,z2,z3]),(0,[z10,z0,z1,z2,z3,z855]),(0,[z376,z211,z0,z2,z3,z4])],[(0,[z856,z0,z1,z2,z3,z4]),(0,[z10,z16,z112,z2,z3,z17]),(0,[z10,z71,z16,z2,z3,z17]),(0,[z10,z16,z2,z3,z857,z4])],[(0,[z233,z36,z1,z2,z3,z4]),(0,[z10,z123,z1,z2,z3,z17])],[(0,[z10,z116,z1,z2,z3,z84]),(0,[z10,z160,z0,z2,z3,z4]),(0,[z298,z0,z16,z2,z3,z4]),(0,[z858,z0,z1,z2,z3,z4]),(0,[z10,z745,z1,z2,z3,z17])],[(0,[z36,z16,z112,z2,z3,z4])],[(0,[z686,z0,z1,z2,z3,z4]),(0,[z10,z108,z1,z2,z3,z142]),(0,[z161,z26,z0,z37,z3,z4])],[(0,[z10,z0,z194,z2,z3,z4]),(0,[z10,z164,z0,z2,z3,z4]),(0,[z34,z0,z1,z2,z3,z17]),(0,[z859,z0,z1,z2,z3,z4]),(0,[z10,z0,z1,z284,z3,z43]),(0,[z10,z105,z1,z2,z3,z84]),(0,[z10,z860,z0,z2,z3,z4])],[(0,[z0,z1,z300,z2,z3,z4]),(0,[z273,z0,z112,z2,z3,z4]),(0,[z10,z160,z105,z2,z3,z4])],[(0,[z22,z0,z1,z2,z3,z84]),(0,[z26,z0,z1,z2,z74,z4])],[(0,[z106,z492,z0,z2,z3,z4]),(0,[z140,z0,z579,z2,z3,z4]),(0,[z119,z0,z95,z2,z3,z4]),(0,[z10,z16,z2,z3,z4,z861]),(0,[z207,z160,z0,z2,z3,z4]),(0,[z10,z0,z615,z37,z3,z4]),(0,[z862,z0,z1,z2,z3,z4])],[(0,[z27,z183,z36,z2,z3,z4]),(0,[z133,z0,z36,z1,z2,z134]),(0,[z0,z108,z1,z2,z3,z40]),(0,[z10,z0,z863,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z864]),(0,[z10,z865,z1,z2,z3,z4])],[(0,[z157,z36,z16,z2,z3,z4]),(0,[z59,z0,z1,z2,z3,z503]),(0,[z6,z0,z1,z2,z3,z221]),(0,[z6,z471,z1,z2,z3,z4]),(0,[z10,z866,z16,z2,z3,z4]),(0,[z10,z867,z16,z2,z3,z4]),(0,[z55,z0,z16,z2,z3,z4]),(0,[z10,z0,z868,z2,z3,z4]),(0,[z158,z10,z1,z90,z3,z84]),(0,[z101,z0,z138,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z869]),(0,[z10,z0,z2,z3,z84,z154]),(0,[z870,z0,z1,z2,z3,z4])],[(0,[z866,z36,z1,z2,z3,z4]),(0,[z10,z16,z2,z3,z84,z17]),(0,[z871,z10,z16,z2,z3,z4]),(0,[z10,z1,z2,z3,z320,z17]),(0,[z10,z779,z27,z2,z3,z4]),(0,[z10,z0,z872,z2,z3,z4]),(0,[z10,z873,z1,z2,z46,z4]),(0,[z10,z0,z874,z2,z3,z148]),(0,[z875,z0,z1,z2,z3,z4])],[(0,[z153,z10,z0,z1,z79,z17]),(0,[z876,z0,z1,z2,z3,z4])],[(0,[z10,z339,z1,z2,z3,z102]),(0,[z26,z0,z1,z2,z3,z4]),(0,[z10,z16,z2,z3,z496,z17]),(0,[z877,z0,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z878])]],
   [[(0,[z0,z36,z295,z2,z3,z4]),(0,[z518,z36,z1,z2,z3,z17]),(0,[z10,z663,z27,z2,z3,z4]),(0,[z137,z10,z16,z2,z3,z17]),(0,[z10,z16,z2,z231,z3,z4]),(0,[z10,z0,z1,z2,z3,z879])],[(0,[z159,z0,z1,z2,z3,z84]),(0,[z10,z1,z2,z3,z880,z17]),(0,[z10,z0,z881,z2,z3,z4])],[(0,[z36,z1,z2,z236,z3,z17]),(0,[z36,z1,z2,z3,z179,z17]),(0,[z882,z0,z1,z2,z3,z4])],[(0,[z699,z10,z0,z2,z3,z41]),(0,[z10,z16,z2,z3,z58,z17]),(0,[z10,z357,z16,z2,z3,z17]),(0,[z883,z0,z1,z2,z3,z4])],[(0,[z10,z0,z1,z2,z3,z884]),(0,[z10,z0,z1,z2,z3,z812]),(0,[z13,z0,z95,z2,z3,z4]),(0,[z10,z885,z0,z2,z3,z4]),(0,[z10,z0,z2,z3,z31,z154]),(0,[z10,z0,z1,z2,z32,z3])],[(0,[z86,z0,z36,z2,z3,z41]),(0,[z10,z339,z16,z2,z3,z4]),(0,[z10,z886,z1,z2,z3,z4]),(0,[z292,z10,z1,z2,z3,z17]),(0,[z10,z429,z16,z2,z3,z4]),(0,[z157,z10,z266,z2,z3,z4])],[(1,[z36,z16,z2,z3,z4]),(0,[z10,z887,z1,z2,z3,z4]),(0,[z10,z0,z95,z2,z3,z40]),(0,[z143,z1,z16,z2,z3,z4]),(1,[z70,z16,z2,z3,z4]),(0,[z10,z16,z2,z3,z553,z17]),(0,[z240,z1,z2,z3,z4,z17]),(0,[z10,z0,z357,z2,z3,z179])],[(0,[z36,z36,z1,z2,z3,z17]),(1,[z10,z1,z2,z3,z139])],[(0,[z6,z0,z1,z2,z78,z3]),(0,[z10,z116,z1,z2,z3,z17]),(0,[z10,z71,z1,z72,z3,z4]),(0,[z10,z0,z1,z2,z3,z888])],[(0,[z36,z16,z2,z3,z553,z4]),(0,[z398,z339,z1,z2,z3,z4]),(0,[z10,z0,z889,z2,z3,z4]),(0,[z10,z0,z890,z2,z3,z4]),(0,[z10,z743,z0,z16,z2,z3]),(0,[z10,z0,z95,z2,z33,z3]),(0,[z10,z178,z1,z2,z3,z4]),(0,[z10,z0,z1,z284,z3,z17]),(0,[z10,z92,z266,z2,z46,z4]),(0,[z10,z183,z23,z2,z3,z84]),(0,[z10,z429,z183,z2,z3,z84])],[(0,[z201,z36,z16,z2,z3,z4]),(0,[z6,z0,z1,z2,z3,z228]),(0,[z891,z0,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z443]),(0,[z10,z118,z1,z2,z3,z84]),(0,[z20,z10,z63,z1,z2,z3])],[(0,[z686,z36,z1,z2,z3,z4]),(0,[z93,z0,z1,z2,z94,z4]),(0,[z10,z105,z1,z2,z3,z17]),(0,[z10,z701,z1,z2,z3,z84]),(0,[z0,z892,z1,z2,z3,z4])],[(0,[z10,z68,z16,z2,z3,z17]),(0,[z59,z0,z1,z2,z3,z382]),(0,[z10,z16,z2,z893,z3,z4]),(0,[z10,z0,z2,z3,z4,z497]),(0,[z518,z10,z0,z16,z199,z3]),(0,[z10,z0,z1,z2,z3,z894]),(0,[z10,z27,z189,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z895])],[(0,[z6,z0,z266,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z102]),(0,[z13,z0,z1,z2,z3,z156]),(0,[z10,z0,z1,z2,z3,z320]),(0,[z10,z182,z0,z2,z3,z4]),(0,[z10,z0,z16,z2,z74,z4]),(0,[z22,z0,z1,z2,z3,z17]),(0,[z769,z0,z1,z2,z3,z4]),(0,[z378,z0,z2,z3,z4,z154]),(0,[z10,z0,z2,z3,z4,z896])],[(0,[z36,z16,z2,z3,z4,z17]),(0,[z10,z0,z1,z2,z3,z897]),(0,[z10,z0,z1,z2,z898,z4]),(0,[z210,z27,z0,z2,z3,z4]),(0,[z10,z0,z1,z2,z91,z109]),(0,[z207,z71,z1,z72,z3,z4]),(0,[z10,z0,z1,z2,z33,z899])],[(0,[z0,z36,z194,z2,z3,z4]),(0,[z10,z472,z1,z2,z3,z17]),(1,[z10,z16,z2,z3,z65]),(0,[z10,z0,z1,z2,z3,z900])]],
   [[(0,[z10,z0,z1,z2,z901,z4]),(0,[z92,z36,z1,z2,z46,z4]),(0,[z0,z36,z1,z2,z3,z31]),(0,[z143,z0,z1,z2,z3,z4]),(0,[z6,z108,z1,z2,z3,z4]),(0,[z6,z0,z1,z2,z3,z109]),(0,[z10,z473,z1,z2,z3,z17]),(0,[z10,z743,z0,z1,z2,z3]),(0,[z10,z0,z902,z2,z3,z4]),(0,[z197,z0,z16,z2,z3,z4]),(0,[z26,z0,z1,z2,z214,z4])],[(0,[z158,z36,z16,z2,z3,z4]),(0,[z36,z1,z278,z2,z3,z17]),(0,[z10,z0,z903,z2,z3,z4]),(0,[z540,z0,z16,z2,z3,z4]),(0,[z48,z10,z27,z2,z3,z17])],[(0,[z0,z45,z1,z2,z3,z4]),(0,[z6,z0,z1,z2,z3,z73]),(0,[z10,z88,z1,z2,z3,z81]),(0,[z10,z289,z95,z2,z3,z4]),(0,[z34,z0,z1,z2,z3,z128]),(0,[z10,z27,z0,z2,z91,z4]),(0,[z10,z0,z1,z2,z3,z232]),(0,[z10,z904,z0,z2,z3,z4]),(0,[z57,z133,z0,z1,z2,z3])],[(0,[z10,z0,z16,z2,z3,z4]),(0,[z36,z1,z72,z2,z3,z17]),(0,[z36,z129,z1,z2,z3,z17]),(0,[z6,z0,z129,z303,z3,z4]),(0,[z140,z116,z39,z2,z3,z4]),(0,[z10,z590,z16,z2,z3,z4]),(0,[z10,z905,z16,z2,z3,z4]),(0,[z518,z10,z0,z1,z199,z3])],[(0,[z6,z27,z0,z2,z3,z4]),(0,[z352,z36,z16,z2,z3,z4]),(0,[z10,z248,z16,z2,z3,z84]),(0,[z157,z10,z1,z2,z746,z4]),(0,[z57,z0,z1,z2,z3,z84])],[(0,[z203,z0,z112,z2,z3,z4]),(0,[z6,z289,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z142,z906]),(0,[z10,z16,z2,z33,z3,z17]),(0,[z10,z0,z1,z2,z3,z907]),(0,[z159,z0,z1,z2,z3,z17]),(0,[z908,z0,z1,z2,z3,z4])],[(0,[z10,z0,z1,z2,z3,z909]),(0,[z10,z0,z1,z2,z3,z910]),(0,[z44,z27,z36,z2,z3,z4]),(0,[z339,z1,z39,z2,z3,z4]),(0,[z86,z10,z0,z2,z3,z452]),(0,[z911,z0,z1,z2,z3,z4])],[(0,[z6,z0,z311,z2,z3,z4]),(0,[z10,z164,z0,z2,z3,z25]),(0,[z912,z0,z1,z2,z3,z4]),(0,[z10,z0,z913,z2,z3,z4])],[(0,[z36,z16,z2,z33,z3,z4]),(0,[z429,z183,z36,z2,z3,z4]),(0,[z6,z0,z1,z2,z3,z147]),(0,[z6,z88,z1,z2,z3,z84]),(0,[z10,z16,z269,z90,z3,z4]),(0,[z158,z10,z1,z90,z184,z4]),(0,[z0,z261,z1,z2,z3,z84]),(0,[z10,z122,z1,z2,z3,z84])],[(1,[z108,z1,z2,z3,z40]),(0,[z10,z352,z16,z2,z3,z17]),(0,[z10,z44,z429,z2,z3,z4])],[(0,[z6,z183,z16,z2,z3,z4]),(0,[z10,z27,z0,z2,z3,z420]),(0,[z10,z16,z2,z46,z3,z84]),(0,[z10,z211,z0,z2,z3,z147])],[(0,[z10,z289,z1,z2,z3,z420]),(0,[z10,z914,z1,z2,z3,z4]),(0,[z10,z27,z104,z2,z3,z4]),(0,[z10,z192,z2,z90,z3,z4]),(0,[z123,z0,z110,z2,z3,z4])],[(0,[z36,z16,z2,z3,z4,z58]),(0,[z161,z36,z16,z2,z3,z4]),(0,[z839,z36,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z915]),(0,[z0,z916,z1,z2,z3,z4])],[(0,[z13,z0,z1,z2,z3,z562]),(0,[z6,z44,z27,z2,z3,z4]),(0,[z6,z177,z1,z2,z3,z4]),(0,[z10,z0,z311,z2,z3,z420]),(0,[z201,z10,z16,z2,z3,z17]),(0,[z917,z10,z16,z2,z3,z4]),(0,[z918,z0,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z184,z4]),(0,[z10,z1,z2,z746,z21,z4]),(0,[z20,z10,z1,z2,z46,z4]),(0,[z10,z1,z513,z2,z3,z17]),(0,[z10,z0,z1,z2,z32,z4])],[(0,[z0,z36,z357,z2,z3,z179]),(0,[z6,z0,z1,z181,z3,z4]),(0,[z10,z0,z365,z2,z3,z4]),(0,[z10,z16,z2,z3,z156,z17]),(0,[z10,z0,z16,z2,z412,z4]),(1,[z10,z1,z2,z746,z4]),(0,[z123,z183,z1,z2,z3,z4]),(0,[z10,z0,z110,z2,z3,z84])],[(0,[z36,z16,z2,z134,z3,z4]),(0,[z36,z1,z2,z3,z4,z127]),(0,[z10,z71,z16,z90,z3,z4]),(0,[z0,z315,z1,z2,z3,z4]),(0,[z10,z105,z1,z2,z3,z75])]],
   [[(0,[z36,z1,z513,z2,z3,z4]),(0,[z260,z10,z16,z2,z3,z17]),(0,[z919,z10,z0,z1,z4,z79]),(0,[z121,z0,z1,z2,z3,z84]),(0,[z10,z0,z2,z3,z4,z920])],[(0,[z10,z0,z185,z2,z184,z4]),(0,[z42,z0,z135,z2,z3,z4]),(0,[z97,z0,z1,z2,z3,z84])],[(0,[z10,z27,z275,z2,z3,z4]),(0,[z10,z0,z16,z2,z426,z4]),(0,[z157,z10,z1,z2,z21,z4]),(0,[z10,z0,z357,z2,z3,z496])],[(0,[z158,z6,z1,z90,z3,z4]),(0,[z0,z695,z68,z2,z3,z4]),(0,[z10,z0,z1,z2,z921,z4]),(0,[z922,z0,z1,z2,z3,z4]),(0,[z923,z0,z1,z2,z3,z4]),(0,[z10,z924,z0,z2,z3,z4]),(0,[z157,z42,z1,z2,z21,z4]),(0,[z10,z925,z1,z2,z3,z4])],[(0,[z36,z1,z2,z90,z3,z17]),(0,[z926,z10,z16,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z927]),(0,[z10,z0,z16,z2,z214,z4]),(0,[z209,z0,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z928,z4]),(0,[z10,z0,z135,z181,z3,z4]),(0,[z0,z1,z2,z3,z4,z929])],[(0,[z0,z36,z1,z2,z3,z102]),(0,[z10,z0,z16,z2,z3,z312]),(0,[z930,z0,z1,z2,z3,z4])],[(0,[z10,z0,z1,z2,z931,z3]),(0,[z932,z0,z1,z2,z3,z4]),(0,[z10,z16,z2,z3,z21,z17]),(0,[z10,z160,z16,z2,z3,z4]),(0,[z10,z92,z1,z2,z746,z4])],[(0,[z36,z16,z2,z828,z3,z4]),(0,[z0,z259,z1,z2,z3,z142]),(0,[z119,z0,z1,z2,z78,z3]),(0,[z509,z0,z1,z2,z3,z40]),(0,[z10,z16,z90,z3,z4,z79]),(0,[z933,z10,z1,z2,z3,z17]),(0,[z10,z0,z1,z2,z184,z205]),(0,[z10,z0,z934,z2,z3,z4])],[(0,[z36,z16,z2,z199,z3,z4]),(0,[z10,z36,z16,z2,z3,z4]),(0,[z10,z70,z16,z2,z3,z4]),(0,[z57,z0,z1,z2,z3,z17])],[(0,[z10,z164,z16,z2,z3,z4]),(0,[z26,z0,z1,z2,z3,z290]),(0,[z935,z0,z1,z2,z3,z4])],[(0,[z0,z936,z1,z2,z3,z4]),(0,[z69,z0,z1,z581,z3,z4])],[(1,[z36,z1,z2,z3,z12]),(0,[z10,z311,z2,z3,z4,z17]),(0,[z10,z0,z1,z2,z3,z937]),(0,[z10,z71,z16,z2,z3,z65]),(0,[z158,z10,z1,z181,z3,z4]),(0,[z10,z0,z1,z2,z3,z824]),(0,[z938,z0,z1,z2,z3,z4])],[(0,[z398,z36,z1,z2,z3,z4]),(0,[z6,z88,z1,z2,z3,z17]),(0,[z162,z0,z16,z2,z3,z4]),(0,[z0,z261,z1,z2,z3,z17]),(0,[z10,z122,z1,z2,z3,z17])],[(0,[z44,z281,z1,z2,z3,z4]),(0,[z442,z36,z1,z2,z3,z17]),(0,[z0,z1,z2,z581,z3,z4]),(0,[z83,z10,z0,z828,z3,z4]),(0,[z10,z0,z1,z269,z82,z84]),(0,[z10,z0,z2,z3,z4,z452]),(0,[z10,z939,z1,z2,z3,z4]),(0,[z518,z10,z0,z1,z940,z3])],[(0,[z10,z0,z16,z2,z3,z455]),(0,[z10,z16,z269,z2,z3,z17]),(0,[z376,z92,z1,z2,z46,z4]),(0,[z468,z10,z0,z2,z3,z428]),(0,[z10,z63,z0,z1,z2,z3])],[(0,[z36,z1,z632,z2,z3,z4]),(0,[z941,z36,z1,z2,z3,z4]),(0,[z10,z942,z0,z2,z3,z4]),(0,[z119,z108,z1,z2,z3,z4]),(0,[z10,z0,z16,z2,z3,z424]),(0,[z10,z0,z2,z615,z3,z4])]],
   [[(0,[z6,z27,z36,z2,z3,z4]),(0,[z10,z943,z0,z2,z3,z4])],[(0,[z36,z16,z269,z2,z3,z4]),(0,[z10,z0,z385,z2,z3,z179]),(0,[z10,z117,z0,z2,z3,z287])],[(0,[z10,z339,z68,z2,z3,z4]),(0,[z10,z27,z0,z2,z3,z221]),(0,[z10,z16,z2,z90,z3,z4]),(0,[z10,z104,z16,z2,z3,z4]),(0,[z10,z0,z110,z2,z3,z17])],[(0,[z6,z0,z1,z2,z774,z3]),(0,[z10,z0,z16,z2,z3,z25]),(0,[z0,z1,z2,z94,z107,z4])],[(0,[z6,z257,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z944]),(0,[z10,z403,z16,z2,z3,z4]),(0,[z689,z27,z0,z2,z3,z4]),(0,[z121,z0,z1,z2,z3,z17]),(0,[z161,z10,z0,z37,z74,z4]),(0,[z10,z945,z1,z2,z3,z4]),(0,[z10,z1,z2,z3,z4,z946]),(0,[z10,z0,z947,z2,z3,z4])],[(0,[z0,z36,z1,z2,z184,z4]),(0,[z10,z0,z948,z2,z3,z4]),(0,[z240,z27,z0,z2,z3,z4]),(0,[z949,z0,z1,z2,z3,z4]),(0,[z101,z0,z1,z2,z3,z43]),(0,[z950,z10,z0,z1,z4,z79]),(0,[z378,z0,z1,z2,z3,z17])],[(0,[z10,z0,z951,z2,z3,z4]),(0,[z10,z339,z1,z2,z3,z84]),(0,[z10,z695,z16,z2,z3,z4]),(0,[z10,z1,z2,z3,z857,z84])],[(0,[z105,z36,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z952]),(0,[z10,z16,z2,z3,z293,z17]),(0,[z10,z16,z2,z3,z4,z230]),(0,[z0,z1,z2,z3,z84,z96]),(0,[z10,z0,z1,z2,z3,z452])],[(0,[z10,z0,z1,z2,z3,z12]),(0,[z10,z0,z1,z2,z953,z3]),(0,[z10,z954,z0,z2,z3,z4]),(0,[z59,z10,z16,z2,z3,z17]),(0,[z27,z0,z45,z2,z3,z4]),(0,[z10,z0,z677,z2,z3,z4])],[(0,[z10,z116,z1,z2,z3,z955]),(0,[z13,z108,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z956,z4]),(0,[z153,z378,z0,z1,z4,z79])],[(0,[z10,z0,z11,z2,z3,z195]),(0,[z957,z36,z1,z2,z3,z4]),(0,[z958,z0,z1,z2,z3,z4]),(0,[z10,z166,z2,z512,z3,z4]),(0,[z161,z10,z0,z37,z3,z4]),(0,[z10,z0,z1,z2,z4,z270]),(0,[z10,z0,z1,z2,z3,z959])],[(0,[z10,z960,z1,z2,z3,z4]),(1,[z0,z39,z2,z3,z221]),(0,[z10,z108,z1,z2,z3,z40]),(0,[z161,z10,z0,z401,z3,z4]),(0,[z685,z0,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z31])],[(0,[z10,z0,z1,z2,z3,z961]),(0,[z59,z27,z0,z2,z3,z40]),(0,[z10,z0,z1,z2,z3,z66]),(0,[z0,z16,z2,z3,z4,z149]),(0,[z10,z87,z1,z2,z3,z804])],[(0,[z10,z0,z77,z2,z3,z4]),(0,[z106,z10,z16,z2,z3,z17]),(0,[z10,z962,z1,z2,z3,z4]),(0,[z59,z289,z1,z2,z3,z40]),(0,[z10,z16,z2,z3,z4,z963]),(0,[z10,z0,z16,z2,z3,z290]),(0,[z10,z0,z1,z762,z3,z172]),(0,[z0,z45,z23,z2,z3,z4]),(0,[z10,z0,z964,z2,z3,z4])],[(0,[z6,z0,z1,z2,z3,z195]),(0,[z36,z1,z303,z2,z3,z17]),(0,[z0,z36,z1,z2,z931,z3]),(0,[z10,z27,z0,z2,z78,z3]),(0,[z10,z108,z1,z2,z33,z3]),(0,[z10,z211,z92,z2,z46,z4]),(0,[z161,z10,z105,z37,z3,z4])],[(0,[z10,z0,z965,z2,z3,z4]),(0,[z71,z36,z1,z72,z3,z4]),(0,[z966,z0,z39,z2,z3,z4]),(0,[z10,z0,z1,z2,z967,z3]),(0,[z10,z182,z16,z2,z3,z4]),(0,[z10,z16,z2,z968,z3,z4]),(0,[z71,z70,z1,z72,z3,z4]),(0,[z10,z189,z2,z512,z3,z4]),(0,[z969,z0,z1,z2,z3,z4])]],
   [[(0,[z10,z218,z0,z2,z3,z4]),(0,[z36,z1,z2,z3,z17,z503]),(0,[z6,z429,z0,z2,z3,z4]),(0,[z970,z0,z39,z2,z3,z4]),(0,[z69,z27,z0,z278,z3,z4]),(0,[z10,z27,z0,z2,z3,z228]),(0,[z157,z10,z192,z2,z3,z4]),(0,[z10,z71,z216,z72,z3,z4]),(0,[z10,z971,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z972])],[(0,[z10,z0,z1,z973,z3,z4]),(0,[z123,z0,z1,z2,z3,z4]),(0,[z10,z1,z2,z3,z84,z139]),(0,[z197,z0,z1,z2,z3,z84]),(0,[z462,z10,z0,z1,z199,z3])],[(0,[z93,z10,z16,z2,z3,z17]),(0,[z13,z0,z1,z2,z3,z495]),(0,[z210,z0,z192,z2,z3,z4]),(0,[z974,z0,z1,z2,z3,z4]),(0,[z871,z10,z1,z2,z3,z17]),(0,[z10,z0,z1,z82,z4,z270])],[(0,[z36,z16,z2,z3,z84,z4]),(0,[z10,z16,z2,z3,z79,z17])],[(0,[z10,z0,z1,z2,z3,z84]),(0,[z10,z0,z2,z3,z4,z975]),(0,[z10,z1,z2,z3,z84,z861]),(0,[z48,z10,z1,z2,z3,z17])],[(0,[z136,z492,z0,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z976]),(0,[z10,z0,z1,z2,z3,z977])],[(0,[z189,z36,z1,z2,z3,z4]),(0,[z6,z27,z16,z2,z3,z4]),(0,[z10,z44,z1,z2,z3,z25]),(0,[z59,z0,z95,z2,z3,z40]),(0,[z10,z44,z16,z2,z3,z17]),(0,[z10,z27,z0,z2,z3,z109]),(0,[z10,z0,z192,z2,z91,z4]),(0,[z20,z153,z10,z1,z4,z79])],[(0,[z83,z10,z16,z90,z3,z4]),(0,[z101,z0,z1,z2,z3,z17]),(0,[z509,z0,z1,z2,z3,z503])],[(0,[z10,z0,z978,z2,z3,z4]),(0,[z234,z36,z16,z2,z3,z4]),(0,[z6,z0,z192,z2,z3,z4]),(0,[z10,z0,z1,z979,z3,z4]),(0,[z187,z44,z1,z2,z3,z17]),(0,[z10,z27,z0,z2,z3,z73]),(0,[z10,z0,z185,z2,z3,z84]),(0,[z10,z980,z0,z1,z2,z3])],[(0,[z36,z357,z16,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z981]),(0,[z10,z448,z71,z2,z3,z4]),(0,[z10,z1,z2,z46,z91,z4])],[(0,[z10,z339,z1,z2,z3,z17]),(0,[z982,z0,z1,z2,z3,z4]),(0,[z207,z0,z1,z2,z3,z84]),(0,[z10,z0,z1,z181,z3,z228])],[(1,[z36,z1,z2,z3,z17]),(0,[z6,z183,z1,z2,z3,z84]),(0,[z10,z983,z1,z2,z3,z4]),(0,[z10,z0,z984,z2,z3,z4]),(0,[z10,z27,z743,z0,z2,z3]),(0,[z10,z0,z1,z985,z3,z4]),(0,[z86,z10,z0,z2,z3,z428]),(0,[z161,z10,z0,z37,z214,z4]),(0,[z0,z986,z1,z2,z3,z4])],[(0,[z10,z0,z987,z2,z3,z4])],[(0,[z10,z36,z1,z2,z3,z12]),(0,[z36,z16,z2,z111,z3,z4]),(0,[z203,z36,z1,z2,z3,z17]),(0,[z36,z1,z112,z2,z3,z17]),(0,[z6,z85,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z988]),(0,[z13,z27,z0,z2,z3,z142]),(0,[z210,z0,z1,z2,z3,z109]),(0,[z10,z989,z1,z2,z3,z4]),(0,[z990,z0,z1,z2,z3,z4])],[(0,[z0,z36,z951,z2,z3,z4]),(0,[z119,z0,z1,z2,z991,z4]),(0,[z10,z0,z992,z2,z3,z4]),(0,[z10,z0,z993,z2,z3,z4]),(0,[z10,z1,z16,z2,z3,z17]),(0,[z10,z27,z0,z2,z3,z147])],[(0,[z124,z36,z1,z2,z3,z195]),(0,[z627,z36,z1,z2,z3,z17]),(0,[z10,z248,z16,z2,z3,z66]),(1,[z10,z178,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z994]),(0,[z10,z0,z1,z2,z995,z4]),(0,[z20,z10,z1,z2,z3,z610])]],
   [[(0,[z0,z36,z1,z2,z3,z12]),(0,[z10,z108,z95,z2,z3,z4]),(0,[z10,z0,z138,z2,z3,z4]),(0,[z10,z16,z2,z82,z3,z17])],[(0,[z36,z16,z2,z3,z4,z41]),(0,[z779,z36,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z996]),(0,[z6,z234,z0,z2,z297,z4]),(0,[z10,z997,z1,z2,z3,z4])],[(0,[z87,z36,z1,z2,z3,z4]),(0,[z36,z68,z16,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z176]),(0,[z10,z0,z1,z2,z3,z998]),(0,[z157,z10,z135,z2,z21,z4]),(0,[z10,z999,z0,z1,z2,z3]),(0,[z10,z1000,z1,z2,z3,z4]),(0,[z20,z10,z616,z2,z3,z4])],[(0,[z36,z16,z2,z82,z3,z4]),(0,[z10,z88,z23,z2,z3,z4]),(0,[z10,z1001,z1,z2,z3,z4]),(0,[z10,z27,z166,z2,z3,z4]),(0,[z10,z27,z0,z2,z3,z749]),(0,[z20,z10,z1,z2,z91,z4]),(0,[z158,z10,z1,z90,z3,z17]),(0,[z10,z0,z1,z2,z134,z32])],[(0,[z0,z36,z1,z2,z3,z66]),(0,[z1002,z10,z0,z2,z3,z41]),(0,[z1003,z0,z1,z2,z3,z4]),(0,[z10,z27,z0,z181,z3,z4]),(0,[z207,z0,z1,z2,z3,z65]),(0,[z86,z10,z122,z2,z3,z41])],[(0,[z36,z1,z2,z3,z4,z861]),(0,[z88,z36,z16,z2,z3,z4]),(0,[z0,z36,z77,z2,z3,z4]),(0,[z6,z0,z295,z2,z3,z4]),(0,[z140,z339,z39,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z1004]),(0,[z10,z1005,z0,z2,z3,z4]),(0,[z197,z0,z1,z2,z3,z17]),(0,[z429,z0,z45,z2,z3,z4]),(0,[z10,z0,z1,z2,z214,z84]),(0,[z197,z0,z1,z2,z3,z41])],[(0,[z10,z0,z1,z1006,z3,z4]),(0,[z158,z36,z1,z2,z3,z17]),(0,[z10,z1007,z1,z2,z3,z4]),(0,[z1008,z10,z0,z2,z3,z41]),(0,[z10,z27,z0,z2,z754,z4])],[(0,[z6,z349,z1,z2,z3,z4]),(0,[z10,z92,z1,z2,z46,z147])],[(0,[z10,z0,z1,z2,z3,z17]),(0,[z10,z1009,z0,z2,z3,z4]),(0,[z10,z289,z756,z2,z3,z4]),(0,[z10,z117,z0,z2,z3,z41]),(0,[z1010,z0,z1,z2,z3,z4]),(0,[z1011,z0,z1,z2,z3,z4]),(0,[z153,z10,z30,z0,z4,z79])],[(0,[z36,z1,z762,z2,z3,z17]),(0,[z10,z0,z1,z2,z3,z1012]),(0,[z201,z27,z0,z202,z3,z4]),(0,[z10,z1013,z0,z2,z3,z4])],[(0,[z36,z1,z2,z3,z496,z17]),(0,[z1014,z10,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z1015]),(0,[z10,z839,z1,z2,z3,z84]),(0,[z10,z30,z0,z2,z297,z4])],[(0,[z140,z866,z0,z2,z3,z4]),(0,[z10,z0,z16,z2,z3,z476]),(0,[z301,z492,z0,z2,z3,z4])],[(0,[z0,z36,z1,z2,z3,z84]),(0,[z10,z0,z185,z2,z3,z17]),(0,[z0,z70,z1,z2,z3,z84]),(0,[z10,z0,z1,z1016,z3,z4])],[(0,[z0,z125,z1,z624,z3,z4]),(0,[z10,z0,z1,z2,z3,z1017]),(0,[z10,z0,z39,z2,z3,z221]),(0,[z83,z10,z16,z2,z3,z17]),(0,[z468,z10,z0,z2,z3,z41]),(0,[z162,z0,z1,z2,z3,z84])],[(1,[z89,z1,z2,z3,z4]),(0,[z0,z36,z1,z2,z3,z43]),(0,[z36,z1,z2,z3,z58,z17]),(0,[z106,z0,z275,z2,z3,z4]),(0,[z10,z16,z2,z3,z355,z4]),(0,[z240,z0,z16,z2,z3,z4]),(0,[z207,z0,z1,z2,z3,z17]),(0,[z10,z1,z2,z3,z4,z1018])],[(0,[z10,z0,z1,z1019,z3,z4]),(0,[z10,z339,z1,z2,z3,z1020]),(0,[z1021,z0,z1,z2,z3,z4]),(0,[z10,z16,z2,z37,z3,z17]),(0,[z49,z27,z0,z2,z3,z4])]],
   [[(0,[z444,z36,z16,z2,z3,z4]),(0,[z398,z0,z691,z2,z3,z4]),(0,[z1002,z0,z39,z2,z3,z4])],[(0,[z124,z10,z16,z2,z3,z17]),(0,[z27,z0,z36,z2,z3,z4]),(0,[z161,z36,z1,z2,z3,z17]),(0,[z6,z160,z0,z2,z3,z4]),(0,[z207,z71,z16,z2,z3,z4]),(0,[z1022,z0,z1,z2,z3,z4]),(0,[z20,z10,z1,z72,z3,z4]),(0,[z101,z0,z1,z284,z3,z4]),(0,[z376,z0,z266,z2,z3,z4])],[(0,[z36,z1,z2,z111,z3,z17]),(0,[z10,z0,z1,z2,z3,z1023]),(0,[z10,z0,z1024,z2,z3,z4])],[(0,[z0,z680,z1,z2,z3,z4]),(0,[z140,z0,z39,z2,z3,z4]),(0,[z10,z0,z1,z1025,z3,z4]),(0,[z0,z1,z2,z3,z149,z17]),(0,[z10,z104,z1,z2,z3,z84]),(0,[z10,z133,z0,z1,z2,z32])],[(0,[z6,z0,z194,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1026]),(0,[z6,z164,z0,z2,z3,z4]),(0,[z518,z10,z0,z1,z3,z293]),(0,[z161,z10,z0,z37,z3,z290])],[(0,[z59,z0,z1,z2,z3,z283]),(0,[z6,z10,z16,z2,z3,z17]),(0,[z10,z88,z311,z2,z3,z17]),(0,[z10,z0,z1,z2,z1027,z4]),(0,[z119,z0,z1,z2,z220,z4]),(0,[z10,z0,z1,z615,z3,z4])],[(0,[z442,z10,z1,z2,z3,z17]),(0,[z10,z122,z1,z2,z3,z76]),(0,[z10,z71,z192,z2,z3,z4]),(0,[z10,z1,z295,z2,z3,z17])],[(0,[z10,z0,z1028,z2,z3,z4]),(0,[z10,z0,z1,z2,z235,z17]),(0,[z197,z0,z357,z2,z3,z4])],[(0,[z0,z36,z138,z2,z3,z4]),(0,[z59,z36,z16,z2,z3,z4]),(0,[z1029,z0,z1,z2,z3,z4]),(0,[z44,z240,z27,z2,z3,z4]),(0,[z376,z27,z0,z2,z3,z4])],[(0,[z0,z36,z1,z2,z3,z996]),(0,[z69,z0,z16,z278,z3,z4]),(0,[z10,z108,z1,z2,z3,z562]),(0,[z10,z0,z16,z2,z3,z228]),(0,[z10,z0,z1,z2,z214,z17]),(0,[z10,z0,z1,z2,z3,z1030]),(0,[z1031,z10,z1,z2,z3,z4]),(0,[z10,z0,z1032,z2,z3,z4])],[(0,[z10,z164,z0,z2,z3,z420]),(0,[z10,z16,z2,z200,z3,z4]),(0,[z157,z10,z16,z2,z46,z4]),(0,[z10,z0,z1033,z2,z3,z4]),(0,[z10,z0,z1,z181,z21,z4])],[(0,[z248,z36,z16,z2,z3,z4]),(0,[z10,z1034,z1,z2,z3,z4]),(0,[z119,z0,z1,z2,z78,z220]),(0,[z10,z248,z16,z2,z3,z17]),(0,[z10,z1035,z0,z2,z3,z4]),(0,[z20,z378,z1,z2,z3,z4])],[(0,[z36,z16,z2,z3,z21,z4]),(0,[z10,z1036,z0,z1,z2,z3]),(0,[z376,z0,z1,z2,z3,z147]),(0,[z10,z0,z1,z2,z3,z75]),(0,[z10,z1037,z0,z2,z3,z4])],[(0,[z36,z16,z2,z3,z4,z287]),(0,[z10,z36,z1,z2,z3,z17]),(0,[z106,z36,z16,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z1038]),(0,[z10,z0,z1,z2,z3,z1020]),(0,[z10,z318,z16,z2,z3,z4])],[(0,[z10,z1,z2,z3,z81,z17]),(0,[z0,z670,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z1039])],[(0,[z1040,z0,z1,z2,z3,z4]),(0,[z758,z36,z1,z2,z3,z4]),(0,[z10,z183,z1,z2,z3,z76]),(0,[z10,z0,z23,z2,z3,z84]),(0,[z10,z0,z874,z2,z3,z179])]],
   [[(0,[z0,z36,z1,z2,z3,z17]),(0,[z36,z1,z2,z33,z3,z17]),(0,[z63,z0,z36,z1,z2,z3]),(0,[z10,z1041,z16,z2,z3,z4]),(0,[z0,z1,z581,z202,z3,z4]),(0,[z10,z344,z16,z2,z3,z4]),(0,[z0,z70,z1,z2,z3,z17]),(0,[z10,z211,z0,z2,z3,z84]),(0,[z55,z0,z1,z2,z3,z84]),(0,[z0,z1042,z1,z2,z3,z4])],[(0,[z10,z0,z1,z1043,z3,z4]),(0,[z10,z0,z16,z2,z3,z73]),(0,[z10,z16,z2,z46,z3,z17]),(0,[z162,z0,z1,z2,z3,z17])],[(0,[z93,z36,z16,z2,z3,z4]),(0,[z10,z218,z16,z2,z3,z4]),(0,[z10,z0,z1,z284,z3,z4]),(0,[z1044,z0,z1,z2,z3,z4])],[(0,[z6,z0,z357,z2,z3,z179]),(0,[z34,z248,z16,z2,z3,z4]),(0,[z1045,z0,z1,z2,z3,z4]),(0,[z10,z0,z2,z3,z4,z154]),(0,[z0,z1046,z1,z2,z3,z4])],[(0,[z10,z27,z0,z2,z3,z195]),(0,[z36,z16,z2,z46,z3,z4]),(0,[z10,z289,z16,z2,z3,z4]),(0,[z13,z0,z1,z2,z3,z861]),(0,[z10,z16,z2,z3,z4,z17])],[(0,[z124,z36,z194,z2,z3,z4]),(0,[z6,z71,z1,z72,z3,z4]),(0,[z10,z1,z16,z2,z3,z66]),(0,[z187,z27,z0,z2,z3,z4])],[(0,[z22,z0,z1,z2,z3,z4]),(0,[z339,z36,z1,z2,z3,z4]),(0,[z10,z707,z289,z2,z3,z4]),(0,[z0,z95,z2,z3,z4,z40]),(0,[z10,z0,z1,z2,z3,z1047])],[(0,[z36,z1,z2,z134,z3,z17]),(0,[z10,z104,z1,z2,z3,z17]),(0,[z0,z1048,z1,z2,z3,z4])],[(0,[z116,z36,z1,z2,z3,z4]),(0,[z157,z10,z16,z2,z3,z4]),(0,[z1049,z0,z1,z2,z3,z4]),(0,[z157,z10,z1,z2,z21,z228]),(0,[z97,z0,z1,z2,z3,z17]),(0,[z26,z166,z1,z2,z3,z4])],[(0,[z10,z16,z2,z3,z1050,z4]),(0,[z86,z121,z0,z2,z3,z41])],[(0,[z6,z0,z1,z2,z3,z102]),(0,[z210,z0,z16,z2,z3,z4]),(0,[z919,z10,z16,z2,z3,z4]),(0,[z10,z27,z0,z2,z3,z810]),(0,[z10,z0,z192,z2,z3,z109]),(0,[z86,z10,z0,z2,z3,z41])],[(0,[z44,z36,z16,z2,z3,z4]),(0,[z10,z695,z1,z2,z3,z17]),(0,[z59,z108,z1,z2,z3,z40]),(0,[z10,z1051,z1,z2,z3,z4]),(0,[z10,z444,z16,z2,z3,z17]),(0,[z10,z234,z16,z2,z3,z17]),(0,[z10,z87,z16,z2,z3,z4]),(0,[z1052,z0,z1,z2,z3,z4])],[(0,[z36,z16,z2,z3,z247,z4]),(0,[z1053,z0,z39,z2,z3,z4]),(0,[z10,z92,z16,z2,z46,z4]),(0,[z10,z16,z2,z3,z4,z622]),(0,[z10,z0,z216,z2,z3,z84])],[(0,[z6,z743,z0,z1,z2,z3]),(0,[z10,z0,z1,z2,z214,z75]),(0,[z10,z1054,z1,z2,z3,z4])],[(0,[z429,z0,z36,z2,z3,z4]),(0,[z10,z0,z16,z2,z91,z4]),(0,[z10,z0,z1,z2,z3,z679]),(0,[z1055,z0,z1,z2,z3,z4])],[(0,[z183,z36,z23,z2,z3,z4]),(0,[z10,z0,z1,z2,z1056,z4]),(0,[z10,z1,z16,z2,z3,z43])]],
   [[(0,[z6,z0,z16,z2,z3,z4]),(0,[z10,z89,z1,z2,z3,z4]),(0,[z36,z1,z2,z199,z3,z17]),(0,[z10,z0,z1057,z2,z3,z4]),(0,[z10,z0,z1058,z2,z3,z4]),(0,[z211,z0,z261,z2,z3,z4])],[(0,[z10,z16,z2,z3,z17,z17]),(0,[z10,z0,z1,z2,z74,z84]),(0,[z10,z1,z2,z3,z84,z230]),(0,[z1059,z0,z1,z2,z3,z4])],[(0,[z169,z36,z1,z2,z3,z4]),(0,[z86,z10,z0,z2,z3,z622])],[(0,[z0,z89,z1,z2,z3,z4]),(0,[z158,z36,z1,z90,z3,z4]),(0,[z10,z0,z1,z2,z3,z1060]),(0,[z10,z27,z289,z2,z3,z4]),(1,[z42,z16,z2,z3,z4]),(0,[z509,z10,z16,z2,z3,z17]),(0,[z10,z0,z23,z2,z3,z17])],[(0,[z1061,z0,z1,z2,z3,z4]),(0,[z157,z36,z1,z2,z3,z17]),(0,[z0,z36,z1,z2,z3,z75]),(0,[z10,z1062,z16,z2,z3,z4]),(0,[z119,z10,z16,z2,z3,z17]),(0,[z10,z0,z1,z2,z3,z1063]),(0,[z55,z0,z1,z2,z3,z17]),(0,[z10,z0,z1,z269,z82,z17]),(0,[z10,z0,z1,z2,z3,z1064]),(0,[z10,z0,z603,z2,z3,z4])],[(0,[z1065,z0,z1,z2,z3,z4]),(0,[z106,z0,z68,z2,z3,z4]),(0,[z10,z16,z2,z3,z220,z17]),(0,[z10,z0,z369,z2,z3,z84]),(0,[z162,z0,z1,z2,z3,z75])],[(0,[z10,z0,z16,z2,z3,z420]),(0,[z10,z0,z1066,z2,z3,z4]),(0,[z10,z248,z16,z2,z3,z128]),(0,[z10,z0,z16,z2,z3,z640]),(0,[z0,z1,z2,z3,z84,z149])],[(0,[z10,z88,z1,z2,z3,z424]),(0,[z10,z0,z1067,z2,z3,z4]),(0,[z10,z1068,z16,z2,z3,z4]),(0,[z10,z1,z16,z2,z3,z65]),(0,[z518,z10,z0,z1,z430,z3])],[(0,[z528,z36,z1,z2,z3,z4]),(0,[z159,z0,z1,z2,z3,z205]),(0,[z10,z1069,z1,z2,z3,z4])],[(0,[z36,z1,z269,z2,z3,z17]),(0,[z10,z0,z1,z2,z3,z955]),(0,[z140,z10,z16,z2,z3,z17]),(0,[z10,z0,z1,z2,z3,z1070]),(0,[z158,z10,z27,z90,z3,z4]),(0,[z10,z0,z1,z2,z1071,z4]),(0,[z10,z0,z1,z2,z3,z43]),(0,[z10,z1,z2,z46,z746,z4]),(0,[z10,z1072,z0,z1,z2,z3]),(0,[z10,z104,z357,z2,z3,z4]),(0,[z10,z1013,z2,z3,z4,z230]),(0,[z10,z1,z2,z3,z31,z230])],[(0,[z0,z36,z1,z284,z3,z4]),(0,[z6,z0,z1,z2,z184,z4]),(0,[z10,z117,z16,z2,z3,z17]),(0,[z42,z0,z1,z2,z3,z228]),(0,[z10,z0,z1073,z2,z3,z4]),(0,[z10,z0,z266,z2,z3,z147])],[(0,[z0,z36,z1,z2,z3,z128]),(0,[z0,z36,z2,z3,z4,z154]),(0,[z10,z0,z1,z2,z3,z1074]),(0,[z10,z425,z16,z2,z3,z4]),(0,[z151,z10,z16,z2,z3,z17]),(0,[z10,z1,z2,z3,z76,z17]),(0,[z20,z10,z1,z2,z3,z733])],[(0,[z27,z36,z16,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z495]),(0,[z10,z166,z16,z2,z3,z4]),(0,[z10,z16,z2,z1075,z3,z4]),(0,[z1076,z0,z1,z2,z3,z4]),(0,[z10,z0,z1,z2,z404,z17])],[(0,[z83,z36,z16,z2,z3,z4]),(0,[z0,z304,z1,z2,z3,z142]),(0,[z157,z10,z1,z2,z1077,z4]),(0,[z829,z0,z1,z2,z3,z4])],[(0,[z36,z357,z1,z2,z3,z17]),(0,[z450,z36,z1,z2,z3,z4]),(0,[z13,z10,z16,z2,z3,z17]),(0,[z568,z0,z1,z2,z3,z84]),(0,[z197,z0,z2,z3,z4,z41]),(0,[z0,z1,z2,z3,z31,z149])],[(0,[z175,z10,z1,z2,z3,z17]),(0,[z0,z1,z2,z3,z4,z1078]),(0,[z0,z1,z2,z3,z4,z1079])]],
   [[(0,[z36,z1,z2,z3,z857,z4]),(0,[z10,z0,z1080,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1081]),(0,[z10,z104,z1,z2,z3,z148])],[(0,[z124,z36,z16,z2,z3,z4]),(0,[z415,z0,z1,z2,z3,z4]),(0,[z376,z0,z16,z2,z3,z4]),(0,[z10,z189,z16,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z65]),(0,[z10,z0,z2,z3,z4,z1082]),(0,[z10,z0,z1,z2,z33,z1083])],[(0,[z36,z1,z2,z3,z293,z17]),(0,[z36,z1,z2,z3,z4,z230]),(0,[z201,z36,z1,z2,z3,z17]),(0,[z137,z0,z1,z2,z3,z276]),(0,[z10,z133,z108,z1,z2,z3]),(0,[z10,z0,z1,z2,z3,z76]),(0,[z10,z234,z0,z2,z394,z4]),(0,[z1084,z0,z1,z2,z3,z4]),(0,[z10,z0,z573,z2,z3,z84]),(0,[z378,z1,z2,z3,z4,z230])],[(0,[z0,z36,z1,z171,z3,z172]),(0,[z578,z335,z0,z2,z3,z4]),(0,[z1085,z0,z1,z2,z3,z4])],[(0,[z36,z1,z16,z2,z3,z4]),(0,[z381,z0,z1,z2,z3,z40]),(0,[z42,z27,z0,z2,z3,z4]),(0,[z10,z0,z1,z1086,z2,z3])],[(0,[z6,z36,z16,z2,z3,z4]),(0,[z10,z0,z1087,z2,z3,z4]),(0,[z10,z335,z16,z2,z3,z4]),(0,[z10,z160,z0,z2,z3,z73]),(0,[z10,z0,z1,z2,z74,z17])],[(0,[z10,z0,z1088,z2,z3,z4]),(0,[z86,z10,z0,z2,z3,z287])],[(0,[z183,z36,z1,z2,z3,z4]),(0,[z10,z1,z275,z2,z3,z17]),(0,[z10,z0,z1,z2,z3,z730]),(0,[z10,z0,z357,z2,z3,z625]),(0,[z10,z0,z1089,z2,z3,z4])],[(0,[z10,z0,z1,z2,z1090,z4])],[(0,[z10,z0,z1,z2,z3,z1091]),(0,[z10,z0,z1,z2,z3,z1092]),(0,[z59,z0,z1,z2,z1093,z3]),(0,[z10,z0,z1,z1094,z2,z3]),(0,[z10,z1,z2,z3,z963,z17]),(0,[z10,z1095,z1,z2,z3,z4])],[(0,[z0,z259,z1,z2,z3,z562]),(0,[z10,z27,z116,z2,z3,z4]),(0,[z10,z0,z2,z3,z4,z1096]),(0,[z157,z101,z1,z2,z21,z4]),(0,[z10,z189,z1,z2,z3,z915]),(0,[z1097,z0,z1,z2,z3,z4])],[(0,[z36,z1,z2,z3,z84,z17]),(0,[z6,z63,z0,z1,z2,z3]),(0,[z0,z95,z2,z94,z3,z4]),(0,[z10,z16,z2,z3,z4,z66]),(0,[z517,z0,z1,z2,z3,z4]),(0,[z1098,z0,z1,z2,z3,z4]),(0,[z97,z0,z1,z2,z3,z56])],[(0,[z183,z45,z16,z2,z3,z4]),(0,[z526,z0,z1,z2,z3,z4])],[(0,[z10,z0,z1099,z2,z3,z4]),(0,[z119,z743,z0,z1,z2,z220]),(0,[z1100,z0,z1,z2,z3,z4]),(0,[z197,z0,z1,z2,z3,z179])],[(0,[z36,z1,z2,z3,z79,z17]),(0,[z6,z27,z88,z2,z3,z4]),(0,[z10,z0,z1,z2,z3,z1101]),(0,[z10,z0,z16,z2,z3,z221]),(0,[z10,z471,z16,z2,z3,z4]),(0,[z378,z0,z1,z2,z3,z4]),(0,[z108,z1,z2,z3,z4,z40]),(0,[z10,z71,z16,z2,z3,z4]),(0,[z42,z0,z1,z181,z3,z4])],[(0,[z0,z1102,z1,z2,z3,z4]),(0,[z6,z16,z2,z90,z3,z4]),(0,[z10,z16,z2,z3,z297,z17])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z10,z16,z2,z3,z1020]),(0,[z116,z39,z2,z3,z221]),(0,[z207,z16,z2,z3,z65])],[(0,[z0,z300,z2,z3,z4]),(0,[z16,z2,z3,z4,z1079])],[(0,[z0,z1,z2,z3,z1103]),(0,[z250,z16,z2,z3,z17]),(0,[z10,z0,z2,z3,z1104])],[(0,[z339,z39,z2,z3,z102]),(0,[z197,z0,z2,z3,z41]),(0,[z0,z1,z581,z3,z17]),(0,[z10,z295,z2,z3,z17])],[(0,[z161,z36,z37,z3,z17])],[(0,[z36,z16,z2,z3,z147]),(0,[z442,z0,z1,z2,z404])],[(0,[z36,z1,z243,z3,z4]),(0,[z36,z414,z2,z3,z4]),(0,[z10,z16,z2,z3,z487]),(0,[z70,z1,z243,z3,z4]),(0,[z10,z0,z615,z3,z84])],[(0,[z10,z16,z2,z3,z631])]],
   [[(0,[z10,z322,z2,z3,z17]),(0,[z10,z192,z90,z91,z4])],[(0,[z133,z36,z16,z2,z134]),(0,[z10,z16,z2,z3,z635]),(0,[z10,z16,z2,z3,z638])],[(0,[z89,z1,z2,z3,z17]),(0,[z627,z16,z655,z3,z4]),(0,[z36,z385,z2,z3,z148]),(0,[z1105,z0,z2,z3,z4]),(0,[z0,z300,z2,z3,z102]),(0,[z399,z1,z2,z3,z17])],[(0,[z36,z16,z181,z3,z4]),(0,[z750,z1,z2,z3,z17]),(0,[z197,z0,z2,z3,z622])],[(0,[z36,z11,z2,z3,z17]),(0,[z0,z1,z2,z107,z84]),(0,[z10,z192,z181,z3,z4])],[(0,[z36,z95,z2,z3,z17]),(0,[z10,z948,z2,z3,z17]),(0,[z223,z16,z2,z3,z4]),(0,[z210,z1,z243,z3,z4])],[(0,[z36,z1,z2,z91,z17]),(0,[z0,z36,z615,z3,z4]),(0,[z0,z1106,z2,z3,z4]),(0,[z0,z39,z2,z3,z443])],[(0,[z36,z1107,z2,z3,z4]),(0,[z418,z16,z2,z3,z4]),(0,[z10,z27,z0,z2,z32]),(0,[z10,z1,z243,z3,z65])]],
   [[],[(0,[z36,z204,z2,z3,z4]),(0,[z36,z1,z284,z3,z17]),(0,[z30,z36,z2,z3,z17]),(0,[z423,z16,z2,z3,z4]),(0,[z10,z0,z1,z270,z17])],[(0,[z1108,z1,z2,z3,z4]),(0,[z16,z2,z3,z4,z5]),(0,[z0,z39,z2,z3,z996]),(0,[z666,z1,z2,z3,z40]),(0,[z10,z16,z2,z3,z66]),(0,[z16,z2,z3,z4,z9]),(0,[z10,z266,z2,z746,z4])],[(0,[z10,z16,z2,z3,z653])],[(0,[z34,z178,z2,z3,z4]),(0,[z540,z16,z2,z3,z17])],[(0,[z36,z1,z762,z3,z302]),(0,[z0,z1,z2,z3,z1109]),(0,[z10,z16,z2,z3,z1110]),(0,[z10,z379,z1,z79,z17]),(0,[z508,z1,z2,z3,z5])],[(0,[z36,z135,z2,z3,z17]),(0,[z10,z178,z2,z3,z128])],[(0,[z83,z36,z828,z3,z4])]],
   [[(0,[z743,z36,z16,z2,z3]),(0,[z104,z310,z2,z3,z41])],[(0,[z89,z311,z2,z3,z4])],[(0,[z0,z39,z2,z3,z1012]),(0,[z143,z16,z2,z3,z128]),(0,[z10,z0,z615,z3,z17])],[(0,[z36,z16,z2,z3,z4]),(0,[z36,z16,z2,z3,z812]),(0,[z70,z16,z2,z3,z4]),(0,[z0,z77,z2,z3,z495]),(0,[z42,z16,z2,z3,z84]),(0,[z187,z178,z2,z3,z4])],[(0,[z10,z16,z2,z3,z43]),(0,[z698,z1,z2,z3,z17]),(0,[z45,z1,z2,z3,z139])],[(0,[z10,z16,z2,z3,z547]),(0,[z10,z0,z2,z3,z1111]),(0,[z10,z1,z2,z746,z147])],[(0,[z6,z16,z2,z3,z25]),(0,[z0,z39,z2,z3,z587]),(0,[z114,z16,z2,z3,z4])],[(0,[z89,z11,z2,z3,z4]),(0,[z281,z16,z2,z3,z4]),(0,[z36,z1,z2,z3,z804]),(0,[z696,z0,z2,z3,z40]),(0,[z10,z16,z2,z404,z17]),(0,[z197,z0,z2,z3,z287]),(0,[z10,z104,z2,z3,z1112])]],
   [[(0,[z339,z39,z2,z3,z1020]),(0,[z697,z1,z2,z3,z40])],[(0,[z0,z1,z2,z3,z1113]),(0,[z10,z16,z2,z3,z681]),(0,[z10,z1,z243,z3,z109])],[(0,[z376,z1,z2,z746,z4]),(0,[z22,z1,z2,z3,z139]),(0,[z10,z166,z37,z74,z4])],[(0,[z0,z36,z2,z3,z452]),(0,[z36,z447,z2,z3,z4]),(0,[z10,z0,z16,z430,z3]),(0,[z10,z16,z2,z3,z566]),(0,[z10,z1,z243,z3,z73]),(0,[z10,z1,z181,z746,z4]),(0,[z328,z1,z2,z3,z375])],[(0,[z36,z16,z2,z3,z102]),(0,[z10,z16,z2,z3,z688]),(0,[z0,z95,z2,z773,z3]),(0,[z10,z16,z2,z3,z65]),(0,[z10,z0,z1,z4,z1114])],[(0,[z36,z16,z2,z3,z205]),(0,[z10,z380,z2,z3,z41]),(0,[z206,z16,z2,z3,z4]),(0,[z10,z397,z2,z3,z17])],[(0,[z36,z16,z2,z412,z4]),(0,[z1102,z1,z2,z3,z17]),(0,[z10,z0,z2,z3,z1115]),(0,[z123,z1,z2,z3,z139])],[(0,[z36,z1,z2,z3,z820]),(0,[z835,z16,z2,z3,z4]),(0,[z10,z0,z1,z2,z32])]],
   [[(0,[z36,z1,z2,z3,z1116]),(0,[z36,z2,z3,z154,z17]),(0,[z10,z16,z2,z74,z17])],[(0,[z936,z16,z2,z3,z4]),(0,[z89,z1,z2,z3,z420]),(0,[z10,z166,z401,z3,z4])],[(0,[z36,z16,z2,z235,z4]),(0,[z36,z16,z2,z426,z4])],[(0,[z36,z16,z2,z3,z195])],[(0,[z310,z16,z2,z3,z4]),(0,[z36,z16,z2,z214,z4]),(0,[z10,z903,z2,z3,z17]),(0,[z845,z16,z2,z3,z4]),(0,[z10,z27,z2,z3,z139]),(0,[z10,z0,z1,z1117,z3])],[(0,[z36,z16,z2,z3,z312]),(0,[z36,z1,z2,z3,z692]),(0,[z273,z112,z2,z3,z17]),(0,[z10,z104,z2,z3,z41])],[(0,[z108,z1,z2,z3,z40]),(0,[z0,z39,z2,z3,z1020]),(0,[z10,z16,z2,z3,z583]),(0,[z108,z1,z2,z1093,z3]),(0,[z16,z2,z3,z17,z100]),(0,[z10,z0,z615,z3,z75])],[(0,[z36,z934,z2,z3,z4]),(0,[z856,z16,z2,z3,z4]),(0,[z841,z16,z2,z3,z4]),(0,[z42,z16,z2,z3,z17]),(0,[z654,z16,z2,z3,z4]),(0,[z10,z16,z2,z3,z570]),(0,[z10,z166,z615,z3,z4]),(0,[z10,z122,z2,z3,z452])]],
   [[],[(0,[z36,z16,z2,z33,z58]),(0,[z580,z108,z2,z3,z40]),(0,[z407,z0,z2,z3,z41])],[(0,[z328,z16,z2,z3,z4]),(0,[z42,z1,z181,z21,z4])],[(0,[z36,z309,z2,z3,z4]),(0,[z13,z16,z2,z3,z861]),(0,[z398,z307,z2,z3,z17])],[(0,[z93,z16,z2,z94,z17]),(0,[z197,z104,z2,z3,z41])],[(0,[z10,z16,z1019,z3,z4]),(0,[z0,z1,z2,z3,z1118]),(0,[z10,z16,z2,z3,z28]),(0,[z197,z16,z2,z3,z17]),(0,[z10,z178,z2,z3,z76]),(0,[z10,z0,z1,z2,z1119]),(0,[z10,z104,z2,z3,z622])],[(0,[z63,z36,z16,z2,z3]),(0,[z36,z357,z2,z3,z19]),(0,[z36,z1,z2,z3,z313]),(0,[z6,z16,z2,z3,z66]),(0,[z339,z300,z2,z3,z4]),(0,[z10,z0,z1,z3,z1120])],[(0,[z36,z23,z2,z3,z4]),(0,[z36,z16,z2,z3,z424]),(0,[z10,z16,z2,z3,z722])]],
   [[(0,[z36,z322,z2,z3,z4])],[(0,[z36,z16,z341,z2,z3]),(0,[z10,z365,z2,z3,z17]),(0,[z485,z16,z2,z3,z4]),(0,[z10,z110,z2,z3,z139]),(0,[z10,z0,z2,z3,z1121]),(0,[z670,z1,z2,z3,z570])],[(0,[z516,z1,z2,z3,z17]),(0,[z339,z39,z2,z3,z84])],[(0,[z10,z1,z90,z91,z205]),(0,[z162,z0,z37,z74,z4])],[],[(0,[z36,z16,z2,z931,z3]),(0,[z36,z1,z2,z3,z334]),(0,[z36,z948,z2,z3,z4]),(0,[z108,z16,z2,z3,z40])],[(0,[z59,z0,z1,z2,z404]),(0,[z0,z1122,z2,z3,z4])],[(0,[z36,z266,z2,z3,z17]),(0,[z379,z36,z1,z4,z79]),(0,[z755,z1,z2,z3,z40]),(0,[z27,z108,z2,z3,z40]),(0,[z26,z0,z615,z3,z4]),(0,[z10,z865,z2,z3,z41])]],
   [[(0,[z27,z89,z2,z3,z4])],[(0,[z0,z300,z2,z3,z84])],[(0,[z339,z39,z2,z3,z221]),(0,[z10,z16,z2,z746,z4]),(0,[z829,z16,z2,z3,z17]),(0,[z10,z0,z2,z3,z1123])],[(0,[z289,z1,z2,z3,z495]),(0,[z10,z27,z2,z746,z4]),(0,[z10,z295,z2,z3,z139]),(0,[z388,z104,z2,z3,z41])],[(0,[z1124,z16,z2,z3,z4]),(0,[z36,z348,z2,z3,z4]),(0,[z388,z16,z2,z3,z17])],[(0,[z36,z16,z2,z3,z290]),(0,[z36,z129,z303,z3,z17]),(0,[z541,z0,z1,z2,z931]),(0,[z36,z1,z2,z3,z351]),(0,[z10,z1,z2,z746,z312])],[(0,[z0,z414,z2,z3,z40])],[(0,[z10,z618,z2,z3,z17]),(0,[z304,z1,z2,z3,z861]),(0,[z10,z16,z2,z184,z17]),(0,[z10,z23,z2,z3,z139])]],
   [[(0,[z866,z0,z2,z3,z221]),(0,[z666,z39,z2,z3,z4]),(0,[z0,z95,z2,z3,z127]),(0,[z162,z0,z615,z3,z4])],[(0,[z36,z311,z2,z3,z17]),(0,[z42,z16,z284,z3,z4]),(0,[z10,z104,z2,z3,z287]),(0,[z10,z16,z2,z3,z757]),(0,[z10,z1,z243,z3,z205])],[(0,[z36,z1,z2,z3,z363])],[(0,[z6,z0,z1,z2,z32]),(0,[z10,z16,z2,z3,z759]),(0,[z10,z403,z16,z2,z236]),(0,[z10,z160,z243,z3,z4]),(0,[z10,z490,z2,z3,z17])],[(0,[z0,z95,z2,z3,z495])],[(0,[z27,z36,z2,z3,z17]),(0,[z892,z16,z2,z3,z4])],[(0,[z339,z579,z2,z3,z4]),(0,[z339,z39,z2,z3,z17]),(0,[z10,z16,z761,z3,z4]),(0,[z10,z637,z2,z3,z17])],[(0,[z36,z16,z2,z3,z12]),(0,[z218,z36,z2,z3,z4]),(0,[z36,z16,z2,z404,z4]),(0,[z36,z1,z2,z3,z375]),(0,[z416,z36,z2,z3,z496]),(0,[z178,z143,z2,z3,z4]),(0,[z8,z0,z2,z3,z469]),(0,[z10,z27,z243,z3,z4]),(0,[z10,z947,z2,z3,z17])]],
   [[(0,[z36,z1,z181,z3,z17]),(0,[z0,z39,z2,z3,z221]),(0,[z335,z339,z2,z3,z4]),(0,[z0,z573,z2,z3,z382])],[(0,[z10,z951,z2,z3,z17]),(0,[z2,z3,z4,z497,z5])],[(0,[z6,z16,z2,z3,z17]),(0,[z36,z16,z2,z3,z31]),(0,[z27,z0,z581,z3,z4]),(0,[z223,z1,z2,z3,z17]),(0,[z10,z429,z2,z3,z139])],[],[(0,[z36,z889,z2,z3,z4]),(0,[z45,z16,z2,z3,z4]),(0,[z119,z0,z1,z2,z967]),(0,[z121,z0,z2,z3,z452])],[(0,[z36,z397,z2,z3,z4]),(0,[z0,z1,z2,z3,z1125]),(0,[z36,z1,z2,z3,z443]),(0,[z10,z27,z0,z430,z3])],[],[(0,[z36,z2,z3,z4,z497]),(0,[z1126,z0,z2,z3,z4]),(0,[z378,z0,z1,z4,z270])]],
   [[(0,[z36,z16,z2,z74,z4]),(0,[z8,z0,z2,z3,z428])],[(0,[z36,z408,z2,z3,z4]),(0,[z10,z16,z2,z3,z775]),(0,[z108,z1,z2,z773,z3]),(0,[z10,z16,z2,z3,z777]),(0,[z10,z192,z243,z3,z4]),(0,[z10,z616,z2,z3,z610]),(0,[z57,z0,z1,z2,z32])],[(0,[z444,z36,z2,z553,z4]),(0,[z647,z16,z2,z3,z4]),(0,[z0,z1,z2,z1127,z4]),(0,[z36,z414,z2,z3,z17]),(0,[z240,z178,z2,z3,z4])],[],[(0,[z36,z903,z2,z3,z4]),(0,[z0,z95,z2,z3,z503]),(0,[z518,z10,z16,z3,z293])],[(0,[z339,z112,z2,z3,z4]),(0,[z477,z0,z2,z3,z41]),(0,[z10,z16,z762,z3,z302]),(0,[z10,z16,z2,z3,z788]),(0,[z10,z0,z1,z84,z270])],[(0,[z916,z16,z2,z3,z4]),(0,[z207,z1,z243,z3,z4])],[(0,[z10,z1,z2,z3,z139])]],
   [[(0,[z10,z1128,z2,z3,z4]),(0,[z42,z16,z2,z3,z43]),(0,[z10,z16,z672,z3,z4]),(0,[z57,z16,z2,z3,z17])],[(0,[z10,z16,z2,z231,z58]),(0,[z10,z135,z181,z21,z4])],[(0,[z680,z16,z2,z3,z4]),(0,[z36,z913,z2,z3,z4])],[(0,[z36,z16,z2,z3,z476]),(0,[z0,z1,z2,z107,z17])],[(0,[z36,z16,z2,z3,z443]),(0,[z10,z178,z2,z3,z4])],[(0,[z10,z0,z1,z31,z270])],[(0,[z0,z414,z2,z3,z503])],[(0,[z36,z1,z2,z3,z915]),(0,[z647,z0,z1,z2,z33]),(0,[z10,z16,z2,z3,z804]),(0,[z240,z27,z2,z3,z424])]],
   [[(0,[z36,z16,z2,z3,z996]),(0,[z143,z16,z2,z3,z4]),(0,[z549,z0,z2,z3,z41])],[(0,[z36,z365,z2,z3,z4]),(0,[z259,z16,z2,z3,z142]),(0,[z10,z993,z2,z3,z17])],[(0,[z541,z16,z2,z247,z4]),(0,[z6,z295,z2,z3,z17]),(0,[z153,z10,z16,z79,z17]),(0,[z206,z1,z2,z3,z17])],[(0,[z36,z1,z2,z3,z424]),(0,[z10,z208,z2,z46,z4]),(0,[z335,z0,z2,z3,z256]),(0,[z10,z0,z2,z3,z1129]),(0,[z296,z1,z2,z3,z17])],[(0,[z0,z95,z2,z3,z382]),(0,[z835,z1,z2,z3,z17])],[(0,[z36,z357,z2,z3,z496]),(0,[z852,z1,z2,z3,z17]),(0,[z10,z1,z4,z270,z230]),(0,[z10,z0,z1,z430,z3])],[(0,[z10,z238,z2,z3,z41]),(0,[z261,z16,z2,z3,z17]),(0,[z10,z16,z2,z3,z139]),(0,[z378,z16,z2,z3,z17])],[(0,[z36,z1,z2,z235,z17]),(0,[z27,z0,z2,z107,z4])]],
   [[(0,[z36,z1,z2,z3,z602]),(0,[z10,z16,z2,z3,z823])],[(0,[z310,z1,z2,z3,z17]),(0,[z36,z1,z2,z3,z1030]),(0,[z0,z579,z2,z3,z256]),(0,[z10,z1130,z2,z3,z4])],[(0,[z695,z275,z2,z3,z4]),(0,[z1046,z16,z2,z3,z4])],[(0,[z36,z1,z2,z3,z607]),(0,[z10,z16,z2,z231,z18]),(0,[z10,z1,z181,z21,z43])],[(0,[z16,z2,z3,z4,z368]),(0,[z1131,z1,z2,z3,z17]),(0,[z541,z0,z1,z2,z78]),(0,[z42,z16,z2,z3,z228]),(0,[z531,z16,z2,z3,z4]),(0,[z159,z1,z90,z91,z4]),(0,[z10,z0,z2,z3,z1132])],[(0,[z10,z1099,z2,z3,z17]),(0,[z36,z1,z2,z3,z1020]),(0,[z0,z1,z2,z3,z1133]),(0,[z10,z16,z2,z3,z692])],[(0,[z36,z194,z2,z3,z12]),(0,[z36,z1,z2,z3,z482]),(0,[z541,z16,z2,z220,z4]),(0,[z10,z1,z2,z746,z4]),(0,[z10,z30,z0,z4,z270])],[(0,[z36,z16,z2,z184,z4]),(0,[z328,z1,z2,z3,z17]),(0,[z36,z23,z2,z3,z84]),(0,[z42,z1,z2,z746,z4])]],
   [[],[(0,[z429,z36,z2,z3,z17]),(0,[z36,z16,z2,z3,z455]),(0,[z10,z16,z181,z46,z4]),(0,[z535,z16,z2,z3,z4])],[(0,[z36,z192,z2,z3,z17])],[(0,[z36,z274,z2,z3,z17]),(0,[z10,z755,z2,z3,z41]),(0,[z0,z16,z581,z3,z4]),(0,[z0,z95,z2,z3,z263]),(0,[z10,z16,z2,z3,z308]),(0,[z509,z0,z1,z2,z404])],[(0,[z36,z385,z2,z3,z179]),(0,[z10,z16,z2,z3,z729]),(0,[z106,z307,z2,z3,z17])],[(0,[z36,z110,z2,z3,z17]),(0,[z108,z1,z2,z3,z127]),(0,[z10,z166,z244,z3,z4])],[(0,[z36,z637,z2,z3,z4]),(0,[z36,z16,z2,z3,z25]),(0,[z10,z16,z2,z3,z313]),(0,[z485,z1,z2,z3,z17])],[(0,[z923,z16,z2,z3,z4])]],
   [[(0,[z310,z16,z2,z3,z17]),(0,[z10,z178,z2,z3,z424]),(0,[z702,z1,z2,z3,z17]),(0,[z829,z0,z1,z2,z231])],[(0,[z108,z1,z2,z3,z495]),(0,[z51,z16,z2,z3,z17])],[(0,[z10,z311,z2,z3,z17]),(0,[z89,z16,z2,z3,z4]),(0,[z323,z1,z2,z3,z17]),(0,[z10,z601,z402,z3,z17]),(0,[z399,z16,z2,z3,z4]),(0,[z159,z1,z243,z3,z4]),(0,[z10,z1,z243,z3,z4])],[(0,[z36,z1,z2,z3,z12]),(0,[z89,z1,z2,z3,z195]),(0,[z117,z36,z2,z3,z287]),(0,[z403,z36,z1,z2,z236]),(0,[z6,z16,z2,z3,z43]),(0,[z10,z16,z90,z91,z4]),(0,[z10,z379,z16,z4,z79]),(0,[z10,z0,z615,z3,z4])],[(0,[z36,z16,z2,z3,z1020])],[(0,[z36,z11,z2,z3,z195]),(0,[z454,z1,z2,z111,z17]),(0,[z27,z0,z2,z3,z495]),(0,[z10,z16,z2,z3,z334]),(0,[z10,z1,z181,z21,z17])],[(0,[z36,z16,z2,z91,z4]),(0,[z36,z513,z2,z3,z179]),(0,[z537,z16,z2,z3,z4]),(0,[z538,z16,z2,z3,z4]),(0,[z10,z185,z243,z3,z4]),(0,[z399,z1,z2,z3,z804])],[(0,[z1040,z16,z2,z3,z4]),(0,[z36,z295,z2,z3,z17]),(0,[z10,z16,z181,z3,z4]),(0,[z10,z105,z615,z3,z4]),(0,[z654,z1,z2,z3,z610])]],
   [[(0,[z339,z39,z2,z3,z658]),(0,[z42,z16,z181,z3,z4]),(0,[z197,z0,z2,z3,z469]),(0,[z0,z1,z2,z3,z1134])],[(0,[z10,z508,z16,z2,z3]),(0,[z10,z616,z2,z3,z17])],[(0,[z234,z36,z2,z297,z17]),(0,[z36,z1,z2,z967,z3]),(0,[z10,z1135,z2,z3,z4]),(0,[z10,z16,z284,z3,z43]),(0,[z654,z616,z2,z3,z4])],[(0,[z6,z16,z2,z3,z65]),(0,[z108,z365,z2,z3,z40])],[(0,[z0,z300,z2,z3,z221])],[(0,[z10,z16,z2,z3,z351]),(0,[z685,z16,z2,z3,z17]),(0,[z986,z16,z2,z3,z4])],[(0,[z86,z36,z2,z3,z287]),(0,[z36,z16,z2,z3,z420])],[(0,[z500,z16,z2,z3,z4]),(0,[z36,z1067,z2,z3,z4]),(0,[z10,z0,z2,z3,z1136]),(0,[z49,z16,z2,z3,z17])]],
   [[(0,[z164,z89,z2,z3,z4])],[(0,[z108,z1,z2,z3,z503]),(0,[z10,z16,z243,z3,z4]),(0,[z319,z0,z2,z3,z41]),(0,[z197,z0,z2,z3,z428])],[(0,[z627,z1,z655,z3,z17]),(0,[z10,z1,z2,z3,z1137])],[(0,[z1138,z16,z2,z3,z4]),(0,[z10,z16,z2,z3,z879])],[(0,[z518,z36,z16,z199,z3]),(0,[z6,z104,z2,z3,z41]),(0,[z101,z16,z2,z3,z43]),(0,[z45,z16,z2,z3,z84])],[],[(0,[z36,z194,z2,z3,z17]),(0,[z36,z16,z2,z3,z66]),(0,[z1,z2,z3,z5,z17]),(0,[z36,z552,z2,z3,z4]),(0,[z10,z16,z2,z3,z1139])],[(0,[z10,z16,z2,z3,z375])]],
   [[(0,[z0,z1140,z2,z3,z4]),(0,[z0,z300,z2,z3,z17]),(0,[z10,z1141,z2,z3,z4]),(0,[z10,z0,z2,z3,z452])],[(0,[z10,z16,z2,z91,z17])],[(0,[z160,z36,z2,z3,z17]),(0,[z6,z1,z2,z746,z4])],[(0,[z10,z1,z243,z184,z4]),(0,[z535,z0,z2,z3,z41])],[(0,[z0,z1,z1142,z3,z4]),(0,[z10,z16,z284,z3,z17])],[(0,[z36,z1,z2,z74,z17]),(0,[z164,z36,z2,z3,z17]),(0,[z289,z95,z2,z3,z40])],[(0,[z36,z16,z2,z3,z84]),(0,[z684,z36,z1,z2,z3]),(0,[z70,z16,z2,z3,z84]),(0,[z57,z0,z1,z2,z231])],[(0,[z125,z16,z624,z3,z4]),(0,[z647,z1,z2,z3,z17]),(0,[z240,z27,z2,z3,z17]),(0,[z197,z0,z2,z3,z452])]],
   [[(0,[z36,z16,z2,z3,z43]),(0,[z711,z108,z1,z2,z3]),(0,[z10,z16,z2,z3,z320]),(0,[z10,z16,z2,z3,z406])],[(0,[z108,z1,z2,z3,z382])],[(0,[z187,z16,z2,z3,z17])],[(0,[z36,z1,z2,z3,z17]),(0,[z298,z16,z2,z3,z17]),(0,[z10,z225,z2,z3,z17])],[(0,[z10,z791,z2,z3,z17]),(0,[z10,z178,z2,z3,z84]),(0,[z593,z16,z2,z3,z4]),(0,[z10,z513,z2,z3,z19])],[(0,[z0,z1143,z2,z3,z4]),(0,[z10,z318,z2,z46,z4])],[(0,[z442,z16,z2,z3,z503]),(0,[z136,z492,z2,z3,z17]),(0,[z104,z36,z2,z3,z41]),(0,[z36,z16,z2,z3,z221]),(0,[z69,z16,z278,z3,z17]),(0,[z101,z16,z2,z3,z17]),(0,[z10,z135,z2,z746,z4])],[(0,[z1144,z16,z2,z3,z4]),(0,[z36,z185,z2,z3,z17]),(0,[z0,z1145,z2,z3,z4]),(0,[z26,z16,z2,z3,z17]),(0,[z1146,z0,z2,z3,z4]),(0,[z49,z295,z2,z3,z17])]],
   [[(0,[z143,z16,z2,z3,z84]),(0,[z45,z16,z2,z3,z17])],[(0,[z89,z194,z2,z3,z4]),(0,[z686,z1,z2,z3,z17]),(0,[z0,z573,z2,z3,z283]),(0,[z306,z39,z2,z3,z4]),(0,[z10,z448,z90,z3,z4])],[(0,[z36,z1,z2,z3,z28]),(0,[z108,z77,z2,z3,z40])],[(0,[z153,z36,z16,z4,z79]),(0,[z6,z16,z181,z3,z4])],[],[(0,[z10,z684,z16,z2,z3]),(0,[z319,z0,z2,z3,z287]),(0,[z922,z1,z2,z3,z17]),(0,[z10,z1,z2,z3,z1147]),(0,[z10,z0,z615,z3,z290])],[(0,[z0,z1,z2,z3,z1148]),(0,[z0,z16,z2,z3,z495]),(0,[z680,z1,z2,z3,z915])],[(0,[z0,z1,z2,z1149,z4]),(0,[z0,z1,z581,z3,z4]),(0,[z10,z16,z2,z3,z915]),(0,[z1100,z16,z2,z3,z4])]],
   [[(0,[z108,z1,z2,z3,z263]),(0,[z162,z16,z2,z3,z17]),(0,[z670,z16,z2,z3,z4]),(0,[z45,z23,z2,z3,z84])],[(0,[z936,z1,z2,z3,z17]),(0,[z10,z2,z3,z497,z17])],[(0,[z36,z16,z2,z3,z17]),(0,[z36,z601,z402,z3,z4]),(0,[z516,z16,z2,z3,z4]),(0,[z0,z36,z1,z2,z32]),(0,[z70,z16,z2,z3,z17]),(0,[z1042,z16,z2,z3,z4])],[(0,[z123,z27,z2,z3,z17])],[(0,[z36,z16,z2,z3,z228]),(0,[z36,z1,z2,z214,z17]),(0,[z0,z1150,z2,z3,z4]),(0,[z0,z112,z2,z3,z443]),(0,[z10,z0,z2,z3,z1151]),(0,[z10,z0,z1,z2,z1152])],[(0,[z36,z1,z181,z21,z4]),(0,[z203,z112,z2,z3,z17]),(0,[z6,z311,z2,z3,z25]),(0,[z315,z16,z2,z3,z17])],[(0,[z89,z1,z2,z3,z4]),(0,[z36,z1,z2,z3,z610]),(0,[z10,z1153,z2,z3,z17]),(0,[z10,z1,z2,z746,z84]),(0,[z261,z1,z2,z746,z4])],[(0,[z866,z339,z2,z3,z4]),(0,[z10,z16,z2,z3,z927]),(0,[z10,z208,z90,z3,z4]),(0,[z16,z2,z3,z170,z17]),(0,[z535,z0,z2,z3,z287]),(0,[z654,z1,z2,z3,z17])]],
   [[(0,[z36,z11,z2,z3,z4]),(0,[z0,z112,z2,z3,z996]),(0,[z10,z1,z2,z746,z43])],[(0,[z36,z616,z2,z3,z4]),(0,[z210,z16,z2,z3,z17]),(0,[z1048,z16,z2,z3,z4])],[(0,[z891,z16,z2,z3,z4]),(0,[z780,z16,z2,z3,z4]),(0,[z10,z216,z243,z3,z4])],[(0,[z10,z104,z2,z3,z428])],[(0,[z36,z16,z2,z3,z73]),(0,[z36,z1,z2,z184,z17]),(0,[z143,z16,z2,z3,z17]),(0,[z70,z16,z2,z3,z73])],[(0,[z36,z365,z2,z3,z17]),(0,[z10,z719,z2,z3,z17])],[(0,[z36,z1,z2,z3,z757]),(0,[z10,z16,z2,z3,z482]),(0,[z10,z508,z2,z3,z497])],[(0,[z36,z1,z2,z3,z631]),(0,[z10,z980,z16,z2,z3])]],
   [[(0,[z108,z1,z2,z3,z1113]),(0,[z123,z110,z2,z3,z17]),(0,[z49,z1,z2,z3,z139]),(0,[z10,z0,z615,z74,z4])],[(0,[z0,z951,z2,z3,z40]),(0,[z10,z444,z2,z553,z17])],[(0,[z36,z639,z2,z3,z4]),(0,[z34,z16,z2,z3,z66]),(0,[z10,z1,z243,z3,z84]),(0,[z10,z138,z2,z746,z4])],[(0,[z1154,z1,z2,z3,z4]),(0,[z954,z0,z2,z3,z40]),(0,[z10,z16,z2,z3,z488]),(0,[z319,z16,z2,z3,z17])],[],[(0,[z0,z95,z2,z3,z283]),(0,[z1155,z339,z2,z3,z4])],[(0,[z36,z16,z2,z3,z75]),(0,[z6,z1,z2,z3,z139])],[(0,[z10,z16,z2,z3,z853]),(0,[z207,z16,z2,z3,z17]),(0,[z10,z16,z181,z3,z84]),(0,[z785,z16,z2,z3,z4])]],
   [[(0,[z292,z36,z2,z3,z287]),(0,[z0,z1156,z2,z3,z4]),(0,[z380,z39,z2,z3,z4]),(0,[z10,z1,z90,z91,z17])],[(0,[z119,z16,z2,z220,z17]),(0,[z10,z16,z181,z3,z43]),(0,[z787,z16,z2,z3,z4]),(0,[z10,z104,z2,z3,z452])],[(0,[z36,z1,z2,z3,z770]),(0,[z1,z2,z3,z368,z17]),(0,[z10,z16,z2,z3,z952]),(0,[z8,z0,z2,z3,z41]),(0,[z10,z1,z2,z746,z17]),(0,[z123,z295,z2,z3,z17])],[(0,[z36,z16,z2,z3,z191]),(0,[z260,z36,z1,z3,z293]),(0,[z10,z16,z2,z404,z4]),(0,[z6,z178,z2,z3,z4]),(0,[z1155,z0,z2,z3,z4]),(0,[z97,z16,z2,z3,z17]),(0,[z10,z505,z2,z3,z41])],[(0,[z36,z16,z284,z3,z4]),(0,[z136,z68,z2,z3,z17]),(0,[z0,z1,z2,z107,z4]),(0,[z13,z16,z2,z3,z156]),(0,[z10,z1,z2,z746,z228])],[(0,[z36,z16,z2,z3,z128]),(0,[z10,z208,z2,z3,z17]),(0,[z535,z16,z2,z3,z17])],[(0,[z36,z1,z2,z3,z777]),(0,[z36,z23,z2,z3,z17]),(0,[z405,z39,z2,z3,z4]),(0,[z0,z1,z2,z3,z1157])],[(0,[z10,z756,z2,z3,z17]),(0,[z304,z16,z2,z3,z142]),(0,[z180,z16,z2,z3,z4])]],
   [[],[(0,[z36,z16,z2,z3,z640]),(0,[z0,z1,z2,z78,z107]),(0,[z711,z0,z95,z2,z3]),(0,[z1158,z0,z1,z2,z3]),(0,[z10,z0,z1159,z3,z4])],[(0,[z27,z36,z2,z3,z424]),(0,[z240,z1,z2,z3,z17]),(0,[z10,z16,z2,z967,z3]),(0,[z137,z16,z2,z3,z156])],[],[(0,[z500,z1,z2,z3,z17]),(0,[z6,z0,z1,z430,z3]),(0,[z10,z16,z2,z3,z1160]),(0,[z10,z0,z1,z4,z270])],[(0,[z36,z16,z171,z3,z172]),(0,[z36,z16,z2,z3,z56]),(0,[z36,z951,z2,z3,z17]),(0,[z0,z39,z2,z3,z431]),(0,[z16,z2,z3,z149,z17]),(0,[z892,z1,z2,z3,z17]),(0,[z10,z63,z0,z1,z270])],[(0,[z208,z36,z2,z3,z4]),(0,[z211,z36,z2,z3,z17]),(0,[z125,z16,z278,z3,z4]),(0,[z89,z1,z2,z3,z25]),(0,[z10,z1,z243,z3,z17])],[(0,[z36,z1,z2,z404,z17]),(0,[z36,z677,z2,z3,z17]),(0,[z10,z0,z1161,z3,z4])]],
   [[(0,[z36,z16,z2,z3,z679]),(0,[z919,z10,z16,z4,z79])],[(0,[z36,z1,z2,z3,z681]),(0,[z0,z1,z2,z3,z1162]),(0,[z509,z16,z2,z3,z503])],[(0,[z36,z1,z2,z3,z239]),(0,[z0,z39,z2,z3,z256]),(0,[z376,z16,z2,z3,z17])],[(0,[z36,z216,z2,z3,z17]),(0,[z42,z16,z2,z3,z4]),(0,[z0,z16,z2,z107,z4]),(0,[z108,z95,z2,z3,z40]),(0,[z10,z16,z181,z3,z17]),(0,[z675,z0,z2,z3,z41])],[(0,[z259,z16,z2,z3,z562]),(0,[z36,z1,z2,z3,z688]),(0,[z36,z77,z2,z3,z17]),(0,[z10,z16,z2,z3,z981])],[(0,[z0,z573,z2,z3,z40]),(0,[z0,z39,z2,z3,z813]),(0,[z10,z16,z181,z3,z228]),(0,[z10,z0,z16,z2,z32]),(0,[z197,z122,z2,z3,z41])],[(0,[z34,z16,z2,z3,z17]),(0,[z10,z0,z37,z74,z75])],[(0,[z59,z16,z2,z3,z503]),(0,[z10,z178,z2,z3,z66])]],
   [[],[(0,[z1102,z16,z2,z3,z4]),(0,[z0,z951,z2,z3,z503]),(0,[z36,z1,z2,z3,z700]),(0,[z0,z1,z2,z3,z1163]),(0,[z335,z0,z2,z3,z221]),(0,[z10,z776,z2,z3,z17]),(0,[z240,z16,z2,z3,z17])],[(0,[z0,z1,z2,z3,z495]),(0,[z83,z10,z828,z3,z17]),(0,[z10,z616,z181,z3,z4]),(0,[z10,z781,z2,z3,z17])],[(0,[z36,z1,z2,z3,z139]),(0,[z143,z16,z2,z3,z66]),(0,[z10,z1164,z2,z3,z4])],[(0,[z140,z112,z2,z3,z17]),(0,[z10,z16,z2,z3,z996]),(0,[z10,z16,z90,z426,z4]),(0,[z10,z1,z284,z746,z4])],[(0,[z0,z1,z1165,z3,z4]),(0,[z852,z16,z2,z3,z4])],[(0,[z123,z1,z2,z3,z17]),(0,[z10,z0,z2,z3,z1166])],[(0,[z36,z1,z2,z3,z570]),(0,[z0,z579,z2,z3,z221])]],
   [[(0,[z36,z1,z2,z231,z18])],[(0,[z732,z16,z2,z3,z4]),(0,[z6,z1,z243,z3,z4]),(0,[z6,z311,z2,z3,z17]),(0,[z593,z1,z2,z3,z17]),(0,[z121,z104,z2,z3,z41])],[(0,[z27,z36,z2,z3,z12]),(0,[z89,z1,z2,z3,z12]),(0,[z680,z1,z2,z3,z17]),(0,[z6,z0,z615,z3,z4]),(0,[z121,z16,z2,z3,z17])],[(0,[z10,z16,z2,z3,z17]),(0,[z36,z16,z2,z3,z65]),(0,[z159,z16,z2,z3,z17]),(0,[z70,z16,z2,z3,z65])],[(0,[z36,z11,z2,z3,z12]),(0,[z36,z16,z2,z3,z658]),(0,[z36,z16,z2,z3,z76]),(0,[z0,z365,z2,z3,z40])],[(0,[z695,z68,z2,z3,z17]),(0,[z10,z1,z243,z91,z4])],[(0,[z101,z1,z2,z746,z4]),(0,[z10,z0,z2,z3,z1112])],[(0,[z36,z138,z2,z3,z17]),(0,[z36,z1,z2,z3,z724]),(0,[z0,z1,z581,z3,z84])]],
   [[(0,[z10,z16,z2,z3,z1017])],[(0,[z36,z16,z2,z3,z730]),(0,[z36,z1,z2,z3,z729]),(0,[z22,z16,z2,z3,z17])],[(0,[z541,z1,z2,z247,z17]),(0,[z106,z275,z2,z3,z17])],[(0,[z508,z36,z1,z2,z3]),(0,[z10,z811,z2,z3,z17])],[(0,[z116,z300,z2,z3,z4])],[(0,[z178,z36,z2,z3,z4]),(0,[z36,z16,z2,z78,z3]),(0,[z123,z16,z2,z3,z17]),(0,[z10,z104,z2,z3,z469]),(0,[z670,z1,z2,z3,z17])],[(0,[z89,z1,z2,z3,z84]),(0,[z36,z1,z2,z3,z81]),(0,[z0,z112,z2,z3,z221]),(0,[z10,z16,z2,z412,z17]),(0,[z10,z182,z2,z3,z17])],[(0,[z201,z16,z202,z3,z17]),(0,[z319,z1,z2,z3,z17]),(0,[z10,z211,z2,z746,z4]),(0,[z1042,z1,z2,z3,z17]),(0,[z279,z1,z2,z3,z17])]],
   [[(0,[z36,z11,z2,z3,z84]),(0,[z126,z16,z2,z3,z4]),(0,[z36,z1,z90,z91,z4]),(0,[z0,z36,z1,z430,z3]),(0,[z260,z10,z16,z3,z293]),(0,[z55,z16,z2,z3,z17])],[(0,[z0,z310,z2,z3,z41]),(0,[z0,z95,z2,z3,z40]),(0,[z0,z95,z2,z1093,z3])],[(0,[z10,z16,z2,z3,z25]),(0,[z36,z1,z2,z746,z4]),(0,[z153,z36,z1,z79,z17]),(0,[z1046,z1,z2,z3,z17]),(0,[z339,z39,z2,z3,z4]),(0,[z108,z1,z2,z3,z283]),(0,[z10,z16,z2,z235,z17]),(0,[z10,z16,z2,z426,z17])],[(0,[z10,z178,z2,z3,z17])],[(0,[z580,z36,z2,z3,z17]),(0,[z10,z16,z2,z3,z1030]),(0,[z10,z16,z2,z214,z17])],[(0,[z454,z16,z2,z111,z4]),(0,[z36,z16,z2,z3,z109]),(0,[z10,z16,z181,z21,z4])],[(0,[z962,z39,z2,z3,z4]),(0,[z10,z16,z2,z3,z607]),(0,[z10,z16,z2,z3,z610]),(0,[z1048,z1,z2,z3,z17])],[(0,[z36,z756,z2,z3,z4]),(0,[z6,z0,z2,z3,z452]),(0,[z101,z16,z181,z3,z4]),(0,[z10,z1072,z16,z2,z3])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 16 512 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

def parents : List (ℕ × List W) := expandN 1 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 1 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 6) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa1 : chunkB SA 2 ((parents.drop 6).take 10) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa2 : chunkB SA 2 ((parents.drop 16).take 8) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa3 : chunkB SA 2 ((parents.drop 24).take 7) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa4 : chunkB SA 2 ((parents.drop 31).take 7) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa5 : chunkB SA 2 ((parents.drop 38).take 8) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa6 : chunkB SA 2 ((parents.drop 46).take 9) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa7 : chunkB SA 2 ((parents.drop 55).take 10) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa8 : chunkB SA 2 ((parents.drop 65).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 66)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [6, 10, 8, 7, 7, 8, 9, 10, 1] = true :=
  windowsG_cons pa0 (windowsG_cons pa1 (windowsG_cons pa2 (windowsG_cons pa3 (windowsG_cons pa4 (windowsG_cons pa5 (windowsG_cons pa6 (windowsG_cons pa7 (windowsG_cons pa8 (windowsG_nil paend)))))))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 630) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 630).take 634) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1264).take 631) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1895).take 628) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb4 : chunkB SB 1 ((bkA.flatten.flatten.drop 2523).take 227) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 2750)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [630, 634, 631, 628, 227] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_cons pb4 (windowsG_nil pbend)))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 4 ((bkB.flatten.drop 0).take 175).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 4 ((bkB.flatten.drop 175).take 81).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 4 bkB.flatten 0 [175, 81] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 1) (J := 4) (d := 2) (g1 := 16) (nb1 := 512) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_39865

theorem PEqualNP.Outside.L_meta_39865 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008636136 * 2 ^ 32 + 4008241888) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008636136 * 2 ^ 32 + 4008241888) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39865.solve