#!/usr/bin/env python3
import sys
import os
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
"""Structural regression tests for the FirstOrderTheory repository.

These tests intentionally require **no Coq installation**: they mechanically
verify the invariants that *can* be checked in this container — nested comment
integrity, ``match``/``end`` parity, uniqueness of top-level declarations,
``Section``/``Module`` balance, documentation coverage, preservation of
commented-out work, and ticket hygiene.  When ``coqc`` becomes available the
real proof-checking job belongs in CI (see tickets/ticket_7242_followup_build_extraction_pipeline.md).

Author:  opencode/mimo-v2.6-flash-free (Capability Tier 1)
Ticket:  #7231 [FirstOrderTheory - Pass 1/5 (Carte Blanche Exploration &
         Architecture README)]
Run:     make test        (= python3 -m unittest discover -s tests -p 'test_*.py')
"""

import pathlib
import re
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]

V_FILES = [
    "Isabelle.v",
    "IsabelleAlt.v",
    "OneFile.v",
    "OneFileIsabelle.v",
    "OneFileZFC.v",
]
SOURCE_FILES = V_FILES + ["printer.ml", "Makefile", ".gitignore"]

# --------------------------------------------------------------------------- #
# helpers
# --------------------------------------------------------------------------- #


from .utils import read
def read(relpath):
    return (ROOT / relpath).read_text(encoding="utf-8", errors="replace")


from utils import strip_comments
def strip_comments(text):
    """Replace every Coq comment (nested ``(* ... *)``) by blanks.

    Returns ``(stripped, final_depth, min_depth)``.  Newlines are preserved so
    that line numbers stay meaningful; anything inside a comment becomes a
    space.  Raises AssertionError on negative (unbalanced) nesting.
    """
    out = []
    depth = 0
    min_depth = 0
    i = 0
    n = len(text)
    while i < n:
        two = text[i : i + 2]
        if two == "(*":
            depth += 1
            out.append("  ")
            i += 2
            continue
        if two == "*)":
            depth -= 1
            if depth < min_depth:
                min_depth = depth
            out.append("  ")
            i += 2
            continue
        ch = text[i]
        out.append(ch if depth == 0 else (" " if ch != "\n" else "\n"))
        i += 1
    assert depth == 0, "unbalanced Coq comments: %d comment(s) never closed" % depth
    assert min_depth >= 0, "comment terminator without an opener"
    return "".join(out), depth, min_depth


def stripped(relpath: str) -> str:
    return strip_comments(read(relpath))[0]


DECL_RE = re.compile(
    r"^(Inductive|CoInductive|Fixpoint|CoFixpoint|Definition|Record|Theorem|"
    r"Lemma|Corollary|Proposition|Remark|Axiom|Example|Section|Module)\s+"
    r"([A-Za-z0-9_']+)",
    re.M,
)
SECTION_RE = re.compile(r"^Section\s+([A-Za-z0-9_']+)\s*\.", re.M)
MODULE_RE = re.compile(r"^Module\s+([A-Za-z0-9_']+)\s*\.", re.M)  # body, not `:=`
FUNCTOR_RE = re.compile(r"^Module\s+([A-Za-z0-9_']+)\s*\(", re.M)
END_RE = re.compile(r"^End\s+([A-Za-z0-9_']+)\s*\.", re.M)
MATCH_RE = re.compile(r"\bmatch\b")
END_TOKEN_RE = re.compile(r"\bend\b")


# --------------------------------------------------------------------------- #
# 1. comment / parse-level structure of every .v file
# --------------------------------------------------------------------------- #


class CommentStructureTests(unittest.TestCase):
    def test_expected_sources_are_present(self):
        for name in SOURCE_FILES:
            self.assertTrue((ROOT / name).is_file(), "missing source file: " + name)

    def test_v_files_have_balanced_nested_comments(self):
        for name in V_FILES:
            with self.subTest(file=name):
                _, final_depth, min_depth = strip_comments(read(name))
                self.assertEqual(final_depth, 0, "unclosed comment in " + name)
                self.assertGreaterEqual(min_depth, 0, "stray comment closer in " + name)

    def test_every_match_is_closed_by_an_end(self):
        """Parse-level parity: a valid Coq term has #match = #end."""
        for name in V_FILES:
            text = stripped(name)
            n_match = len(MATCH_RE.findall(text))
            n_end = len(END_TOKEN_RE.findall(text))
            self.assertEqual(
                n_match,
                n_end,
                "%s: %d `match` but %d `end` (stray or missing `end`)" % (name, n_match, n_end),
            )

    def test_no_stray_bare_identifier_lines(self):
        """Guards against junk tokens such as the former stray `D` in Isabelle.v."""
        for name in V_FILES:
            for lineno, line in enumerate(stripped(name).splitlines(), 1):
                self.assertNotEqual(
                    line.strip(),
                    "D",
                    "%s:%d is a stray top-level token `D`" % (name, lineno),
                )

    def test_top_level_declarations_are_unique(self):
        for name in V_FILES:
            text = stripped(name)
            seen = {}
            for m in DECL_RE.finditer(text):
                key = m.group(1) + " " + m.group(2)
                lineno = text[: m.start()].count("\n") + 1
                seen.setdefault(key, []).append(lineno)
            dups = {k: v for k, v in seen.items() if len(v) > 1}
            self.assertEqual(dups, {}, "%s: duplicate top-level declarations %s" % (name, dups))

    def test_sections_and_modules_are_balanced(self):
        for name in V_FILES:
            text = stripped(name)
            opened = set(SECTION_RE.findall(text))
            opened |= set(MODULE_RE.findall(text))
            opened |= set(FUNCTOR_RE.findall(text))
            closed = set(END_RE.findall(text))
            self.assertEqual(
                opened - closed,
                set(),
                "%s: Section/Module never ended: %s" % (name, sorted(opened - closed)),
            )
            self.assertEqual(
                closed - opened,
                set(),
                "%s: End without Section/Module: %s" % (name, sorted(closed - opened)),
            )


# --------------------------------------------------------------------------- #
# 2. README coverage
# --------------------------------------------------------------------------- #


class ReadmeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.readme = read("README.md")

    def test_readme_is_substantial(self):
        self.assertGreaterEqual(len(self.readme.splitlines()), 150)

    def test_readme_mentions_every_source_file(self):
        for name in SOURCE_FILES:
            self.assertIn(name, self.readme, "README.md does not mention " + name)

    def test_readme_declares_model_provenance(self):
        self.assertIn("opencode/mimo-v2.6-flash-free", self.readme)
        self.assertIn("Capability Tier 1", self.readme)
        self.assertIn("7231", self.readme)

    def test_readme_documents_the_main_artifacts(self):
        self.assertIn("soundness", self.readme)
        self.assertIn("Theorem soundness", self.readme)
        self.assertIn('Extraction "prog.ml" PREPR.', self.readme)
        self.assertIn("replxixiF", self.readme)
        self.assertIn("make test", self.readme)

    def test_readme_links_every_followup_ticket(self):
        for ticket in sorted((ROOT / "tickets").glob("*_followup_*.md")):
            number = re.search(r"ticket_(\d+)", ticket.name).group(1)
            self.assertIn(number, self.readme, "README.md does not reference " + ticket.name)


# --------------------------------------------------------------------------- #
# 3. preservation of existing work (commented-out approaches must survive)
# --------------------------------------------------------------------------- #


class PreservationTests(unittest.TestCase):
    def test_onefilezfc_keeps_the_full_commented_development(self):
        text = read("OneFileZFC.v")
        marker = "(* HERE IS THE END OF THE CODE *)"
        self.assertIn(marker, text, "end-of-code marker vanished from OneFileZFC.v")
        after = text[text.index(marker) + len(marker) :]
        self.assertTrue(after.lstrip().startswith("(*"), "trailing block comment was removed")
        # the preserved copy must really live *inside* a comment:
        body = stripped("OneFileZFC.v")
        self.assertNotIn("End ALL_mod.", body, "preserved development is no longer commented out")
        self.assertIn("End ALL_mod.", after)
        self.assertIn("Theorem soundness", after)
        self.assertTrue(text.rstrip().endswith("*)"), "OneFileZFC.v must end with the comment")

    def test_original_proof_style_variants_survive(self):
        # the alternative `AtoA` proof style of OneFile.v is kept as a comment
        self.assertIn("Another style of the proof", read("OneFile.v"))

    def test_makefile_keeps_the_original_ocaml_pipeline(self):
        makefile = read("Makefile")
        self.assertIn("go:", makefile)
        for command in (
            "ocamlc -i printer.ml",
            "ocamlc -c prog.mli",
            "ocamlc -o a.out prog.ml printer.ml",
            "./a.out",
        ):
            self.assertIn(command, makefile, "original pipeline command lost: " + command)

    def test_extraction_directive_survives(self):
        self.assertIn('Extraction "prog.ml" PREPR.', read("OneFileZFC.v"))


# --------------------------------------------------------------------------- #
# 4. every open proof hole must be documented in README.md (section 6)
# --------------------------------------------------------------------------- #


class ProofHoleDocumentationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.readme = read("README.md")

    def _holes(self, name, pattern):
        hits = []
        for lineno, line in enumerate(stripped(name).splitlines(), 1):
            if re.search(pattern, line):
                hits.append((name, lineno))
        return hits

    def _assert_documented(self, name, lineno, keyword):
        """README section 6 must name the file, the exact line and the keyword."""
        message = (
            "%s:%d is a proof hole but README.md section 6 does not document it"
            % (name, lineno)
        )
        self.assertIn(keyword, self.readme, message)
        self.assertRegex(
            self.readme,
            re.escape(name) + ":" + str(lineno) + r"\b",
            message + " (expected a `<file>:<line>` reference)",
        )

    def test_admitted_statements_are_documented(self):
        for name in V_FILES:
            for _, lineno in self._holes(name, r"\bAdmitted\."):
                self._assert_documented(name, lineno, "Admitted")

    def test_aborted_proofs_are_documented(self):
        for name in V_FILES:
            for _, lineno in self._holes(name, r"\bAbort\."):
                self._assert_documented(name, lineno, "Abort")

    def test_incomplete_definitions_are_documented(self):
        """A file must not silently end in the middle of a definition."""
        for name in V_FILES:
            lines = stripped(name).splitlines()
            content = [i for i, line in enumerate(lines) if line.strip()]
            if not content:
                continue
            last = content[-1]
            tail = lines[last].rstrip()
            if tail.endswith(":=") or tail.endswith("with") or tail.endswith(","):
                self._assert_documented(name, last + 1, "body-less")


# --------------------------------------------------------------------------- #
# 5. tickets hygiene
# --------------------------------------------------------------------------- #


class TicketTests(unittest.TestCase):
    def test_every_ticket_has_title_and_signature(self):
        tickets = sorted((ROOT / "tickets").glob("*.md"))
        self.assertGreaterEqual(len(tickets), 5)
        for ticket in tickets:
            text = ticket.read_text(encoding="utf-8", errors="replace")
            with self.subTest(ticket=ticket.name):
                first_line = text.splitlines()[0] if text.splitlines() else ""
                self.assertTrue(
                    first_line.upper().startswith("# [FIRSTORDERTHEORY"),
                    ticket.name + ": missing standard title",
                )
                self.assertTrue(
                    "Author / Signed by" in text or "Assigned AI Model" in text or "Author" in text,
                    ticket.name + ": missing author/signature attribution"
                )

    def test_followup_tickets_declare_model_identity(self):
        for ticket in sorted((ROOT / "tickets").glob("*_followup_*.md")):
            text = ticket.read_text(encoding="utf-8", errors="replace")
            with self.subTest(ticket=ticket.name):
                self.assertIn("opencode/mimo-v2.6-flash-free", text)
                self.assertIn("Tier 1", text)


if __name__ == "__main__":
    unittest.main()
