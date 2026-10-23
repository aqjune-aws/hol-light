#!/usr/bin/env python3

import pathlib
import subprocess
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "make-checkpoint.sh"


class MakeCheckpointScriptTest(unittest.TestCase):
    def test_script_parses_with_macos_system_bash(self):
        result = subprocess.run(
            ["/bin/bash", "-n", str(SCRIPT)],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_script_avoids_gnu_only_utility_options(self):
        source = SCRIPT.read_text(encoding="utf-8")
        self.assertNotIn("mktemp --suffix", source)
        self.assertNotIn("readlink -f", source)
        self.assertIn('${TMPDIR:-/tmp}/hol-light-init.XXXXXX', source)
        self.assertIn('${TMPDIR:-/tmp}/hol-light-loaded.XXXXXX', source)
        self.assertIn('CDPATH= cd -- "$(dirname -- "$0")" && pwd -P', source)

    def test_darwin_uses_injectable_runtime_and_cooperative_wait(self):
        source = SCRIPT.read_text(encoding="utf-8")
        self.assertIn(
            'external __dmtcp_checkpoint_wait : unit -> unit = '
            '"caml_dmtcp_checkpoint_wait"',
            source,
        )
        self.assertIn(
            'ocamlrun=${DMTCP_OCAMLRUN:-${HOLLIGHT_DIR}/'
            'ocaml-dmtcp-5.4.0/_install/bin/ocamlrun}',
            source,
        )
        self.assertIn(
            '"$ocamlrun" "${HOLLIGHT_DIR}/ocaml-hol"',
            source,
        )

    def test_linux_keeps_the_existing_hol_script_launch(self):
        source = SCRIPT.read_text(encoding="utf-8")
        self.assertIn(
            'bash -i -c "dmtcp_launch --new-coordinator --ckptdir '
            '${output_dmtcp_dir_path} ${hol_sh_path}"',
            source,
        )

    def test_bad_arity_still_reports_usage(self):
        result = subprocess.run(
            ["/bin/bash", str(SCRIPT)],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        self.assertEqual(result.returncode, 1)
        self.assertIn("make-checkpoint.sh <output script path>", result.stdout)


if __name__ == "__main__":
    unittest.main()
