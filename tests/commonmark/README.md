# CommonMark's examples

`spec.json` is every example of the CommonMark Spec, version 0.31.2
(https://spec.commonmark.org/0.31.2/), as its own `test/spec_tests.py
--dump-tests` writes them (commonmark-spec at tag 0.31.2, commit
9103e341a973013013bb1a80e13567007c5cef6f). The spec is Copyright (C) 2014-16
John MacFarlane, released under the Creative Commons CC-BY-SA 4.0 license
(https://creativecommons.org/licenses/by-sa/4.0/); `spec.json` is copied from
it unchanged, under the same license.

`run.ck` parses each example's Markdown with `std.markdown` and compares its
HTML with the spec's, byte for byte (#640 f): the golden tests run it
(`tests/run/commonmark.args`), and every example must pass.

    ckc run tests/commonmark/run.ck tests/commonmark/spec.json [N]
