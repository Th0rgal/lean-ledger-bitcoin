import argparse
from pathlib import Path
import re

parser = argparse.ArgumentParser()
parser.add_argument('baseline', type=Path)
parser.add_argument('candidate', type=Path)
args = parser.parse_args()


def counts(path):
    text = path.read_text()
    bodies = re.findall(r'^define\b[^\n]*@([^\s(]+)[^\n]*\{\n(.*?)^}',
                        text, re.MULTILINE | re.DOTALL)
    matches = [(name, body) for name, body in bodies
               if 'llb_format_sats_ascii' in name or 'llbFormatSatsAscii' in name]
    if len(matches) != 1:
        raise SystemExit(f'{path}: expected one formatter definition, got {len(matches)}')
    name, body = matches[0]
    calls = re.findall(r'\bcall\b[^\n]*@([^\s(]+)\(', body)
    result = {helper: sum(helper in call for call in calls)
              for helper in ('emitDec', 'maybeWriteByte', 'copyTicker', 'fracSigLen')}
    print(path, name, result)
    return result


old = counts(args.baseline)
new = counts(args.candidate)
if list(old.values()) != [24, 16, 8, 4]:
    raise SystemExit('Baseline differs from reported 24/16/8/4; inspect provenance/raw IR')
if list(new.values()) != [3, 2, 1, 1]:
    raise SystemExit('Candidate does not meet raw-IR 3/2/1/1 falsification gate')
print('Raw-IR call-count gate passed; Flash/stack/BSS/equivalence still required')
