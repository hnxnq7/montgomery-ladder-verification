"""Extract native signature types without interpreting their packed dimensions."""
import argparse
import hashlib
import json
from pathlib import Path
import re


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


def extract(text, entry):
    start = re.search(r'^function automatic ', text, re.M)
    if start is None:
        raise ValueError('No global native function declarations')
    prefix = text[:start.start()]
    # The printer emits one argument and a two-line signature. Reject other formats.
    declarations = re.findall(r'^function automatic ([^\n]+) ([A-Za-z_][A-Za-z_0-9]*) \(\n'
                              r'  input ([^\n;]+) ([A-Za-z_][A-Za-z_0-9]*)\);\n', text, re.M)
    starts = re.findall(r'^function automatic ', text, re.M)
    if len(starts) != len(declarations):
        raise ValueError('Unsupported or invalid global function signature')
    names = [row[1] for row in declarations]
    if len(names) != len(set(names)):
        raise ValueError('Duplicate native function name')
    matches = [row for row in declarations if row[1] == entry]
    if len(matches) != 1:
        raise ValueError('Missing or ambiguous entry signature')
    result, name, argument, variable = matches[0]
    for type_text in (result, argument):
        # Types are kept verbatim. Do not accept additional arguments or declarations.
        if re.search(r'[;{}]|\b(input|output|inout)\b', type_text):
            raise ValueError('Unsupported signature type text')
    return prefix, result, argument, variable


def generate(text, k):
    if k not in (2, 4, 256):
        raise ValueError('Unsupported share count')
    entry = f'cycle{k}'
    prefix, result, argument, variable = extract(text, entry)
    state = 16 + 282 * k * 255
    randomness = 255 * k * k + 282 * (k - 1) * 255
    request = state + 512 + randomness
    response = state + 1 + k * 255
    probe = prefix + f'''\nmodule controller_signature_probe;
  typedef {argument} actual_request_t;
  typedef {result} actual_response_t;
  initial begin
    if ($bits(actual_request_t) != {request}) $fatal(1, "Native request width mismatch");
    if ($bits(actual_response_t) != {response}) $fatal(1, "Native response width mismatch");
    $display("PASS signature K={k} request=%0d response=%0d", $bits(actual_request_t), $bits(actual_response_t));
    $finish;
  end
endmodule
'''
    evidence = dict(shares=k, entry=entry, argument_name=variable,
                    argument_type=argument, return_type=result, prefix_sha256=sha(prefix),
                    argument_type_sha256=sha(argument), return_type_sha256=sha(result),
                    adapted_source_sha256=sha(text), probe_sha256=sha(probe),
                    state_bits=state, randomness_bits=randomness,
                    expected_request_bits=request, expected_response_bits=response,
                    status='generated_only_not_executed')
    return probe, evidence


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--shares', type=int, required=True)
    args = parser.parse_args()
    probe, evidence = generate(args.source.read_text(), args.shares)
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'signature.sv').write_text(probe)
    (args.output / 'signature.json').write_text(json.dumps(evidence, indent=2) + '\n')


if __name__ == '__main__':
    main()
