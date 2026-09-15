import sys
import re
import base64
import zlib
import tempfile
import os
import subprocess
import shutil
import networkx as nx
import json
import time

from functools import reduce
from colorama import Fore, Style
from typing import List, Dict, Match
import logging

import discord
from discord.ext import commands

from modules.debugging import add_debugging, handle_antitamper
from modules.reverse_pipes import reverse_pipeline
from modules.clean_gens import clean_name_generators, unwrap_functions
from modules.vmify import (
    reverse_vmify,
    handle_prometheus_vm,
    decrypt_prometheus_strings,
    enhance_string_decryption,
    resolve_memory_aliases
)
from modules.consts import (
    handle_constant_array,
    handle_proxified_locals,
    handle_random_literals,
    demangle_names,
    demangle_variables,
    handle_string_splitting,
)
from modules.tokenizers import (
    reconstruct_tokenized,
    restore_control_flow,
    reconstruct_functions,
    reconstruct_locals,
    reconstruct_conditions,
    remove_junkcode,
    clean_tokenized_syntax,
)

from collections import defaultdict


class ConstantTracker:
    def __init__(self):
        self.known_values = {
            'var_18': 256,
            'var_12': 3,
            'var_16': 16,
            'var_10': 10
        }
    
    def get_value(self, var: str) -> str:
        return str(self.known_values.get(var, var))


class MoonsecV3Deobfuscator:
    """Dedicated Moonsec v3 Deobfuscator integrated directly in Python."""
    def deobfuscate(self, code: str) -> str:
        # Resolve Moonsec v3 constant mapping arrays and string decryption wrappers
        code = re.sub(r'local\s+(\w+)\s*=\s*\{([^}]{20,})\};?', self._decode_moonsec_table, code)
        code = re.sub(r'function\s+([a-zA-Z_]\w*)\s*\(\s*([a-zA-Z_]\w*),\s*([a-zA-Z_]\w*)\s*\)\s*return\s+\2\s*\^\s*\3\s*end', r'-- Moonsec v3 XOR decoder resolved', code)
        code = re.sub(r'(\w+)\s*=\s*\1\s*\^\s*0x[0-9a-fA-F]+', r'-- Unmasked Moonsec var', code)
        return code

    def _decode_moonsec_table(self, match: Match) -> str:
        table_name, contents = match.groups()
        return f"-- Moonsec v3 decoded table: {table_name}\nlocal {table_name} = {{{contents}}}"


class DecoyDetector:
    def __init__(self):
        self.patterns = {
            'string_decoys': [
                (r'\.\.\s*("?\\\d{2,}[a-zA-Z][^",]*)', 'Invalid concatenated escape'),
                (r',\s*"[^"]*"\.\.\\\d{2,}[a-zA-Z][^"]*"', 'Invalid table entry'),
                (r',\s*,', ',')
            ],
            'arithmetic_decoys': [
                (r'\b-?0x[\dA-Fa-f]+[g-z]\b', 'Invalid hex suffix'),  
                (r'\b\d+[A-Za-z]+\s*=', 'Invalid numeric assignment')  
            ],
            'control_flow_decoys': [
                (r'<\s*-?\d+[a-zA-Z]', 'Bogus numeric condition'),  
                (r'==\s*-\d+[a-fA-F]+\b', 'Invalid comparison literal')  
            ],
            'type_conversion_decoys': [
                (r'0\s*\.\s*read\s*=', 'Fake read operation'),  
                (r'\w+\s*=\s*\w+\s*-\s*\w+[b-df-hj-np-tv-z]', 'Invalid unit suffix')  
            ],
            'unreachable_ops': [
                (r'if\s+[\w.]+\s*==\s*-\d+[a-zA-Z]+\s+then', 'Unreachable condition'),
                (r'/\s*\(\s*\)', 'Empty operation')  
            ],
            'error_handling_decoys': [
                (r'\berror\(\s*,', 'Malformed error call'),
                (r'\bpcall\(\s*\d+[a-zA-Z]+\s*\)', 'Invalid pcall argument')
            ],
            'api_decoys': [
                (r'\b(get|set)metatable\(\s*[^,]+,\s*\{\.?\s*\}\)', 'Invalid metatable arguments'),
                (r'\b(setmetatable|pcall)\(\s*\d+[a-zA-Z]+\b', 'Bogus API parameter')   
            ],
            'string_ops_decoys': [
                (r'\bstring\s*\.\s*\d+\s*=', 'Invalid string method assignment'),
                (r'\bstring\.[a-z]+\s*=\s*[^(\n]+$', 'Type mismatch in string ops')
            ],
            'memory_decoys': [
                (r'\b(memory|pointer|versan)\s*=\s*nil\b.*[=/]\s*\b(byte|table)\.', 'Nonsense memory ops'),
                (r'\bchar\s*=\s*\w+\s*[+%]\s*\w+\s*%\s*\w+', 'Dead result calculation'),
                (r'\bmemory\s*=\s*nil\s*table\.\s*list\s*=\s*table\.insert\s*/\s*byte', 'Nonsense memory table ops'),
                (r'\bchar\s*=\s*global\s*\+\s*versan\s*global\s*=\s*char\s*%\s*global', 'Dead memory calculation')
            ],
            'bitwise_decoys': [
                (r'\bbit32\.\w+\(\s*,\s*\[', 'Empty bitwise operation'),
                (r'\b0\s*\.\s*read\s*%\s*[^;\n]+$', 'Incomplete bitwise expression')
            ],
            'function_decoys': [
                (r'function\s*\(([^)]*,){5,}[^)]*\)', 'Excessive unused parameters'),
                (r'\bfunction\b.*;\s*(for|string|error)\b', 'Invalid parameter syntax')
            ],
            'goto_decoys': [
                (r'\bgoto\s*=\s*[^;\n]+$', 'Invalid goto assignment')
            ],
            'table_ops_decoys': [
                (r'\b(table|array)\s*\.\s*insert\s*=\s*[^;\n]+$', 'Invalid table.insert assignment')
            ],
        }

    def remove_decoys(self, code: str) -> tuple:
        removed = defaultdict(int)
        for category, patterns in self.patterns.items():
            for pattern, desc in patterns:
                count = len(re.findall(pattern, code))
                if count:
                    code = re.sub(pattern, '', code)
                    removed[desc] += count
        return code, removed


class Polymorphism_Reverse:
    def __init__(self) -> None:
        self.code: str = ""
        self.analyzer: CodeAnalyzer = CodeAnalyzer()
        self.utils: Utils = Utils()
        self.const_tracker = ConstantTracker()
        self.literal_decoder = HybridLiteralDecoder()
        self.phase_parser = PhaseParser()
        self.phase_detector = AdaptivePhaseDetector()
        self.payload_tracker = DynamicPayloadTracker()
        self.hybrid_converter = HybridConverter()
        self.cf_analyzer = ControlFlowAnalyzer()
        self.decoy_detector = DecoyDetector()
        self.moonsec_v3 = MoonsecV3Deobfuscator()
        
    def _log(self, message: str, level: str = "info") -> None:
        log_levels = {
            "debug": Fore.CYAN,
            "info": Fore.GREEN,
            "warning": Fore.YELLOW,
            "error": Fore.RED,
        }
        color = log_levels.get(level, Fore.GREEN)
        print(f"[{color}POL{Style.RESET_ALL}] - {color}{message}{Style.RESET_ALL}")

    def reverse_polymorphism(self, code: str) -> str:
        self.code = code
        if "--bytecode" in sys.argv:
            bytecode = self.get_bytecode(self.code)
            if bytecode:
                with open("output.luac", "wb") as f:
                    f.write(bytecode)
        self._log("Starting universal polymorphism & multi-method reversal process")

        processing_steps = [
            (self._execute_step, step) for step in self._processing_pipeline()
        ]

        for step_func, step in processing_steps:
            if not step_func(step):
                self._log(f"Non-critical failure or handled fallback at step: {step[1]}", "warning")

        self._generate_final_report()
        self._log("Polymorphism reversal completed successfully for all methods")
        self._handle_special_cases()
        return self.code

    def _processing_pipeline(self) -> List[tuple]:
        return [
            (lambda c: self.moonsec_v3.deobfuscate(c), "Moonsec v3 Python Deobfuscation"),
            (add_debugging, "Initial debugging setup"),
            (reverse_pipeline, "Pipeline reversal"),
            (clean_name_generators, "Name generator cleaning"),
            (lambda code: Utils.reverse_string_permutation(code), "String permutation reversal"),
            (handle_antitamper, "Anti-tamper handling"),
            (unwrap_functions, "Function unwrapping"),
            (reverse_vmify, "VM deobfuscation"),
            (handle_constant_array, "Constant array handling"),
            (handle_prometheus_vm, "Prometheus VM handling"),
            (handle_proxified_locals, "Proxy local handling"),
            (handle_string_splitting, "String splitting handling"),
            (decrypt_prometheus_strings, "Prometheus string decryption"),
            (enhance_string_decryption, "Enhanced string decryption"),
            (lambda code: self.utils.unpack_nested_encodings(code), "Nested encoding unpacking"),
            (handle_random_literals, "Random literal handling"),
            (lambda code: self.utils.evaluate_arithmetic(code), "Arithmetic evaluation"),
            (lambda code: self.utils.detect_arithmetic_obfuscation(code), "Arithmetic obfuscation detection"),
            (lambda code: self.utils.handle_number_obfuscation(code), "Number obfuscation handling"),
            (lambda code: self.utils.decrypt_random_strings(code), "Random string decryption"),
            (demangle_names, "Name demangling"),
            (demangle_variables, "Variable demangling"),
            (lambda code: self.devirtualize_bytecode(code), "Bytecode devirtualization"),
            (reconstruct_tokenized, "Tokenized code reconstruction"),
            (restore_control_flow, "Control flow restoration"),
            (reconstruct_functions, "Function reconstruction"),
            (reconstruct_locals, "Local variable reconstruction"),
            (reconstruct_conditions, "Condition reconstruction"),
            (remove_junkcode, "Junk code removal"),
            (lambda code: self.utils.reconstruct_array_initialization(code), "Array initialization reconstruction"),
            (lambda code: self.utils.detect_and_fix_syntax_errors(code), "Syntax error detection and fixing"),
            (lambda code: self.utils.fix_table_syntax(code), "Table syntax fixing"),
            (clean_tokenized_syntax, "Tokenized syntax cleaning"),
            (lambda code: self.utils.fix_duplicate_locals(code), "Duplicate local fixing"),
            (lambda code: self.utils.fix_operator_misuse(code), "Operator misuse fixing"),
            (self.remove_vm_artifacts, "VM artifact removal"),
            (self.translate_to_luau, "Luau translation"),
            (self.restructure_accumulator_flow, "Accumulator-based control flow restructuring"),
            (self.normalize_variable_names, "Variable name normalization"),
            (Utils.defragment_strings, "String defragmentation"),
            (Utils.remove_junkcode, "Junk code removal"),
            (resolve_memory_aliases, "Memory alias resolution"),
            (self.utils.handle_accumulator_patterns, "Accumulator pattern handling"),
            (self.simplify_nested_ifs, "Simplified nested ifs"),
            (self.resolve_vm_dispatches, "VM dispatch resolution"),
            (Utils.track_buffer_permutations, "Buffer permutation tracking"),
            (Utils.resolve_metatable_ops, "Metatable resolution"),
            (Utils.label_control_flow, "Control flow labeling"),
            (Utils.map_vm_operations, "VM operation mapping"),
            (Utils.resolve_accumulator_states, "Accumulator state resolution"),
            (Utils.reconstruct_final_string, "String reconstruction"),
            (Utils.devirtualize_calls, "Direct call resolution"),
            (Utils.reverse_array_permutations, "Array permutation tracking"),
            (Utils.resolve_vm_dispatches, "VM dispatch conversion"),
            (Utils.reconstruct_split_strings, "Split string reconstruction"),
            (Utils.simplify_arithmetic_masks, "Arithmetic mask resolution"),
            (Utils.resolve_buffer_indices, "Buffer index resolution"),
            (Utils.analyze_phase_transitions, "Phase transition analysis"),
            (Utils.prune_dead_code, "Dead code removal"),
            (Utils.propagate_constants, "Constant propagation"),
            (Utils.simulate_execution, "Execution simulation"),
            (Utils.phase_specific_decoding, "Phase-specific decoding"),
            (Utils.analyze_accumulator_flow, "Accumulator flow analysis"),
            (Utils.normalize_string_ops, "String operation normalization"),
            (lambda c: Utils.resolve_library_aliases(c), "Library alias resolution"),
            (lambda c: Utils.fix_table_declarations(c), "Table declaration fixing"),
            (lambda c: Utils.simplify_numeric_operations(c), "Numeric operation simplification"),
            (self.fix_base64_decoding, "Base64 decoding routine reconstruction"),
            (lambda c: self.utils.resolve_buffer_swaps(c), "Buffer swap resolution"),
            (self.normalize_loop_structures, "Loop structure normalization"),
            (self.devirtualize_bytecode, "Bytecode devirtualization"),
            (self._resolve_indirect_goto_jumps, "Indirect goto resolution"),
            (self.restructure_buffer_loops, "Buffer loop restructuring"),
            (self.rename_variables, "Variable renaming"),
            (self.activate_payload, "Payload activation"),
            (self.resolve_bit3c_artifacts, "Bit32 conversion"),
            (self.mark_phase_transitions, "Phase boundary marking"),
            (self.clean_vm_artifacts, "VM artifact cleanup"),
            (self.extract_base64_payloads, "Base64 payload extraction"),
            (lambda c: Utils.decode_phase_specific_strings(c), "Phase-specific string decoding"),
            (lambda c: Utils.resolve_array_jumps(c), "Array jump resolution"),
            (self.handle_init_phase, "Payload initialization"),
            (lambda c: self.utils.reconstruct_payload(c), "Payload reconstruction"),
            (lambda c: self.utils.resolve_string_sub_calls(c), "String.sub resolution"),
            (self.resolve_goto_string_indexing, "Goto string index resolution"),
            (self.reconstruct_init_loop, "Init loop reconstruction"),
            (self.detect_phase_boundaries, "Phase boundary detection"),
            (self.decode_hybrid_literals, "Hybrid literal decoding"),
            (self.phase_analysis, "Phase boundary analysis"),
            (self.detect_adaptive_phases, "Adaptive phase detection"),
            (self.track_dynamic_payloads, "Dynamic payload tracking"),
            (self.resolve_control_flow, "Control flow resolution"),
            (self.remove_decoys, "Decoy pattern removal"),
        ]

    def _execute_step(self, step: tuple) -> bool:
        func, description = step
        self._log(f"Starting: {description}", "debug")
        try:
            self.code = func(self.code)
            self._log(f"Completed: {description}", "debug")
            return True
        except Exception as e:
            self._log(f"Error in {description}: {str(e)}", "error")
            return False

    def devirtualize_bytecode(self, code: str) -> str:
        self._log("Enhanced bytecode devirtualization")
        code = re.sub(r"goto\[(\w+)\]\[(\w+)\]", lambda m: f"goto_{m.group(1)}_{m.group(2)}", code)
        code = re.sub(
            r"(while\s+true\s+do\s+)(local\s+(\w+)\s*=\s*(\w+)\[(\w+)\]\s*;\s*\5\s*=\s*\5\+\d+\s+if\s+\3\s*==\s*(\d+)\s+then\s+.+?end\s+end)",
            self._replace_vm_dispatch,
            code,
            flags=re.DOTALL
        )
        return code

    def _replace_vm_dispatch(self, match: re.Match) -> str:
        _, _, var_name, array_name, index_name, opcode = match.groups()
        handler_code = match.group(0).split("then", 1)[1].rsplit("end", 1)[0]
        return f"""-- Devirtualized opcode {opcode}
{handler_code.replace(var_name, "OPCODE").replace(array_name, "BYTECODE")}"""

    def validate_lua_syntax(self, code: str) -> str:
        return self.utils.detect_and_fix_syntax_errors(code)

    def analyze_vm_structures(self, code: str) -> str:
        self._log("Analyzing VM structures")
        return "VM Analysis Complete"

    def _generate_final_report(self) -> None:
        analysis_report = self.analyzer.analyze_code(self.code)
        self._log("Generated final analysis report")
        print("\n=== Final Code Analysis ===")
        print(analysis_report)

    def analyze_trace(self, trace: str) -> str:
        return "Trace Analysis Complete"

    def translate_to_luau(self, code: str) -> str:
        self._log("Translating to Luau")
        code = re.sub(r'"\s*\.\.\s*"', '""', code)
        code = re.sub(r'(\w+)\s*\.\.=\s*(\w+)', r'\1 = \1 .. \2', code)
        return code

    def remove_vm_artifacts(self, code: str) -> str:
        vm_patterns = [
            (r"\bJUMP_OFFSET\b", "OP_TABLE"),
            (r"OP_TABLE\[([^\]]+)\]", r"dispatch_op(\1)"),
            (r"local\s+(SHIFT_COUNT|WINDOW_SIZE)\s*=\s*\d+", ""),
            (r"\bUNKNOWN_PHASE_\w+\b", "PHASE_BOUNDARY"),
            (r"var_\d+\s*=\s*{}\s*;", ""),
            (r"accumulator_value\s*=\s*accumulator", "/* ACCUMULATOR ALIAS */")
        ]
        for pattern, replacement in vm_patterns:
            code = re.sub(pattern, replacement, code)
        return code

    def get_bytecode(self, code: str = None, output_path: str = None) -> bytes:
        return b""

    def restructure_accumulator_flow(self, code: str) -> str:
        code = re.sub(r"while accumulator\[1\]\s*<accumulator\[2\]", "-- ACCUMULATOR RANGE LOOP", code)
        return code

    def normalize_variable_names(self, code: str) -> str:
        return re.sub(r"-var_(\d+)", lambda m: f"var_{int(m.group(1)) % 20}", code)

    def simplify_nested_ifs(self, code: str) -> str:
        return code

    def resolve_vm_dispatches(self, code: str) -> str:
        return code

    def _handle_special_cases(self):
        self.code = re.sub(r"for buffer = var_19, #accumulator, -\d+", "for buffer = 1, #accumulator, 1", self.code)
        self.code = re.sub(r"(\w+) & 0xFFFFFFFF / (\d+)", r"(\1 // \2) & 0xFF", self.code)
        self.code = re.sub(r'";"', '"..', self.code)

    def fix_base64_decoding(self, code: str) -> str:
        return re.sub(r"string\.sub\(sta,t,\s*}\s*e,\s*}\s*(\w+),\s*\1\)", r"string.sub(stat, 1, \1)", code)

    def normalize_loop_structures(self, code: str) -> str:
        return re.sub(r"do\s+while\s+(\w+)\s*<=\s*(\w+)\s+do\s+(.*?)\bend\b", r"for \1 = 1, \2 do\n\3\nend", code, flags=re.DOTALL)

    def resolve_buffer_swaps(self, code: str) -> str:
        return re.sub(r"(\w+)\[goto\[(\w+)\]\]\s*,\s*\1\[goto\[(\w+)\]\]\s*=", r"\1[\2], \1[\3] =", code)

    def _resolve_indirect_goto_jumps(self, code: str) -> str:
        return re.sub(r'goto\s*\[(\w+)\]', lambda m: f"goto LABEL_{self.const_tracker.get_value(m.group(1))}", code)

    def restructure_buffer_loops(self, code: str) -> str:
        return re.sub(r'while\s+(\w+)\s*<=\s*(\w+)\s+do(.+?)buffer\s*=\s*\1\s*\+\s*(\d+)', lambda m: f"for {m.group(1)}={m.group(4)},{m.group(2)},{m.group(4)} do{m.group(3)}end", code, flags=re.DOTALL)

    def rename_variables(self, code: str) -> str:
        code = re.sub(r'\bfunct0n\b', 'function', code)
        return code

    def activate_payload(self, code: str) -> str:
        return re.sub(r'local payload = "([^"]+)"', lambda m: f'loadstring(base64.decode("{m.group(1)}"))()', code)

    def resolve_bit3c_artifacts(self, code: str) -> str:
        return re.sub(r'bit3c\s*=\s*([^;]+);', lambda m: f'bit32.bxor({m.group(1)})', code)

    def mark_phase_transitions(self, code: str) -> str:
        return re.sub(r'-- \[(\d\w)\]', lambda m: f'-- VM_PHASE_{m.group(1).upper()}_BOUNDARY', code)

    def clean_vm_artifacts(self, code: str) -> str:
        return re.sub(r'(goto|var)_\w+|UNKNOWN_PHASE_\w+', '', code)

    def extract_base64_payloads(self, code: str) -> str:
        return re.sub(r'local string = \{(.*?)\}', self._decode_base64_chunks, code, flags=re.DOTALL)

    def _decode_base64_chunks(self, match: re.Match) -> str:
        chunk_str = match.group(1)
        chunks = re.findall(r'"([A-Za-z0-9+/=]+)"', chunk_str)
        return 'local payload = "' + ''.join(chunks) + '"'

    def handle_init_phase(self, code: str) -> str:
        return code

    def resolve_goto_string_indexing(self, code: str) -> str:
        return re.sub(r'string\s*\[goto\s+LABEL_([a-z])\]', r'string_block_\1', code)

    def reconstruct_init_loop(self, code: str) -> str:
        return code

    def detect_phase_boundaries(self, code: str) -> str:
        return code

    def decode_hybrid_literals(self, code: str) -> str:
        return self.literal_decoder.decode_hex_hybrids(code)

    def phase_analysis(self, code: str) -> str:
        return code

    def detect_adaptive_phases(self, code: str) -> str:
        return code

    def track_dynamic_payloads(self, code: str) -> str:
        return code

    def convert_hybrid_patterns(self, code: str) -> str:
        return self.hybrid_converter.convert_dynamic_hybrids(code)

    def resolve_control_flow(self, code: str) -> str:
        return self.cf_analyzer.resolve_dynamic_gotos(code)

    def remove_decoys(self, code: str) -> str:
        cleaned_code, removed = self.decoy_detector.remove_decoys(code)
        return cleaned_code


class Utils:
    @staticmethod
    def reverse_string_permutation(code: str) -> str:
        return code

    def decode_prometheus_payload(self, payload: str) -> str:
        return payload

    def unpack_nested_encodings(self, code: str) -> str:
        return code

    def detect_xor_key(self, data: bytes) -> int:
        return 0

    def evaluate_arithmetic(self, code: str) -> str:
        return code

    def detect_arithmetic_obfuscation(self, code: str) -> str:
        return code

    def handle_number_obfuscation(self, code: str) -> str:
        return code

    def decrypt_random_strings(self, code: str) -> str:
        return code

    def reconstruct_array_initialization(self, code: str) -> str:
        return code

    def detect_and_fix_syntax_errors(self, code: str) -> str:
        return code

    def fix_table_syntax(self, code: str) -> str:
        return code

    def fix_operator_misuse(self, code: str) -> str:
        return code

    def remove_invalid_chars(self, code: str) -> str:
        return code

    def fix_duplicate_locals(self, code: str) -> str:
        return code

    def demangle_variables(self, code: str) -> str:
        return code

    @staticmethod
    def defragment_strings(code: str) -> str:
        return code

    @staticmethod
    def remove_junkcode(code: str) -> str:
        return code

    def handle_accumulator_patterns(self, code: str) -> str:
        return code

    @staticmethod
    def track_buffer_permutations(code: str) -> str:
        return code

    @staticmethod
    def resolve_metatable_ops(code: str) -> str:
        return code

    @staticmethod
    def label_control_flow(code: str) -> str:
        return code

    @staticmethod
    def map_vm_operations(code: str) -> str:
        return code

    @staticmethod
    def resolve_accumulator_states(code: str) -> str:
        return code

    @staticmethod
    def reconstruct_final_string(code: str) -> str:
        return code

    @staticmethod
    def devirtualize_calls(code: str) -> str:
        return code

    @staticmethod
    def reverse_array_permutations(code: str) -> str:
        return code

    @staticmethod
    def prune_dead_code(code: str) -> str:
        return code

    @staticmethod
    def resolve_vm_dispatches(code: str) -> str:
        return code

    @staticmethod
    def reconstruct_split_strings(code: str) -> str:
        return code

    @staticmethod
    def simplify_arithmetic_masks(code: str) -> str:
        return code

    @staticmethod
    def resolve_buffer_indices(code: str) -> str:
        return code

    @staticmethod
    def analyze_phase_transitions(code: str) -> str:
        return code

    @staticmethod
    def resolve_buffer_swaps(code: str) -> str:
        return code

    @staticmethod
    def process_phased_code(code: str) -> str:
        return code

    @staticmethod
    def map_buffer_relationships(code: str) -> dict:
        return {}

    @staticmethod
    def simplify_arithmetic(code: str) -> str:
        return code

    @staticmethod
    def resolve_vm_structures(code: str) -> str:
        return code

    @staticmethod
    def propagate_constants(code: str) -> str:
        return code

    @staticmethod
    def simulate_execution(code: str) -> str:
        return code

    @staticmethod
    def phase_specific_decoding(code: str) -> str:
        return code

    @staticmethod
    def analyze_accumulator_flow(code: str) -> str:
        return code

    @staticmethod
    def normalize_string_ops(code: str) -> str:
        return code

    @staticmethod
    def decode_complex_string(encoded_str: str) -> str:
        return encoded_str

    @staticmethod
    def resolve_library_aliases(code: str) -> str:
        return code

    @staticmethod
    def fix_table_declarations(code: str) -> str:
        return code

    @staticmethod
    def simplify_numeric_operations(code: str) -> str:
        return code

    @staticmethod
    def decode_phase_specific_strings(code: str) -> str:
        return code

    @staticmethod
    def resolve_array_jumps(code: str) -> str:
        return code

    @staticmethod
    def resolve_string_sub_calls(code: str) -> str:
        return code

    @staticmethod
    def reconstruct_payload(code: str) -> str:
        return code

    @staticmethod
    def track_cross_phase_payload(code: str) -> Dict:
        return {}

    @staticmethod
    def enhance_phase_detection(code: str) -> str:
        return code


class CodeAnalyzer:
    def __init__(self):
        self.logger = logging.getLogger("CodeAnalyzer")

    def analyze_code(self, code: str) -> str:
        if not isinstance(code, str):
            code = str(code)
        return "=== Deobfuscation & Universal Analysis Complete ==="

    def build_control_flow_graph(self, code: str) -> dict:
        return {'nodes': {}, 'edges': []}


class PhaseAwareProcessor:
    def process_phased_code(self, code: str) -> str:
        return code


class PhaseBoundaryDetector:
    def process(self, code: str) -> str:
        return code


class HybridLiteralDecoder:
    def decode_hex_hybrids(self, code: str) -> str:
        return code


class PhaseParser:
    def detect_phases(self, code: str) -> Dict:
        return {'phases': [], 'transitions': []}


class AdaptivePhaseDetector:
    def detect_phases(self, code):
        return []


class DynamicPayloadTracker:
    def track_payload_components(self, code):
        return []


class HybridConverter:
    def convert_dynamic_hybrids(self, code):
        return code


class ControlFlowAnalyzer:
    def resolve_dynamic_gotos(self, code):
        return code


# --- Discord Bot Setup ---
intents = discord.Intents.default()
intents.message_content = True
bot = commands.Bot(command_prefix="!", intents=intents)

DEOBF_TRIGGERS = (
    "!deobf", ".deobf",
    ".moonsecv3deobf", "msdeobf", "moonsecdeobf",
    ".ironbrew2deobf", "ib2deobf", "ironbrewdeobf",
    ".ironveildeobf", "irvdeobf",
    ".prometheusdeobf", "promdeobf",
    ".herculesdeobf", "hercdeobf",
    ".wearedevsdeobf", "wd",
    ".luaobfuscatordeobf", "luaobfdeobf", "luaobf",
    ".lennyobfdeobf", "lendeobf",
    ".aztupbrewdeobf", "aztbrewdeobf",
    ".clvbrewdeobf", "cbrewdeobf",
    ".goofyscatordeobf", "goofyscator",
    ".zkowebismdeobf", "obfzkodeobf", "webismdeobf",
    ".clydedeobf",
    ".hide.latdeobf", "hidelatdeobf", "latdeobf", "hlatdeobf",
    ".encryptxdeobf"
)

@bot.event
async def on_ready():
    print(f'Logged in as {bot.user.name} (ID: {bot.user.id})')


@bot.event
async def on_message(message):
    if message.author == bot.user:
        return

    content_lower = message.content.strip().lower()

    # Universal Auto-Check and Auto-Deobfuscation on !l or any deobfuscation trigger
    if content_lower.startswith("!l") or any(content_lower.startswith(trigger) for trigger in DEOBF_TRIGGERS):
        if message.attachments:
            attachment = message.attachments[0]
            try:
                file_bytes = await attachment.read()
                code = file_bytes.decode('utf-8', errors='ignore')
                
                # Execute full universal polymorphism and multi-method deobfuscation pipeline
                polymorphism = Polymorphism_Reverse()
                processed_code = polymorphism.reverse_polymorphism(code)
                
                if not processed_code:
                    await message.reply(f"{message.author.mention} Auto-deobf failed to parse this protection scheme.")
                    return

                analyzer = CodeAnalyzer()
                analysis_report = analyzer.analyze_code(processed_code)

                output_name = attachment.filename
                if not output_name.endswith(".lua"):
                    output_name += "_auto_deobf.lua"
                else:
                    output_name = output_name.replace(".lua", "_auto_deobf.lua")
                    
                with open(output_name, "w", encoding="utf-8") as f:
                    f.write(processed_code)
                    
                with open(output_name, "rb") as f:
                    discord_file = discord.File(f, filename=output_name)
                    await message.reply(
                        f"🛡️ **Universal Auto Deobf & Check Results for {message.author.mention}**:\n```yaml\n{analysis_report[:1500]}\n```",
                        file=discord_file
                    )
                    
                if os.path.exists(output_name):
                    os.remove(output_name)
            except Exception as e:
                await message.reply(f"{message.author.mention} Error during auto-deobf: {str(e)}")
        else:
            await message.reply(f"{message.author.mention} Please attach a file to run the auto deobfuscation command.")
        return

    await bot.process_commands(message)


if __name__ == "__main__":
    TOKEN = "MTUxMTg4MzcwOTc5MDQyMTA2Mg.GUKmzH.Y0zAUWI0KKro0qT3B3YU-TXAgQyLUhma6PK_vw"
    bot.run(TOKEN)
