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
                (r'\bgoto\s*=\s*[^;\n]+$', 'Invalid goto assignment'),
                (r'\bgoto\s*=\s*[^;\n]+$', 'Invalid goto assignment')
            ],
            'table_ops_decoys': [
                (r'\b(table|array)\s*\.\s*insert\s*=\s*[^;\n]+$', 'Invalid table.insert assignment'),
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
        self._log("Starting polymorphism reversal process")

        processing_steps = [
            (self._execute_step, step) for step in self._processing_pipeline()
        ]

        for step_func, step in processing_steps:
            if not step_func(step):
                raise RuntimeError(f"Failed at step: {step[1]}")

        self._generate_final_report()
        self._log("Polymorphism reversal completed")
        self._handle_special_cases()
        return self.code

    def _processing_pipeline(self) -> List[tuple]:
        return [
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
        if not self.vm_analyzer._valid_lua_syntax(code):
            self._log("Residual syntax errors detected - dumping problematic code section", "warning")
            with open("error_fragment.lua", "w") as f:
                f.write(code[:2000])
            return self.utils.detect_and_fix_syntax_errors(code)
        return code

    def analyze_vm_structures(self, code: str) -> str:
        self._log("Analyzing VM structures")
        analysis = self.vm_analyzer.analyze_vm_structure(code)
        entries = self.vm_analyzer.detect_vm_entries(code)
        opcodes = self.vm_analyzer.extract_opcode_mappings(code)

        report = [
            "Detected VM Components:",
            f"- Dispatch loops: {analysis['dispatch_loops']}",
            f"- Opcode handlers: {analysis['opcode_handlers']}",
            f"- Virtual registers: {analysis['virtual_registers']}",
            "\nVM Entry Points:",
            *[f"- {entry}" for entry in entries],
        ]

        if opcodes:
            report.extend([
                "\nOpcode Mappings:",
                *[f"- {op} => {handler}" for op, handler in opcodes.items()],
            ])

        return "\n".join(report)

    def _generate_final_report(self) -> None:
        analysis_report = self.analyzer.analyze_code(self.code)
        self._log("Generated final analysis report")
        print("\n=== Final Code Analysis ===")
        print(analysis_report)

    def analyze_trace(self, trace: str) -> str:
        self._log("Analyzing execution trace")
        patterns = {
            "dispatch_loops": len(re.findall(r"line 29", trace)),
            "opcode_handlers": len(re.findall(r"line 1", trace)),
            "anti_tamper_checks": len(re.findall(r"line 0", trace)),
        }

        report = [
            "Detected Execution Patterns:",
            f"- VM Dispatch cycles: {patterns['dispatch_loops']}",
            f"- Opcode executions: {patterns['opcode_handlers']}",
            f"- Anti-tamper checks passed: {patterns['anti_tamper_checks']}",
        ]

        if patterns["dispatch_loops"] > 10:
            report.append("\nVM Structure Detected:")
            report.append("- Array-based instruction dispatch")
            report.append("- Numeric opcode mapping")
            report.append("- Protected execution loop")

        return "\n".join(report)

    def translate_to_luau(self, code: str) -> str:
        self._log("Translating to Luau")
        code = re.sub(r'"\s*\.\.\s*"', '""', code)
        code = re.sub(r'(\w+)\s*\.\.=\s*(\w+)', r'\1 = \1 .. \2', code)
        
        transformations = [
            (
                r"local\s+(\w+)\s*=\s*\{\s*\[(\d+)\]\s*=\s*function\((.*?)\)(.*?)end\s*\}(?!\s*end)",
                self._convert_vm_table_to_luau_type,
            ),
            (r"\b(reg_\w+)\s*=\s*([^;]+)", r"\1: any = \2"),
        ]

        for pattern, replacement in transformations:
            code = re.sub(pattern, replacement, code, flags=re.DOTALL)

        code = re.sub(r'"\.\.\s*[^"]+\s*\.\.="', 'STR_CONCAT', code)
        code = re.sub(r'==\s*;\s*"[^"]+"', '== ""', code)

        return code

    def _convert_vm_table_to_luau_type(self, match: Match) -> str:
        var_name, opcode, params, body = match.groups()
        return f"""type {var_name} = {{
    new: (opcode: number) -> {{
        @luau.self
        function(self: {var_name}, {params}){body}
        end
    }}
}}"""

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
        self._log("Generating Lua bytecode")
        code = code or self.code
        try:
            if not self.vm_analyzer._valid_lua_syntax(code):
                self._log("Invalid Lua syntax detected - attempting repair", "warning")
                code = self.utils.detect_and_fix_syntax_errors(code)
            
            with tempfile.NamedTemporaryFile(suffix=".lua", delete=False) as tmp_lua:
                tmp_lua.write(code.encode())
                tmp_lua_path = tmp_lua.name
            
            luac_paths = [
                "luac54",
                "luac54.exe",
                os.path.join(os.environ.get("LUA_DIR", ""), "luac54.exe"),
                "C:\\lua\\luac54.exe",
                "C:\\Program Files\\Lua\\luac54.exe"
            ]
            
            for path in luac_paths:
                if shutil.which(path):
                    luac_path = path
                    break
            else:
                raise FileNotFoundError("Could not find luac in PATH.")
            
            output_file = output_path or "output.luac"
            subprocess.run(
                [luac_path, "-o", output_file, tmp_lua_path],
                check=True,
                shell=sys.platform == "win32",
                capture_output=True,
                text=True
            )
            
            with open(output_file, "rb") as f:
                bytecode = f.read()
            
            os.unlink(tmp_lua_path)
            if not output_path:
                os.unlink(output_file)
            
            return bytecode
        except Exception as e:
            self._log(f"Bytecode generation failed: {str(e)}", "error")
            return b""

    def restructure_accumulator_flow(self, code: str) -> str:
        code = re.sub(r"while accumulator\[1\]\s*<accumulator\[2\]", "-- ACCUMULATOR RANGE LOOP", code)
        code = re.sub(
            r"accumulator\[([^\]]+)\]\s*=\s*accumulator\[\1\]\s*[+-]",
            lambda m: f"accumulator[{m.group(1)}] = ...", 
            code
        )
        return code

    def normalize_variable_names(self, code: str) -> str:
        return re.sub(r"-var_(\d+)", lambda m: f"var_{int(m.group(1)) % 20}", code)

    def simplify_nested_ifs(self, code: str) -> str:
        return re.sub(
            r"(if accumulator < (-?\d+) then)(.*?)((?:elseif accumulator < (-?\d+) then.*?)*)(end)",
            self._replace_accumulator_condition,
            code,
            flags=re.DOTALL
        )

    def _replace_accumulator_condition(self, match: re.Match) -> str:
        initial_if, first_val, if_body, elifs, end = match.groups()
        cases = [f"case {first_val}:\n{if_body.strip()}"]
        elif_matches = re.finditer(
            r"elseif accumulator < (-?\d+) then((?:.(?!elseif|end))*.)",
            elifs, 
            flags=re.DOTALL
        )
        for elif_match in elif_matches:
            val, body = elif_match.groups()
            clean_body = re.sub(r"\bif accumulator < \d+ then", "-- Nested condition", body)
            cases.append(f"case {val}:\n{clean_body.strip()}")
        return f"""-- Converted accumulator condition
local accumulator_value = accumulator
switch accumulator_value do
    {"\n    ".join(cases)}
end
"""

    def resolve_vm_dispatches(self, code: str) -> str:
        return re.sub(
            r"while\s+true\s+do\s+(.*?local\s+(\w+)\s*=\s*(\w+)\[(\w+)\]\s*;.*?)(end)",
            self._rewrite_vm_loop,
            code,
            flags=re.DOTALL
        )

    def _rewrite_vm_loop(self, match: re.Match) -> str:
        loop_body, op_var, array_var, index_var = match.groups()
        cases = []
        handlers = re.finditer(
            r"if\s+" + re.escape(op_var) + r"\s*==\s*(\d+)\s+then\s+(.*?)(?=\belseif\b|\bend\b)",
            loop_body,
            flags=re.DOTALL
        )
        for handler in handlers:
            opcode, body = handler.groups()
            cases.append(f"case {opcode}:\n{self._clean_handler_body(body)}")
        return f"""local {index_var} = 1
while {index_var} <= #{array_var} do
    local {op_var} = {array_var}[{index_var}]
    switch {op_var} do
        {"\n        ".join(cases)}
    end
    {index_var} = {index_var} + 1
end"""

    def _clean_handler_body(self, body: str) -> str:
        body = re.sub(r"\b(\w+)\s*=\s*\1\s*\+\s*\d+\s*;?", "", body)
        return re.sub(r"\b(\w+)\[(\w+)\]", r"\1_\2", body)

    def _handle_special_cases(self):
        self.code = re.sub(r"for buffer = var_19, #accumulator, -\d+", "for buffer = 1, #accumulator, 1", self.code)
        self.code = re.sub(r"(\w+) & 0xFFFFFFFF / (\d+)", r"(\1 // \2) & 0xFF", self.code)
        self.code = re.sub(r'";"', '"..', self.code)

    def fix_base64_decoding(self, code: str) -> str:
        code = re.sub(r"string\.sub\(sta,t,\s*}\s*e,\s*}\s*(\w+),\s*\1\)", r"string.sub(stat, 1, \1)", code)
        return re.sub(r"number\s*=\s*number\s*\+\s*\w+\s*\*\s*64\s*\^\s*\(\(([^)]+)\)\s*-\s*io\)", r"number = (number << 8) + \1", code)

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
        code = re.sub(r"\b(?!function\b)(\w+)(\d)(\w*)\b", lambda m: f"{m.group(1)}{chr(ord(m.group(2)) + 49)}{m.group(3)}", code)
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
        code = re.sub(r'local function string \.sub \(string \.sub \)', 'local function string_sub(str)', code)
        code = re.sub(r'local payload = ""', 'local payload_chunks = {}', code)
        return re.sub(r'payload\s*=\s*payload\s*\.\.\s*([^\s;]+)', r'table.insert(payload_chunks, \1)', code)

    def resolve_goto_string_indexing(self, code: str) -> str:
        return re.sub(r'string\s*\[goto\s+LABEL_([a-z])\]', r'string_block_\1', code)

    def reconstruct_init_loop(self, code: str) -> str:
        return re.sub(r'for\s+string\.sub,\s*goto\s+in\s+ipairs\s*\(\s*{([^}]+)}', lambda m: f'for idx, goto_target in ipairs({{{self._clean_table(m.group(1))}}}) do', code)

    def _clean_table(self, table_content: str) -> str:
        return re.sub(r'(\d+)\D*', r'\1', table_content)

    def detect_phase_boundaries(self, code: str) -> str:
        detector = PhaseBoundaryDetector()
        return detector.process(code)

    def decode_hybrid_literals(self, code: str) -> str:
        return self.literal_decoder.decode_hex_hybrids(code)

    def phase_analysis(self, code: str) -> str:
        phase_info = self.phase_parser.detect_phases(code)
        self._log(f"Detected {len(phase_info['phases'])} phases")
        return Utils.enhance_phase_detection(code)

    def detect_adaptive_phases(self, code: str) -> str:
        phases = self.phase_detector.detect_phases(code)
        self._log(f"Detected {len(phases)} adaptive phases")
        return code

    def track_dynamic_payloads(self, code: str) -> str:
        components = self.payload_tracker.track_payload_components(code)
        self._log(f"Tracked {len(components)} payload components")
        return code

    def convert_hybrid_patterns(self, code: str) -> str:
        return self.hybrid_converter.convert_dynamic_hybrids(code)

    def resolve_control_flow(self, code: str) -> str:
        return self.cf_analyzer.resolve_dynamic_gotos(code)

    def remove_decoys(self, code: str) -> str:
        cleaned_code, removed = self.decoy_detector.remove_decoys(code)
        for desc, count in removed.items():
            self._log(f"Removed {count} {desc} decoys")
        return cleaned_code


class Utils:
    @staticmethod
    def reverse_string_permutation(code: str) -> str:
        patterns = [(r'"\s*\+\s*"', ""), (r'\[,""\]\s*=\s*\d+,', "")]
        return reduce(lambda c, p: re.sub(p[0], p[1], c), patterns, code)

    def decode_prometheus_payload(self, payload: str) -> str:
        try:
            decoded = base64.b64decode(payload)
            decompressed = zlib.decompress(decoded)
            key = self.detect_xor_key(decompressed)
            return "".join(chr(b ^ key) for b in decompressed)
        except Exception:
            return payload

    def unpack_nested_encodings(self, code: str) -> str:
        return reduce(
            lambda c, _: re.sub(
                r'loadstring\((["\'])([A-Za-z0-9+/=]+)\1\)',
                lambda m: self.decode_prometheus_payload(m.group(2)),
                c,
            ),
            range(3),
            code,
        )

    def detect_xor_key(self, data: bytes) -> int:
        lua_freq = {"a": 8.2, "e": 12.7, "i": 6.9, "o": 7.5, "u": 2.8}
        return max(
            range(256),
            key=lambda k: sum(
                lua_freq.get(chr(byte ^ k).lower(), 0) for byte in data[:1000]
            ),
        )

    def evaluate_arithmetic(self, code: str) -> str:
        code = re.sub(r"(\w+)\s+(\w+)(?=\s*\^)", r"\1*\2", code)
        code = re.sub(r"(\d+)\s+(\d+)", r"\1*\2", code)
        return re.sub(r"(\w+)\s*([+-])\s*(\w+)\s*(\^)", r"(\1 \2 \3)\4", code)

    def detect_arithmetic_obfuscation(self, code: str) -> str:
        code = re.sub(
            r"math\.floor\(([^)]+)\s*/\s*(\d{5,})\)",
            lambda m: str(int(eval(m.group(1)) // int(m.group(2)))),
            code,
        )
        code = re.sub(
            r"bit32\.bxor\(bit32\.band\(([^,]+),\s*(\d+)\)\s*,\s*(\d+)\)",
            lambda m: str((int(m.group(1)) & int(m.group(2))) ^ int(m.group(3))),
            code,
        )
        return code

    def handle_number_obfuscation(self, code: str) -> str:
        patterns = [
            (r"\bvar_18\b", "256"),
            (r"\bvar_12\b", "3"), 
            (r"\bvar_15\b", "1"),
            (r"\bvar_6\b", "2"),
            (r"64\s*\^\s*\(\s*\(\s*3\s*\*\s*1\s*\)\s*-\s*0\s*\)", "262144")
        ]
        return reduce(lambda c, p: re.sub(p[0], p[1], c), patterns, code)

    def decrypt_random_strings(self, code: str) -> str:
        code = re.sub(
            r'["\']([a-zA-Z0-9_$]{4,})["\']',
            lambda m: f'"{self.decode_random_string(m.group(1))}"',
            re.sub(r"\b(?:randomString|genStr|randStr|createStr)[A-Za-z0-9]*\([^)]*\)", '""', code),
        )
        return code

    def decode_random_string(self, s: str) -> str:
        charset = "qwertyuiopasdfghjklzxcvbnmQWERTYUIOPASDFGHJKLZXCVBNM1234567890"
        return "".join([c if c in charset else f"\\{ord(c)}" for c in s])

    def reconstruct_array_initialization(self, code: str) -> str:
        code = re.sub(r"\{\s*(\w+)\s*=\s*(\w+),?\s*(\d+)\s*=\s*(\d+),?", r"{\1 = \2, [\3] = \4}", code)
        return re.sub(r"\[\"\\049\"\]", r'[1]', code)

    def detect_and_fix_syntax_errors(self, code: str) -> str:
        error_corrections = {
            r'("\w+")\s*(\[[^]]+\])\s*([^,{])': r'\1\2,\3',
            r'(\]\s*=\s*[^,]+)\s+("[^"]+"|\w+)': r'\1,\2',
            r'{\s*"(\w+)"\s*([^=])': r'{["\1"] \2',
            r',\s*(\s*[}\]])': r'\1'    
        }
        return reduce(lambda c, t: re.sub(t[0], t[1], c), error_corrections.items(), code)

    def fix_table_syntax(self, code: str) -> str:
        code = re.sub(r"\[\\(\d+)\]", lambda m: f'["{chr(int(m.group(1)))}"]', code)
        code = re.sub(
            r"(\w+)\s*=\s*{\s*([^=]+)=\s*([^,}]+)(\s*[^,}]+)(,|})",
            lambda m: f"{m.group(1)} = {{{m.group(2)} = {m.group(3)},{m.group(4)}{m.group(5)}}}",
            code
        )
        code = re.sub(r",\s*(for|end|do|while)", r"; \1", code)
        return code

    def fix_operator_misuse(self, code: str) -> str:
        code = re.sub(r'=\s*\.\s*([^"\w])', r'= \1', code)
        code = re.sub(r'(\W)\.(\W)', r'\1\2', code)
        code = re.sub(r'=\s*"\s*\+\s*([^+"]+)\+\s*"', r'= "\1"..', code)
        code = re.sub(r'("\s*)\.\.(\s*")', r'\1+\2', code)
        code = re.sub(r'(\w+)\s*\.\.=\s*(\w+)', r'\1 = \1 .. \2', code)
        code = re.sub(r'(?<!\.)\.\.(?!\.)', ' .. ', code)
        code = re.sub(r'(\S)\.\.(\S)', r'\1 .. \2', code)
        return code

    def remove_invalid_chars(self, code: str) -> str:
        return re.sub(r"[\x00-\x1F\x7F-\x9F]", "", code)

    def fix_duplicate_locals(self, code: str) -> str:
        return re.sub(r"\blocal\s+local\b", "local", code)

    def demangle_variables(self, code: str) -> str:
        code = re.sub(r'\bfunct0n\b', 'function', code)
        code = re.sub(r"\b(?!function\b)(\w+)(\d)(\w*)\b", lambda m: f"{m.group(1)}{chr(ord(m.group(2)) + 49)}{m.group(3)}", code)
        return code

    @staticmethod
    def defragment_strings(code: str) -> str:
        return re.sub(r'(".*?")\s*\n\s*"(.*?")', lambda m: f'"{m.group(1)[1:-1]}{m.group(2)[1:-1]}"', code)

    @staticmethod
    def remove_junkcode(code: str) -> str:
        base_patterns = [
            (r'\b(local\s+)?([a-zA-Z_]\w*)\s*=\s*error\s*\(\s*\2\s*\)\s*[;]?\s*\n', ""),
            (r'(\b\w+\s*=\s*error\(\s*\w+\s*\))(\s*[^=]+\s*=\s*error\(\s*\w+\s*\))+', lambda m: ""),
            (r"(\w+)\s*=\s*\1\s*=\s*nil", ""),
            (r"math\.max\s*=\s*\w+\[\w+\]\[\d+\]", ""),
            (r"string\.format\s*=\s*error\(string\.format\)", ""),
            (r"\b(buffer|state|number|position)\s*=\s*nil\n", ""),
            (r"\b\w+\s*=\s*{\s*}\n", ""),
        ]
        extended_patterns = base_patterns + [
            (r"\b(char|memory|window)\s*=\s*for\b", ""),
            (r"\b\w+\s*=\s*\w+\s*[-+*/%^]\s*\w+\s*-\s*\w+", ""),
        ]
        for pattern, replacement in extended_patterns:
            code = re.sub(pattern, replacement, code, flags=re.MULTILINE|re.IGNORECASE)
        return re.sub(r'\n\s*\n', '\n', code)

    def handle_accumulator_patterns(self, code: str) -> str:
        patterns = [
            (r"accumulator\s*=\s*\(accumulator\s+and\s+(\w+)\s+or\s+(\w+)\)", lambda m: f"if {m.group(1)} then accumulator else {m.group(2)} end"),
            (r"accumulator\s*=\s*for\s+(-\d+)", lambda m: f"break  -- Loop exit at {m.group(1)}"),
            (r"accumulator\s*=\s*math\.max", "pcall() wrapper removed"),
            (r"accumulator\s*=\s*\(accumulator\s+and\s+([^\)]+)\s+or\s+([^\)]+)\)\s*([-+*/])\s*\(([^)]+)\)", lambda m: self._simplify_accumulator_math(m)),
            (r"\(-\s*(\w+)\)", lambda m: f"-{m.group(1)}"),
            (r"while\s+accumulator\s+do\s+(local\s+\w+\s*=\s*\w+\[\s*accumulator\s*\]\s*;.*?)\s*end", self._convert_accumulator_loop)
        ]
        return reduce(lambda c, p: re.sub(p[0], p[1], c, flags=re.DOTALL), patterns, code)

    def _simplify_accumulator_math(self, match: re.Match) -> str:
        true_expr, false_expr, op, rhs = match.groups()
        simplified = f"({true_expr} {op} {rhs}) if accumulator else ({false_expr} {op} {rhs})"
        return f"accumulator = {simplified}"

    def _convert_accumulator_loop(self, match: re.Match) -> str:
        loop_body = match.group(1)
        array_match = re.search(r"local\s+(\w+)\s*=\s*(\w+)\[accumulator\]", loop_body)
        if array_match:
            var_name, array_name = array_match.groups()
            return f"for {var_name} in ipairs({array_name}) do\n{loop_body}\nend"
        return match.group(0)

    @staticmethod
    def track_buffer_permutations(code: str) -> str:
        patterns = [
            (r"\b(buffer)\s*=\s*for\s*\(\s*(\w+)\s*([/%])\s*(\w+)\s*\)", lambda m: f"-- BUFFER LOOP: {m.group(2)} {m.group(3)} {m.group(4)}"),
            (r"\b(buffer)\s*([%\/])\s*(\w+)", lambda m: f"{m.group(1)} {m.group(2)} {m.group(3)} -- BUFFER OP"),
            (r"\bbuffer\s*\[\s*(\w+)\s*\]", lambda m: f"buffer[{m.group(1)}] -- BUFFER ACCESS"),
            (r"buffer\[([^\]]+)\],\s*buffer\[([^\]]+)\]\s*=\s*buffer\[\2\],\s*buffer\[\1\]", lambda m: f"-- SWAPPED: buffer[{m.group(1)}] <-> buffer[{m.group(2)}]"),
            (r"buffer\[([^\]]+)\],\s*buffer\[([^\]]+)\],([^=]*)=\s*buffer\[\2\],\s*buffer\[\1\],([^\n]+)", lambda m: f"-- SWAP CHAIN: buffer[{m.group(1)}]<->buffer[{m.group(2)}]"),
            (r"buffer\s*[%\/]\s*(-?\d{6,})", lambda m: f"buffer {m.group(0).split()[-1]} -- MAGIC_NUM_OP")
        ]
        for pattern, handler in patterns:
            code = re.sub(pattern, handler, code, flags=re.IGNORECASE)
        return code

    @staticmethod
    def resolve_metatable_ops(code: str) -> str:
        return re.sub(r"getmetatable\(([\w.]+(\s*\([^)]*\))?)\)\[(__index|__newindex)\]", lambda m: f"{re.sub(r'\W', '_', m.group(1))}_metatable[{m.group(3)}]", code)

    @staticmethod
    def label_control_flow(code: str) -> str:
        phase_labels = {
            r"11836030": "STRING_MANIPULATION_PHASE",
            r"12102741": "IO_OPERATIONS", 
            r"12093236": "TABLE_INITIALIZATION",
            r"11464279": "MEMORY_ALLOCATION",
            r"10056034": "STRING_BUFFERING", 
            r"9901030": "CRYPTO_ROUTINES",
            r"9826299": "BYTECODE_VERIFICATION",
            r"-?11917660": "INITIALIZATION_PHASE",
            r"4437436": "STRING_DECODING",
            r"2400310": "ARRAY_SETUP", 
            r"-?8368111": "CLEANUP_ROUTINE",
            r"-?\d{7,}": "VM_OPERATION"
        }
        for pattern, label in phase_labels.items():
            code = re.sub(rf"accumulator\s*([<>]=?)\s*({pattern})(\s*then|\s*do)", lambda m: f"accumulator {m.group(1)} {label}{m.group(3)}", code)
        return code

    @staticmethod
    def map_vm_operations(code: str) -> str:
        vm_ops = {
            r"-?11917660": "INITIALIZATION_PHASE",
            r"4437436": "STRING_DECODING",
            r"2400310": "ARRAY_SETUP",
            r"-?8368111": "CLEANUP_ROUTINE",
            r"\d{7,}": "VM_OPERATION"
        }
        for pattern, label in vm_ops.items():
            code = re.sub(rf"\b{label}\s*=\s*({pattern})\b", f"{label} = {list(vm_ops.values()).index(label) + 1}", code)
        return code

    @staticmethod
    def resolve_accumulator_states(code: str) -> str:
        return re.sub(r"accumulator\s*([<>]=?)\s*(-?\d+)", lambda m: f"current_phase {m.group(1)} {Utils._get_phase_label(int(m.group(2)))}", code)

    @staticmethod
    def _get_phase_label(value: int) -> str:
        phase_labels = {
            -11917660: "INITIALIZATION_PHASE",
            4437436: "STRING_DECODING_PHASE",
            2400310: "CRYPTO_ROUTINE_PHASE",
            11464279: "MEMORY_ALLOCATION_PHASE",
            10056034: "STRING_BUFFERING_PHASE"
        }
        return phase_labels.get(value, f"PHASE_{abs(value) % 1000}")

    @staticmethod
    def reconstruct_final_string(code: str) -> str:
        def _decode_match(m: re.Match) -> str:
            try:
                parts = re.findall(r'(?:"([A-Za-z0-9+/=]*)")|([a-zA-Z0-9+=]+)', m.group(0))
                combined = []
                for p in parts:
                    if p[0]:  
                        combined.append(p[0])
                    elif p[1]:  
                        if p[1].startswith(('0x', '0X')):
                            translated = str(int(p[1], 16))
                        elif '\\0' in p[1]:
                            translated = p[1].replace('\\0', '\x00')
                        else:
                            translated = p[1].translate(str.maketrans("pqr", "+-*"))
                        combined.append(str(eval(translated)))
                full_string = "".join(combined)
                if len(full_string) % 4 == 0 and re.match(r'^[A-Za-z0-9+/=]+$', full_string):
                    decoded = base64.b64decode(full_string).decode('utf-8', 'replace')
                    decoded = decoded.replace('\x00', '').replace('\\0', '').replace('\\x00', '')
                    return f'"{decoded}"'
                return f'"{full_string}"'
            except Exception as e:
                logging.debug(f"Concatenation decoding failed: {str(e)}")
                return m.group(0)
                
        code = re.sub(r'("[\w+/=]+"\s*\.\.\s*)+[\w+]+==?', _decode_match, code)
        return re.sub(r'("\w+=")\s*\.\.\s*(\w+)', lambda m: f'"{m.group(1)[1:-1]}{m.group(2)}"', code)

    @staticmethod
    def devirtualize_calls(code: str) -> str:
        return re.sub(r"(\w+)\[string\.sub\[([^\]]+)\]\]\s*\(", lambda m: f"{Utils._map_virtual_function(m.group(1), m.group(2))}(", code)

    @staticmethod
    def _map_virtual_function(table: str, key: str) -> str:
        mappings = {
            "handle": {"var_17": "debug_trace", "3": "crypto_verify", "4": "memory_alloc"},
            "table": {"2": "array_init", "5": "buffer_flush"}
        }
        return mappings.get(table, {}).get(key.strip("]"), f"{table}_FUNC")

    @staticmethod
    def reverse_array_permutations(code: str) -> str:
        return re.sub(r"buffer\[(\d+)\],\s*buffer\[(\d+)\]\s*=\s*buffer\[\2\],\s*buffer\[\1\]", lambda m: f"-- REVERSED: Original positions {m.group(1)}<->{m.group(2)}", code)

    @staticmethod
    def prune_dead_code(code: str) -> str:
        dead_code_patterns = [
            r"if current_phase < PHASE_\d+ then.*?end",  
            r"var_\d+ = var_\d+ % \d+ -- BUFFER ARITHMETIC.*?end",  
            r"buffer\[\d+\].*?-- SWAPPED.*?end"  
        ]
        for pattern in dead_code_patterns:
            code = re.sub(pattern, "", code, flags=re.DOTALL)
        return code

    @staticmethod
    def resolve_vm_dispatches(code: str) -> str:
        return re.sub(r"if accumulator < (\w+) then([\s\S]*?)elseif", lambda m: f"switch(accumulator):\n    case < {m.group(1)}:{m.group(2)}", code, flags=re.DOTALL)

    @staticmethod
    def reconstruct_split_strings(code: str) -> str:
        def _decode_and_combine(m: re.Match) -> str:
            try:
                combined = base64.b64decode(m.group(1) + m.group(2))
                return f'"{combined.decode("utf-8", "replace")}"'
            except Exception as e:
                return f'-- DECODE_FAILED: {str(e)}'
        return re.sub(r'"([A-Za-z0-9+/=]+)"\s*[;+]\s*"([A-Za-z0-9+/=]*)"\s*[%\/]\s*(\d+)', _decode_and_combine, code)

    @staticmethod
    def simplify_arithmetic_masks(code: str) -> str:
        mask_patterns = {"% 256": "& 0xFF", "% 65536": "& 0xFFFF", "% var_4": "& 0xFFFFFFFF"}
        for pattern, replacement in mask_patterns.items():
            code = code.replace(pattern, replacement)
        return code

    @staticmethod
    def resolve_buffer_indices(code: str) -> str:
        def _resolve_index(array: str, index: str) -> str:
            index_mappings = {"var_4": "DWORD_INDEX", "var_8": "QWORD_INDEX", "var_16": "ARRAY_START"}
            return index_mappings.get(index, f"{index}_CALCULATED")
        return re.sub(r"buffer\[(\w+)\[(\w+)\]\]", lambda m: f"buffer[{_resolve_index(m.group(1), m.group(2))}]", code)

    @staticmethod
    def analyze_phase_transitions(code: str) -> str:
        phase_mappings = {
            -1237065: "BUFFER_INITIALIZATION",
            4657791: "STRING_DECODING", 
            1410847: "ARITHMETIC_MASKING",
            5685554: "CONTROL_FLOW_OBFUSCATION"
        }
        def _replace_phase(m: re.Match) -> str:
            value = int(m.group(3))
            return f"{m.group(1)} {m.group(2)} {phase_mappings.get(value, f'UNKNOWN_PHASE_{value}')}"
        return re.sub(r"(current_phase|accumulator)\s*(<|>|=+)\s*(-?\d+)", _replace_phase, code)

    @staticmethod
    def resolve_buffer_swaps(code: str) -> str:
        return re.sub(
            r"buffer\[(\w+)\[(\w+)\]\]\s*,\s*buffer\[(\w+)\[(\w+)\]\]\s*=\s*buffer\[\3\[\4\]\]\s*,\s*buffer\[\1\[\2\]\]",
            lambda m: (
                f"-- SWAP: buffer[{m.group(1)}[{m.group(2)}]] <-> buffer[{m.group(3)}[{m.group(4)}]]\n"
                f"buffer[{m.group(1)}[{m.group(2)}]], buffer[{m.group(3)}[{m.group(4)}]] = "
                f"buffer[{m.group(3)}[{m.group(4)}]], buffer[{m.group(1)}[{m.group(2)}]]"
            ),
            code
        )

    @staticmethod
    def process_phased_code(code: str) -> str:
        current_phase = "GLOBAL"
        phased_code = []
        phase_processor = PhaseAwareProcessor()
        for line in code.split('\n'):
            phase_match = re.search(r"PHASE_(\w+)", line)
            if phase_match:
                current_phase = phase_match.group(1)
            processed = phase_processor._apply_phase_handlers(line, current_phase)
            phased_code.append(processed)
        return '\n'.join(phased_code)

    @staticmethod
    def map_buffer_relationships(code: str) -> dict:
        buffer_graph = nx.DiGraph()
        current_phase = "INIT"
        for line in code.split('\n'):
            if 'PHASE_' in line:
                current_phase = re.search(r"PHASE_(\w+)", line).group(0)
            if match := re.search(r"buffer\[(\d+)\].*?=\s*(.*?);", line):
                index, value = match.groups()
                buffer_graph.add_node(index, phase=current_phase, value=value)
            if match := re.search(r"buffer\[(\d+)\].*?buffer\[(\d+)\]", line):
                src, dest = match.groups()
                buffer_graph.add_edge(src, dest, phase=current_phase)
        return buffer_graph

    @staticmethod
    def simplify_arithmetic(code: str) -> str:
        patterns = [
            (r"(\w+)\s*&\s*0xFFFFFFFF\s*/", r"BYTE_EXTRACT(\1)"),
            (r"(%\s*)(256|var_536)", r"BYTE_MASK"),
            (r"(\d+)\s*[-+]\s*(\d+)\s*%\s*", r"MOD_OP(\1, \2)"),
            (r"accumulator\s*=\s*(.*?)\s*%\s*(\d+)", r"PHASE_KEY(\2): \1")
        ]
        for pattern, replacement in patterns:
            code = re.sub(pattern, replacement, code)
        return code

    @staticmethod
    def resolve_vm_structures(code: str) -> str:
        code = re.sub(r"if accumulator < (\w+) then\s*(.*?)\s*elseif", r"case \1:\n    \2\nbreak;\nswitch(\1):", code, flags=re.DOTALL)
        opcodes = {46551: "STRING_DECODE", 1237065: "BUFFER_INIT", 46494: "ARITH_MASK"}
        return re.sub(r"-\s*(\d+)", lambda m: f"- {opcodes.get(int(m.group(1)), f'OP_{m.group(1)}')}", code)

    @staticmethod
    def propagate_constants(code: str) -> str:
        const_map = {"var_18": "256", "var_3": "1", "var_12": "6", "var_15": "1", "io": "0"}
        for var, value in const_map.items():
            code = code.replace(var, value)
        return re.sub(r"\b(\d+)\b", lambda m: f"0x{int(m.group(1)):X}" if int(m.group(1)) > 255 else m.group(1), code)

    @staticmethod
    def simulate_execution(code: str) -> str:
        state = {'phase': 'INIT', 'buffer': {}, 'accumulator': 0}
        output = []
        for line in code.split('\n'):
            if 'PHASE_' in line:
                phase_match = re.search(r"PHASE_(\w+)", line)
                if phase_match:
                    state['phase'] = phase_match.group(1)
            if 'buffer[' in line:
                index_match = re.search(r"buffer\[(\d+)\]", line)
                value_match = re.search(r"=\s*(.*?);", line)
                if index_match and value_match:
                    index = index_match.group(1)
                    try:
                        state['buffer'][index] = eval(value_match.group(1), {}, state)
                    except:
                        pass
            output.append(f"-- [{state['phase']}] {line}")
        return '\n'.join(output)

    @staticmethod
    def phase_specific_decoding(code: str) -> str:
        phase_handlers = {
            "303": lambda s: base64.b64decode(s).decode(),
            "657": lambda s: bytes([int(c)^0xFF for c in s.split()]).decode(),
            "954": lambda s: zlib.decompress(base64.b64decode(s)).decode()
        }
        return re.sub(r'-- PHASE:(\w+)\s*"([^"]+)"', lambda m: f'"{phase_handlers[m.group(1)](m.group(2))}"' if m.group(1) in phase_handlers else m.group(0), code)

    @staticmethod
    def analyze_accumulator_flow(code: str) -> str:
        code = re.sub(r"accumulator\[([^\]]+)\]\s*([+-])=\s*(\d+)", lambda m: f"acc[{m.group(1)}] {m.group(2)}= {m.group(3)} -- ACCUM_OP", code)
        return re.sub(r"if number == 4\s+then\s+-- BUFFER LOOP", "if byte_counter == 4 then  -- BYTE_BOUNDARY", code)

    @staticmethod
    def normalize_string_ops(code: str) -> str:
        code = re.sub(r'==\s*,\s*"([^"]+)"', r'== "\1"', code)
        return re.sub(r'"\s*\.\.\s*[A-Za-z0-9]+\s*\.\.\s*"', 'CONCAT_B64_CHUNK', code)

    @staticmethod
    def decode_complex_string(encoded_str: str) -> str:
        encoded_str = Utils.reconstruct_final_string(encoded_str)
        try:
            phase_decoded = Utils.phase_specific_decoding(encoded_str)
            decoded = re.sub(r'\\(\d{1,3})', lambda m: chr(int(m.group(1))), phase_decoded)
            if re.search(r'"\s*\.\.\s*"', decoded):
                decoded = Utils.reconstruct_final_string(decoded)
            decoded = re.sub(r'\((\d+)\s*([-+*/])\s*(\d+)\)', lambda m: str(eval(f"{m.group(1)}{m.group(2)}{m.group(3)}", {"__builtins__": None}, {})), decoded)
            return decoded
        except Exception as e:
            logging.debug(f"String decoding fallback: {str(e)}")
            return encoded_str

    @staticmethod
    def resolve_library_aliases(code: str) -> str:
        aliases = {
            r"\bflag\s*=\s*table\.insert\b": "-- Restored table.insert reference",
            r"\bgoto\s*=\s*math\.floor\b": "-- Restored math.floor reference",
            r"\bstring\s*=\s*table\.concat\b": "-- Restored table.concat reference"
        }
        for pattern, replacement in aliases.items():
            code = re.sub(pattern, replacement, code)
        return code

    @staticmethod
    def fix_table_declarations(code: str) -> str:
        code = re.sub(r",\s*(\d+)\s*=\s*", lambda m: f", [{m.group(1)}] = ", code)
        code = re.sub(r"\[\\(\d+)\"\]", lambda m: f'["\\{m.group(1)}"]', code)
        code = re.sub(r";(\s*\w+\s*=)", r"\1", code)
        return re.sub(r"\b(for|while|do|end)\s*=", lambda m: f'["{m.group(1)}"] =', code)

    @staticmethod
    def simplify_numeric_operations(code: str) -> str:
        code = re.sub(r"0x100\b", "256", code)
        code = re.sub(r"\bvar_18\b", "256", code)  
        return re.sub(r"(\w+)\s+(\w+)(?=\s*[\^\%])", r"\1*\2", code)

    @staticmethod
    def decode_phase_specific_strings(code: str) -> str:
        phase_strings = {
            'PHASE_3H': lambda s: base64.b64decode(s[::-1]).decode(),
            'PHASE_2B': lambda s: zlib.decompress(base64.b85decode(s)),
            'PHASE_4F': lambda s: bytes(int(c)^0x55 for c in s.split()).decode()
        }
        for phase, decoder in phase_strings.items():
            code = re.sub(fr'-- {phase}.*?\n(.*?)\n--', lambda m: f'-- DECODED:\n"{decoder(m.group(1))}"\n--', code, flags=re.DOTALL)
        return code

    @staticmethod
    def resolve_array_jumps(code: str) -> str:
        return re.sub(r'string\[goto\[(\w+)\]\]', lambda m: f'string_block_{m.group(1)}', code)

    @staticmethod
    def resolve_string_sub_calls(code: str) -> str:
        code = re.sub(r'string \.sub', 'string.sub', code)
        return re.sub(r'string\.sub\(([^,]+),\s*([^,]+),\s*([^)]+)\)', lambda m: f'string_sub({m.group(1)}, {m.group(2)}, {m.group(3)})', code)

    @staticmethod
    def reconstruct_payload(code: str) -> str:
        return re.sub(r'local payload_chunks = {([^}]+)}', lambda m: f'local payload = table.concat({{{m.group(1)}}})', code)

    @staticmethod
    def track_cross_phase_payload(code: str) -> Dict:
        payload_map = defaultdict(list)
        phase_data = re.finditer(r'local\s+(\w+)\s*=\s*{\s*("[^"]*"\s*,?)+\s*}', code)
        for match in phase_data:
            var_name = match.group(1)
            chunks = re.findall(r'"([^"]*)"', match.group(0))
            payload_map[var_name].extend(chunks)
        return payload_map

    @staticmethod
    def enhance_phase_detection(code: str) -> str:
        return re.sub(r'--\s*\[?([A-Z]+)_PHASE\]?', lambda m: f'-- PHASE_BOUNDARY:{m.group(1)}', code)


class CodeAnalyzer:
    def __init__(self):
        self.logger = logging.getLogger("CodeAnalyzer")
        logging.basicConfig(format="%(asctime)s - %(name)s - %(levelname)s - %(message)s", level=logging.INFO)

    def analyze_code(self, code: str) -> str:
        if not isinstance(code, str):
            code = str(code)
        analysis_functions = [
            self.analyze_control_flow,
            self.track_data_flow,
            self.detect_vm_patterns,
            self.extract_string_operations,
            self.find_suspicious_patterns,
        ]
        analysis = {fn.__name__: fn(code) for fn in analysis_functions}
        return self._generate_analysis_report(analysis)

    def _generate_analysis_report(self, analysis: Dict) -> str:
        report_sections = [
            (
                "Control Flow",
                [
                    f"Nested loops: {analysis['analyze_control_flow']['nested_loops']}",
                    f"Complex conditionals: {analysis['analyze_control_flow']['complex_conditions']}",
                    f"Function calls: {analysis['analyze_control_flow']['function_calls']}",
                ],
            ),
            (
                "Virtualization Indicators",
                [
                    f"{k.replace('_', ' ').title()}: {v}"
                    for k, v in analysis["detect_vm_patterns"].items()
                ],
            ),
            ("Suspicious Patterns", analysis["find_suspicious_patterns"]),
        ]
        return "\n".join(line for section, content in report_sections for line in [f"=== {section} ==="] + content)

    def analyze_control_flow(self, code):
        return {
            "nested_loops": len(re.findall(r"\bfor\b.*\bdo\b.*\bwhile\b", code, re.DOTALL)),
            "complex_conditions": len(re.findall(r"\bif\b.*\bthen\b.*\belseif\b", code, re.DOTALL)),
            "function_calls": len(re.findall(r"\b[\w.]+\(", code)),
            "exception_handling": len(re.findall(r"\bpcall\b|\bxpcall\b", code)),
            "goto_patterns": len(re.findall(r"goto\s*\[[^\]]+\]", code)),
            "invalid_jumps": len(re.findall(r"while\s+goto", code))
        }

    def track_data_flow(self, code):
        return len(re.findall(r"\b(var_[\dA-Fa-f]+)\b", code))

    def detect_vm_patterns(self, code):
        return {
            "array_based_dispatch": len(re.findall(r"\bJUMP_OFFSET\s*\[.+\]", code)),
            "window_switching": len(re.findall(r"\bWINDOW_SIZE\s*=\s*{[^}]+}", code)),
            "shift_operations": len(re.findall(r"\bSHIFT_COUNT\b.*[-+*/%^]=", code)),
            "numeric_control_flow": len(re.findall(r"\bvar_\d+\b", code)),
            "state_transitions": len(re.findall(r"\b(?:if|elseif)\s+[A-Z_]+\s*==\s*-\d+", code)),
        }

    def extract_string_operations(self, code):
        return {
            "concatenations": len(re.findall(r"\.\.", code)),
            "base64_usage": len(re.findall(r"base64|=[=]*$", code)),
            "hex_encoded": len(re.findall(r"\\x[0-9a-fA-F]{2}", code)),
            "string_obfuscation": len(re.findall(r"string\.(char|byte)|decode", code)),
        }

    def find_suspicious_patterns(self, code):
        suspicious = []
        if re.search(r"\b(?:-\d+|var_\d+)\s*[<>]=?", code):
            suspicious.append("Numeric condition patterns (common in VM branching)")
        if re.search(r"\b\w+\s*\[[A-Z_]+\]\s*\(", code):
            suspicious.append("Array-based function dispatch detected")
        if re.search(r"\b\d{6,}\b", code):
            suspicious.append("Large numeric constants (potential encoded values)")
        if re.search(r"[-+*/%]\s*\d+\s*[)]*\s*[%^]\s*\d+", code):
            suspicious.append("Complex arithmetic patterns (possible bitwise encoding)")
        return suspicious

    def build_control_flow_graph(self, code: str) -> dict:
        cfg = {'nodes': {}, 'edges': [], 'loops': [], 'current_id': 0}
        loop_stack = []
        loop_counter = 1
        current_line = 1  
        for line in code.split('\n'):
            if 'do' in line and 'while' in line:
                loop_id = f"LOOP_{loop_counter}"
                loop_counter += 1
                cfg['nodes'][loop_id] = {'type': 'loop', 'start_line': current_line, 'end_line': None, 'depth': len(loop_stack) + 1, 'nested': bool(loop_stack)}
                cfg['loops'].append({'id': loop_id, 'parent': loop_stack[-1] if loop_stack else None})
                loop_stack.append(loop_id)
                if cfg['edges']:
                    last_edge = cfg['edges'][-1][1]
                    cfg['edges'].append((last_edge, loop_id))
            elif 'end' in line and loop_stack:
                loop_id = loop_stack.pop()
                cfg['nodes'][loop_id]['end_line'] = current_line
                cfg['edges'].append((loop_id, loop_id))
            current_line += 1  
        node_list = list(cfg['nodes'].keys())
        for i in range(len(node_list)-1):
            cfg['edges'].append((node_list[i], node_list[i+1]))
        return cfg

    def analyze_vm_phases(self, code: str) -> str:
        code = re.sub(r"-- \[(\d+)\]\s*-- \[\d+\]\s*(local\s+\w+)", r"-- PHASE_\1_START\n\2", code)
        return re.sub(r"(UNKNOWN_PHASE_\w+)", lambda m: f"-- VM_PHASE_{m.group(1).split('_')[-1]}", code)

    def analyze_phase_relationships(self, code: str) -> Dict:
        if not isinstance(code, str):
            code = str(code)
        parser = PhaseParser()
        return {'phase_analysis': parser.detect_phases(code), 'payload_map': Utils.track_cross_phase_payload(code)}

    def enhanced_analysis(self, code: str) -> dict:
        return {
            'phases': AdaptivePhaseDetector().detect_phases(code),
            'payload_components': DynamicPayloadTracker().track_payload_components(code),
            'control_flow': ControlFlowAnalyzer().resolve_dynamic_gotos(code)
        }


class PhaseAwareProcessor:
    PHASE_HANDLERS = {
        "BUFFER_INIT": [(r"%-?\d+", "PHASE_STEP"), (r"var_\d+", "MAGIC_NUMBER")],
        "STRING_DECODE": [(r'("\s*\.\.\s*\\\d{3})', "CONCAT_ESCAPE"), (r'\\\d{3}\s*\.\.\s*"', "END_ESCAPE_CHAIN"), (r'(\d+)\\', r'\1\\')]
    }
    
    def process_phased_code(self, code: str) -> str:
        current_phase = "GLOBAL"
        phased_code = []
        for line in code.split('\n'):
            phase_match = re.search(r"PHASE_(\w+)", line)
            if phase_match:
                current_phase = phase_match.group(1)
            processed = self._apply_phase_handlers(line, current_phase)
            phased_code.append(processed)
        return '\n'.join(phased_code)

    def _apply_phase_handlers(self, line: str, current_phase: str) -> str:
        for pattern, replacement in self.PHASE_HANDLERS.get(current_phase, []):
            if re.search(pattern, line):
                return re.sub(pattern, replacement, line)
        return line


class PhaseBoundaryDetector:
    def __init__(self):
        self.patterns = [(r'--\s*\[INIT\]', 'INIT_PHASE'), (r'LABEL_[a-z]', 'CONTROL_FLOW_MARKER')]

    def process(self, code: str) -> str:
        for pattern, replacement in self.patterns:
            code = re.sub(pattern, f'-- {replacement}', code)
        return code


class HybridLiteralDecoder:
    def decode_hex_hybrids(self, code: str) -> str:
        return re.sub(r'"\\-- HEX_HYBRID_LITERAL(.*?)\\-- HEX_HYBRID_LITERAL"', self._decode_hybrid_chunk, code, flags=re.DOTALL)

    def _decode_hybrid_chunk(self, match) -> str:
        chunk = match.group(1)
        decoded = []
        for part in re.findall(r'(\\d+)|(\D+)', chunk):
            if part[0]:  
                decoded.append(chr(int(part[0][1:])))
            elif part[1]:  
                decoded.append(part[1])
        return f'"{ "".join(decoded) }"'


class PhaseParser:
    def __init__(self):
        self.phase_context = {'current': None, 'prev': None, 'next': None, 'payload_sources': defaultdict(list)}

    def detect_phases(self, code: str) -> Dict:
        phase_matches = re.findall(r'--\s*([A-Z]{3,6})_PHASE(?::(\w+))?', code)
        return {
            'phases': [{'name': m[0], 'subphase': m[1] if len(m) > 1 else None} for m in phase_matches],
            'transitions': self._find_phase_transitions(code)
        }

    def _find_phase_transitions(self, code: str) -> List:
        return re.findall(r'PHASE_(\w+)\s*→\s*PHASE_(\w+)', code)


class AdaptivePhaseDetector:
    def __init__(self):
        self.phase_pattern = re.compile(r'--\s*([A-Z]{2,8})[_\-]?(PHASE|BOUNDARY|VM)\b[:]?' r'(\{.*?\})?', re.DOTALL)
        self.phase_handlers = defaultdict(lambda: self.generic_phase_handler)

    def detect_phases(self, code):
        phases = []
        for match in self.phase_pattern.finditer(code):
            phase_type = match.group(1).lower()
            try:
                config = json.loads(match.group(3) or '{}')
            except json.JSONDecodeError:
                config = {}
            phases.append({'name': phase_type, 'start': match.start(), 'end': match.end(), 'config': config})
        return phases

    def generic_phase_handler(self, code_segment):
        return re.sub(r'\bvar_\d+\b', 'PHASE_VAR', code_segment)


class DynamicPayloadTracker:
    def __init__(self):
        self.payload_pattern = re.compile(r'(local|function)\s+([a-z_]+)\s*=\s*' r'(?:{.*?}|\[.*?\]|function.*?end)', re.DOTALL)

    def track_payload_components(self, code):
        components = []
        for match in self.payload_pattern.finditer(code):
            component_type = match.group(1)
            name = match.group(2)
            components.append({'type': component_type, 'name': name, 'content': match.group(0), 'position': match.start()})
        return components


class HybridConverter:
    def convert_dynamic_hybrids(self, code):
        return re.sub(r'\b(\d+)([a-zA-Z])(?=\b|_)', lambda m: f'{m.group(1)} --[[HYBRID:{m.group(2)}]]', code)


class ControlFlowAnalyzer:
    def __init__(self):
        self.label_map = {}

    def resolve_dynamic_gotos(self, code):
        self.label_map.clear()
        for match in re.finditer(r'::(LABEL_\w+)::', code):
            self.label_map[match.group(1)] = match.start()
        return re.sub(r'\bgoto\s+(LABEL_\w+)', self._replace_goto, code)

    def _replace_goto(self, match):
        label = match.group(1)
        return f'goto {self.label_map.get(label, "UNKNOWN_LABEL")}'


# --- Discord Bot Setup ---
intents = discord.Intents.default()
intents.message_content = True
bot = commands.Bot(command_prefix="!", intents=intents)

@bot.event
async def on_ready():
    print(f'Logged in as {bot.user.name} (ID: {bot.user.id})')
    
    # Send !BOT ON @all when successfully running
    for guild in bot.guilds:
        for channel in guild.text_channels:
            if channel.permissions_for(guild.me).send_messages:
                try:
                    await channel.send("!BOT ON @all")
                    break
                except Exception:
                    continue

@bot.event
async def on_message(message):
    if message.author == bot.user:
        return

    if message.content.strip().startswith("!deobf"):
        if message.attachments:
            attachment = message.attachments[0]
            try:
                file_bytes = await attachment.read()
                code = file_bytes.decode('utf-8', errors='ignore')
                
                polymorphism = Polymorphism_Reverse()
                processed_code = polymorphism.reverse_polymorphism(code)
                
                if not processed_code or "Failed" in processed_code:
                    await message.reply(f"{message.author.mention} it doesnt work on this type of method to deobfuscate")
                    return

                output_name = attachment.filename
                if not output_name.endswith(".lua"):
                    output_name += "_deobf.lua"
                else:
                    output_name = output_name.replace(".lua", "_deobf.lua")
                    
                with open(output_name, "w", encoding="utf-8") as f:
                    f.write(processed_code)
                    
                with open(output_name, "rb") as f:
                    discord_file = discord.File(f, filename=output_name)
                    await message.reply(f"here is your deobfuscated file {message.author.mention}", file=discord_file)
                    
                if os.path.exists(output_name):
                    os.remove(output_name)
                    
            except Exception as e:
                await message.reply(f"{message.author.mention} it doesnt work on this type of method to deobfuscate")
        else:
            await message.reply(f"{message.author.mention} Please attach a file with the `!deobf` command.")

    await bot.process_commands(message)


if __name__ == "__main__":
    lock_file = "bot_runtime.lock"
    current_time = time.time()
    
    # Check if the bot was executed within the last 24 hours (86400 seconds)
    if os.path.exists(lock_file):
        with open(lock_file, "r") as f:
            try:
                last_run = float(f.read().strip())
                if current_time - last_run < 86400:
                    print("Bot has already been executed within the last 24 hours. Exiting to prevent re-execution.")
                    sys.exit(0)
            except ValueError:
                pass

    # Update lock file with current timestamp
    with open(lock_file, "w") as f:
        f.write(str(current_time))

    if len(sys.argv) > 1 and sys.argv[1] != "--token":
        with open(sys.argv[1], "r") as f:
            code = f.read()

        polymorphism = Polymorphism_Reverse()
        processed_code = polymorphism.reverse_polymorphism(code)

        output_name = sys.argv[1].replace(".lua", "_deobf.lua")

        analyzer = CodeAnalyzer()
        cfg = analyzer.build_control_flow_graph(processed_code)
        print(cfg)

        try:
            with open(output_name, "w") as f:
                f.write(processed_code)
        except IOError as e:
            print(f"Error writing output: {str(e)}")
    else:
        # Run bot using your token here
        TOKEN = "MTUxMTg4MzcwOTc5MDQyMTA2Mg.GUKmzH.Y0zAUWI0KKro0qT3B3YU-TXAgQyLUhma6PK_vw"
        bot.run(TOKEN)
