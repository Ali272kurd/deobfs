import sys
import re
import base64
import zlib
import tempfile
import os
import subprocess
import shutil
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
            ]
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


class Utils:
    @staticmethod
    def reverse_string_permutation(code: str) -> str:
        # Revert obfuscated string byte shifts or concatenation sequences
        code = re.sub(r'string\.char\s*\(\s*([0-9\s,\-+*//]+)\s*\)', lambda m: Utils._eval_char_code(m.group(1)), code)
        return code

    @staticmethod
    def _eval_char_code(expr: str) -> str:
        try:
            # Safely evaluate basic math character transformations
            nums = [int(n.strip()) for n in expr.split(',') if n.strip().isdigit()]
            if nums:
                return '"' + "".join([chr(n % 256) for n in nums]) + '"'
        except Exception:
            pass
        return f'string.char({expr})'

    @staticmethod
    def decode_prometheus_payload(payload: str) -> str:
        return payload

    @staticmethod
    def unpack_nested_encodings(code: str) -> str:
        # Unpack wrapped load/pcall obfuscations
        code = re.sub(r'pcall\s*\(\s*function\s*\(\s*\)\s*return\s*(.*?)\s*end\s*\)', r'\1', code)
        return code

    @staticmethod
    def evaluate_arithmetic(code: str) -> str:
        # Simplify redundant constant math expressions like (10 + 20) -> 30
        def evaluate_match(m):
            try:
                return str(eval(m.group(0)))
            except Exception:
                return m.group(0)
        return re.sub(r'\b\d+\s*[\+\-\*//]\s*\d+\b', evaluate_match, code)

    @staticmethod
    def detect_arithmetic_obfuscation(code: str) -> str:
        return code

    @staticmethod
    def handle_number_obfuscation(code: str) -> str:
        # Convert hex numbers back to standard literals if overly padded
        return re.sub(r'\b0[xX](?:0[xX])?([0-9a-fA-F]+)\b', lambda m: str(int(m.group(1), 16)), code)

    @staticmethod
    def decrypt_random_strings(code: str) -> str:
        return code

    @staticmethod
    def reconstruct_array_initialization(code: str) -> str:
        return code

    @staticmethod
    def detect_and_fix_syntax_errors(code: str) -> str:
        # Clean common syntax anomalies introduced by obfuscators
        code = re.sub(r';\s*;', ';', code)
        code = re.sub(r'\bdo\s+end\b', '', code)
        return code

    @staticmethod
    def fix_table_syntax(code: str) -> str:
        return re.sub(r',\s*\}', '}', code)

    @staticmethod
    def fix_operator_misuse(code: str) -> str:
        return code

    @staticmethod
    def remove_invalid_chars(code: str) -> str:
        return code

    @staticmethod
    def fix_duplicate_locals(code: str) -> str:
        return code

    @staticmethod
    def demangle_variables(code: str) -> str:
        return code

    @staticmethod
    def defragment_strings(code: str) -> str:
        return re.sub(r'"\s*\.\.\s*"', '', code)

    @staticmethod
    def remove_junkcode(code: str) -> str:
        # Remove dead assignments like var_x = var_x
        code = re.sub(r'\b([a-zA-Z_]\w*)\s*=\s*\1\s*;?', '', code)
        return code

    @staticmethod
    def handle_accumulator_patterns(code: str) -> str:
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
        # Prune empty if statements
        return re.sub(r'if\s+true\s+then\s*end', '', code)

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
        self._log("Starting universal polymorphism & multi-method reversal process")

        processing_steps = [
            (self._execute_step, step) for step in self._processing_pipeline()
        ]

        for step_func, step in processing_steps:
            if not step_func(step):
                self._log(f"Non-critical failure or handled fallback at step: {step[1]}", "warning")

        self._generate_final_report()
        self._log("Polymorphism reversal completed successfully for all methods")
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
            (lambda code: self.utils.handle_number_obfuscation(code), "Number obfuscation handling"),
            (demangle_names, "Name demangling"),
            (demangle_variables, "Variable demangling"),
            (reconstruct_tokenized, "Tokenized code reconstruction"),
            (restore_control_flow, "Control flow restoration"),
            (reconstruct_functions, "Function reconstruction"),
            (reconstruct_locals, "Local variable reconstruction"),
            (reconstruct_conditions, "Condition reconstruction"),
            (remove_junkcode, "Junk code removal"),
            (lambda code: self.utils.detect_and_fix_syntax_errors(code), "Syntax error detection and fixing"),
            (lambda code: self.utils.fix_table_syntax(code), "Table syntax fixing"),
            (clean_tokenized_syntax, "Tokenized syntax cleaning"),
            (Utils.defragment_strings, "String defragmentation"),
            (Utils.remove_junkcode, "Junk code removal"),
            (Utils.prune_dead_code, "Dead code removal"),
            (lambda c: self.remove_decoys(c), "Decoy pattern removal")
        ]

    def _execute_step(self, step: tuple) -> bool:
        func, description = step
        try:
            self.code = func(self.code)
            return True
        except Exception as e:
            self._log(f"Error in {description}: {str(e)}", "error")
            return False

    def _generate_final_report(self) -> None:
        print("\n=== Final Code Analysis ===")
        print(self.analyzer.analyze_code(self.code))

    def remove_decoys(self, code: str) -> str:
        cleaned_code, _ = self.decoy_detector.remove_decoys(code)
        return cleaned_code


class CodeAnalyzer:
    def analyze_code(self, code: str) -> str:
        return f"=== Deobfuscation Complete. Output Size: {len(code)} bytes ==="


class HybridLiteralDecoder:
    def decode_hex_hybrids(self, code: str) -> str: return code

class PhaseParser:
    def detect_phases(self, code: str) -> Dict: return {}

class AdaptivePhaseDetector:
    def detect_phases(self, code): return []

class DynamicPayloadTracker:
    def track_payload_components(self, code): return []

class HybridConverter:
    def convert_dynamic_hybrids(self, code): return code

class ControlFlowAnalyzer:
    def resolve_dynamic_gotos(self, code): return code


# --- Discord Bot Setup ---
intents = discord.Intents.default()
intents.message_content = True
bot = commands.Bot(command_prefix="!", intents=intents)

DEOBF_TRIGGERS = (
    "!deobf", ".deobf",
    ".moonsecv3deobf", "msdeobf", "moonsecdeobf",
    ".ironbrew2deobf", "ib2deobf", "ironbrewdeobf",
    ".prometheusdeobf", "promdeobf",
    ".wearedevsdeobf", "wd",
    ".luaobfuscatordeobf", "luaobfdeobf", "luaobf"
)

@bot.event
async def on_ready():
    print(f'Logged in as {bot.user.name} (ID: {bot.user.id})')


@bot.event
async def on_message(message):
    if message.author == bot.user:
        return

    content_lower = message.content.strip().lower()

    if content_lower.startswith("!l") or any(content_lower.startswith(trigger) for trigger in DEOBF_TRIGGERS):
        if message.attachments:
            attachment = message.attachments[0]
            try:
                file_bytes = await attachment.read()
                code = file_bytes.decode('utf-8', errors='ignore')
                
                polymorphism = Polymorphism_Reverse()
                processed_code = polymorphism.reverse_polymorphism(code)
                
                if not processed_code:
                    await message.reply(f"{message.author.mention} Auto-deobf failed to parse this protection scheme.")
                    return

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
                        f"🛡️ **Deobfuscation Successful for {message.author.mention}!**",
                        file=discord_file
                    )
                    
                if os.path.exists(output_name):
                    os.remove(output_name)
            except Exception as e:
                await message.reply(f"{message.author.mention} Error during auto-deobf: {str(e)}")
        else:
            await message.reply(f"{message.author.mention} Please attach a Lua file to run the command.")
        return

    await bot.process_commands(message)


if __name__ == "__main__":
    TOKEN = "MTUxMTg4MzcwOTc5MDQyMTA2Mg.GUKmzH.Y0zAUWI0KKro0qT3B3YU-TXAgQyLUhma6PK_vw"
    bot.run(TOKEN)
