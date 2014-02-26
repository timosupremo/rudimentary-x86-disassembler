#
# 695.744 - Reverse Engineering and Vulnerability Analysis
# Homework 2
#
# Tim Nary <tnary1@jhu.edu>
#
# This is a rudimentary x86 disassembler that implements linear sweep and recursive descent algorithms.
# It was developed and tested on Windows 7 with Python 2.7.6.
# 
# Usage: disassembler.py <path_to_binary> [-m recursive|linear]
#

import argparse
import binascii
from struct import unpack
import sys
import string
import os
import ntpath
import traceback

# Parse Command Line Arguments
parser = argparse.ArgumentParser(description="A very rudimentary x86 disassembler that implements linear sweep and recursive descent algorithms")
parser.add_argument("file", type=str, help="Location of binary to disassemble")
parser.add_argument('-m','--mode', type=str, default='recursive', help="Disassembler mode: linear = linear sweep, recursive = recursive descent (default)")
args = parser.parse_args()

# Global Variables
# file to disassemble
filename = args.file
# disassembly mode (linear sweep or recursive descent)
mode = args.mode
# byte to keep track of current read byte
byte = ""

# dictionary to store translated machine code
disassembly = {}

# dictionary to store the raw bytes for a particular disassembled instruction
machine = {}

# store addresses jumped from to return for further processing
call_stack = []

# list of labels referenced by a call or jump function
offset_labels = []

# x86 Registers
x86Registers = [
	'eax',
	'ecx',
	'edx',
	'ebx',
	'esp',
	'ebp',
	'esi',
	'edi'
]

# x86 Register Encodings (for ModR/M Byte)
x86RegisterEncodings = {
	'000':'eax',
	'001':'ecx',
	'010':'edx',
	'011':'ebx',
	'100':'esp',
	'101':'ebp',
	'110':'esi',
	'111':'edi'
}

# lookup table for opcode+reg instructions 
encodedOperandLookupTable = {
	'40':'inc eax',
	'41':'inc ecx',
	'42':'inc edx',
	'43':'inc ebx',
	'44':'inc esp',
	'45':'inc ebp',
	'46':'inc esi',
	'47':'inc edi',
	'48':'dec eax',
	'49':'dec ecx',
	'4a':'dec edx',
	'4b':'dec ebx',
	'4c':'dec esp',
	'4d':'dec ebp',
	'4e':'dec esi',
	'4f':'dec edi',
	'58':'pop eax',
	'59':'pop ecx',
	'5a':'pop edx',
	'5b':'pop ebx',
	'5c':'pop esp',
	'5d':'pop ebp',
	'5e':'pop esi',
	'5f':'pop edi',
	'50':'push eax',
	'51':'push ecx',
	'52':'push edx',
	'53':'push ebx',
	'54':'push esp',
	'55':'push ebp',
	'56':'push esi',
	'57':'push edi',
	'b8':'mov eax',
	'b9':'mov ecx',
	'ba':'mov edx',
	'bb':'mov ebx',
	'bc':'mov esp',
	'bd':'mov ebp',
	'be':'mov esi',
	'bf':'mov edi',
}

# bswap mnemonic - pg 146
# BSWAP r32 - 0F C8+rd
bswapLookupTable = {
	'c8':'bswap eax',
	'c9':'bswap ecx',
	'ca':'bswap edx',
	'cb':'bswap ebx',
	'cc':'bswap esp',
	'cd':'bswap ebp',
	'ce':'bswap esi',
	'cf':'bswap edi',
}

# Helper Functions
def dec2bin(x):
	return "".join(map(lambda y:str((x>>y)&1), range(8-1, -1, -1)))

def hexToSigned8(h):
	return int(h, 16) if int(h,16) < int('0x80', 16) else (-int('0xff', 16)+int(h,16)-1)

def hexToSigned32(h):
	return int(h, 16) if int(h,16) < int('0x80000000', 16) else (-int('0xffffffff', 16)+int(h,16)-1)

def make_dword_printable(dword):
	return ' '.join(a+b for a,b in zip(dword[::2], dword[1::2]))
	
# ModR/M byte parser - pg 33
def parseModRM(mod, rm, eip, f, mc):
	if mod == "00": # [reg]
		if rm == "100":
			raise Exception("ModR/M [--][--] Not Implemented")
		elif rm == "101":
			dword = f.read(4)
			mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
			disp32 = str(hex(unpack('<L', dword)[0])) # little endian
			eip.addr += 4 # disp32
			return "["  + disp32 + "]"
		else:
			return "[" + x86RegisterEncodings[rm] + "]"
	elif mod == "01": # [reg+byte]
		if rm == "100":
			raise Exception("ModR/M [--][--]+disp8 Not Implemented")
		else: 
			disp8 = binascii.hexlify(f.read(1))
			mc.bytes = mc.bytes + " " + disp8
			eip.addr += 1 # disp8
			return "[" + x86RegisterEncodings[rm] + "+0x" + disp8 + "]"
	elif mod == "10": # [reg+dword]
		if rm == "100":
			raise Exception("ModR/M [--][--]+disp32 Not Implemented")
		else:
			dword = f.read(4)
			mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
			disp32 = str(hex(unpack('<L', dword)[0])) # little endian
			eip.addr += 4 # disp32
			return "[" + x86RegisterEncodings[rm] + "+0x" + disp32 + "]"
	elif mod == "11": # reg
		return x86RegisterEncodings[rm]
	else:
		raise Exception("Invalid ModR/M Encoding")

# make the call and 'push' the return address onto the call_stack to 'pop' it later on return
def call_next(f, eip, op, offset):
	# if already branched and haven't returned yet, stop
	if eip.addr in call_stack:
		handle_ret(f, eip, op)
		return
	call_stack.append(eip.addr)
	if mode == "recursive":
		eip.addr = offset
		f.seek(offset)

# unconditional jump, don't append return address to call_stack
def jmp_next(f, eip, op, offset):
	if mode == "recursive":
		eip.addr = offset
		f.seek(offset)

# handle resetting the eip when we return
def handle_ret(f, eip, op):
	if mode == "recursive":
		if not call_stack:
			# if the call stack is empty, stop
			global byte
			byte = ""
			return
		else:
			# jump back to previous address
			eip.addr = call_stack.pop()
			f.seek(eip.addr)

# EIP class to keep track of current instruction address and previous jump address
class EIP(object):
	addr = 0
	jump_addr = 0

# MachineCode class to keep track of machine code bytes
class MachineCode(object): 
	bytes = ""

# Certain opcodes require checking the second byte to determine the operation
# This method figures out which parser should be called for ambiguous 1 byte opcodes
def ambiguous(f, eip, op):
	if op == "0f":
		byte_two = binascii.hexlify(f.read(1))
		if byte_two in bswapLookupTable:
			eip.addr +=2 # 0F C8+rd
			return {"machine":mc.bytes, "assembly":bswapLookupTable[byte_two]}
		elif byte_two == "84":
			f.seek(-1,1) # go back 1 byte
			return jz(f, eip, op)
		elif byte_two == "85":
			f.seek(-1,1) # go back 1 byte
			return jnz(f, eip, op)
		elif byte_two == "af":
			f.seek(-1,1) # go back 1 byte
			return imul(f, eip, op)
		elif byte_two == "b7":
			byte_three = binascii.hexlify(f.read(1))
			eip.addr += 3
			if byte_three == "c8":
				return {"machine":"0f b7 c8", "assembly":"movzx ecx, ax"}
			else:
				raise Exception("Error parsing movzx mnemonic")
		else:
			raise Exception("Unsupported Opcode")
	elif op == "83" or op == "81":
		byte_two = binascii.hexlify(f.read(1))
		binary_string = dec2bin(int(byte_two, 16))
		reg = binary_string[2:5]
		f.seek(-1,1) # go back 1 byte
		if reg == "000": # /0
			return add(f, eip, op)
		elif reg == "100": # /4
			return x86and(f, eip, op)
		elif reg == "111": # /7
			return x86cmp(f, eip, op)
		elif reg == "001": # /1
			return x86or(f, eip, op)
		elif reg == "011": # /3
			return sbb(f, eip, op)
		elif reg == "110": # /6
			return xor(f, eip, op)
		else:
			raise Exception("Unsupported Opcode")
	elif op == "f2":
		byte_two = binascii.hexlify(f.read(1))
		eip.addr += 2
		if byte_two == "a7":
			return {"machine":"f2 a7", "assembly":"repne cmps DWORD PTR ds:[esi], DWORD PTR es:[edi]"}
		else:
			raise Exception("Error parsing repne cmpsd mnemonic")
	elif op == "f3":
		byte_two = binascii.hexlify(f.read(1))
		byte_three = binascii.hexlify(f.read(1))
		eip.addr += 3
		if byte_two == "0f" and byte_three == "b8":
			# F3 0F B8 /r POPCNT r32, r/m32
			modrm = binascii.hexlify(f.read(1))
			mc.bytes = mc.bytes +  " " + modrm
			eip.addr += 1 # modrm
			binary_string = dec2bin(int(modrm, 16))
			mod = binary_string[0:2]
			reg = binary_string[2:5]
			rm = binary_string[5:]
			parsedmod = parseModRM(mod, rm, eip, f, mc)
			return {"machine":"f3 0f b8" + modrm, "assembly":"popcnt " + x86RegisterEncodings[reg] + ", " + parsedmod}
		else:
			raise Exception("Error parsing popcnt mnemonic")
	elif op == "f7":
		byte_two = binascii.hexlify(f.read(1))
		binary_string = dec2bin(int(byte_two, 16))
		reg = binary_string[2:5]
		f.seek(-1,1)
		if reg == "000": # /0
			return test(f, eip, op)
		elif reg == "010": # /2
			return x86not(f, eip, op)
		elif reg == "011": # /3
			return neg(f, eip, op)
		elif reg == "100": # /4
			return mul(f, eip, op)
		elif reg == "101": # /5
			return imul(f, eip, op)
		elif reg == "111": # /7
			return idiv(f, eip, op)
		else:
			raise Exception("Unsupported Opcode")
	elif op == "fe":
		byte_two = binascii.hexlify(f.read(1))
		binary_string = dec2bin(int(byte_two, 16))
		reg = binary_string[2:5]
		f.seek(-1,1)
		if reg == "000" or reg == "001": # /0 INC, /1 DEC
			return incdec(f, eip, op)
		else:
			raise Exception("Unsupported Opcode")
	elif op == "ff":
		byte_two = binascii.hexlify(f.read(1))
		binary_string = dec2bin(int(byte_two, 16))
		reg = binary_string[2:5]
		f.seek(-1,1)
		if reg == "000" or reg == "001": # /0 INC, /1 DEC
			return incdec(f, eip, op)
		elif reg == "100" or reg == "101": # /4  / 5
			return jmp(f, eip, op)
		elif reg == "010" or reg == "011": # /2  /3
			return call(f, eip, op)
		elif reg == "110": #/6
			return push(f, eip, op)
		else:
			raise Exception("Unsupported Opcode")
	else:
		raise Exception("Unsupported Opcode")

# add mnemonic - pg 89
def add(f, eip, op):
	mc = MachineCode()
	mc.bytes = op
	eip.addr += 1 # opcode
	if op == "01" or op == "03":
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes +  " " + modrm
		eip.addr += 1 # modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		reg = binary_string[2:5]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		if op == "01": # ADD r/m32, r32
			return {"machine":mc.bytes, "assembly":"add " + parsedmod + ", " + x86RegisterEncodings[reg]}
		else: # ADD r32, r/m32
			return {"machine":mc.bytes, "assembly":"add " + x86RegisterEncodings[reg] + ", " + parsedmod}
	elif op == "81" or op == "83":
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + modrm
		eip.addr += 1 # modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		if op == "81": # ADD r/m32, imm32
			dword = f.read(4)
			imm32 = str(hex(unpack('<L', dword)[0]))
			mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
			eip.addr += 4 #imm32
			return {"machine":mc.bytes, "assembly": "add " + parsedmod + ", 0x" + imm32}
		else: # ADD r/m32, imm8
			byte = f.read(1)
			imm8 = binascii.hexlify(byte)
			mc.bytes = mc.bytes + " " + binascii.hexlify(byte)
			eip.addr += 1 #imm8
			return {"machine":mc.bytes, "assembly":"add " + parsedmod + ", 0x" + imm8}
	elif op == "05": # ADD EAX, imm32
		dword = f.read(4)
		imm32 = str(hex(unpack('<L', dword)[0]))
		mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
		eip.addr += 4 #imm32
		return {"machine":mc.bytes, "assembly":"add eax, 0x" + imm32}	
	else:
		raise Exception("Error parsing add mnemonic")

# and mnemonic - pg 113
def x86and(f, eip, op): # and is a reserved word in python
	mc = MachineCode()
	mc.bytes = op
	eip.addr += 1 #opcode
	if op == "21" or op == "23":
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes +  " " + modrm
		eip.addr += 1 #modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		reg = binary_string[2:5]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		if op == "21": # AND r/m32, r32
			return {"machine":mc.bytes, "assembly":"and " + parsedmod + ", " + x86RegisterEncodings[reg]}
		else: # AND r32, r/m32
			return {"machine":mc.bytes, "assembly":"and " + x86RegisterEncodings[reg] + ", " + parsedmod}
	elif op == "81" or op == "83":
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + modrm
		eip.addr += 1 #modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		if op == "81": # AND r/m32, imm32
			dword = f.read(4)
			imm32 = str(hex(unpack('<L', dword)[0]))
			mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
			eip.addr += 4 #imm32
			return {"machine":mc.bytes, "assembly": "and " + parsedmod + ", 0x" + imm32}
		else: # AND r/m32, imm8
			byte = f.read(1)
			imm8 = binascii.hexlify(byte)
			mc.bytes = mc.bytes + " " + binascii.hexlify(byte)
			eip.addr += 1 #imm8
			return {"machine":mc.bytes, "assembly":"and " + parsedmod + ", 0x" + imm8}
	elif op == "25": # AND EAX, imm32
		dword = f.read(4)
		imm32 = str(hex(unpack('<L', dword)[0]))
		mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
		eip.addr += 4 #imm32
		return {"machine":mc.bytes, "assembly":"and eax, 0x" + imm32}	
	else:
		raise Exception("Error parsing and mnemonic")

# bswap mnemonic - pg 146
# see bswapLookupTable / ambiguous function

# call mnemonic - pg 157
def call(f, eip, op):
	mc = MachineCode()
	mc.bytes = op
	eip.addr += 1 #opcode
	if op == "ff": # CALL r/m32
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + modrm
		eip.addr += 1 #modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		return {"machine":mc.bytes, "assembly":"call " + parsedmod}
	elif op == "e8": # CALL rel32
		dword = f.read(4)
		offset = hex(unpack('<L', dword)[0])
		mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
		eip.addr += 4 #imm32
		signed = hexToSigned32(offset)
		# eip may change based on call_next, so save values
		ret = {"machine":mc.bytes, "assembly":"call offset_" + '{:x}'.format(eip.addr + signed) + "h"}
		offset_labels.append(str(hex(eip.addr + signed)))
		if signed != 0:
			call_next(f, eip, op, eip.addr + signed)
		return ret
	else:
		raise Exception("Error parsing call mnemonic")

# cmp mnemonic - pg 183
def x86cmp(f, eip, op): # cmp is a python built-in function
	mc = MachineCode()
	mc.bytes = op
	eip.addr += 1 #opcode
	if op == "39" or op == "3b":
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + modrm
		binary_string = dec2bin(int(modrm, 16))
		eip.addr += 1 #modrm
		mod = binary_string[0:2]
		reg = binary_string[2:5]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		if op == "39": # CMP r/m32, r32
			return {"machine":mc.bytes, "assembly":"cmp " + parsedmod + ", " +  x86RegisterEncodings[reg]}
		else: # CMP r32, r/m32
			return {"machine":mc.bytes, "assembly":"cmp " + x86RegisterEncodings[reg] + ", " +  parsedmod}
	elif op == "81" or op == "83":
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + modrm
		binary_string = dec2bin(int(modrm, 16))
		eip.addr += 1 #modrm
		mod = binary_string[0:2]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		if op == "81": # CMP r/m32, imm32
			dword = f.read(4)
			imm32 = str(hex(unpack('<L', dword)[0]))
			eip.addr += 4 #imm32
			mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
			return {"machine":mc.bytes, "assembly":"cmp" + parsedmod  + ", " + imm32}
		else: # CMP r/m32, imm8
			byte = f.read(1)
			imm8 = binascii.hexlify(byte)
			mc.bytes = mc.bytes + " " + binascii.hexlify(byte)
			eip.addr += 1 #imm8
			return {"machine":mc.bytes, "assembly":"cmp " + parsedmod  + ", 0x" + imm8}
	elif op == "3d": # CMP EAX, imm32
		dword = f.read(4)
		imm32 = str(hex(unpack('<L', dword)[0]))
		mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
		eip.addr += 4 #imm32
		return {"machine":mc.bytes, "assembly":"cmp eax, 0x" + imm32}
	else:	
		raise Exception("Error parsing cmp mnemonic")

# dec mnemonic - pg 292
# uses same code as inc
def incdec(f, eip, op):
	mc = MachineCode()
	mc.bytes = op
	eip.addr +=1 #opcode
	if op in encodedOperandLookupTable: # DEC r32  INC r32
		return {"machine":mc.bytes, "assembly":encodedOperandLookupTable[op]}
	elif op == "ff":
		modrm = binascii.hexlify(f.read(1))
		eip.addr += 1 #modrm
		mc.bytes = mc.bytes + " " + modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		reg = binary_string[2:5]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		if reg == "000": # INC r/m32
			return {"machine":mc.bytes, "assembly":"inc " + parsedmod}
		else: # DEC r/m32
			return {"machine":mc.bytes, "assembly":"dec " + parsedmod}
	else:
		raise Exception("Error parsing inc/dec mnemonic")

# idiv mnemonic - pg 446
def idiv(f, eip, op):
	mc = MachineCode()
	mc.bytes = op
	eip.addr += 1 #opcode
	if op == "f7": # IDIV r/m32
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes +  " " + modrm
		eip.addr += 1 #modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		return {"machine":mc.bytes, "assembly":"idiv " + parsedmod}
	else:
		raise Exception("Error parsing idiv mnemonic")

# imul mnemonic - pg 449
def imul(f, eip, op):
	mc = MachineCode()
	mc.bytes = op
	eip.addr += 1 #opcode
	if op == "0f": # IMUL r32, r/m32
		byte_two = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes +  " " + byte_two
		eip.addr += 1 #opcode
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes +  " " + modrm
		eip.addr += 1 #modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		reg = binary_string[2:5]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		return {"machine":mc.bytes, "assembly":"imul " + x86RegisterEncodings[reg] + ", " + parsedmod}
	elif op == "6b" or op == "69": 
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + modrm
		eip.addr += 1 #modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		reg = binary_string[2:5]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		if op == "69": # IMUL r32, r/m32, imm32
			dword = f.read(4)
			imm32 = str(hex(unpack('<L', dword)[0]))
			mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
			eip.addr += 4 #imm32
			return {"machine":mc.bytes, "assembly": "imul " + x86RegisterEncodings[reg] + ", " + parsedmod + ", 0x" + imm32}
		else: # IMUL r32, r/m32, imm8
			byte = f.read(1)
			imm8 = binascii.hexlify(byte)
			mc.bytes = mc.bytes + " " + binascii.hexlify(byte)
			eip.addr += 1 #imm8
			return {"machine":mc.bytes, "assembly":"imul " + x86RegisterEncodings[reg] + ", " + parsedmod + ", 0x" + imm8}
	elif op == "f7": # IMUL r/m32
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + modrm
		eip.addr += 1 #modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		return {"machine":mc.bytes, "assembly":"imul eax, " + parsedmod}	
	else:
		raise Exception("Error parsing imul mnemonic")

# inc mnemonic - pg 455
# see incdec function

# jmp mnemonic - pg 495
def jmp(f, eip, op):
	mc = MachineCode()
	mc.bytes = op
	eip.addr += 1 #opcode
	if op == "ff": # JMP r/m32
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + modrm
		eip.addr += 1 #modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		return {"machine":mc.bytes, "assembly":"jmp " + parsedmod}
	elif op == "e9": # JMP rel32
		dword = f.read(4)
		offset = hex(unpack('<L', dword)[0])
		eip.addr += 4 #rel32
		mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
		signed = hexToSigned32(offset)
		rel32 = '{:x}'.format(eip.addr + signed)
		offset_labels.append(str(hex(eip.addr + signed)))
		jmp_next(f, eip, op, eip.addr + signed)
		return {"machine":mc.bytes, "assembly":"jmp offset_" + rel32 + "h"}
	elif op == "eb": # JMP rel8
		rel8 = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + rel8
		signed = hexToSigned8(rel8)
		eip.addr += 1 #rel8
		rel8 = '{:x}'.format(eip.addr + signed)
		offset_labels.append(str(hex(eip.addr + signed)))
		jmp_next(f, eip, op,eip.addr + signed)
		return {"machine":mc.bytes, "assembly":"jmp offset_" + rel8 + "h"}
	else:
		raise Exception("Error parsing jmp mnemonic")

# jz/jnz mnemonic - pg 490
def jz(f, eip, op):
	mc = MachineCode()
	mc.bytes = op
	eip.addr += 1 #opcode
	if op == "74": # JZ rel8
		rel8 = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + rel8
		signed = hexToSigned8(rel8)
		eip.addr += 1 #rel8
		rel8 = '{:x}'.format(eip.addr + signed)
		offset_labels.append(str(hex(eip.addr + signed)))
		call_next(f, eip, op,eip.addr + signed)
		return {"machine":mc.bytes, "assembly":"jz offset_" + rel8 + "h"}
	elif op == "0f": # JZ rel32
		byte_two = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes +  " " + byte_two
		eip.addr += 1 #opcode
		dword = f.read(4)
		offset = hex(unpack('<L', dword)[0])
		mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
		eip.addr += 4 #rel32
		signed = hexToSigned32(offset)
		rel32 = '{:x}'.format(eip.addr + signed)
		offset_labels.append(str(hex(eip.addr + signed)))
		call_next(f, eip, op, eip.addr + signed)
		return {"machine":mc.bytes, "assembly":"jz offset_" + rel32 + "h"}
	else:
		raise Exception("Error parsing jz mnemonic")

def jnz(f, eip, op):
	mc = MachineCode()
	mc.bytes = op
	eip.addr += 1 #opcode
	if op == "75": # JNZ rel8
		rel8 = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + rel8
		signed = hexToSigned8(rel8)
		eip.addr += 1 #rel8
		rel8 = '{:x}'.format(eip.addr + signed)
		offset_labels.append(str(hex(eip.addr + signed)))
		call_next(f, eip, op,eip.addr + signed)
		return {"machine":mc.bytes, "assembly":"jnz offset_" + rel8 + "h"}
	elif op == "0f": # JNZ rel32
		byte_two = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes +  " " + byte_two
		eip.addr += 1 #opcode
		dword = f.read(4)
		offset = hex(unpack('<L', dword)[0])
		mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
		eip.addr += 4 #rel32
		signed = hexToSigned32(offset)
		rel32 = '{:x}'.format(eip.addr + signed)
		offset_labels.append(str(hex(eip.addr + signed)))
		call_next(f, eip, op, eip.addr + signed)
		return {"machine":mc.bytes, "assembly":"jnz offset_" + rel32 + "h"}
	else:
		raise Exception("Error parsing jnz mnemonic")

# lea mnemonic - pg 514
def lea(f, eip, op): # LEA r32,m
	mc = MachineCode()
	mc.bytes = op
	eip.addr += 1 #opcode
	if op == "8d":
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + modrm
		eip.addr += 1 #modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		reg = binary_string[2:5]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		return {"machine":mc.bytes, "assembly":"lea " + x86RegisterEncodings[reg] + ", " + parsedmod}
	else:
		raise Exception("Error parsing lea mnemonic")

# mov mnemonic - pg 564
def mov(f, eip, op):
	mc = MachineCode()
	mc.bytes = op
	eip.addr += 1 #opcode
	if op == "89" or op == '8b': 
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + modrm
		eip.addr += 1 #modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		reg = binary_string[2:5]
		rm = binary_string[5:]	
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		if op == '89': # MOV r/m32,r32
			return {"machine":mc.bytes, "assembly":"mov " + parsedmod + ", " + x86RegisterEncodings[reg]}
		elif op == "8b": # MOV r32,r/m32
			return {"machine":mc.bytes, "assembly":"mov " + x86RegisterEncodings[reg]+ ", " +  parsedmod}
	elif op == "c7": # MOV r/m32, imm32
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + modrm
		eip.addr += 1 #modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		rm = binary_string[5:]		
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		dword = f.read(4)
		mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
		imm32 = str(hex(unpack('<L', dword)[0]))
		eip.addr += 4 #imm32
		return {"machine":mc.bytes, "assembly":"mov " + parsedmod + ", 0x" + imm32}
	elif op in encodedOperandLookupTable: # MOV r32, imm32
		dword = f.read(4)
		mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
		imm32 = str(hex(unpack('<L', dword)[0]))
		eip.addr += 4
		return {"machine":mc.bytes, "assembly": encodedOperandLookupTable[op] + ", 0x" + imm32}
	else:
		raise Exception("Error parsing mov mnemonic")

# movsb/movsd mnemonic - pg 620
def movs(f, eip, op):
	mc = MachineCode()
	mc.bytes = op
	eip.addr += 1 #opcode
	if op == "a4":
		return {"machine":mc.bytes, "assembly": "movs BYTE PTR es:[edi], BYTE PTR ds:[esi]"}
	elif op == "a5":
		return {"machine":mc.bytes, "assembly": "movs DWORD PTR es:[edi], DWORD PTR ds:[esi]"}
	else:
		raise Exception("Error parsing movsb/movsd mnemonic")

# movzx mnemonic - pg 638
# See ambiguous
# movzx ecx, ax -> 0f b7 c8 

# mul mnemonic - pg 648
def mul(f, eip, op):
	mc = MachineCode()
	mc.bytes = op
	eip.addr += 1 #opcode
	if op == "f7": # MUL r/m32
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + modrm
		eip.addr += 1 #modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		return {"machine":mc.bytes, "assembly":"mul " + parsedmod}
	else:
		raise Exception("Error parsing mul mnemonic")

# neg mnemonic - pg 666
def neg(f, eip, op):
	mc = MachineCode()
	mc.bytes = op
	eip.addr += 1 #opcode
	if op == "f7": # NEG r/m32
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + modrm
		eip.addr += 1 #modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		return {"machine":mc.bytes, "assembly":"neg " + parsedmod}
	else:
		raise Exception("Error parsing neg mnemonic")

# nop mnemonic - pg 668
def nop(f, eip, op):
	mc = MachineCode()
	mc.bytes = op
	eip.addr += 1 #opcode
	if op == "90": # NOP
		return {"machine":mc.bytes, "assembly":"nop"}
	elif op == "1f": # NOP r/m32
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + modrm
		eip.addr += 1 #modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		return {"machine":mc.bytes, "assembly":"nop " + parsedmod}
	else:
		raise Exception("Error parsing neg mnemonic")

# not mnemonic - pg 669
def x86not(f, eip, op): # not is a reserved word in python
	mc = MachineCode()
	mc.bytes = op
	eip.addr += 1 #opcode
	if op == "f7": # NOT r/m32
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + modrm
		eip.addr += 1 #modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		return {"machine":mc.bytes, "assembly":"not " + parsedmod}
	else:
		raise Exception("Error parsing not mnemonic")

# or mnemonic - pg 671
def x86or(f, eip, op): # or is a reserved word in python
	mc = MachineCode()
	mc.bytes = op
	eip.addr += 1 #opcode
	if op == "09" or op == "0b":
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes +  " " + modrm
		eip.addr += 1 #modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		reg = binary_string[2:5]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		if op == "09": # OR r/m32, r32
			return {"machine":mc.bytes, "assembly":"or " + parsedmod + ", " + x86RegisterEncodings[reg]}
		else: # OR r32, r/m32
			return {"machine":mc.bytes, "assembly":"or " + x86RegisterEncodings[reg] + ", " + parsedmod}
	elif op == "81" or op == "83":
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + modrm
		eip.addr += 1 #modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		if op == "81": # OR r/m32, imm32
			dword = f.read(4)
			imm32 = str(hex(unpack('<L', dword)[0]))
			mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
			eip.addr += 4 #imm32
			return {"machine":mc.bytes, "assembly": "or " + parsedmod + ", 0x" + imm32}
		else: # OR r/m32, imm8
			byte = f.read(1)
			imm8 = binascii.hexlify(byte)
			mc.bytes = mc.bytes + " " + binascii.hexlify(byte)
			eip.addr += 1 #imm8
			return {"machine":mc.bytes, "assembly":"or " + parsedmod + ", 0x" + imm8}
	elif op == "0d": # OR EAX, imm32
		dword = f.read(4)
		imm32 = str(hex(unpack('<L', dword)[0]))
		mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
		eip.addr += 4 #imm32
		return {"machine":mc.bytes, "assembly":"or eax, 0x" + imm32}	
	else:
		raise Exception("Error parsing or mnemonic")

# pop mnemonic - pg 842
def pop(f, eip, op):
	mc = MachineCode()
	mc.bytes = op
	if op in encodedOperandLookupTable: # POP r32
		eip.addr += 1 #opcode
		return {"machine":mc.bytes, "assembly":encodedOperandLookupTable[op]}
	elif op == "8f": # POP r/m32
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + modrm
		eip.addr += 1 #modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		return {"machine":mc.bytes, "assembly":"pop " + parsedmod}
	else:
		raise Exception("Error parsing pop mnemonic")

# popcnt mnemonic - pg 849
# See ambiguous
# F3 0F B8 /r POPCNT r32, r/m32

# push mnemonic - pg 927
def push(f, eip, op):
	mc = MachineCode()
	mc.bytes = op
	eip.addr += 1 #opcode
	if op in encodedOperandLookupTable: # PUSH r32
		return {"machine":mc.bytes, "assembly":encodedOperandLookupTable[op]}
	elif op == "68": # PUSH imm32
		dword = f.read(4)
		mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
		imm32 = str(hex(unpack('<L', dword)[0]))
		eip.addr += 4 #imm32
		return {"machine":mc.bytes, "assembly":"push 0x" + imm32}
	elif op == "6a": # PUSH imm8
		byte = f.read(1)
		imm8 = binascii.hexlify(byte)
		mc.bytes = mc.bytes + " " + binascii.hexlify(byte)
		eip.addr += 1 #imm8
		return {"machine":mc.bytes, "assembly":"push 0x" + imm8}
	elif op == "ff": # PUSH r/m32
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + modrm
		eip.addr += 1 #modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		return {"machine":mc.bytes, "assembly":"push 0x" + parsedmod}
	else:
		raise Exception("Error parsing push mnemonic")

# repne cmpsd mnemonic - pg 960
# See ambiguous
# F2 A7 REPNE CMPS m32, m32

# retf/retn mnemonic - pg 963
def ret(f, eip, op):
	mc = MachineCode()
	mc.bytes = op
	eip.addr += 1 #opcode
	if op == "c3": # ret (near)
		handle_ret(f, eip, op)
		return {"machine":op, "assembly":"retn"}
	elif op == "cb": # ret (far)
		handle_ret(f, eip, op)
		return {"machine":op, "assembly":"retf"}
	elif op == "c2": # ret (near) imm16
		word = f.read(2)
		mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(word))
		imm16 = str(hex(unpack('<h', word)[0]))
		eip.addr +=2 #imm16
		handle_ret(f, eip, op)
		return {"machine":mc.bytes, "assembly":"retn " + imm16}
	elif op == "ca": # ret (far) imm16
		word = f.read(2)
		mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(word))
		imm16 = str(hex(unpack('<h', word)[0]))
		eip.addr +=2 #imm16
		handle_ret(f, eip, op)
		return {"machine":mc.bytes, "assembly":"retf " + imm16}
	else:
		raise Exception("Error parsing retn/retf mnemonic")		

# sal mnemonic - pg 992
# sar mnemonic - pg 992
# shl mnemonic - pg 992
# shr mnemonic - pg 992
def shift(f, eip, op):
	mc = MachineCode()
	mc.bytes = op
	eip.addr += 1 #opcode
	if op == "d1": 
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + modrm
		eip.addr += 1 #modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		reg = binary_string[2:5]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		if reg == "101": # d1 /5 - SHR r/m32, 1
			return {"machine":mc.bytes, "assembly":"shr " + parsedmod + ", 1"}
		elif reg == "100": # d1 /4 - SHL r/m32, 1   and   SAL r/m32, 1 (equivalent function)
			return {"machine":mc.bytes, "assembly":"shl " + parsedmod + ", 1"}
		elif reg == "111": # d1 /7 - SAR r/m32, 1
			return {"machine":mc.bytes, "assembly":"sar " + parsedmod + ", 1"}
		else:
			raise Exception("Unsupported shr/shl/sal/sar mnemonic")
	else:
		raise Exception("Error parsing shr/shl/sal/sar mnemonic")

# sbb mnemonic - pg 999
def sbb(f, eip, op):
	mc = MachineCode()
	mc.bytes = op
	eip.addr += 1 # opcode
	if op == "19" or op == "1b":
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes +  " " + modrm
		eip.addr += 1 # modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		reg = binary_string[2:5]
		rm = binary_string[5:]	
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		if op == "19": # SBB r/m32, r32
			return {"machine":mc.bytes, "assembly":"sbb " + parsedmod + ", " + x86RegisterEncodings[reg]}
		else: # SBB r32, r/m32
			return {"machine":mc.bytes, "assembly":"sbb " + x86RegisterEncodings[reg] + ", " + parsedmod}
	elif op == "81" or op == "83":
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + modrm
		eip.addr += 1 # modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		if op == "81": # SBB r/m32, imm32
			dword = f.read(4)
			imm32 = str(hex(unpack('<L', dword)[0]))
			mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
			eip.addr += 4 #imm32
			return {"machine":mc.bytes, "assembly": "sbb " + parsedmod + ", 0x" + imm32}
		else: # SBB r/m32, imm8
			byte = f.read(1)
			imm8 = binascii.hexlify(byte)
			mc.bytes = mc.bytes + " " + binascii.hexlify(byte)
			eip.addr += 1 #imm8
			return {"machine":mc.bytes, "assembly":"sbb " + parsedmod + ", 0x" + imm8}
	elif op == "1d": # SBB EAX, imm32
		dword = f.read(4)
		imm32 = str(hex(unpack('<L', dword)[0]))
		mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
		eip.addr += 4 #imm32
		return {"machine":mc.bytes, "assembly":"sbb eax, 0x" + imm32}	
	else:
		raise Exception("Error parsing sbb mnemonic")

# test mnemonic - pg 1068
def test(f, eip, op):
	mc = MachineCode()
	mc.bytes = op
	eip.addr += 1 #opcode
	if op == "a9": # TEST EAX, imm32
		dword = f.read(4)
		imm32 = str(hex(unpack('<L', dword)[0]))
		mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
		eip.addr += 4 #imm32
		return {"machine":mc.bytes, "assembly":"test eax, 0x" + imm32}
	elif op == "f7": # TEST r/m32, imm32
		modrm = binascii.hexlify(f.read(1))
		eip.addr += 1 #modrm
		mc.bytes = mc.bytes + " " + modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		dword = f.read(4)
		eip.addr += 4 #imm32
		imm32 = str(hex(unpack('<L', dword)[0]))
		mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
		return {"machine":mc.bytes, "assembly":"test " + parsedmod  + ", 0x" + imm32}
	elif op == "85": # TEST r/m32, r32
		modrm = binascii.hexlify(f.read(1))
		eip.addr += 1 #modrm
		mc.bytes = mc.bytes + " " + modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		reg = binary_string[2:5]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		return {"machine":mc.bytes, "assembly":"test " + parsedmod + ", " +  x86RegisterEncodings[reg]}
	else:	
		raise Exception("Error parsing test mnemonic")	

# xor mnemonic - pg 1232
def xor(f, eip, op):
	mc = MachineCode()
	mc.bytes = op
	eip.addr += 1 #opcode
	if op == "35": # XOR EAX, imm32
		dword = f.read(4)
		mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
		imm32 = str(hex(unpack('<L', dword)[0]))
		eip.addr += 4 #imm32
		return {"machine":mc.bytes, "assembly":"xor eax, 0x" + imm32}
	elif op == "31" or op == "33":
		modrm = binascii.hexlify(f.read(1))
		mc.bytes = mc.bytes + " " + modrm
		eip.addr += 1 #modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		reg = binary_string[2:5]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		if op == "31": # XOR r/m32, r32
			return {"machine":mc.bytes, "assembly":"xor " + parsedmod + ", " + x86RegisterEncodings[reg]}
		else: # XOR r32, r/m32
			return {"machine":mc.bytes, "assembly":"xor " + x86RegisterEncodings[reg] + ", " + parsedmod}
	elif op == "81" or op == "83":
		modrm = binascii.hexlify(f.read(1))
		eip.addr += 1 #modrm
		binary_string = dec2bin(int(modrm, 16))
		mod = binary_string[0:2]
		rm = binary_string[5:]
		parsedmod = parseModRM(mod, rm, eip, f, mc)
		if op == "81": # XOR r/m32, imm32
			dword = f.read(4)
			mc.bytes = mc.bytes + " " + make_dword_printable(binascii.hexlify(dword))
			imm32 = str(hex(unpack('<L', dword)[0]))
			eip.addr += 4 #imm32
			return {"machine":mc.bytes, "assembly":"xor 0x" + parsedmod + ", " + imm32}
		elif op == "83": # XOR r/m32, imm8
			byte = f.read(1)
			imm8 = binascii.hexlify(byte)
			mc.bytes = mc.bytes + " " + binascii.hexlify(byte)
			eip.addr += 1 #imm8
			return {"machine":mc.bytes, "assembly":"xor 0x" + parsedmod + ", " + imm8}
	else:
		raise Exception("Error parsing xor mnemonic")

# Determine which opcode function to call based on the first byte
opcodeLookupTable = {
	'01': add,
	'03': add,
	'05': add,
	'09': x86or,
	'0b': x86or,
	'0d': x86or,
#	'0f c8': bswap,
#	'0f a7': imul,
#	'0f 84': jz,
#	'0f 85': jnz,
#	'0f b7': movzx,
	'0f': ambiguous,
	'19': sbb,
	'1b': sbb,
	'1d': sbb,
	'1f': nop,
	'21': x86and,
	'23': x86and,
	'25': x86and,
	'31': xor,
	'33': xor,
	'35': xor,
	'39': x86cmp,
	'3b': x86cmp,
	'3d': x86cmp,
	'40': incdec,
	'41': incdec,
	'42': incdec,
	'43': incdec,
	'44': incdec,
	'45': incdec,
	'46': incdec,
	'47': incdec,
	'48': incdec,
	'49': incdec,
	'4a': incdec,
	'4b': incdec,
	'4c': incdec,
	'4d': incdec,
	'4e': incdec,
	'4f': incdec,
	'50': push,
	'51': push,
	'52': push,
	'53': push,
	'54': push,
	'55': push,
	'56': push,
	'57': push,
	'58': pop,
	'59': pop,
	'5a': pop,
	'5b': pop,
	'5c': pop,
	'5d': pop,
	'5e': pop,
	'5f': pop,
	'68': push,
	'6a': push,
	'6b': imul,
	'69': imul,
	'74': jz,
	'75': jnz,
#	'81': add,
#	'81': x86and,
#	'81': x86cmp,
#	'81': x86or,
#	'81': sbb,
#	'81': xor,
	'81': ambiguous,
#	'83': add,
#	'83': x86and,
#	'83': x86cmp,
#	'83': x86or,
#	'83': sbb,
#	'83': xor,
	'83': ambiguous,
	'85': test,
	'89': mov,
	'8b': mov,
	'8d': lea,
	'8f': pop,
	'90': nop,
 	'a4': movs,
	'a5': movs,
	'af': imul,
	'a9': test,
	'b8': mov,
	'b9': mov,
	'ba': mov,
	'bb': mov,
	'bc': mov,
	'bd': mov,
	'be': mov,
	'bf': mov,
	'c2': ret,
	'c3': ret,
	'c7': mov,
	'ca': ret,
	'cb': ret,
	'd1': shift,
	'e8': call,
	'e9': jmp,
	'eb': jmp,
	'f2': ambiguous, # repne cmpsd
	'f3': ambiguous, # popcnt
#	'f7': idiv,
#	'f7': imul,
#	'f7': mul,
#	'f7': neg,
#	'f7': x86not,
#	'f7': test,
	'f7': ambiguous,
#	'ff': call,
#	'ff': incdec,
#	'ff': jmp
#	'ff': push,
	'fe': ambiguous,
	'ff': ambiguous,
}
		
def main():

	# clear screen
	os.system('cls' if os.name == 'nt' else 'clear')

	# print snazzy title, just because
	print """

			 _|. _ _  _ _ _  _ _ |_ | _  _
			(_||_\(_|_\_\(/_| | ||_)|(/_| 
		       Tim Nary <tnary1@jhu.edu>   v1.0

	"""

	# print out algorithm we are using
	if mode == "recursive": 
		print "Algorithm: Recursive Descent\n" 
	else: 
		print "Algorithm: Linear Sweep\n"

	# read the file as a string of hex characters
	try:
		f = open(filename, "rb")
		print "File: " + ntpath.basename(filename) + "\n"

		# main loop
		try:
			start = 0
			f.seek(-1, 2)
			end = f.tell()
			f.seek(0, 0)
			eip = EIP()
			output_buffer = ""
			error_buffer = ""
			global byte
			try:
				byte = f.read(1)
				while byte != "":
					# check byte
					byte_string = binascii.hexlify(byte)
					if byte_string in opcodeLookupTable:
						loc = str(hex(eip.addr))
						instr = opcodeLookupTable[byte_string](f, eip, byte_string)
						# store our machine code and assembly instructions sequences in matching tables.
						disassembly[loc] = instr["assembly"]
						machine[loc] = instr["machine"]
						# we know what 0x00 is so it's not unknown.  Skip it.
					elif byte_string == "00":
						eip.addr += 1
					else:
						print "Encountered unknown opcode: " + byte_string + " at location: " + str(hex(eip.addr)) + ".  Continuing to next location."
						eip.addr += 1
					if byte != "":
						byte = f.read(1)
			except:
				# add errors to error_buffer to display at end
				error_buffer += "Error: " + str(sys.exc_info()[1]) + "\n\n"
				error_buffer += traceback.format_exc() + "\n\n"
			for instr in range(start,end): 
				try:
					output_buffer += '{0:>4s}:\t{1:30s} {2:4s}\n'.format(str(hex(instr)) , machine[str(hex(instr))], disassembly[str(hex(instr))])
				except:
					continue	
		finally:
			# print output_buffer without labels
			# print output_buffer

			# print output_buffer and add offset labels
			line_output = output_buffer.split('\n')
			for line in line_output:
				offset = line[:4]
				if offset in offset_labels:
					print "\noffset_" + '{:x}'.format(int(offset, 16)) + "h:"
				print line

			f.close()

			# print error_buffer
			print "\n"
			print "Unfortunately, there were some errors during disassembly:\n"
			print error_buffer
	except:
		print "Error: Invalid file."

if __name__ == "__main__":
	main()