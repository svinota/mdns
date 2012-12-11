""" Multicast DNS Service Discovery for Python

    This module provides a framework for the use of DNS Service Discovery
    using IP multicast.  It has been tested against the JRendezvous
    implementation from <a href="http://strangeberry.com">StrangeBerry</a>,
    and against the mDNSResponder from Mac OS X 10.3.8.

    Also, it provides:
        * DNSSEC extension for mDNS service.
        * Heartbeat extension
"""

#    mDNS library
#    Copyright (c) 2003, Paul Scott-Murphy
#    Copyright (c) 2008-2012, Peter V. Saveliev
#
#    This program is free software: you can redistribute it and/or modify
#    it under the terms of the GNU General Public License as published by
#    the Free Software Foundation, either version 3 of the License, or
#    (at your option) any later version.
#
#    This program is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#    GNU General Public License for more details.
#
#    You should have received a copy of the GNU General Public License
#    along with this program.  If not, see <http://www.gnu.org/licenses/>.


import string
import time
import struct
import socket
import select
import threading
import traceback

from pickle import dumps, loads
from base64 import b64encode, b64decode
from threading import Thread
from Crypto.Hash import MD5
from Crypto.Util.number import getPrime
from Crypto import Random

# py3k

try:
    from functools import reduce
except:
    pass

__all__ = ["Zeroconf", "ServiceInfo", "ServiceBrowser"]

# hook for threads

globals()['_GLOBAL_DONE'] = 0

# Some timing constants

_UNREGISTER_TIME = 125
_CHECK_TIME = 175
_REGISTER_TIME = 225
_LISTENER_TIME = 200
_BROWSER_TIME = 500

# Some DNS constants

_MDNS_ADDR = '224.0.0.251'
_MDNS_PORT = 5353
_DNS_PORT = 53
_DNS_TTL = 60 * 60    # one hour default TTL
_DNS_HEARTBEAT_DIV = 3    # beats per TTL

_MAX_MSG_TYPICAL = 1460  # unused
_MAX_MSG_ABSOLUTE = 8972

_FLAGS_QR_MASK = 0x8000  # query response mask
_FLAGS_QR_QUERY = 0x0000  # query
_FLAGS_QR_RESPONSE = 0x8000  # response

_FLAGS_AA = 0x0400  # Authorative answer
_FLAGS_TC = 0x0200  # Truncated
_FLAGS_RD = 0x0100  # Recursion desired
_FLAGS_RA = 0x8000  # Recursion available

_FLAGS_Z = 0x0040  # Zero
_FLAGS_AD = 0x0020  # Authentic data
_FLAGS_CD = 0x0010  # Checking disabled

_CLASS_IN = 1
_CLASS_CS = 2
_CLASS_CH = 3
_CLASS_HS = 4
_CLASS_NONE = 254
_CLASS_ANY = 255
_CLASS_MASK = 0x7FFF
_CLASS_UNIQUE = 0x8000

###
#
# RFC:
#    DNS
#
#    1034    DOMAIN NAMES - CONCEPTS AND FACILITIES
#    1035    DOMAIN NAMES - IMPLEMENTATION AND SPECIFICATION
#
#    DNSSEC
#
#    http://www.dnssec.net/rfc
#    4033    DNS Security Introduction and Requirements
#    4034    Resource Records for the DNS Security Extensions
#    4035    Protocol Modifications for the DNS Security Extensions
#
#    mDNS
#
#    http://files.multicastdns.org/draft-cheshire-dnsext-multicastdns.txt
#    Multicast DNS
#
# see also:
#    1982    Serial Number Arithmetic
#    2535    Domain Name System Security Extensions
#    2536    DSA KEYs and SIGs in the Domain Name System (DNS)
#    3110    RSA/SHA-1 SIGs and RSA KEYs in the Domain Name System (DNS)
#    2931    DNS Request and Transaction Signatures ( SIG(0)s )
#    4716    The Secure Shell (SSH) Public Key File Format
#
#
# see also:
#    DNS Zone Transfer Protocol Clarifications
#       http://tools.ietf.org/html/draft-ietf-dnsext-axfr-clarify-02
###

_TYPE_A = 1
_TYPE_NS = 2
_TYPE_MD = 3
_TYPE_MF = 4
_TYPE_CNAME = 5
_TYPE_SOA = 6
_TYPE_MB = 7
_TYPE_MG = 8
_TYPE_MR = 9
_TYPE_NULL = 10
_TYPE_WKS = 11
_TYPE_PTR = 12
_TYPE_HINFO = 13
_TYPE_MINFO = 14
_TYPE_MX = 15
_TYPE_TXT = 16
_TYPE_AAAA = 28
_TYPE_SRV = 33
_TYPE_RRSIG = 46
_TYPE_DNSKEY = 48
_TYPE_AXFR = 252    # query only, see rfc 1035, section 3.2.3
_TYPE_ANY = 255

# Mapping constants to names

_CLASSES = {_CLASS_IN: "in",
        _CLASS_CS: "cs",
        _CLASS_CH: "ch",
        _CLASS_HS: "hs",
        _CLASS_NONE: "none",
        _CLASS_ANY: "any"}

_TYPES = {_TYPE_A: "a",
        _TYPE_NS: "ns",
        _TYPE_MD: "md",
        _TYPE_MF: "mf",
        _TYPE_CNAME: "cname",
        _TYPE_SOA: "soa",
        _TYPE_MB: "mb",
        _TYPE_MG: "mg",
        _TYPE_MR: "mr",
        _TYPE_NULL: "null",
        _TYPE_WKS: "wks",
        _TYPE_PTR: "ptr",
        _TYPE_HINFO: "hinfo",
        _TYPE_MINFO: "minfo",
        _TYPE_MX: "mx",
        _TYPE_TXT: "txt",
        _TYPE_AAAA: "aaaa",
        _TYPE_SRV: "srv",
        _TYPE_RRSIG: "rrsig",
        _TYPE_DNSKEY: "dnskey",
        _TYPE_AXFR: "axfr",
        _TYPE_ANY: "any"}

# utility functions


def current_time_millis():
    """Current system time in milliseconds"""
    return time.time() * 1000


def dict_to_text(d):
    list = []
    result = ''
    for key in d.keys():
        value = d[key]
        if value is None:
            suffix = ''.encode('utf-8')
        elif isinstance(value, str):
            suffix = value.encode('utf-8')
        elif isinstance(value, int):
            if value:
                suffix = 'true'
            else:
                suffix = 'false'
        else:
            suffix = ''.encode('utf-8')
        list.append('='.join((key, suffix)))
    for item in list:
        result = ''.join((result, struct.pack('!c', chr(len(item))), item))
    return result


def text_to_dict(text):
    result = {}
    end = len(text)
    index = 0
    strs = []
    while index < end:
        length = ord(text[index])
        index += 1
        strs.append(text[index:index + length])
        index += length

    for s in strs:
        eindex = s.find('=')
        if eindex == -1:
            # No equals sign at all
            key = s
            value = 0
        else:
            key = s[:eindex]
            value = s[eindex + 1:]
            if value == 'true':
                value = 1
            elif value == 'false' or not value:
                value = 0

        # Only update non-existent properties
        if key and result.get(key) == None:
            result[key] = value
    return result


def prime(size=140):
    return getPrime(size, Random.get_random_bytes)


# Exceptions

class NonLocalNameException(Exception):
    pass


class NonUniqueNameException(Exception):
    pass


class NamePartTooLongException(Exception):
    pass


class AbstractMethodException(Exception):
    pass


class BadTypeInNameException(Exception):
    pass

# implementation classes


class DNSEntry(object):
    """A DNS entry"""

    def __init__(self, name, type, clazz):
        self.key = string.lower(name)
        self.name = name
        self.type = type
        self.clazz = clazz & _CLASS_MASK
        self.unique = (clazz & _CLASS_UNIQUE) != 0
        self.rrsig = None

    def __eq__(self, other):
        """Equality test on name, type, and class"""
        if isinstance(other, DNSEntry):
            return self.name == other.name and \
                    self.type == other.type and \
                    self.clazz == other.clazz
        return 0

    def __ne__(self, other):
        """Non-equality test"""
        return not self.__eq__(other)

    def get_clazz(self, clazz):
        """Class accessor"""
        try:
            return _CLASSES[clazz]
        except:
            return "?(%s)" % (clazz)

    def get_type(self, type):
        """Type accessor"""
        try:
            return _TYPES[type]
        except:
            return "?(%s)" % (type)

    def to_string(self, hdr, other):
        """String representation with additional information"""
        result = "%s[%s,%s" % (
                hdr, self.get_type(self.type), self.get_clazz(self.clazz))
        if self.unique:
            result += "-unique,"
        else:
            result += ","
        result += self.name
        if other is not None:
            result += ",%s]" % (other)
        else:
            result += "]"
        return result

    def sp(self):
        return "%s %s %s" % (self.key, self.type, self.clazz)


class DNSQuestion(DNSEntry):
    """A DNS question entry"""

    def __init__(self, name, type, clazz):
        # FIXME: why?
        # if not name.endswith(".local."):
        #    raise NonLocalNameException
        DNSEntry.__init__(self, name, type, clazz)

    def answered_by(self, rec):
        """Returns true if the question is answered by the record"""
        return self.clazz == rec.clazz and \
                (self.type == rec.type or self.type == _TYPE_ANY) and \
                self.name == rec.name

    def __repr__(self):
        """String representation"""
        return DNSEntry.to_string(self, "question", None)


class DNSRecord(DNSEntry):
    """A DNS record - like a DNS entry, but has a TTL"""

    def __init__(self, name, type, clazz, ttl):
        DNSEntry.__init__(self, name, type, clazz)
        self.ttl = ttl
        self.created = current_time_millis()

    def __eq__(self, other):
        """Tests equality as per DNSRecord"""
        return DNSEntry.__eq__(self, other)

    def suppressed_by(self, msg):
        """Returns true if any answer in a message can suffice for the
        information held in this record."""
        for record in msg.answers:
            if self.suppressed_by_answer(record):
                return 1
        return 0

    def suppressed_by_answer(self, other):
        """Returns true if another record has same name, type and class,
        and if its TTL is at least half of this record's."""
        if self == other and other.ttl > (self.ttl // 2):
            return 1
        return 0

    def get_expiration_time(self, percent):
        """Returns the time at which this record will have expired
        by a certain percentage."""
        return self.created + (percent * self.ttl * 10)

    def get_remaining_ttl(self, now):
        """Returns the remaining TTL in seconds."""
        return max(0, (self.get_expiration_time(100) - now) // 1000)

    def is_expired(self, now):
        """Returns true if this record has expired."""
        return self.get_expiration_time(100) <= now

    def is_stale(self, now):
        """Returns true if this record is at least half way expired."""
        return self.get_expiration_time(50) <= now

    def reset_ttl(self, other):
        """Sets this record's TTL and created time to that of
        another record."""
        self.created = other.created
        self.ttl = other.ttl

    def write(self, out):
        """Abstract method"""
        raise AbstractMethodException

    def to_string(self, other):
        """String representation with addtional information"""
        arg = "%s/%s,%s" % (
                self.ttl, self.get_remaining_ttl(current_time_millis()), other)
        return DNSEntry.to_string(self, "record", arg)


class DNSSignature(DNSRecord):
    """An abstract DNS signature record class"""

    def __init__(self, name, type, clazz, ttl):
        DNSRecord.__init__(self, name, type, clazz, ttl)
        self.type_covered = _TYPE_ANY
        # we use private algorithm type 253
        # according to RFC 2535, Section 11
        self.algorithm = 253
        self.labels = 0
        self.original_ttl = 0
        self.expiration = 0
        self.inception = 0
        self.tag = 0
        self.signer = "none"
        self.signature = "none"

    def write(self, out):
        # write header
        out.write_short(self.type_covered)
        out.write_uchar(self.algorithm)
        out.write_uchar(self.labels)
        out.write_int(self.original_ttl)
        out.write_int(self.expiration)
        out.write_int(self.inception)
        out.write_short(self.tag)
        out.write_name(self.signer)
        out.write_uchar(len(self.signature))
        out.write_string(self.signature, len(self.signature))

    def __eq__(self, other):
        if isinstance(other, DNSSignature):
            return self.type_covered == other.type_covered and \
                    self.signer == other.signer and \
                    self.signature == other.signature
        return 0

    def __repr__(self):
        return "RRSIG: [%s] %s" % (_TYPES[self.type_covered], self.signer)


class DNSSignatureI(DNSSignature):
    """Create a DNSRecord from a signature"""

    def __init__(self, name, type, clazz, ttl, header, signer, signature):
        DNSSignature.__init__(self, name, type, clazz, ttl)
        (self.type_covered,
                self.algorithm,
                self.labels,
                self.original_ttl,
                self.expiration,
                self.inception,
                self.tag) = struct.unpack("!HBBIIIH", header)
        self.signer = signer
        self.signature = signature


class DNSSignatureS(DNSSignature):
    """Create signature from a DNSRecord"""

    def __init__(self, name, type, clazz, record, key, signer=None):
        DNSSignature.__init__(self, name, type, clazz, record.ttl)
        self.type_covered = record.type
        self.original_ttl = record.ttl
        if signer:
            self.signer = signer
        else:
            self.signer = record.name
        h = MD5.new(record.sp()).digest()
        self.signature = b64encode(dumps(key.sign(h, prime())))


class DNSAddress(DNSRecord):
    """A DNS address record"""

    def __init__(self, name, type, clazz, ttl, address):
        DNSRecord.__init__(self, name, type, clazz, ttl)
        self.address = address
        self.state = "reachable"
        if len(self.address) == 4:
            self.family = 4
        elif len(self.address) == 16:
            self.family = 6
        else:
            raise Exception("Unknown IP address family")

    def write(self, out):
        """Used in constructing an outgoing packet"""
        out.write_string(self.address, len(self.address))

    def __eq__(self, other):
        """Tests equality on address"""
        if isinstance(other, DNSAddress):
            return self.address == other.address and self.name == other.name
        return DNSRecord.__eq__(self, other)

    def _address(self):
        if self.family == 4:
            a = socket.inet_ntoa(self.address)
        elif self.family == 6:
            a = "%x:%x:%x:%x:%x:%x:%x:%x:%x:%x:%x:%x:%x:%x:%x:%x" % \
                    struct.unpack('BBBBBBBBBBBBBBBB', self.address)
        else:
            raise Exception("Unknown IP address family")
        return a

    def __repr__(self):
        """String representation"""
        return "%s (%s)" % (self._address(), self.state)

    def sp(self):
        return "%s %s %s %s" % (
                self.key,
                self.get_clazz(self.clazz),
                self.get_type(self.type),
                self._address())


class DNSHinfo(DNSRecord):
    """A DNS host information record"""

    def __init__(self, name, type, clazz, ttl, cpu, os):
        DNSRecord.__init__(self, name, type, clazz, ttl)
        self.cpu = cpu
        self.os = os

    def write(self, out):
        """Used in constructing an outgoing packet"""
        out.write_string(self.cpu, len(self.cpu))
        out.write_string(self.os, len(self.os))

    def __eq__(self, other):
        """Tests equality on cpu and os"""
        if isinstance(other, DNSHinfo):
            return self.cpu == other.cpu and self.os == other.os
        return DNSRecord.__eq__(self, other)

    def __repr__(self):
        """String representation"""
        return self.cpu + " " + self.os


class DNSPointer(DNSRecord):
    """A DNS pointer record"""

    def __init__(self, name, type, clazz, ttl, alias):
        DNSRecord.__init__(self, name, type, clazz, ttl)
        self.alias = alias

    def write(self, out):
        """Used in constructing an outgoing packet"""
        out.write_name(self.alias)

    def __eq__(self, other):
        """Tests equality on alias"""
        if isinstance(other, DNSPointer):
            return self.alias == other.alias
        return DNSRecord.__eq__(self, other)

    def __repr__(self):
        """String representation"""
        return self.to_string(self.alias)


class DNSText(DNSRecord):
    """A DNS text record"""

    def __init__(self, name, type, clazz, ttl, text):
        DNSRecord.__init__(self, name, type, clazz, ttl)
        self.text = text
        try:
            self.properties = text_to_dict(text)
        except:
            self.properties = {}

    def write(self, out):
        """Used in constructing an outgoing packet"""
        out.write_string(self.text, len(self.text))

    def set_property(self, key, value):
        """
        Update only one property in the dict
        """
        self.properties[key] = value
        self.sync_properties()

    def sync_properties(self):
        """
        Set text from dict
        """
        self.text = dict_to_text(self.properties)

    def set_properties(self, properties):
        if isinstance(properties, dict):
            self.properties = properties
            self.sync_properties()

    def __eq__(self, other):
        """Tests equality on text"""
        if isinstance(other, DNSText):
            return self.text == other.text
        return DNSRecord.__eq__(self, other)

    def __repr__(self):
        """String representation"""
        if len(self.text) > 30:
            return self.to_string(repr(self.text[:27] + "..."))
        else:
            return self.to_string(repr(self.text))


class DNSService(DNSRecord):
    """A DNS service record"""

    def __init__(self, name, type, clazz, ttl, priority, weight, port, server):
        DNSRecord.__init__(self, name, type, clazz, ttl)
        self.priority = priority
        self.weight = weight
        self.port = port
        self.server = server

    def write(self, out):
        """Used in constructing an outgoing packet"""
        out.write_short(self.priority)
        out.write_short(self.weight)
        out.write_short(self.port)
        out.write_name(self.server)

    def __eq__(self, other):
        """Tests equality on priority, weight, port and server"""
        if isinstance(other, DNSService):
            return self.priority == other.priority and \
                    self.weight == other.weight and \
                    self.port == other.port and \
                    self.server == other.server
        return DNSRecord.__eq__(self, other)

    def __repr__(self):
        """String representation"""
        return self.to_string("%s:%s" % (self.server, self.port))


class DNSIncoming(object):
    """Object representation of an incoming DNS packet"""

    def __init__(self, data):
        """Constructor from string holding bytes of packet"""
        self.offset = 0
        self.data = data
        self.questions = []
        self.answers = []
        self.num_questions = 0
        self.num_answers = 0
        self.num_authorities = 0
        self.num_additionals = 0

        self.read_header()
        self.read_questions()
        self.read_others()

    def read_header(self):
        """Reads header portion of packet"""
        format = '!HHHHHH'
        length = struct.calcsize(format)
        info = struct.unpack(format,
                self.data[self.offset:self.offset + length])
        self.offset += length

        self.id = info[0]
        self.flags = info[1]
        self.num_questions = info[2]
        self.num_answers = info[3]
        self.num_authorities = info[4]
        self.num_additionals = info[5]

    def read_questions(self):
        """Reads questions section of packet"""
        format = '!HH'
        length = struct.calcsize(format)
        for i in range(0, self.num_questions):
            name = self.read_name()
            info = struct.unpack(format,
                    self.data[self.offset:self.offset + length])
            self.offset += length

            question = DNSQuestion(name, info[0], info[1])
            self.questions.append(question)

    def read_int(self):
        """Reads an integer from the packet"""
        format = '!I'
        length = struct.calcsize(format)
        info = struct.unpack(format,
                self.data[self.offset:self.offset + length])
        self.offset += length
        return info[0]

    def read_character_string(self):
        """Reads a character string from the packet"""
        length = ord(self.data[self.offset])
        self.offset += 1
        return self.read_string(length)

    def read_string(self, len):
        """Reads a string of a given length from the packet"""
        format = '!' + str(len) + 's'
        length = struct.calcsize(format)
        info = struct.unpack(format,
                self.data[self.offset:self.offset + length])
        self.offset += length
        return info[0]

    def read_unsigned_short(self):
        """Reads an unsigned short from the packet"""
        format = '!H'
        length = struct.calcsize(format)
        info = struct.unpack(format,
                self.data[self.offset:self.offset + length])
        self.offset += length
        return info[0]

    def read_others(self):
        """Reads the answers, authorities and additionals section
        of the packet"""
        format = '!HHiH'
        length = struct.calcsize(format)
        n = self.num_answers + self.num_authorities + self.num_additionals
        for i in range(0, n):
            domain = self.read_name()
            info = struct.unpack(format,
                    self.data[self.offset:self.offset + length])
            self.offset += length

            rec = None
            if info[0] == _TYPE_A:
                rec = DNSAddress(domain,
                        info[0], info[1], info[2],
                        self.read_string(4))
            elif info[0] == _TYPE_CNAME or info[0] == _TYPE_PTR:
                rec = DNSPointer(domain,
                        info[0], info[1], info[2],
                        self.read_name())
            elif info[0] == _TYPE_TXT:
                rec = DNSText(domain,
                        info[0], info[1], info[2],
                        self.read_string(info[3]))
            elif info[0] == _TYPE_SRV:
                rec = DNSService(domain,
                        info[0], info[1], info[2],
                        self.read_unsigned_short(),
                        self.read_unsigned_short(),
                        self.read_unsigned_short(),
                        self.read_name())
            elif info[0] == _TYPE_HINFO:
                rec = DNSHinfo(domain,
                        info[0], info[1], info[2],
                        self.read_character_string(),
                        self.read_character_string())
            elif info[0] == _TYPE_RRSIG:
                rec = DNSSignatureI(domain,
                        info[0], info[1], info[2],
                        self.read_string(18),
                        self.read_name(),
                        self.read_character_string())
            elif info[0] == _TYPE_AAAA:
                rec = DNSAddress(domain,
                        info[0], info[1], info[2],
                        self.read_string(16))
            else:
                # Try to ignore types we don't know about
                # this may mean the rest of the name is
                # unable to be parsed, and may show errors
                # so this is left for debugging.  New types
                # encountered need to be parsed properly.
                #
                #print "UNKNOWN TYPE = " + str(info[0])
                #raise BadTypeInNameException
                pass

            if rec is not None:
                self.answers.append(rec)

    def is_query(self):
        """Returns true if this is a query"""
        return (self.flags & _FLAGS_QR_MASK) == _FLAGS_QR_QUERY

    def is_response(self):
        """Returns true if this is a response"""
        return (self.flags & _FLAGS_QR_MASK) == _FLAGS_QR_RESPONSE

    def read_utf(self, offset, len):
        """Reads a UTF-8 string of a given length from the packet"""
        result = self.data[offset:offset + len].decode('utf-8')
        return result

    def read_name(self):
        """Reads a domain name from the packet"""
        result = ''
        off = self.offset
        next = -1
        first = off

        while 1:
            len = ord(self.data[off])
            off += 1
            if len == 0:
                break
            t = len & 0xC0
            if t == 0x00:
                result = ''.join((result, self.read_utf(off, len) + '.'))
                off += len
            elif t == 0xC0:
                if next < 0:
                    next = off + 1
                off = ((len & 0x3F) << 8) | ord(self.data[off])
                if off >= first:
                    raise Exception(
                            "Bad domain name (circular) at " + str(off))
                first = off
            else:
                raise Exception("Bad domain name at " + str(off))

        if next >= 0:
            self.offset = next
        else:
            self.offset = off

        return result


class DNSOutgoing(object):
    """Object representation of an outgoing packet"""

    def __init__(self, flags, multicast=1):
        self.finished = 0
        self.id = 0
        self.multicast = multicast
        self.flags = flags
        self.names = {}
        self.data = []
        self.size = 12

        self.questions = []
        self.answers = []
        self.authorities = []
        self.additionals = []

    def add_question(self, record):
        """Adds a question"""
        self.questions.append(record)

    def add_answer(self, inp, record):
        """Adds an answer"""
        if not record.suppressed_by(inp):
            self.add_answer_at_time(record, 0)

    def add_answer_at_time(self, record, now):
        """Adds an answer if if does not expire by a certain time"""
        if record is not None:
            if now == 0 or not record.is_expired(now):
                self.answers.append((record, now))
                if record.rrsig is not None:
                    self.answers.append((record.rrsig, now))

    def add_authorative_answer(self, record):
        """Adds an authoritative answer"""
        self.authorities.append(record)

    def add_additional_answer(self, record):
        """Adds an additional answer"""
        self.additionals.append(record)

    def write_byte(self, value):
        """Writes a single byte to the packet"""
        format = '!c'
        self.data.append(struct.pack(format, chr(value)))
        self.size += 1

    def write_uchar(self, value):
        """Writes an unsigned char to the packet"""
        format = '!B'
        self.data.append(struct.pack(format, value))
        self.size += 1

    def insert_short(self, index, value):
        """Inserts an unsigned short in a certain position in the packet"""
        format = '!H'
        self.data.insert(index, struct.pack(format, value))
        self.size += 2

    def write_short(self, value):
        """Writes an unsigned short to the packet"""
        format = '!H'
        self.data.append(struct.pack(format, value))
        self.size += 2

    def write_int(self, value):
        """Writes an unsigned integer to the packet"""
        format = '!I'
        self.data.append(struct.pack(format, int(value)))
        self.size += 4

    def write_string(self, value, length):
        """Writes a string to the packet"""
        format = '!' + str(length) + 's'
        self.data.append(struct.pack(format, value))
        self.size += length

    def write_utf(self, s):
        """Writes a UTF-8 string of a given length to the packet"""
        utfstr = s.encode('utf-8')
        length = len(utfstr)
        if length > 64:
            raise NamePartTooLongException
        self.write_byte(length)
        self.write_string(utfstr, length)

    def write_name(self, name):
        """Writes a domain name to the packet"""

        try:
            # Find existing instance of this name in packet
            #
            index = self.names[name]
        except KeyError:
            # No record of this name already, so write it
            # out as normal, recording the location of the name
            # for future pointers to it.
            #
            self.names[name] = self.size
            parts = name.split('.')
            if parts[-1] == '':
                parts = parts[:-1]
            for part in parts:
                self.write_utf(part)
            self.write_byte(0)
            return

        # An index was found, so write a pointer to it
        #
        self.write_byte((index >> 8) | 0xC0)
        self.write_byte(index)

    def write_question(self, question):
        """Writes a question to the packet"""
        self.write_name(question.name)
        self.write_short(question.type)
        self.write_short(question.clazz)

    def write_record(self, record, now):
        """Writes a record (answer, authoritative answer, additional) to
        the packet"""
        self.write_name(record.name)
        self.write_short(record.type)
        if record.unique and self.multicast:
            self.write_short(record.clazz | _CLASS_UNIQUE)
        else:
            self.write_short(record.clazz)
        if now == 0:
            self.write_int(record.ttl)
        else:
            self.write_int(record.get_remaining_ttl(now))
        index = len(self.data)
        # Adjust size for the short we will write before this record
        #
        self.size += 2
        record.write(self)
        self.size -= 2

        length = len(''.join(self.data[index:]))
        self.insert_short(index, length)  # Here is the short we adjusted for

    def packet(self):
        """Returns a string containing the packet's bytes

        No further parts should be added to the packet once this
        is done."""
        if not self.finished:
            self.finished = 1
            for question in self.questions:
                self.write_question(question)
            for answer, time in self.answers:
                self.write_record(answer, time)
            for authority in self.authorities:
                self.write_record(authority, 0)
            for additional in self.additionals:
                self.write_record(additional, 0)

            self.insert_short(0, len(self.additionals))
            self.insert_short(0, len(self.authorities))
            self.insert_short(0, len(self.answers))
            self.insert_short(0, len(self.questions))
            self.insert_short(0, self.flags)
            if self.multicast:
                self.insert_short(0, 0)
            else:
                self.insert_short(0, self.id)
        return ''.join(self.data)


class DNSCache(object):
    """A cache of DNS entries"""

    def __init__(self, private=None):
        self.cache = {}
        self.private = private

    def add(self, entry):
        """Adds an entry"""
        if self.get(entry) is not None:
            return
        try:
            list = self.cache[entry.key]
        except:
            list = self.cache[entry.key] = []
        list.append(entry)

    def sign(self, entry, signer=None):
        """Adds and sign an entry"""
        if (self.get(entry) is not None):
            return
        if (entry.rrsig is None) and (self.private is not None):
            entry.rrsig = DNSSignatureS(entry.name,
                    _TYPE_RRSIG, _CLASS_IN, entry, self.private, signer)
        self.add(entry)
        if (self.private is not None):
            self.add(entry.rrsig)

    def remove(self, entry):
        """Removes an entry"""
        try:
            list = self.cache[entry.key]
            list.remove(entry)
        except:
            pass

    def get(self, entry):
        """Gets an entry by key.  Will return None if there is no
        matching entry."""
        try:
            list = self.cache[entry.key]
            return list[list.index(entry)]
        except:
            return None

    def get_by_details(self, name, type, clazz):
        """Gets an entry by details.  Will return None if there is
        no matching entry."""
        entry = DNSEntry(name, type, clazz)
        return self.get(entry)

    def entries_with_name(self, name):
        """Returns a list of entries whose key matches the name."""
        try:
            return self.cache[name]
        except:
            return []

    def entries(self):
        """Returns a list of all entries"""
        def add(x, y):
            return x + y
        try:
            return reduce(add, list(self.cache.values()))
        except:
            return []


class Engine(Thread):
    """An engine wraps read access to sockets, allowing objects that
    need to receive data from sockets to be called back when the
    sockets are ready.

    A reader needs a handle_read() method, which is called when the socket
    it is interested in is ready for reading.

    Writers are not implemented here, because we only send short
    packets.
    """

    def __init__(self, zeroconf):
        Thread.__init__(self)
        self.zeroconf = zeroconf
        self.readers = {}  # maps socket to reader
        self.timeout = 5
        self.condition = threading.Condition()
        self.name = "zeroconf.Engine"
        self.daemon = True
        self.start()

    def run(self):
        while not globals()['_GLOBAL_DONE']:
            rs = self.get_readers()
            if len(rs) == 0:
                # No sockets to manage, but we wait for the timeout
                # or addition of a socket
                #
                self.condition.acquire()
                self.condition.wait(self.timeout)
                self.condition.release()
            else:
                try:
                    rr, wr, er = select.select(rs, [], [], self.timeout)
                    for socket in rr:
                        try:
                            self.readers[socket].handle_read()
                        except:
                            traceback.print_exc()
                except:
                    pass

    def get_readers(self):
        result = []
        self.condition.acquire()
        result = list(self.readers.keys())
        self.condition.release()
        return result

    def add_reader(self, reader, socket):
        self.condition.acquire()
        self.readers[socket] = reader
        self.condition.notify()
        self.condition.release()

    def del_reader(self, socket):
        self.condition.acquire()
        del(self.readers[socket])
        self.condition.notify()
        self.condition.release()

    def notify(self):
        self.condition.acquire()
        self.condition.notify()
        self.condition.release()


class Listener(object):
    """A Listener is used by this module to listen on the multicast
    group to which DNS messages are sent, allowing the implementation
    to cache information as it arrives.

    It requires registration with an Engine object in order to have
    the read() method called when a socket is availble for reading."""

    def __init__(self, zeroconf, socket):
        self.zeroconf = zeroconf
        self.socket = socket
        self.zeroconf.engine.add_reader(self, self.socket)

    def handle_read(self):
        data, (addr, port) = self.socket.recvfrom(_MAX_MSG_ABSOLUTE)
        self.data = data
        msg = DNSIncoming(data)
        if msg.is_query():
            # Always multicast responses
            #
            if port == _MDNS_PORT:
                self.zeroconf.handle_query(msg, _MDNS_ADDR, _MDNS_PORT, addr)
            # If it's not a multicast query, reply via unicast
            # and multicast
            #
            elif port == _DNS_PORT:
                self.zeroconf.handle_query(msg, addr, port, addr)
                self.zeroconf.handle_query(msg, _MDNS_ADDR, _MDNS_PORT, addr)
        else:
            self.zeroconf.handle_response(msg, addr)


class Reaper(Thread):
    """A Reaper is used by this module to remove cache entries that
    have expired."""

    def __init__(self, zeroconf):
        Thread.__init__(self)
        self.zeroconf = zeroconf
        self.name = "zeroconf.Reaper"
        self.daemon = True
        self.start()

    def run(self):
        while 1:
            self.zeroconf.wait(10 * 1000)
            if globals()['_GLOBAL_DONE']:
                return
            now = current_time_millis()
            for record in self.zeroconf.cache.entries():
                if record.is_expired(now):
                    for i in self.zeroconf.hooks:
                        try:
                            i.expire(record)
                        except:
                            pass
                    self.zeroconf.update_record(now, record)
                    self.zeroconf.cache.remove(record)


class ServiceBrowser(Thread):
    """Used to browse for a service of a specific type.

    The listener object will have its add_service() and
    remove_service() methods called when this browser
    discovers changes in the services availability."""

    def __init__(self, zeroconf, type, listener):
        """Creates a browser for a specific type"""
        Thread.__init__(self)
        self.zeroconf = zeroconf
        self.type = type
        self.listener = listener
        self.services = {}
        self.next_time = current_time_millis()
        self.delay = _BROWSER_TIME
        self.list = []

        self.done = 0

        self.zeroconf.add_listener(self,
                DNSQuestion(self.type, _TYPE_PTR, _CLASS_IN))
        self.name = "zeroconf.ServiceBrowser"
        self.daemon = True
        self.start()

    def update_record(self, zeroconf, now, record):
        """Callback invoked by Zeroconf when new information arrives.

        Updates information required by browser in the Zeroconf cache."""
        if record.type == _TYPE_PTR and record.name == self.type:
            expired = record.is_expired(now)
            try:
                oldrecord = self.services[record.alias.lower()]
                if not expired:
                    oldrecord.reset_ttl(record)
                else:
                    del(self.services[record.alias.lower()])
                    callback = lambda x: self.listener.remove_service(x,
                            self.type, record.alias)
                    self.list.append(callback)
                    return
            except:
                if not expired:
                    self.services[record.alias.lower()] = record
                    callback = lambda x: self.listener.add_service(x,
                            self.type, record.alias)
                    self.list.append(callback)

            expires = record.get_expiration_time(75)
            if expires < self.next_time:
                self.next_time = expires

    def cancel(self):
        self.done = 1
        self.zeroconf.notify_all()

    def run(self):
        while 1:
            event = None
            now = current_time_millis()
            if len(self.list) == 0 and self.next_time > now:
                self.zeroconf.wait(self.next_time - now)
            if globals()['_GLOBAL_DONE'] or self.done:
                return
            now = current_time_millis()

            if self.next_time <= now:
                out = DNSOutgoing(_FLAGS_QR_QUERY)
                out.add_question(DNSQuestion(self.type, _TYPE_PTR, _CLASS_IN))
                for record in self.services.values():
                    if not record.is_expired(now):
                        out.add_answer_at_time(record, now)
                self.zeroconf.send(out)
                self.next_time = now + self.delay
                self.delay = min((_DNS_TTL * 1000) // _DNS_HEARTBEAT_DIV,
                        self.delay * 2)

            if len(self.list) > 0:
                event = self.list.pop(0)

            if event is not None:
                try:
                    event(self.zeroconf)
                except:
                    pass


class ServiceInfo(object):
    """Service information"""

    def __init__(self, type, name, address=None, port=None, weight=0,
            priority=0, properties=None, server=None, records=None,
            ttl=_DNS_TTL, signer=None):
        """Create a service description.

        domain: fully qualified service type name
        name: fully qualified service name
        address: IP address as unsigned short, network byte order
        port: port that the service runs on
        weight: weight of the service
        priority: priority of the service
        properties: dictionary of properties (or a string holding the bytes
            for the text field)
        server: fully qualified name for service host (defaults to name)"""

        if not name.endswith(type):
            raise BadTypeInNameException
        self.type = type
        self.name = name
        self.signer = signer
        if address is None:
            self.address = []
        elif isinstance(address, tuple):
            self.address = list(address)
        elif isinstance(address, list):
            self.address = address
        else:
            self.address = [address, ]
        self.port = port
        self.weight = weight
        self.priority = priority
        if records is None:
            self.records = [_TYPE_A, _TYPE_SRV, _TYPE_TXT]
        else:
            self.records = records
        self.ttl = ttl
        self.announced = 0
        if server:
            self.server = server
        else:
            self.server = self.name
        if properties is None:
            self.properties = {}
        else:
            self.properties = {}
        self.set_properties(properties)

    def time_to_go(self, now):
        d = (now - self.announced) // 1000
        if d * _DNS_HEARTBEAT_DIV >= self.ttl:
            self.announced = now
            return True
        return False

    def set_property(self, key, value):
        """
        Update only one property in the dict
        """
        self.properties[key] = value
        self.sync_properties()

    def sync_properties(self):
        """
        Set text from dict
        """
        self.text = dict_to_text(self.properties)

    def set_properties(self, properties):
        """Sets properties and text of this info from a dictionary"""
        if isinstance(properties, dict):
            self.properties = properties
            self.sync_properties()
        else:
            self.text = properties

    def set_text(self, text):
        """Sets properties and text given a text field"""
        self.text = text
        try:
            self.properties = text_to_dict(text)
        except:
            traceback.print_exc()
            self.properties = None

    def get_type(self):
        """Type accessor"""
        return self.type

    def get_name(self):
        """Name accessor"""
        if self.type is not None and self.name.endswith("." + self.type):
            return self.name[:len(self.name) - len(self.type) - 1]
        return self.name

    def get_address(self):
        """Address accessor"""
        return self.address

    def get_port(self):
        """Port accessor"""
        return self.port

    def get_priority(self):
        """Pirority accessor"""
        return self.priority

    def get_weight(self):
        """Weight accessor"""
        return self.weight

    def get_properties(self):
        """Properties accessor"""
        return self.properties

    def get_text(self):
        """Text accessor"""
        return self.text

    def get_server(self):
        """Server accessor"""
        return self.server

    def update_record(self, zeroconf, now, record):
        """Updates service information from a DNS record"""
        if record is not None and not record.is_expired(now):
            if record.type == _TYPE_A:
                if record.name == self.name:
                    if not record.address in self.address:
                        self.address.append(record.address)
            elif record.type == _TYPE_SRV:
                if record.name == self.name:
                    self.server = record.server
                    self.port = record.port
                    self.weight = record.weight
                    self.priority = record.priority
                    self.address = []
                    self.update_record(zeroconf, now,
                            zeroconf.cache.get_by_details(self.server,
                                _TYPE_A, _CLASS_IN))
            elif record.type == _TYPE_TXT:
                if record.name == self.name:
                    self.set_text(record.text)

    def request(self, zeroconf, timeout):
        """Returns true if the service could be discovered on the
        network, and updates this object with details discovered.
        """
        now = current_time_millis()
        delay = _LISTENER_TIME
        next = now + delay
        last = now + timeout
        result = 0
        try:
            zeroconf.add_listener(self,
                    DNSQuestion(self.name, _TYPE_ANY, _CLASS_IN))
            while self.server is None or \
                    len(self.address) == 0 or \
                    self.text is None:
                if last <= now:
                    return 0
                if next <= now:
                    out = DNSOutgoing(_FLAGS_QR_QUERY)
                    out.add_question(DNSQuestion(self.name,
                        _TYPE_SRV, _CLASS_IN))
                    out.add_answer_at_time(
                            zeroconf.cache.get_by_details(self.name,
                                _TYPE_SRV, _CLASS_IN), now)
                    out.add_question(
                            DNSQuestion(self.name, _TYPE_TXT, _CLASS_IN))
                    out.add_answer_at_time(
                            zeroconf.cache.get_by_details(self.name,
                                _TYPE_TXT, _CLASS_IN), now)
                    if self.server is not None:
                        out.add_question(
                                DNSQuestion(self.server, _TYPE_A, _CLASS_IN))
                        out.add_answer_at_time(
                                zeroconf.cache.get_by_details(self.server,
                                    _TYPE_A, _CLASS_IN), now)
                    zeroconf.send(out)
                    next = now + delay
                    delay = delay * 2

                zeroconf.wait(min(next, last) - now)
                now = current_time_millis()
            result = 1
        finally:
            zeroconf.remove_listener(self)

        return result

    def __eq__(self, other):
        """Tests equality of service name"""
        if isinstance(other, ServiceInfo):
            return other.name == self.name
        return 0

    def __ne__(self, other):
        """Non-equality test"""
        return not self.__eq__(other)

    def __repr__(self):
        """String representation"""
        addr = self.get_address()
        addrl = []
        for i in addr:
            addrl.append(socket.inet_ntoa(i))
        result = "service[%s,%s:%s," % (self.name, addrl, self.port)
        if self.text is None:
            result += "None"
        else:
            if len(self.text) < 20:
                result += self.text
            else:
                result += self.text[:17] + "..."
        result += "]"
        return result


class Heartbeat(Thread):
    """
    Optional heartbeat thread
    """
    def __init__(self, zeroconf):
        Thread.__init__(self)
        self.zeroconf = zeroconf
        self.condition = threading.Condition()
        self.name = "zeroconf.Heartbeat"
        self.daemon = True
        self.start()

    def wait(self, timeout):
        """Calling thread waits for a given number of milliseconds or
        until notified."""
        self.condition.acquire()
        self.condition.wait(timeout // 1000)
        self.condition.release()

    def notify_all(self):
        """Notifies all waiting threads"""
        self.condition.acquire()
        # python 3.x
        try:
            self.condition.notify_all()
        except:
            self.condition.notifyAll()
        self.condition.release()

    def run(self):
        while 1:
            self.wait(1000)
            if globals()['_GLOBAL_DONE']:
                return

            now = current_time_millis()
            for (i, k) in self.zeroconf.services.items():
                if k.time_to_go(now):
                    self.zeroconf.announce_service(k.name, iterations=1)


class Announcer(object):
    """
    Template class for ZeroConf hooks
    """

    def add(self, record):
        pass

    def remove(self, record):
        pass

    def expire(self, record):
        pass

    def update(self, record):
        pass


class Zeroconf(object):
    """Implementation of Zeroconf Multicast DNS Service Discovery

    Supports registration, unregistration, queries and browsing.
    """
    # interfaces to bind to
    intf = None

    def __init__(self, address=[], psk=False, private=None, keys=None,
            adaptive=False, heartbeat=False, bypass=True):
        """
        Creates an instance of the Zeroconf class, establishing
        multicast communications, listening and reaping threads.

        bindaddress    - address to bind() to
        adaptive    - DNS hack. When receives address 0.0.0.0,
            substitute it with sender's IP
        heartbeat    - run mDNS in the heartbeat mode
        """
        globals()['_GLOBAL_DONE'] = 0
        self.intf = {}
        self.adaptive = adaptive

        assert isinstance(address, list) or isinstance(address, tuple)

        for i in address:
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            try:
                s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
                s.socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEPORT, 1)
            except:
                # SO_REUSEADDR should be equivalent to SO_REUSEPORT for
                # multicast UDP sockets (p 731, "TCP/IP Illustrated,
                # Volume 2"), but some BSD-derived systems require
                # SO_REUSEPORT to be specified explicity.  Also, not all
                # versions of Python have SO_REUSEPORT available.  So
                # if you're on a BSD-based system, and haven't upgraded
                # to Python 2.3 yet, you may find this library doesn't
                # work as expected.
                #
                pass
            s.setsockopt(socket.SOL_IP, socket.IP_MULTICAST_TTL, 255)
            s.setsockopt(socket.SOL_IP, socket.IP_MULTICAST_LOOP, 1)
            s.setsockopt(socket.SOL_IP, socket.IP_MULTICAST_IF,
                    socket.inet_aton(i) + socket.inet_aton('0.0.0.0'))
            s.setsockopt(socket.SOL_IP, socket.IP_ADD_MEMBERSHIP,
                    socket.inet_aton(_MDNS_ADDR) + socket.inet_aton(i))
            try:
                s.bind(("0.0.0.0", _MDNS_PORT))
            except:
                # Some versions of linux raise an exception even though
                # the SO_REUSE* options have been set, so ignore it
                #
                pass
            self.intf[i] = s

        self.hooks = []
        self.listeners = []
        self.listns = []
        self.browsers = []
        self.services = {}
        # hook for AXFR requests
        self.zones = {}
        # public keys store
        self.bypass = bypass
        self.psk = psk
        self.private = private
        if keys is None:
            self.keys = {}
        else:
            self.keys = keys

        self.cache = DNSCache(self.private)

        self.condition = threading.Condition()

        self.engine = Engine(self)
        for i in self.intf.values():
            self.listns.append(Listener(self, i))

        self.reaper = Reaper(self)
        self.heartbeat = None

        if heartbeat:
            self.heartbeat = Heartbeat(self)

    def wait(self, timeout):
        """Calling thread waits for a given number of milliseconds or
        until notified."""
        self.condition.acquire()
        self.condition.wait(timeout // 1000)
        self.condition.release()

    def notify_all(self):
        """Notifies all waiting threads"""
        self.condition.acquire()
        # python 3.x
        try:
            self.condition.notify_all()
        except:
            self.condition.notifyAll()
        self.condition.release()

    def get_service_info(self, type, name, timeout=3000):
        """Returns network's service information for a particular
        name and type, or None if no service matches by the timeout,
        which defaults to 3 seconds."""
        info = ServiceInfo(type, name)
        if info.request(self, timeout):
            return info
        return None

    def add_serviceListener(self, type, listener):
        """Adds a listener for a particular service type.  This object
        will then have its update_record method called when information
        arrives for that type."""
        self.remove_service_listener(listener)
        self.browsers.append(ServiceBrowser(self, type, listener))

    def remove_service_listener(self, listener):
        """Removes a listener from the set that is currently listening."""
        for browser in self.browsers:
            if browser.listener == listener:
                browser.cancel()
                del(browser)

    def register_zone(self, svc):
        self.zones[svc.type] = svc

    def register_service(self, info):
        """Registers service information to the network with a default TTL
        of 60 seconds.  Zeroconf will then respond to requests for
        information for that service.  The name of the service may be
        changed if needed to make it unique on the network."""
        self.check_service(info)
        self.services[info.name.lower()] = info

        # zone transfer
        self.transfer_zone(info.type)
        self.announce_service(info.name)

    def transfer_zone(self, name):
        out = DNSOutgoing(_FLAGS_QR_QUERY | _FLAGS_AA)
        out.add_question(DNSQuestion(name, _TYPE_AXFR, _CLASS_IN))
        self.send(out)

    def announce_service(self, name, iterations=3):
        info = self.services[name.lower()]
        now = current_time_millis()
        next_time = now

        self.cache.sign(
                DNSPointer(info.type,
                    _TYPE_PTR, _CLASS_IN, info.ttl, info.name), info.signer)
        self.cache.sign(
                DNSService(info.name,
                    _TYPE_SRV, _CLASS_IN, info.ttl, info.priority,
                    info.weight, info.port, info.server), info.signer)
        self.cache.sign(
                DNSText(info.name,
                    _TYPE_TXT, _CLASS_IN, info.ttl, info.text), info.signer)
        for i in info.address:
            self.cache.sign(
                    DNSAddress(info.server,
                        _TYPE_A, _CLASS_IN, info.ttl, i), info.signer)

        while iterations > 0:
            if now < next_time:
                self.wait(next_time - now)
                now = current_time_millis()
                continue
            out = DNSOutgoing(_FLAGS_QR_RESPONSE | _FLAGS_AA)
            out.add_answer_at_time(
                    self.cache.get(
                        DNSPointer(info.type,
                            _TYPE_PTR, _CLASS_IN, info.ttl, info.name)), 0)
            if _TYPE_SRV in info.records:
                out.add_answer_at_time(
                        self.cache.get(
                            DNSService(info.name,
                                _TYPE_SRV, _CLASS_IN, info.ttl, info.priority,
                                info.weight, info.port, info.server)), 0)
            if _TYPE_TXT in info.records:
                out.add_answer_at_time(
                        self.cache.get(
                            DNSText(info.name,
                                _TYPE_TXT, _CLASS_IN, info.ttl, info.text)), 0)
            if info.address and _TYPE_A in info.records:
                for i in info.address:
                    out.add_answer_at_time(
                            self.cache.get(
                                DNSAddress(info.server,
                                    _TYPE_A, _CLASS_IN, info.ttl, i)), 0)
            self.send(out)
            iterations -= 1
            next_time += _REGISTER_TIME

    def unregister_service(self, info):
        """Unregister a service."""
        try:
            del(self.services[info.name.lower()])
        except:
            pass
        now = current_time_millis()
        next_time = now
        i = 0
        while i < 3:
            if now < next_time:
                self.wait(next_time - now)
                now = current_time_millis()
                continue
            out = DNSOutgoing(_FLAGS_QR_RESPONSE | _FLAGS_AA)
            out.add_answer_at_time(
                    DNSPointer(info.type,
                        _TYPE_PTR, _CLASS_IN, 0, info.name), 0)
            out.add_answer_at_time(
                    DNSService(info.name,
                        _TYPE_SRV, _CLASS_IN, 0, info.priority,
                        info.weight, info.port, info.name), 0)
            out.add_answer_at_time(
                    DNSText(info.name, _TYPE_TXT, _CLASS_IN, 0, info.text), 0)
            for k in info.address:
                out.add_answer_at_time(
                        DNSAddress(info.server, _TYPE_A, _CLASS_IN, 0, k), 0)
            self.send(out)
            i += 1
            next_time += _UNREGISTER_TIME

    def unregister_all_services(self):
        """Unregister all registered services."""
        if len(self.services) > 0:
            now = current_time_millis()
            next_time = now
            i = 0
            while i < 3:
                if now < next_time:
                    self.wait(next_time - now)
                    now = current_time_millis()
                    continue
                out = DNSOutgoing(_FLAGS_QR_RESPONSE | _FLAGS_AA)
                for info in self.services.values():
                    out.add_answer_at_time(
                            DNSPointer(info.type,
                                _TYPE_PTR, _CLASS_IN, 0, info.name), 0)
                    out.add_answer_at_time(
                            DNSService(info.name,
                                _TYPE_SRV, _CLASS_IN, 0, info.priority,
                                info.weight, info.port, info.server), 0)
                    out.add_answer_at_time(
                            DNSText(info.name,
                                _TYPE_TXT, _CLASS_IN, 0, info.text), 0)
                    for k in info.address:
                        out.add_answer_at_time(
                                DNSAddress(info.server,
                                    _TYPE_A, _CLASS_IN, 0, k), 0)
                self.send(out)
                i += 1
                next_time += _UNREGISTER_TIME

    def check_service(self, info):
        """Checks the network for a unique service name, modifying the
        ServiceInfo passed in if it is not unique."""
        now = current_time_millis()
        next_time = now
        i = 0
        while i < 3:
            for record in self.cache.entries_with_name(info.type):
                if record.type == _TYPE_PTR and \
                        not record.is_expired(now) and \
                        record.alias == info.name:
                    if (info.name.find('.') < 0):
                        info.name = info.name + ".[" + \
                                info.address + \
                                ":" + info.port + \
                                "]." + info.type
                        self.check_service(info)
                        return
                    raise NonUniqueNameException
            if now < next_time:
                self.wait(next_time - now)
                now = current_time_millis()
                continue
            out = DNSOutgoing(_FLAGS_QR_QUERY | _FLAGS_AA)
            self.debug = out
            out.add_question(
                    DNSQuestion(info.type, _TYPE_PTR, _CLASS_IN))
            out.add_authorative_answer(
                    DNSPointer(info.type,
                        _TYPE_PTR, _CLASS_IN, info.ttl, info.name))
            self.send(out)
            i += 1
            next_time += _CHECK_TIME

    def add_cache_hook(self, hook):
        if not hook in self.hooks:
            self.hooks.append(hook)

    def add_listener(self, listener, question):
        """Adds a listener for a given question.  The listener will have
        its update_record method called when information is available to
        answer the question."""
        now = current_time_millis()
        self.listeners.append(listener)
        if question is not None:
            for record in self.cache.entries_with_name(question.name):
                if question.answered_by(record) and not record.is_expired(now):
                    listener.update_record(self, now, record)
        self.notify_all()

    def remove_listener(self, listener):
        """Removes a listener."""
        try:
            self.listeners.remove(listener)
            self.notify_all()
        except:
            pass

    def update_record(self, now, rec):
        """Used to notify listeners of new information that has updated
        a record."""
        for listener in self.listeners:
            listener.update_record(self, now, rec)
        self.notify_all()

    def verify(self, entry, signature):
        s = loads(b64decode(signature.signature))
        key = None

        if not self.psk:
            if signature.signer in list(self.keys.keys()):
                key = signature.signer
            elif isinstance(entry, DNSPointer):
                if entry.alias in list(self.keys.keys()):
                    key = entry.alias
            if not key:
                return False

        h = MD5.new(entry.sp()).digest()
        if self.psk:
            return self.private.verify(h, s)
        else:
            return self.keys[key].verify(h, s)

    def handle_response(self, msg, address):
        """Deal with incoming response packets.  All answers
        are held in the cache, and listeners are notified."""
        now = current_time_millis()

        sigs = []
        precache = []

        for record in msg.answers:
            if isinstance(record, DNSSignature):
                sigs.append(record)
            else:
                precache.append(record)

            for e in precache:
                for s in sigs:
                    if self.verify(e, s):
                        # print "DNS: %s verified with %s" % (e,s)

                        if self.adaptive and e.type == _TYPE_A:
                            if e.address == '\x00\x00\x00\x00':
                                e.address = socket.inet_aton(address)

                        if e in self.cache.entries():
                            if e.is_expired(now):
                                for i in self.hooks:
                                    try:
                                        i.remove(e)
                                    except:
                                        pass
                                self.cache.remove(e)
                                self.cache.remove(s)
                            else:
                                entry = self.cache.get(e)
                                sig = self.cache.get(s)
                                if (entry is not None) and (sig is not None):
                                    for i in self.hooks:
                                        try:
                                            i.update(e)
                                        except:
                                            pass
                                    entry.reset_ttl(e)
                                    sig.reset_ttl(s)
                        else:
                            e.rrsig = s
                            self.cache.add(e)
                            self.cache.add(s)
                            for i in self.hooks:
                                try:
                                    i.add(e)
                                except:
                                    pass

                        precache.remove(e)
                        sigs.remove(s)
                        self.update_record(now, record)

        if self.bypass:
            for e in precache:
                if e in self.cache.entries():
                    if e.is_expired(now):
                        for i in self.hooks:
                            try:
                                i.remove(e)
                            except:
                                pass
                        self.cache.remove(e)
                    else:
                        entry = self.cache.get(e)
                        if (entry is not None):
                            for i in self.hooks:
                                try:
                                    i.update(e)
                                except:
                                    pass
                            entry.reset_ttl(e)
                else:
                    self.cache.add(e)
                    for i in self.hooks:
                        try:
                            i.add(e)
                        except:
                            pass

                self.update_record(now, record)
        #for i in sigs:
        #    print "DNS: orphan signature %s" % (i)

    def handle_query(self, msg, addr, port, orig):
        """
        Deal with incoming query packets.  Provides a response if
        possible.

        msg    - message to process
        addr    - dst addr
        port    - dst port
        orig    - originating address (for adaptive records)
        """
        out = None

        # Support unicast client responses
        #
        if port != _MDNS_PORT:
            out = DNSOutgoing(_FLAGS_QR_RESPONSE | _FLAGS_AA, 0)
            for question in msg.questions:
                out.add_question(question)
        for question in msg.questions:
            if question.type == _TYPE_PTR:
                for service in self.services.values():
                    if question.name == service.type:
                        # FIXME: sometimes we just not in time filling cache
                        answer = self.cache.get(
                                DNSPointer(service.type,
                                    _TYPE_PTR, _CLASS_IN,
                                    service.ttl, service.name))
                        if out is None and answer is not None:
                            out = DNSOutgoing(_FLAGS_QR_RESPONSE | _FLAGS_AA)
                        if answer:
                            out.add_answer(msg, answer)
            if question.type == _TYPE_AXFR:
                if question.name in list(self.zones.keys()):
                    if out is None:
                        out = DNSOutgoing(_FLAGS_QR_RESPONSE | _FLAGS_AA)
                    for i in self.zones[question.name].services.values():
                        out.add_answer(msg, i)
            else:
                try:
                    if out is None:
                        out = DNSOutgoing(_FLAGS_QR_RESPONSE | _FLAGS_AA)

                    service = self.services.get(question.name.lower(), None)
                    try:
                        rs = service.records
                    except:
                        rs = []

                    # Answer A record queries for any service addresses we know
                    if (question.type == _TYPE_A or \
                            question.type == _TYPE_ANY) \
                            and (_TYPE_A in rs):
                        for service in self.services.values():
                            if service.server == question.name.lower():
                                for i in service.address:
                                    out.add_answer(msg, self.cache.get(
                                        DNSAddress(question.name,
                                            _TYPE_A, _CLASS_IN | _CLASS_UNIQUE,
                                            service.ttl, i)))

                    if not service:
                        continue

                    if (question.type == _TYPE_SRV or \
                            question.type == _TYPE_ANY) and (_TYPE_SRV in rs):
                        out.add_answer(msg, self.cache.get(
                            DNSService(question.name,
                                _TYPE_SRV, _CLASS_IN | _CLASS_UNIQUE,
                                service.ttl, service.priority, service.weight,
                                service.port, service.server)))
                    if (question.type == _TYPE_TXT or \
                            question.type == _TYPE_ANY) and \
                            (_TYPE_TXT in rs):
                        out.add_answer(msg, self.cache.get(
                            DNSText(question.name,
                                _TYPE_TXT, _CLASS_IN | _CLASS_UNIQUE,
                                service.ttl, service.text)))
                    if (question.type == _TYPE_SRV) and (_TYPE_SRV in rs):
                        for i in service.address:
                            out.add_additional_answer(self.cache.get(
                                DNSAddress(service.server,
                                    _TYPE_A, _CLASS_IN | _CLASS_UNIQUE,
                                    service.ttl, i)))
                except:
                    traceback.print_exc()

        if out is not None and out.answers:
            out.id = msg.id
            self.send(out, addr, port)

    def send(self, out, addr=_MDNS_ADDR, port=_MDNS_PORT):
        """Sends an outgoing packet."""
        # This is a quick test to see if we can parse the packets we generate
        #temp = DNSIncoming(out.packet())
        for i in self.intf.values():
            try:
                return i.sendto(out.packet(), 0, (addr, port))
            except:
                # Ignore this, it may be a temporary loss of network connection
                return -1

    def close(self):
        """Ends the background threads, and prevent this instance from
        servicing further queries."""
        if globals()['_GLOBAL_DONE'] == 0:
            globals()['_GLOBAL_DONE'] = 1
            self.notify_all()
            self.engine.notify()
            self.unregister_all_services()
            for i in self.intf.values():
                try:
                    # there are cases, when we start mDNS without network
                    i.setsockopt(socket.SOL_IP, socket.IP_DROP_MEMBERSHIP,
                            socket.inet_aton(_MDNS_ADDR) + \
                                    socket.inet_aton('0.0.0.0'))
                except:
                    pass
                i.close()
