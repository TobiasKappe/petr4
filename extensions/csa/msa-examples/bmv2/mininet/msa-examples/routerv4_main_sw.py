#!/usr/bin/env python2

#
# Author: Hardik Soni
# Email: hks57@cornell.edu
#

import sys
from mininet.net import Mininet
from mininet.topo import Topo
from mininet.log import setLogLevel, info
from mininet.cli import CLI

sys.path.insert(1, './bmv2/mininet/')
sys.path.insert(1, './../')
from p4_mininet import P4Switch, P4Host

import argparse
from time import sleep

parser = argparse.ArgumentParser(description='Mininet demo')
parser.add_argument('--behavioral-exe', help='Path to behavioral executable',
                    type=str, action="store", required=True)
parser.add_argument('--thrift-port', help='Thrift server port for table updates',
                    type=int, action="store", default=9090)
parser.add_argument('--num-hosts', help='Number of hosts to connect to switch',
                    type=int, action="store", default=2)
parser.add_argument('--json', help='Path to JSON config file',
                    type=str, action="store", required=True)
parser.add_argument('--pcap-dump', help='Dump packets on interfaces to pcap files',
                    type=str, action="store", required=False, default=False)

args = parser.parse_args()


class SingleSwitchTopo(Topo):
    "Single switch connected to n (< 256) hosts."
    def __init__(self, sw_path, json_path, thrift_port, pcap_dump, n, **opts):
        # Initialize topology and default options
        Topo.__init__(self, **opts)

        switch = self.addSwitch('s1',
                                sw_path = sw_path,
                                json_path = json_path,
                                thrift_port = thrift_port,
                                pcap_dump = pcap_dump,
                                log_console = True,
                                enable_debugger = True)

        for h in xrange(n):
            host = self.addHost('h%d' % (h + 1),
                                ip = "10.0.%d.1/16" % (h+1),
                                mac = '00:00:00:00:00:%02x' %(h+1))
            self.addLink(host, switch, 0, (h+1))

def main():
    num_hosts = args.num_hosts

    topo = SingleSwitchTopo(args.behavioral_exe,
                            args.json,
                            args.thrift_port,
                            args.pcap_dump,
                            num_hosts)
    net = Mininet(topo = topo,
                  host = P4Host,
                  switch = P4Switch,
                  controller = None)
    net.start()


    sw_mac = ["00:00:00:00:00:%02x" % (n+1) for n in xrange(num_hosts)]

    sw_addr = ["10.0.%d.1" % (n+1) for n in xrange(num_hosts)]

    for n in xrange(num_hosts):
        h = net.get('h%d' % (n + 1))
        for k in xrange(num_hosts):
            if n+1 == k+1:
                continue
            # print 'setting arp ' + sw_addr[n] + ' '+ sw_mac[n] +' in h'+str(n+1)
            # h.setARP(sw_addr[n], sw_mac[n])
            h.cmd('ethtool -K eth0 tx off ')
            h.cmd('ethtool -K eth0 rx off ')
            h.cmd('arp -s ' +sw_addr[k] +' '+ sw_mac[k])
            # print 'dev eth0 via ' + sw_addr[n]
        # h.setDefaultRoute("dev eth0 via %s" % sw_addr[k])
        h.cmd('ip route add '+'10.0.0.0/16 ' +'dev eth0 ')

    for n in xrange(num_hosts):
        h = net.get('h%d' % (n + 1))
        h.describe()

    sleep(3)

    print "Ready !"

    # enable following line and type h1 ping h2 on the CLI
    # CLI( net ) 
    net.pingAll()
    net.stop()

if __name__ == '__main__':
    setLogLevel( 'info' )
    main()
