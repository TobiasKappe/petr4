#include <core.p4>
#include <v1model.p4>

header head {
    bit<8> v;
}

struct metadata { }

parser MyParser(packet_in packet,
                out head[13] hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        transition accept;
    }

}

control MyChecksum(inout head[13] hdr, inout metadata meta) {
    apply { }
}

control MyIngress(inout head[13] hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    apply {

    }
}

control MyEgress(inout head[13] hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {

    action set_one () {
        standard_metadata.egress_spec = 1;
    }

    action set_two () {
        standard_metadata.egress_spec = 2;
    }

    table my_table {
        key = { standard_metadata.egress_spec : exact;
                standard_metadata.ingress_port : exact;}
        actions = { set_one; set_two; }
        default_action = set_two();
        const entries = {
            (9w0, 9w0) : set_two;
            (9w1, 9w1) : set_one;
            }
    }

    apply {
        if (my_table.apply().hit) {standard_metadata.egress_spec = 42;}
        else {standard_metadata.egress_spec = 43;}
        exit;
    }

}

control MyDeparser(packet_out packet, in head[13] hdr) {
    apply {
        packet.emit(hdr);
    }
}

V1Switch(
    MyParser(),
    MyChecksum(),
    MyIngress(),
    MyEgress(),
    MyChecksum(),
    MyDeparser()
    )
main;
