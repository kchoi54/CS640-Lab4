package edu.wisc.cs.sdn.apps.loadbalancer;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.List;

import org.openflow.protocol.OFMessage;
import org.openflow.protocol.OFOXMFieldType;
import org.openflow.protocol.OFPacketIn;
import org.openflow.protocol.OFType;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import edu.wisc.cs.sdn.apps.l3routing.L3Routing;
import edu.wisc.cs.sdn.apps.util.ArpServer;

import edu.wisc.cs.sdn.apps.util.SwitchCommands;

import org.openflow.protocol.OFMatch;
// import.org.openflow.protocol.OFMatchField;
import org.openflow.protocol.OFPort;
import org.openflow.protocol.action.OFAction;
import org.openflow.protocol.action.OFActionOutput;
import org.openflow.protocol.action.OFActionSetField;
import org.openflow.protocol.instruction.OFInstruction;
import org.openflow.protocol.instruction.OFInstructionActions;
import org.openflow.protocol.instruction.OFInstructionApplyActions;
import org.openflow.protocol.instruction.OFInstructionGotoTable;

import net.floodlightcontroller.core.FloodlightContext;
import net.floodlightcontroller.core.IFloodlightProviderService;
import net.floodlightcontroller.core.IOFMessageListener;
import net.floodlightcontroller.core.IOFSwitch.PortChangeType;
import net.floodlightcontroller.core.IOFSwitch;
import net.floodlightcontroller.core.IOFSwitchListener;
import net.floodlightcontroller.core.ImmutablePort;
import net.floodlightcontroller.core.module.FloodlightModuleContext;
import net.floodlightcontroller.core.module.FloodlightModuleException;
import net.floodlightcontroller.core.module.IFloodlightModule;
import net.floodlightcontroller.core.module.IFloodlightService;
import net.floodlightcontroller.devicemanager.IDevice;
import net.floodlightcontroller.devicemanager.IDeviceService;
import net.floodlightcontroller.devicemanager.internal.DeviceManagerImpl;

import net.floodlightcontroller.packet.*;
import net.floodlightcontroller.util.MACAddress;

public class LoadBalancer implements IFloodlightModule, IOFSwitchListener,
		IOFMessageListener
{
	public static final String MODULE_NAME = LoadBalancer.class.getSimpleName();
	
	private static final byte TCP_FLAG_SYN = 0x02;
	
	private static final short IDLE_TIMEOUT = 20;
	
	// Interface to the logging system
    private static Logger log = LoggerFactory.getLogger(MODULE_NAME);
    
    // Interface to Floodlight core for interacting with connected switches
    private IFloodlightProviderService floodlightProv;
    
    // Interface to device manager service
    private IDeviceService deviceProv;
    
    // Switch table in which rules should be installed
    private byte table;
    
    // Set of virtual IPs and the load balancer instances they correspond with
    private Map<Integer,LoadBalancerInstance> instances;

    /**
     * Loads dependencies and initializes data structures.
     */
	@Override
	public void init(FloodlightModuleContext context)
			throws FloodlightModuleException 
	{
		log.info(String.format("Initializing %s...", MODULE_NAME));
		
		// Obtain table number from config
		Map<String,String> config = context.getConfigParams(this);
        this.table = Byte.parseByte(config.get("table"));
        
        // Create instances from config
        this.instances = new HashMap<Integer,LoadBalancerInstance>();
        String[] instanceConfigs = config.get("instances").split(";");
        for (String instanceConfig : instanceConfigs)
        {
        	String[] configItems = instanceConfig.split(" ");
        	if (configItems.length != 3)
        	{ 
        		log.error("Ignoring bad instance config: " + instanceConfig);
        		continue;
        	}
        	LoadBalancerInstance instance = new LoadBalancerInstance(
        			configItems[0], configItems[1], configItems[2].split(","));
            this.instances.put(instance.getVirtualIP(), instance);
            log.info("Added load balancer instance: " + instance);
        }
        
		this.floodlightProv = context.getServiceImpl(
				IFloodlightProviderService.class);
        this.deviceProv = context.getServiceImpl(IDeviceService.class);
        
        /*********************************************************************/
        /* TODO: Initialize other class variables, if necessary              */
        
        /*********************************************************************/
	}

	/**
     * Subscribes to events and performs other startup tasks.
     */
	@Override
	public void startUp(FloodlightModuleContext context)
			throws FloodlightModuleException 
	{
		log.info(String.format("Starting %s...", MODULE_NAME));
		this.floodlightProv.addOFSwitchListener(this);
		this.floodlightProv.addOFMessageListener(OFType.PACKET_IN, this);
		log.info(String.format("Finisehd startup process"));
		/*********************************************************************/
		/* TODO: Perform other tasks, if necessary                           */
		
		/*********************************************************************/
	}

	
	
	/**
     * Event handler called when a switch joins the network.
     * @param DPID for the switch
     */
	@Override
	public void switchAdded(long switchId) 
	{
		IOFSwitch sw = this.floodlightProv.getSwitch(switchId);
		log.info(String.format("Switch s%d added", switchId));


		//Install rules to send

		for (Integer virtualIP : instances.keySet()) {
			// IP rules
			log.info(String.format("Adding IP RULES"));
			OFMatch ipMatchCriteria = new OFMatch();
			ipMatchCriteria.setDataLayerType(OFMatch.ETH_TYPE_IPV4);
			ipMatchCriteria.setNetworkProtocol(OFMatch.IP_PROTO_TCP);
			ipMatchCriteria.setNetworkDestination(virtualIP);
			OFAction ipAction = new OFActionOutput(OFPort.OFPP_CONTROLLER);
			OFInstruction ipInstr = new OFInstructionApplyActions(Arrays.asList(ipAction));
			SwitchCommands.installRule(sw, this.table, (short)(SwitchCommands.DEFAULT_PRIORITY+1), 
										ipMatchCriteria, Arrays.asList(ipInstr));
		}
		
		// ARP rules
		log.info(String.format("Adding ARP Handling"));
		OFMatch arpMatchCriteria = new OFMatch();
		arpMatchCriteria.setDataLayerType(OFMatch.ETH_TYPE_ARP);
		//arpMatchCriteria.setNetworkDestination(virtualIP);
		//arpMatchCriteria.setField(OFOXMFieldType.ARP_TPA, virtualIP);
		OFAction arpAction = new OFActionOutput(OFPort.OFPP_CONTROLLER);
		OFInstruction arpInstr = new OFInstructionApplyActions(Arrays.asList(arpAction));
		SwitchCommands.installRule(sw, this.table, (short)(SwitchCommands.DEFAULT_PRIORITY+1), 
												arpMatchCriteria, Arrays.asList(arpInstr));
		
		// all other packets to the next rule table in the switch 
		OFInstruction l3RoutingInstr = new OFInstructionGotoTable(L3Routing.table);
		SwitchCommands.installRule(sw, this.table, SwitchCommands.DEFAULT_PRIORITY, 
									new OFMatch(), Arrays.asList(l3RoutingInstr));	
		/*********************************************************************/
		/* TODO: Install rules to send:                                      */
		/*       (1) packets from new connections to each virtual load       */
		/*       balancer IP to the controller                               */
		/*       (2) ARP packets to the controller, and                      */
		/*       (3) all other packets to the next rule table in the switch  */
		
		/*********************************************************************/
	}
	
	/**
	 * Handle incoming packets sent from switches.
	 * @param sw switch on which the packet was received
	 * @param msg message from the switch
	 * @param cntx the Floodlight context in which the message should be handled
	 * @return indication whether another module should also process the packet
	 */
	@Override
	public net.floodlightcontroller.core.IListener.Command receive(
			IOFSwitch sw, OFMessage msg, FloodlightContext cntx) 
	{
		// We're only interested in packet-in messages
		if (msg.getType() != OFType.PACKET_IN)
		{ return Command.CONTINUE; }
		OFPacketIn pktIn = (OFPacketIn)msg;
		
		// Handle the packet
		Ethernet ethPkt = new Ethernet();
		ethPkt.deserialize(pktIn.getPacketData(), 0,
				pktIn.getPacketData().length);

		//Handle ARP packets

		if (Ethernet.TYPE_ARP == ethPkt.getEtherType()) {
			ARP arpPkt = (ARP) ethPkt.getPayload();
			if (arpPkt.getOpCode() == ARP.OP_REQUEST) { 
				int virtualIP = IPv4.toIPv4Address(arpPkt.getTargetProtocolAddress());
				if (this.instances.containsKey(virtualIP)) {		
					// construct Ethernet header
					Ethernet arpReplyPacket = new Ethernet();
					arpReplyPacket.setEtherType(Ethernet.TYPE_ARP);
					arpReplyPacket.setSourceMACAddress(this.instances.get(virtualIP).getVirtualMAC());
					arpReplyPacket.setDestinationMACAddress(ethPkt.getSourceMACAddress());
					// construct ARP header
					ARP arpHeader = new ARP();
					arpHeader.setHardwareType(ARP.HW_TYPE_ETHERNET);
					arpHeader.setProtocolType(ARP.PROTO_TYPE_IP);
					arpHeader.setHardwareAddressLength((byte) Ethernet.DATALAYER_ADDRESS_LENGTH);
					arpHeader.setProtocolAddressLength((byte) 4);
					arpHeader.setOpCode(ARP.OP_REPLY);
					arpHeader.setSenderHardwareAddress(this.instances.get(virtualIP).getVirtualMAC());
					arpHeader.setSenderProtocolAddress(virtualIP);
					arpHeader.setTargetHardwareAddress(arpPkt.getSenderHardwareAddress());
					arpHeader.setTargetProtocolAddress(arpPkt.getSenderProtocolAddress());
					// link together & send reply packet
					arpReplyPacket.setPayload(arpHeader);
					SwitchCommands.sendPacket(sw, (short)pktIn.getInPort(), arpReplyPacket);
				}
			}
		}

		// handle TCP SYN
		if (Ethernet.TYPE_IPv4 == ethPkt.getEtherType()) {
			IPv4 ipPkt = (IPv4) ethPkt.getPayload();
			if (ipPkt.getProtocol() == IPv4.PROTOCOL_TCP) {
				TCP tcpPkt = (TCP) ipPkt.getPayload();
				if (tcpPkt.getFlags() == TCP_FLAG_SYN) {
					int virtualIP = ipPkt.getDestinationAddress();
					int nextHostIP = this.instances.get(virtualIP).getNextHostIP();
					
					// client --> virtual IP
					OFMatch cvMatchCriteria = new OFMatch();
					cvMatchCriteria.setDataLayerType(Ethernet.TYPE_IPv4);
					cvMatchCriteria.setNetworkSource(ipPkt.getSourceAddress());
					cvMatchCriteria.setNetworkDestination(virtualIP);
					cvMatchCriteria.setNetworkProtocol(OFMatch.IP_PROTO_TCP);
					cvMatchCriteria.setTransportSource(tcpPkt.getSourcePort());
					cvMatchCriteria.setTransportDestination(tcpPkt.getDestinationPort());
					OFAction cvIP = new OFActionSetField(OFOXMFieldType.IPV4_DST, nextHostIP);
					OFAction cvMAC = new OFActionSetField(OFOXMFieldType.ETH_DST, this.getHostMACAddress(nextHostIP));
					OFInstruction cvInstr =  new OFInstructionApplyActions(Arrays.asList(cvIP, cvMAC));
		     		OFInstruction cvInstrGotoTable = new OFInstructionGotoTable(L3Routing.table);
					SwitchCommands.installRule(sw, this.table, (short)(SwitchCommands.DEFAULT_PRIORITY + 2), cvMatchCriteria, 
												Arrays.asList(cvInstr, cvInstrGotoTable), SwitchCommands.NO_TIMEOUT, IDLE_TIMEOUT);
					
					// virtual IP --> client
					OFMatch vcMatchCriteria = new OFMatch();
					vcMatchCriteria.setDataLayerType(Ethernet.TYPE_IPv4);
					vcMatchCriteria.setNetworkSource(nextHostIP);
					vcMatchCriteria.setNetworkDestination(ipPkt.getSourceAddress());
					vcMatchCriteria.setNetworkProtocol(OFMatch.IP_PROTO_TCP);
					vcMatchCriteria.setTransportSource(OFMatch.IP_PROTO_TCP, tcpPkt.getDestinationPort());
					vcMatchCriteria.setTransportDestination(OFMatch.IP_PROTO_TCP, tcpPkt.getSourcePort());
					OFAction vcIP = new OFActionSetField(OFOXMFieldType.IPV4_SRC, virtualIP);
					OFAction vcMAC = new OFActionSetField(OFOXMFieldType.ETH_SRC, this.instances.get(virtualIP).getVirtualMAC());
					OFInstruction vcInstr  =  new OFInstructionApplyActions(Arrays.asList(vcIP, vcMAC));
					OFInstruction vcInstrGotoTable = new OFInstructionGotoTable(L3Routing.table);
					SwitchCommands.installRule(sw, this.table, (short)(SwitchCommands.DEFAULT_PRIORITY + 2), vcMatchCriteria, 
												Arrays.asList(vcInstr, vcInstrGotoTable), SwitchCommands.NO_TIMEOUT, IDLE_TIMEOUT);
				}
			}
		}
		
		/*********************************************************************/
		/* TODO: Send an ARP reply for ARP requests for virtual IPs; for TCP */
		/*       SYNs sent to a virtual IP, select a host and install        */
		/*       connection-specific rules to rewrite IP and MAC addresses;  */
		/*       ignore all other packets                                    */
		
		/*********************************************************************/

		
		// We don't care about other packets
		return Command.CONTINUE;
	}
	
	/**
	 * Returns the MAC address for a host, given the host's IP address.
	 * @param hostIPAddress the host's IP address
	 * @return the hosts's MAC address, null if unknown
	 */
	private byte[] getHostMACAddress(int hostIPAddress)
	{
		Iterator<? extends IDevice> iterator = this.deviceProv.queryDevices(
				null, null, hostIPAddress, null, null);
		if (!iterator.hasNext())
		{ return null; }
		IDevice device = iterator.next();
		return MACAddress.valueOf(device.getMACAddress()).toBytes();
	}

	/**
	 * Event handler called when a switch leaves the network.
	 * @param DPID for the switch
	 */
	@Override
	public void switchRemoved(long switchId) 
	{ /* Nothing we need to do, since the switch is no longer active */ }

	/**
	 * Event handler called when the controller becomes the master for a switch.
	 * @param DPID for the switch
	 */
	@Override
	public void switchActivated(long switchId)
	{ /* Nothing we need to do, since we're not switching controller roles */ }

	/**
	 * Event handler called when a port on a switch goes up or down, or is
	 * added or removed.
	 * @param DPID for the switch
	 * @param port the port on the switch whose status changed
	 * @param type the type of status change (up, down, add, remove)
	 */
	@Override
	public void switchPortChanged(long switchId, ImmutablePort port,
			PortChangeType type) 
	{ /* Nothing we need to do, since load balancer rules are port-agnostic */}

	/**
	 * Event handler called when some attribute of a switch changes.
	 * @param DPID for the switch
	 */
	@Override
	public void switchChanged(long switchId) 
	{ /* Nothing we need to do */ }
	
    /**
     * Tell the module system which services we provide.
     */
	@Override
	public Collection<Class<? extends IFloodlightService>> getModuleServices() 
	{ return null; }

	/**
     * Tell the module system which services we implement.
     */
	@Override
	public Map<Class<? extends IFloodlightService>, IFloodlightService> 
			getServiceImpls() 
	{ return null; }

	/**
     * Tell the module system which modules we depend on.
     */
	@Override
	public Collection<Class<? extends IFloodlightService>> 
			getModuleDependencies() 
	{
		Collection<Class<? extends IFloodlightService >> floodlightService =
	            new ArrayList<Class<? extends IFloodlightService>>();
        floodlightService.add(IFloodlightProviderService.class);
        floodlightService.add(IDeviceService.class);
        return floodlightService;
	}

	/**
	 * Gets a name for this module.
	 * @return name for this module
	 */
	@Override
	public String getName() 
	{ return MODULE_NAME; }

	/**
	 * Check if events must be passed to another module before this module is
	 * notified of the event.
	 */
	@Override
	public boolean isCallbackOrderingPrereq(OFType type, String name) 
	{
		return (OFType.PACKET_IN == type 
				&& (name.equals(ArpServer.MODULE_NAME) 
					|| name.equals(DeviceManagerImpl.MODULE_NAME))); 
	}

	/**
	 * Check if events must be passed to another module after this module has
	 * been notified of the event.
	 */
	@Override
	public boolean isCallbackOrderingPostreq(OFType type, String name) 
	{ return false; }
}
