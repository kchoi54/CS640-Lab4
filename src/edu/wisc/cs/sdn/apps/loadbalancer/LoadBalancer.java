package edu.wisc.cs.sdn.apps.loadbalancer;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

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

		for (int virtualHost : this.instances.keySet()){
			OFMatch ofMatchIP = new OFMatch();
			OFMatchField fieldEthIP = new OFMatchField(OFOXMFieldType.ETH_TYPE, Ethernet.TYPE_IPv4);
			OFMatchField fieldIP = new OFMatchField(OFOXMFieldType.IPV4_DST, virtualIP);

			ArrayList<OFMatchField> matchFieldsIP = new ArrayList<OFMatchField>();
			matchFieldsIP.add(fieldEthIP);
			matchFieldsIP.add(fieldIP);

			ofMatchIP.setMatchFields(matchFieldsIP);

			OFActionOutput ofActionOutput = new OFActionOutput();
			ofActionOutput.setPort(OFPort.OFPP_CONTROLLER);

			OFInstructionApplyActions ofActions = new OFInstructionApplyActions(Arrays.asList(ofActionOutput));

			SwitchCommands.installRule(sw, this.table, SwitchCommands.DEFAULT_PRIORITY, ofMatch, Arrays.asList(ofActions));

		}
		//ARP rules
		for (int virtualHost : this.instances.keySet()){
			OFMatch ofMatchARP = new OFMatch();
			OFMatchField fieldEthARP = new OFMatchField(OFOXMFieldType.ETH_TYPE, Ethernet.TYPE_ARP);
			OFMatchField fieldARP = new OFMatchField(OFOXMFieldType.ARP_TPA, virtualIP);

			ArrayList<OFMatchField> matchFieldsARP = new ArrayList<OFMatchField>();
			matchFieldsARP.add(fieldEthARP);
			matchFieldsARP.add(fieldARP);

			ofMatchIP.setMatchFields(matchFieldsIP);

			OFActionOutput ofActionOutput = new OFActionOutput();
			ofActionOutput.setPort(OFPort.OFPP_CONTROLLER);

			OFInstructionApplyActions ofActions = new OFInstructionApplyActions(Arrays.asList(ofActionOutput));

			SwitchCommands.installRule(sw, this.table, SwitchCommands.DEFAULT_PRIORITY, ofMatch, Arrays.asList(ofActions));

		}
		//Other rules
		OFMatch ofMatchDefault = new OFMatch();

		OFInstructionGotoTable ofInstructionGotoTable = new OFInstructionGotoTable();
		ofInstructionGotoTable.setTableId(L3Routing.table);

		ArrayList<OFInstruction> listOfInstructions = new ArrayList<OFInstruction>();
		listOfInstructions.add(ofInstructionGotoTable);

		SwitchCommands.installRule(sw, this.table, (short)(SwitchCommands.DEFAULT_PRIORITY - 1), ofMatchDefault, listOfInstructions);
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

		short etherType = ethPkt.getEtherType();
		if(etherType==Ethernet.TYPE_ARP) {
			ARP arpPkt = (ARP)ethPkt.getPayload();
			if(arpPkt.getOpCode()==ARP.OP_REQUEST) {
				int requestIp = IPv4.toIPv4Address(arpPkt.getTargetProtocolAddress());
				for(Integer vIp: this.instances.keySet())
					if(vIp==requestIp) {
						Ethernet ether = new Ethernet();
						ARP arp = new ARP();
						byte[] mac = instances.get(vIp).getVirtualMAC();
						
						arp.setHardwareType(ARP.HW_TYPE_ETHERNET);
						arp.setProtocolType(ARP.PROTO_TYPE_IP);
						arp.setHardwareAddressLength((byte)Ethernet.DATALAYER_ADDRESS_LENGTH);
						arp.setProtocolAddressLength((byte)4);
						arp.setOpCode(ARP.OP_REPLY);
						arp.setSenderHardwareAddress(mac);
						arp.setSenderProtocolAddress(vIp);
						arp.setTargetHardwareAddress(arpPkt.getSenderHardwareAddress());
						arp.setTargetProtocolAddress(arpPkt.getSenderProtocolAddress());
						
						ether.setEtherType(Ethernet.TYPE_ARP);
						ether.setDestinationMACAddress(ethPkt.getSourceMACAddress());
						ether.setSourceMACAddress(mac);
						ether.setPayload(arp);
						
						SwitchCommands.sendPacket(sw,(short)pktIn.getInPort(),ether);
					}					
			}	
		}



		//handle SYNs

		if(etherType==Ethernet.TYPE_IPv4) {
			IPv4 ipv4 = (IPv4)ethPkt.getPayload();
			if(ipv4.getProtocol() == IPv4.PROTOCOL_TCP) {
				TCP tcp = (TCP) ipv4.getPayload();
				if(tcp.getFlags()==TCP_FLAG_SYN) {
					int dstVIp = ipv4.getDestinationAddress();		
					if(instances.containsKey(dstVIp)) {
						LoadBalancerInstance instance = instances.get(dstVIp);
						int nxtIp = instance.getNextHostIP();
						
						OFMatch match = new OFMatch();
						match.setDataLayerType(OFMatch.ETH_TYPE_IPV4);
						match.setNetworkProtocol(OFMatch.IP_PROTO_TCP);
						match.setNetworkDestination(dstVIp);
						match.setNetworkSource(ipv4.getSourceAddress());
						match.setTransportDestination(tcp.getDestinationPort());
						match.setTransportSource(tcp.getSourcePort());
						
						OFAction setIP = new OFActionSetField(OFOXMFieldType.IPV4_DST,nxtIp);
						OFAction setMAC = new OFActionSetField(OFOXMFieldType.ETH_DST,getHostMACAddress(nxtIp));
						OFInstruction inst = new OFInstructionApplyActions(new ArrayList<OFAction>(Arrays.asList(setIP,setMAC)));
						
						OFInstruction instL3 = new  OFInstructionGotoTable(L3Routing.table);
						SwitchCommands.installRule(sw,this.table,(short)(SwitchCommands.DEFAULT_PRIORITY+1),match,new ArrayList<OFInstruction>(Arrays.asList(inst,instL3)));
						
						match = new OFMatch();
						match.setDataLayerType(OFMatch.ETH_TYPE_IPV4);
						match.setNetworkProtocol(OFMatch.IP_PROTO_TCP);
						match.setNetworkDestination(ipv4.getSourceAddress());
						match.setNetworkSource(nxtIp);
						match.setTransportDestination(tcp.getSourcePort());
						match.setTransportSource(tcp.getDestinationPort());
						
						setIP = new OFActionSetField(OFOXMFieldType.IPV4_SRC,dstVIp);
						setMAC = new OFActionSetField(OFOXMFieldType.ETH_SRC,instances.get(dstVIp).getVirtualMAC());
						inst = new OFInstructionApplyActions(new ArrayList<OFAction>(Arrays.asList(setIP,setMAC)));
						
						SwitchCommands.installRule(sw,this.table,(short)(SwitchCommands.DEFAULT_PRIORITY+1),match,new ArrayList<OFInstruction>(Arrays.asList(inst,instL3)));
					}
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
