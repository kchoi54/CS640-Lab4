package edu.wisc.cs.sdn.apps.l3routing;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.LinkedList;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.Queue;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import edu.wisc.cs.sdn.apps.util.Host;
import edu.wisc.cs.sdn.apps.util.SwitchCommands;

import net.floodlightcontroller.core.IFloodlightProviderService;
import net.floodlightcontroller.core.IOFSwitch;
import net.floodlightcontroller.core.IOFSwitch.PortChangeType;
import net.floodlightcontroller.core.IOFSwitchListener;
import net.floodlightcontroller.core.ImmutablePort;
import net.floodlightcontroller.core.module.FloodlightModuleContext;
import net.floodlightcontroller.core.module.FloodlightModuleException;
import net.floodlightcontroller.core.module.IFloodlightModule;
import net.floodlightcontroller.core.module.IFloodlightService;
import net.floodlightcontroller.devicemanager.IDevice;
import net.floodlightcontroller.devicemanager.IDeviceListener;
import net.floodlightcontroller.devicemanager.IDeviceService;
import net.floodlightcontroller.linkdiscovery.ILinkDiscoveryListener;
import net.floodlightcontroller.linkdiscovery.ILinkDiscoveryService;
import net.floodlightcontroller.routing.Link;
import net.floodlightcontroller.packet.IPv4;

import org.openflow.util.HexString;
import org.openflow.protocol.OFMatch;
import org.openflow.protocol.action.OFAction;
import org.openflow.protocol.action.OFActionOutput;
import org.openflow.protocol.instruction.OFInstruction;
import org.openflow.protocol.instruction.OFInstructionApplyActions;

public class L3Routing implements IFloodlightModule, IOFSwitchListener, 
		ILinkDiscoveryListener, IDeviceListener
{
	public static final String MODULE_NAME = L3Routing.class.getSimpleName();
	
	// Interface to the logging system
	private static Logger log = LoggerFactory.getLogger(MODULE_NAME);
	
	// Interface to Floodlight core for interacting with connected switches
	private IFloodlightProviderService floodlightProv;

	// Interface to link discovery service
	private ILinkDiscoveryService linkDiscProv;

	// Interface to device manager service
	private IDeviceService deviceProv;
	
	// Switch table in which rules should be installed
	public static byte table;
	
	// Map of hosts to devices
	private Map<IDevice,Host> knownHosts;

	/**
	 * Loads dependencies and initializes data structures.
	 */
	@Override
	public void init(FloodlightModuleContext context)
			throws FloodlightModuleException 
	{
		log.info(String.format("Initializing %s...", MODULE_NAME));
		Map<String,String> config = context.getConfigParams(this);
		table = Byte.parseByte(config.get("table"));
		
		this.floodlightProv = context.getServiceImpl(
				IFloodlightProviderService.class);
		this.linkDiscProv = context.getServiceImpl(ILinkDiscoveryService.class);
		this.deviceProv = context.getServiceImpl(IDeviceService.class);
		
		this.knownHosts = new ConcurrentHashMap<IDevice,Host>();
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
		this.linkDiscProv.addListener(this);
		this.deviceProv.addListener(this);
		
		/*********************************************************************/
		/* TODO: Initialize variables or perform startup tasks, if necessary */

		/*********************************************************************/
	}
	
	/**
	 * Get a list of all known hosts in the network.
	 */
	private Collection<Host> getHosts()
	{ return this.knownHosts.values(); }

	/**
	 * Get a map of all known hosts in the network. SwitchID is used as the key if the host is connected to a switch.
	 * @author kj
	 */
	private Map<Long, List<Host>> getHostsAsMap()
    {
		Collection<Host> hosts = this.getHosts();
		Map<Long, List<Host>> hostMap = new ConcurrentHashMap<Long, List<Host>>();

		for (IOFSwitch sw : this.getSwitches().values())
		{ hostMap.put(sw.getId(), new ArrayList<Host>()); }

		for (Host host : hosts)
		{
			if (!host.isAttachedToSwitch())
			{ continue; }

			hostMap.get(host.getSwitch().getId()).add(host);
		}
		
		return hostMap;
	}

	/**
	 * Get a map of all active switches in the network. Switch DPID is used as
	 * the key.
	 */
	private Map<Long, IOFSwitch> getSwitches()
	{ return floodlightProv.getAllSwitchMap(); }

	/**
	 * Get a list of all active links in the network.
	 */
	private Collection<Link> getLinks()
	{ return linkDiscProv.getLinks().keySet(); }

	/**
	 * Get a map of all active links in the network. Source Switch DPID is used as the key.
	 * @author kj
	 */
	private Map<Long, List<Link>> getLinksAsMap() 
	{
		Map<Long, List<Link>> links = new ConcurrentHashMap<Long, List<Link>>();

		for (Link lk : this.getLinks())
		{ 
			Long src = lk.getSrc();
			
			if (!links.containsKey(src))
			{ links.put(src, new ArrayList<Link>()); }

			links.get(src).add(lk);
		}

		return links;
	}

	/**
	 * Calculate shortest path using bellman-ford.
	 * Forwarding port to each swithes is returned as the value.
	 * @author kj
	 */
	private Map<Long, Integer> findBestRoutes(IOFSwitch rootSwitch)
	{	
		Collection<IOFSwitch> vertices = this.getSwitches().values();
		Map<Long, List<Link>> edges = this.getLinksAsMap();

		//System.out.println("vertices: "+vertices);
		//System.out.println("edges: "+edges);

		Map<Long, Integer> distance = new ConcurrentHashMap<Long, Integer>(); //distance vector
		Map<Long, Integer> nextHop = new ConcurrentHashMap<Long, Integer>(); //nextHop with port as value
		
		Long root = rootSwitch.getId();
		//initialize distance of all switches as infinite
		for (IOFSwitch sw : vertices)
		{ distance.put(sw.getId(), Integer.MAX_VALUE); }
		distance.put(root, 0); //distance to itself is zero

		//n-1 iterations
		for(int i=0; i<vertices.size()-1; i++)
		{
			for (IOFSwitch sw : vertices)
			{
				Long src = sw.getId();
				int newDist = distance.get(src);
				if (!edges.containsKey(src))
				{ continue; }
				for (Link lk : edges.get(src))
				{
					Long dst = lk.getDst();
					int currDist = distance.get(dst);

					//update distance if new link is shorter to the root
					if (newDist < currDist)
					{ 
						distance.put(dst, newDist+1); 

						//update nextHop
						if (src == root)
						{ nextHop.put(dst, lk.getSrcPort()); }
						else
						{ nextHop.put(dst, nextHop.get(src)); }
					}
				}
			}
		}

		return nextHop;
	}

	/**
	 * Generate OFMatch object from ip address
	 * @author kj
	 */
	private OFMatch matchFromHost(Host host)
	{
		OFMatch match = new OFMatch();
		match.setDataLayerType(OFMatch.ETH_TYPE_IPV4);
		match.setNetworkDestination(host.getIPv4Address());
		return match;
	}

	/**
	 * Install swicth-to-host.
	 * @author kj
	 */
	private void installRule()
	{
		for (IOFSwitch sw : this.getSwitches().values())
		{ this.installPath(sw); }
	}

	/**
	 * Install path to given switch using shortest path routes.
	 * @author kj
	 */
	private void installPath(IOFSwitch sw)
	{
		Map<Long, IOFSwitch> switches = this.getSwitches();
		Map<Long, List<Host>> hostMap = this.getHostsAsMap();

		//calculate shortest path to all other switches
		Map<Long, Integer> routes = findBestRoutes(sw);
		// System.out.println("Bellman-Ford:");
		// System.out.println("	root: " + sw.getId());
		// System.out.println("	routes<DstIP, outPort>: "+routes);
		
		//add switch-to-switch rule
		for (Map.Entry<Long, Integer> entry : routes.entrySet())
		{
			OFAction action = new OFActionOutput(entry.getValue());
			OFInstruction instruction = new OFInstructionApplyActions(Arrays.asList(action));

			for(Host h : hostMap.get(entry.getKey()))
			{
				OFMatch match = matchFromHost(h);
				SwitchCommands.installRule(sw, this.table, SwitchCommands.DEFAULT_PRIORITY, match, Arrays.asList(instruction));
				log.info(String.format("Rule Installed: s%d:%d -> %s", sw.getId(), entry.getValue(), IPv4.fromIPv4Address(h.getIPv4Address())));
			}
		}

		//add switch-to-host rule
		for(Host h : hostMap.get(sw.getId()))
		{
			OFMatch match = matchFromHost(h);
			OFAction actionToHost = new OFActionOutput(h.getPort());
			OFInstruction instructionToHost = new OFInstructionApplyActions(Arrays.asList(actionToHost));
			SwitchCommands.installRule(h.getSwitch(), this.table, SwitchCommands.DEFAULT_PRIORITY, match, Arrays.asList(instructionToHost));
			log.info(String.format("Rule Installed: s%d:%d -> %s", h.getSwitch().getId(), h.getPort(), IPv4.fromIPv4Address(h.getIPv4Address())));
		}
	}

	/**
	 * Remove any rule containing given host.
	 * @author kj
	 */
	private void removeRule(Host host)
	{
		for (IOFSwitch sw : this.getSwitches().values()) 
		{ SwitchCommands.removeRules(sw, this.table, matchFromHost(host)); }
	}

	/**
	 * Remove and reinstall all rules.
	 * @author kj
	 */
	private void updateRule()
	{
		//remove all rules
		for(Host h : this.getHosts())
		{ this.removeRule(h); }
		
		//install rules
		this.installRule();
	}


	/**
	 * Event handler called when a host joins the network.
	 * @param device information about the host
	 */
	@Override
	public void deviceAdded(IDevice device) 
	{
		Host host = new Host(device, this.floodlightProv);
		// We only care about a new host if we know its IP
		if (host.getIPv4Address() != null)
		{
			log.info(String.format("Host %s added", host.getName()));
			this.knownHosts.put(device, host);
			
			/*****************************************************************/
			/* TODO: Update routing: add rules to route to new host          */

			// String hostStr = "    Hosts: ";
			// for (Host h : this.getHosts())
			// { hostStr += h.getName()+" "; }
			// System.out.println(hostStr+this.getHosts().size()+" hosts");
			
			// String swStr = "    Switches: ";
			// for(IOFSwitch sw : this.getSwitches().values())
			// { swStr += "s"+sw.getId()+" "; }
			// System.out.println(swStr+this.getSwitches().values().size()+" switches");
			
			// System.out.println("    Links: " + this.getLinks().size()+" links");
			
			this.installRule();
			/*****************************************************************/
		}
	}

	/**
	 * Event handler called when a host is no longer attached to a switch.
	 * @param device information about the host
	 */
	@Override
	public void deviceRemoved(IDevice device) 
	{
		Host host = this.knownHosts.get(device);
		if (null == host)
		{ return; }
		this.knownHosts.remove(device);
		
		log.info(String.format("Host %s is no longer attached to a switch", 
				host.getName()));
		
		/*********************************************************************/
		/* TODO: Update routing: remove rules to route to host               */
		this.removeRule(host);
		this.installRule();
		/*********************************************************************/
	}

	/**
	 * Event handler called when a host moves within the network.
	 * @param device information about the host
	 */
	@Override
	public void deviceMoved(IDevice device) 
	{
		Host host = this.knownHosts.get(device);
		if (null == host)
		{
			host = new Host(device, this.floodlightProv);
			this.knownHosts.put(device, host);
		}
		
		if (!host.isAttachedToSwitch())
		{
			this.deviceRemoved(device);
			return;
		}
		log.info(String.format("Host %s moved to s%d:%d", host.getName(),
				host.getSwitch().getId(), host.getPort()));
		
		/*********************************************************************/
		/* TODO: Update routing: change rules to route to host               */
		this.removeRule(host);
		this.installRule();
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
		
		/*********************************************************************/
		/* TODO: Update routing: change routing rules for all hosts          */
		this.installRule();
		/*********************************************************************/
	}

	/**
	 * Event handler called when a switch leaves the network.
	 * @param DPID for the switch
	 */
	@Override
	public void switchRemoved(long switchId) 
	{
		IOFSwitch sw = this.floodlightProv.getSwitch(switchId);
		log.info(String.format("Switch s%d removed", switchId));
		
		/*********************************************************************/
		/* TODO: Update routing: change routing rules for all hosts          */
		for (Host h : this.getHostsAsMap().get(switchId))
		{
			this.removeRule(h);
		}

		this.updateRule();
		/*********************************************************************/
	}

	/**
	 * Event handler called when multiple links go up or down.
	 * @param updateList information about the change in each link's state
	 */
	@Override
	public void linkDiscoveryUpdate(List<LDUpdate> updateList) 
	{
		for (LDUpdate update : updateList)
		{
			// If we only know the switch & port for one end of the link, then
			// the link must be from a switch to a host
			if (0 == update.getDst())
			{
				log.info(String.format("Link s%s:%d -> host updated", 
					update.getSrc(), update.getSrcPort()));
			}
			// Otherwise, the link is between two switches
			else
			{
				log.info(String.format("Link s%s:%d -> s%s:%d updated", 
					update.getSrc(), update.getSrcPort(),
					update.getDst(), update.getDstPort()));
			}
		}
		
		/*********************************************************************/
		/* TODO: Update routing: change routing rules for all hosts          */
		this.installRule();
		/*********************************************************************/
	}

	/**
	 * Event handler called when link goes up or down.
	 * @param update information about the change in link state
	 */
	@Override
	public void linkDiscoveryUpdate(LDUpdate update) 
	{ this.linkDiscoveryUpdate(Arrays.asList(update)); }
	
	/**
	 * Event handler called when the IP address of a host changes.
	 * @param device information about the host
	 */
	@Override
	public void deviceIPV4AddrChanged(IDevice device) 
	{ this.deviceAdded(device); }

	/**
	 * Event handler called when the VLAN of a host changes.
	 * @param device information about the host
	 */
	@Override
	public void deviceVlanChanged(IDevice device) 
	{ /* Nothing we need to do, since we're not using VLANs */ }
	
	/**
	 * Event handler called when the controller becomes the master for a switch.
	 * @param DPID for the switch
	 */
	@Override
	public void switchActivated(long switchId) 
	{ /* Nothing we need to do, since we're not switching controller roles */ }

	/**
	 * Event handler called when some attribute of a switch changes.
	 * @param DPID for the switch
	 */
	@Override
	public void switchChanged(long switchId) 
	{ /* Nothing we need to do */ }
	
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
	{ /* Nothing we need to do, since we'll get a linkDiscoveryUpdate event */ }

	/**
	 * Gets a name for this module.
	 * @return name for this module
	 */
	@Override
	public String getName() 
	{ return this.MODULE_NAME; }

	/**
	 * Check if events must be passed to another module before this module is
	 * notified of the event.
	 */
	@Override
	public boolean isCallbackOrderingPrereq(String type, String name) 
	{ return false; }

	/**
	 * Check if events must be passed to another module after this module has
	 * been notified of the event.
	 */
	@Override
	public boolean isCallbackOrderingPostreq(String type, String name) 
	{ return false; }
	
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
		floodlightService.add(ILinkDiscoveryService.class);
		floodlightService.add(IDeviceService.class);
		return floodlightService;
	}
}
