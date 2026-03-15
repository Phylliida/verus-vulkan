use ash::{vk, Entry, Instance, Device};
use ash::khr;
use std::ffi::CString;

/// Holds all ash loaders for real Vulkan calls.
/// Users create this directly and pass `&VulkanContext` to FFI functions
/// (via the `VkCtx` opaque wrapper visible to Verus).
pub struct VulkanContext {
    pub entry: Entry,
    pub instance: Instance,
    pub physical_device: vk::PhysicalDevice,
    pub device: Device,
    pub swapchain_loader: khr::swapchain::Device,
    pub surface_loader: khr::surface::Instance,
}

impl VulkanContext {
    /// Create a VulkanContext: loads Vulkan, creates instance + device.
    ///
    /// # Safety
    /// Caller must ensure Vulkan is available and queue_family_index is valid.
    pub unsafe fn new(
        app_name: &str,
        enable_validation: bool,
        surface_extensions: &[*const i8],
        device_extensions: &[*const i8],
        queue_family_index: u32,
    ) -> Self {
        // 1. Load Vulkan
        let entry = Entry::load().expect("Failed to load Vulkan");

        // 2. Create Instance
        let app_name_c = CString::new(app_name).unwrap();
        let engine_name = CString::new("verus-vulkan").unwrap();
        let app_info = vk::ApplicationInfo::default()
            .application_name(&app_name_c)
            .engine_name(&engine_name)
            .application_version(vk::make_api_version(0, 1, 0, 0))
            .engine_version(vk::make_api_version(0, 1, 0, 0))
            .api_version(vk::make_api_version(0, 1, 2, 0));

        let validation_layer = CString::new("VK_LAYER_KHRONOS_validation").unwrap();
        let layer_names: Vec<*const i8> = if enable_validation {
            vec![validation_layer.as_ptr()]
        } else {
            vec![]
        };

        // Collect instance extensions — start with caller-provided surface extensions,
        // then add portability enumeration on macOS for MoltenVK compatibility.
        let mut all_instance_extensions: Vec<*const i8> = surface_extensions.to_vec();
        #[cfg(target_os = "macos")]
        {
            all_instance_extensions.push(ash::vk::KHR_PORTABILITY_ENUMERATION_NAME.as_ptr());
        }

        let mut instance_flags = vk::InstanceCreateFlags::empty();
        #[cfg(target_os = "macos")]
        {
            instance_flags |= vk::InstanceCreateFlags::ENUMERATE_PORTABILITY_KHR;
        }

        let instance_create_info = vk::InstanceCreateInfo::default()
            .application_info(&app_info)
            .enabled_layer_names(&layer_names)
            .enabled_extension_names(&all_instance_extensions)
            .flags(instance_flags);

        // Try creating instance; if validation layers are missing, retry without them
        let instance = match entry.create_instance(&instance_create_info, None) {
            Ok(inst) => inst,
            Err(vk::Result::ERROR_LAYER_NOT_PRESENT) if enable_validation => {
                eprintln!("Validation layers not found, continuing without validation");
                let no_layers: Vec<*const i8> = vec![];
                let fallback = vk::InstanceCreateInfo::default()
                    .application_info(&app_info)
                    .enabled_layer_names(&no_layers)
                    .enabled_extension_names(&all_instance_extensions)
                    .flags(instance_flags);
                entry.create_instance(&fallback, None)
                    .expect("Failed to create Vulkan instance")
            }
            Err(e) => panic!("Failed to create Vulkan instance: {:?}", e),
        };

        // 3. Pick first physical device
        let physical_devices = instance
            .enumerate_physical_devices()
            .expect("Failed to enumerate physical devices");
        assert!(!physical_devices.is_empty(), "No Vulkan physical devices found");
        let physical_device = physical_devices[0];

        // 4. Create logical device with one queue
        let queue_priorities = [1.0_f32];
        let queue_create_info = vk::DeviceQueueCreateInfo::default()
            .queue_family_index(queue_family_index)
            .queue_priorities(&queue_priorities);
        let queue_create_infos = [queue_create_info];

        let features = vk::PhysicalDeviceFeatures::default();

        // Enable timeline semaphore via Vulkan 1.2 features
        let mut vk12_features = vk::PhysicalDeviceVulkan12Features::default()
            .timeline_semaphore(true);

        // Auto-add portability subset on macOS for MoltenVK compatibility
        let mut all_device_extensions: Vec<*const i8> = device_extensions.to_vec();
        #[cfg(target_os = "macos")]
        {
            all_device_extensions.push(c"VK_KHR_portability_subset".as_ptr());
        }

        let device_create_info = vk::DeviceCreateInfo::default()
            .queue_create_infos(&queue_create_infos)
            .enabled_extension_names(&all_device_extensions)
            .enabled_features(&features)
            .push_next(&mut vk12_features);

        let device = instance
            .create_device(physical_device, &device_create_info, None)
            .expect("Failed to create Vulkan device");

        // 5. Create swapchain loader
        let swapchain_loader = khr::swapchain::Device::new(&instance, &device);

        // 6. Create surface loader
        let surface_loader = khr::surface::Instance::new(&entry, &instance);

        VulkanContext {
            entry,
            instance,
            physical_device,
            device,
            swapchain_loader,
            surface_loader,
        }
    }

    /// Destroy in reverse order. Call before dropping.
    pub unsafe fn destroy(&mut self) {
        self.device.device_wait_idle().expect("device_wait_idle failed");
        self.device.destroy_device(None);
        self.instance.destroy_instance(None);
    }

}
