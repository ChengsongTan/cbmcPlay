/*
 * Copyright (c) 2016-2019 Arm Limited
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/**
 * \file lan9118_drv.h
 * \brief Generic driver for LAN9118 Ethernet controller
 */

#ifndef __LAN9118_ETH_H__
#define __LAN9118_ETH_H__

#include <stdbool.h>
#include <stdint.h>
#include "los_config.h"
#include "los_event.h"
#include "los_interrupt.h"
#include "los_reg.h"
#include "stdio.h"
#include "los_reg.h"
#include "los_arch_context.h"
#include "netinet/if_ether.h"
#include "lwip/opt.h"
#include <lwip/netif.h>
#include "lwip/etharp.h"
#include "lwip/tcpip.h"
#include "lwip/mem.h"
#include <lwip/pbuf.h>
#include <lwip/netifapi.h>

#define LAN9118_BASE         0x40200000UL /* Ethernet LAN9118 BASE Address */
#define ETHERNET_IRQn        13           /* Ethernet Interrupt */
#define LAN9118_ETH_MTU_SIZE 1500U        /* Ethernet MTU */

/** LAN9118 device configuration structure */
struct lan9118_eth_dev_cfg_t {
    const uint32_t base; /*!< LAN9118 base address */
};

/** LAN9118 device data structure */
struct lan9118_eth_dev_data_t {
    uint32_t state;                      /*!< Indicates if the LAN9118 driver
                                              is initialized and enabled */
    void (*wait_ms)(uint32_t);           /*!< function pointer to system's millisec delay
                                         function, will be used for delays */
    uint32_t ongoing_packet_length;      /*!< size in bytes of the packet
                                                  is being sent */
    uint32_t ongoing_packet_length_sent; /*!< size in bytes of the packet
                                                  has been sent */
    uint32_t current_rx_size_words;      /*!< Data length in words,
                                                  currently is being read */
};

/** LAN9118 device structure */
struct lan9118_eth_dev_t {
    const struct lan9118_eth_dev_cfg_t* const cfg; /*!< configuration */
    struct lan9118_eth_dev_data_t* const data;     /*!< data */
};

/**
 * \brief Error code definitions
 *
 */
enum lan9118_error_t {
    LAN9118_ERROR_NONE = 0U,    /*!< no error */
    LAN9118_ERROR_TIMEOUT = 1U, /*!< timeout */
    LAN9118_ERROR_BUSY = 2U,    /*!< no error */
    LAN9118_ERROR_PARAM = 3U,   /*!< invalid parameter */
    LAN9118_ERROR_INTERNAL = 4U /*!< internal error */
};

/**
 * \brief Interrupt source definitions
 *
 */
enum lan9118_interrupt_source {
    LAN9118_INTERRUPT_GPIO0 = 0U,
    LAN9118_INTERRUPT_GPIO1 = 1U,
    LAN9118_INTERRUPT_GPIO2 = 2U,
    LAN9118_INTERRUPT_RX_STATUS_FIFO_LEVEL = 3U,
    LAN9118_INTERRUPT_RX_STATUS_FIFO_FULL = 4U,
    /* 5 Reserved according to Datasheet */
    LAN9118_INTERRUPT_RX_DROPPED_FRAME = 6U,
    LAN9118_INTERRUPT_TX_STATUS_FIFO_LEVEL = 7U,
    LAN9118_INTERRUPT_TX_STATUS_FIFO_FULL = 8U,
    LAN9118_INTERRUPT_TX_DATA_FIFO_AVAILABLE = 9U,
    LAN9118_INTERRUPT_TX_DATA_FIFO_OVERRUN = 10U,
    /* 11, 12 Reserved according to Datasheet */
    LAN9118_INTERRUPT_TX_ERROR = 13U,
    LAN9118_INTERRUPT_RX_ERROR = 14U,
    LAN9118_INTERRUPT_RX_WATCHDOG_TIMEOUT = 15U,
    LAN9118_INTERRUPT_TX_STATUS_OVERFLOW = 16U,
    LAN9118_INTERRUPT_TX_POWER_MANAGEMENT = 17U,
    LAN9118_INTERRUPT_PHY = 18U,
    LAN9118_INTERRUPT_GP_TIMER = 19U,
    LAN9118_INTERRUPT_RX_DMA = 20U,
    LAN9118_INTERRUPT_TX_IOC = 21U,
    /* 22 Reserved according to Datasheet*/
    LAN9118_INTERRUPT_RX_DROPPED_FRAME_HALF = 23U,
    LAN9118_INTERRUPT_RX_STOPPED = 24U,
    LAN9118_INTERRUPT_TX_STOPPED = 25U,
    /* 26 - 30 Reserved according to Datasheet*/
    LAN9118_INTERRUPT_SW = 31U
};

/**
 * \brief MAC register offset definitions
 *
 */
enum lan9118_mac_reg_offsets_t {
    LAN9118_MAC_REG_OFFSET_CR = 0x1U,
    LAN9118_MAC_REG_OFFSET_ADDRH = 0x2U,
    LAN9118_MAC_REG_OFFSET_ADDRL = 0x3U,
    LAN9118_MAC_REG_OFFSET_HASHH = 0x4U,
    LAN9118_MAC_REG_OFFSET_HASHL = 0x5U,
    LAN9118_MAC_REG_OFFSET_MII_ACC = 0x6U,
    LAN9118_MAC_REG_OFFSET_MII_DATA = 0x7U,
    LAN9118_MAC_REG_OFFSET_FLOW = 0x8U,
    LAN9118_MAC_REG_OFFSET_VLAN1 = 0x9U,
    LAN9118_MAC_REG_OFFSET_VLAN2 = 0xAU,
    LAN9118_MAC_REG_OFFSET_WUFF = 0xBU,
    LAN9118_MAC_REG_OFFSET_WUCSR = 0xCU,
};

/**
 * \brief PHY register offset definitions
 *
 */
enum phy_reg_offsets_t {
    LAN9118_PHY_REG_OFFSET_BCTRL = 0U,
    LAN9118_PHY_REG_OFFSET_BSTATUS = 1U,
    LAN9118_PHY_REG_OFFSET_ID1 = 2U,
    LAN9118_PHY_REG_OFFSET_ID2 = 3U,
    LAN9118_PHY_REG_OFFSET_ANEG_ADV = 4U,
    LAN9118_PHY_REG_OFFSET_ANEG_LPA = 5U,
    LAN9118_PHY_REG_OFFSET_ANEG_EXP = 6U,
    LAN9118_PHY_REG_OFFSET_MCONTROL = 17U,
    LAN9118_PHY_REG_OFFSET_MSTATUS = 18U,
    LAN9118_PHY_REG_OFFSET_CSINDICATE = 27U,
    LAN9118_PHY_REG_OFFSET_INTSRC = 29U,
    LAN9118_PHY_REG_OFFSET_INTMASK = 30U,
    LAN9118_PHY_REG_OFFSET_CS = 31U
};

/**
 * \brief FIFO Level Interrupt bit definitions
 *
 */
enum lan9118_fifo_level_irq_pos_t {
    LAN9118_FIFO_LEVEL_IRQ_RX_STATUS_POS = 0U,
    LAN9118_FIFO_LEVEL_IRQ_TX_STATUS_POS = 16U,
    LAN9118_FIFO_LEVEL_IRQ_TX_DATA_POS = 24U
};

/**
 * \brief FIFO Level Interrupt limits
 *
 */
#define LAN9118_FIFO_LEVEL_IRQ_MASK      0xFFU
#define LAN9118_FIFO_LEVEL_IRQ_LEVEL_MIN 0U
#define LAN9118_FIFO_LEVEL_IRQ_LEVEL_MAX LAN9118_FIFO_LEVEL_IRQ_MASK

/**
 * \brief Initializes LAN9118 Ethernet controller to a known default state:
 *          - device ID is checked
 *          - global interrupt is enabled, but all irq sources are disabled
 *          - all capabilities are advertised
 *              - 10Mbps able
 *              - 10Mbps with full duplex
 *              - 100Mbps Tx able
 *              - 100Mbps with full duplex
 *              - Symmetric Pause
 *              - Asymmetric Pause
 *          - Establish link enabled
 *          - Rx enabled
 *          - Tx enabled
 *        Init should be called prior to any other process and
 *        it's the caller's responsibility to follow proper call order.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 * \param[in] wait_ms_function function pointer to a millisec delay function
 *                             for proper timing of some processes
 *
 * \return error code /ref lan9118_error_t
 */
enum lan9118_error_t lan9118_init(const struct lan9118_eth_dev_t* dev, void (*wait_ms_function)(uint32_t));

/**
 * \brief Reads the MAC register.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 * \param[in] regoffset Register offset
 * \param[in, out] data Pointer to register will be read
 *
 * \return error code /ref lan9118_error_t
 */
enum lan9118_error_t lan9118_mac_regread(const struct lan9118_eth_dev_t* dev, enum lan9118_mac_reg_offsets_t regoffset,
                                         uint32_t* data);

/**
 * \brief Writes the MAC register.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 * \param[in] regoffset Register offset
 * \param[in] data Register value to write
 *
 * \return error code /ref lan9118_error_t
 */
enum lan9118_error_t lan9118_mac_regwrite(const struct lan9118_eth_dev_t* dev, enum lan9118_mac_reg_offsets_t regoffset,
                                          uint32_t data);

/**
 * \brief Reads the PHY register.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 * \param[in] regoffset Register offset
 * \param[out] data Register value is read
 *
 * \return error code /ref lan9118_error_t
 */
enum lan9118_error_t lan9118_phy_regread(const struct lan9118_eth_dev_t* dev, enum phy_reg_offsets_t regoffset, \
                                         uint32_t* data);

/**
 * \brief Writes the PHY register.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 * \param[in] regoffset Register offset
 * \param[in] data Register value to write
 *
 * \return error code /ref lan9118_error_t
 */
enum lan9118_error_t lan9118_phy_regwrite(const struct lan9118_eth_dev_t* dev, enum phy_reg_offsets_t regoffset, \
                                          uint32_t data);

/**
 * \brief Reads the Ethernet Controller's ID.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 *
 * \return ID number
 */
uint32_t lan9118_read_id(const struct lan9118_eth_dev_t* dev);

/**
 * \brief Initiates a soft reset, returns failure or success.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 *
 * \return error code /ref lan9118_error_t
 */
enum lan9118_error_t lan9118_soft_reset(const struct lan9118_eth_dev_t* dev);

/**
 * \brief Sets the Maximum Transmission Unit by Tx fifo size.
 *        Note: The MTU will be smaller than 512 bytes,
 *        which is used by the status.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 * \param[in] val Size of the fifo in kbytes
 *                \ref HW_CFG_REG_TX_FIFO_SIZE_MIN
 *                \ref HW_CFG_REG_TX_FIFO_SIZE_MAX
 */
void lan9118_set_txfifo(const struct lan9118_eth_dev_t* dev, uint32_t val);

/**
 * \brief Sets the FIFO level interrupt for a given source.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 * \param[in] irq_level_pos Bit position of the FIFO to set
 *            \ref lan9118_fifo_level_irq_pos_t
 * \param[in] level Level of the FIFO, when the FIFO used space is greater
 *             than this value, corresponding interrupt will be generated.
 *
 * \return error code /ref lan9118_error_t
 */
enum lan9118_error_t lan9118_set_fifo_level_irq(const struct lan9118_eth_dev_t* dev,
                                                enum lan9118_fifo_level_irq_pos_t irq_level_pos, uint32_t level);

/**
 * \brief Waits for EEPROM to be ready to use.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 *
 * \return error code /ref lan9118_error_t
 */
enum lan9118_error_t lan9118_wait_eeprom(const struct lan9118_eth_dev_t* dev);

/**
 * \brief Initializes irqs by clearing and disabling all interrupt sources
 *        and enable interrupts. Since all interrupt sources are disabled,
 *        interrupt won't be triggered, until interrupt sources won't be
 *        enabled by \ref lan9118_enable_interrupt
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 */
void lan9118_init_irqs(const struct lan9118_eth_dev_t* dev);

/**
 * \brief Checks PHY ID registers.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 *
 * \return error code /ref lan9118_error_t
 */
enum lan9118_error_t lan9118_check_phy(const struct lan9118_eth_dev_t* dev);

/**
 * \brief Resets PHY.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 *
 * \return error code /ref lan9118_error_t
 */
enum lan9118_error_t lan9118_reset_phy(const struct lan9118_eth_dev_t* dev);

/**
 * \brief Advertises all speeds and pauses capabilities.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 */
void lan9118_advertise_cap(const struct lan9118_eth_dev_t* dev);

/**
 * \brief Enables transmission.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 */
void lan9118_enable_xmit(const struct lan9118_eth_dev_t* dev);

/**
 * \brief Enables MAC Transmitter.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 */
void lan9118_enable_mac_xmit(const struct lan9118_eth_dev_t* dev);

/**
 * \brief Enables receiving.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 */
void lan9118_enable_mac_recv(const struct lan9118_eth_dev_t* dev);

/**
 * \brief Enables the given interrupt source.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 * \param[in] source Enum of the interrupt source.
 */
void lan9118_enable_interrupt(const struct lan9118_eth_dev_t* dev, enum lan9118_interrupt_source source);

/**
 * \brief Disables the given interrupt source.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 * \param[in] source Enum of the interrupt source.
 */
void lan9118_disable_interrupt(const struct lan9118_eth_dev_t* dev, enum lan9118_interrupt_source source);

/**
 * \brief Disables all interrupt sources.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 */
void lan9118_disable_all_interrupts(const struct lan9118_eth_dev_t* dev);

/**
 * \brief Clears the given interrupt source.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 * \param[in] source Enum of the interrupt source.
 */
void lan9118_clear_interrupt(const struct lan9118_eth_dev_t* dev, enum lan9118_interrupt_source source);

/**
 * \brief Clears all interrupt sources.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 */
void lan9118_clear_all_interrupts(const struct lan9118_eth_dev_t* dev);

/**
 * \brief Gets the status of the given interrupt source.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 * \param[in] source Enum of the interrupt source.
 *
 * \return non-zero if the given interrupt source is triggered, zero otherwise
 */
int lan9118_get_interrupt(const struct lan9118_eth_dev_t* dev, enum lan9118_interrupt_source source);

/**
 * \brief Establishes link
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 */
void lan9118_establish_link(const struct lan9118_eth_dev_t* dev);

/**
 * \brief Reads the Ethernet Controller's MAC address from its EEPROM.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 * \param[in,out] mac array will include the read MAC address in
 *                6 bytes hexadecimal format.
 *                It should be allocated by the caller to 6 bytes.
 *
 * \return error code /ref lan9118_error_t
 */
enum lan9118_error_t lan9118_read_mac_address(const struct lan9118_eth_dev_t* dev, char* mac);

/**
 * \brief Check device ID.
 *
 * \return error code /ref lan9118_error_t
 */
int lan9118_check_id(const struct lan9118_eth_dev_t* dev);

/**
 * \brief Sends data from the given buffer as an Ethernet packet.
 *        The full packet length must be specified at the beginning
 *        of a new packet transmission.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 * \param[in] total_payload_length Length of the ethernet payload.
 *            Should be equal to the sum of passed buffers within a packet.
 * \param[in] is_new_packet Should be set to true if the input buffer has to
 *            be sent as the start of a new packet or as a full packet.
 * \param[in] data Pointer to the data buffer to be sent.
 * \param[in] current_size Size of the data in bytes.
 *
 * \return error code /ref lan9118_error_t
 */
enum lan9118_error_t lan9118_send_by_chunks(const struct lan9118_eth_dev_t* dev, uint32_t total_payload_length,
                                            bool is_new_packet, const char* data, uint32_t current_size);

/**
 * \brief Reads an incoming Ethernet packet into the given buffer.
 *        Stops reading at packet border.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 * \param[in,out] data Pointer to a pre-allocated input buffer.
 *                     Allocating sufficient memory space is the caller's
 *                     responsibility, which is typically done by calling
 *                     \ref lan9118_peek_next_packet_size.
 * \param[in] dlen Length of the allocated data in bytes.
 *
 * \return Number of bytes read from the Rx FIFO into the given buffer.
 */
uint32_t lan9118_receive_by_chunks(const struct lan9118_eth_dev_t* dev, char* data, uint32_t dlen);

/**
 * \brief Get the used space of Rx fifo in bytes.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 *
 * \return Data received and waiting for read in bytes
 */
uint32_t lan9118_get_rxfifo_data_used_space(const struct lan9118_eth_dev_t* dev);

/**
 * \brief Gets the size of next unread packet in Rx buffer, using the peak
 *        register, which is not destructive so can be read asynchronously.
 *        Warning: In case of heavy receiving loads, this register may not
 *        be in perfect sync.
 *
 * \param[in] dev Ethernet device structure \ref lan9118_eth_dev_t
 *
 * \return Size of the next packet in bytes, read from the Rx Peek register.
 */
uint32_t lan9118_peek_next_packet_size(const struct lan9118_eth_dev_t* dev);

/** \brief  Allocates a buf and returns the data from the incoming
 * packet.
 *
 *  \return a buf filled with the received packet
 * (including MAC header)
 */
struct pbuf* LowLevelInput(void);

/**
 * \brief Sends the packet over the link
 *
 * That can not be called from an interrupt context.
 *
 * @param netif a pre-allocated netif structure
 * @param buf  Packet to be send
 * @return     True if the packet was send successfully, False otherwise
 */
err_t Lan9118LinkOut(struct netif* netif, struct pbuf* buf);

/** \brief  Packet reception task
 *
 * This task is called when a packet is received. It will
 * pass the packet to the Network Stack.
 */
void Lan9118PacketRx(void);

/** \brief  interrupt called
 *
 * This task is handle rx data.
 */
void EthernetReceiveHandler(void);

/**
 * \brief In this function, the hardware should be initialized.
 * Called from EthernetifInit().
 *
 * @param netif the already initialized lwip network interface structure
 *        for this ethernetif
 */
void LowLevelInit(struct netif* netif);

/**
 * \brief Init net config
 *
 * This task is called when netif_add()
 */
err_t EthernetifInit(struct netif* netif);

/**
 * \brief Init Lan9118 net
 *
 */
void Lan9118NetInit(void);

/**
 * \brief Init net
 *
 */
void NetInit(void);

#endif /* __LAN9118_ETH_H__ */
